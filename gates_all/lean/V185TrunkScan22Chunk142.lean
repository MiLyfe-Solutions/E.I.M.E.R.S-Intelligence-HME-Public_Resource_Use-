import V185TrunkScan22Chunk141

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1270186 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1270186 : Nat := 118140960795 + 1270186 * 2 ^ 59
def prefixEnd_1270186 : Nat := 4983230072969 + 3 ^ 40 * 1270186 * 2
def baseEnd_1270186 : Nat := 434810625741248416755685

theorem tailTrace_1270186 : CollatzResearch.WordTrace tailWord_1270186 prefixEnd_1270186 434810625741248416755685 := by
  unfold tailWord_1270186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11581872344085131835797603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30884992917560351562126941 11581872344085131835797603)
  ·
    refine ⟨17372808516127697753696405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11581872344085131835797603 17372808516127697753696405)
    ·
      refine ⟨814350399193485832204519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17372808516127697753696405 814350399193485832204519)
      ·
        refine ⟨1221525598790228748306779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814350399193485832204519 1221525598790228748306779)
        ·
          refine ⟨1832288398185343122460169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221525598790228748306779 1832288398185343122460169)
          ·
            refine ⟨1374216298639007341845127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1832288398185343122460169 1374216298639007341845127)
            ·
              refine ⟨2061324447958511012767691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374216298639007341845127 2061324447958511012767691)
              ·
                refine ⟨3091986671937766519151537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061324447958511012767691 3091986671937766519151537)
                ·
                  refine ⟨2318990003953324889363653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3091986671937766519151537 2318990003953324889363653)
                  ·
                    refine ⟨434810625741248416755685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2318990003953324889363653 434810625741248416755685)
                    ·
                      rfl

theorem cell22_1270186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1270186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270186 prefixEnd_1270186 := by exact prefixLift 1270186
  have htrace : WordTrace (prefixWord ++ tailWord_1270186) baseStart_1270186 baseEnd_1270186 := by
    simpa [prefixWord, tailWord_1270186, baseEnd_1270186] using wordTrace_append hprefix tailTrace_1270186
  have hstable : (prefixWord ++ tailWord_1270186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270186).length < 2 ^ (prefixWord ++ tailWord_1270186).sum := by decide
  have hdescent : baseEnd_1270186 < baseStart_1270186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270274 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1270274 : Nat := 118140960795 + 1270274 * 2 ^ 59
def prefixEnd_1270274 : Nat := 4983230072969 + 3 ^ 40 * 1270274 * 2
def baseEnd_1270274 : Nat := 144946916646548506851805

theorem tailTrace_1270274 : CollatzResearch.WordTrace tailWord_1270274 prefixEnd_1270274 144946916646548506851805 := by
  unfold tailWord_1270274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11582674750005429593098469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30887132666681145581595917 11582674750005429593098469)
  ·
    refine ⟨2171751515626018048705963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11582674750005429593098469 2171751515626018048705963)
    ·
      refine ⟨3257627273439027073058945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171751515626018048705963 3257627273439027073058945)
      ·
        refine ⟨2443220455079270304794209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3257627273439027073058945 2443220455079270304794209)
        ·
          refine ⟨1832415341309452728595657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2443220455079270304794209 1832415341309452728595657)
          ·
            refine ⟨1374311505982089546446743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1832415341309452728595657 1374311505982089546446743)
            ·
              refine ⟨2061467258973134319670115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374311505982089546446743 2061467258973134319670115)
              ·
                refine ⟨3092200888459701479505173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061467258973134319670115 3092200888459701479505173)
                ·
                  refine ⟨144946916646548506851805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3092200888459701479505173 144946916646548506851805)
                  ·
                    rfl

theorem cell22_1270274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1270274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270274 prefixEnd_1270274 := by exact prefixLift 1270274
  have htrace : WordTrace (prefixWord ++ tailWord_1270274) baseStart_1270274 baseEnd_1270274 := by
    simpa [prefixWord, tailWord_1270274, baseEnd_1270274] using wordTrace_append hprefix tailTrace_1270274
  have hstable : (prefixWord ++ tailWord_1270274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270274).length < 2 ^ (prefixWord ++ tailWord_1270274).sum := by decide
  have hdescent : baseEnd_1270274 < baseStart_1270274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270330 : List Nat := [3, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_1270330 : Nat := 118140960795 + 1270330 * 2 ^ 59
def prefixEnd_1270330 : Nat := 4983230072969 + 3 ^ 40 * 1270330 * 2
def baseEnd_1270330 : Nat := 144953306628026680385081

theorem tailTrace_1270330 : CollatzResearch.WordTrace tailWord_1270330 prefixEnd_1270330 144953306628026680385081 := by
  unfold tailWord_1270330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11583185371954709984108111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30888494325212559957621629 11583185371954709984108111)
  ·
    refine ⟨17374778057932064976162167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11583185371954709984108111 17374778057932064976162167)
    ·
      refine ⟨26062167086898097464243251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17374778057932064976162167 26062167086898097464243251)
      ·
        refine ⟨39093250630347146196364877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26062167086898097464243251 39093250630347146196364877)
        ·
          refine ⟨14659968986380179823636829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39093250630347146196364877 14659968986380179823636829)
          ·
            refine ⟨5497488369892567433863811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14659968986380179823636829 5497488369892567433863811)
            ·
              refine ⟨8246232554838851150795717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497488369892567433863811 8246232554838851150795717)
              ·
                refine ⟨1546168604032284590774197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8246232554838851150795717 1546168604032284590774197)
                ·
                  refine ⟨144953306628026680385081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1546168604032284590774197 144953306628026680385081)
                  ·
                    rfl

theorem cell22_1270330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_1270330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270330 prefixEnd_1270330 := by exact prefixLift 1270330
  have htrace : WordTrace (prefixWord ++ tailWord_1270330) baseStart_1270330 baseEnd_1270330 := by
    simpa [prefixWord, tailWord_1270330, baseEnd_1270330] using wordTrace_append hprefix tailTrace_1270330
  have hstable : (prefixWord ++ tailWord_1270330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270330).length < 2 ^ (prefixWord ++ tailWord_1270330).sum := by decide
  have hdescent : baseEnd_1270330 < baseStart_1270330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270360 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_1270360 : Nat := 118140960795 + 1270360 * 2 ^ 59
def prefixEnd_1270360 : Nat := 4983230072969 + 3 ^ 40 * 1270360 * 2
def baseEnd_1270360 : Nat := 434870189497169962905151

theorem tailTrace_1270360 : CollatzResearch.WordTrace tailWord_1270360 prefixEnd_1270360 434870189497169962905151 := by
  unfold tailWord_1270360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23166917838855077530012267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30889223785140103373349689 23166917838855077530012267)
  ·
    refine ⟨34750376758282616295018401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23166917838855077530012267 34750376758282616295018401)
    ·
      refine ⟨26062782568711962221263801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34750376758282616295018401 26062782568711962221263801)
      ·
        refine ⟨19547086926533971665947851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26062782568711962221263801 19547086926533971665947851)
        ·
          refine ⟨29320630389800957498921777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19547086926533971665947851 29320630389800957498921777)
          ·
            refine ⟨21990472792350718124191333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29320630389800957498921777 21990472792350718124191333)
            ·
              refine ⟨4123213648565759648285875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21990472792350718124191333 4123213648565759648285875)
              ·
                refine ⟨6184820472848639472428813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123213648565759648285875 6184820472848639472428813)
                ·
                  refine ⟨2319307677318239802160805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6184820472848639472428813 2319307677318239802160805)
                  ·
                    refine ⟨434870189497169962905151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2319307677318239802160805 434870189497169962905151)
                    ·
                      rfl

theorem cell22_1270360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_1270360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270360 prefixEnd_1270360 := by exact prefixLift 1270360
  have htrace : WordTrace (prefixWord ++ tailWord_1270360) baseStart_1270360 baseEnd_1270360 := by
    simpa [prefixWord, tailWord_1270360, baseEnd_1270360] using wordTrace_append hprefix tailTrace_1270360
  have hstable : (prefixWord ++ tailWord_1270360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270360).length < 2 ^ (prefixWord ++ tailWord_1270360).sum := by decide
  have hdescent : baseEnd_1270360 < baseStart_1270360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270405 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_1270405 : Nat := 118140960795 + 1270405 * 2 ^ 59
def prefixEnd_1270405 : Nat := 4983230072969 + 3 ^ 40 * 1270405 * 2
def baseEnd_1270405 : Nat := 434885593916804845530013

theorem tailTrace_1270405 : CollatzResearch.WordTrace tailWord_1270405 prefixEnd_1270405 434885593916804845530013 := by
  unfold tailWord_1270405
  simp only [CollatzResearch.WordTrace]
  refine ⟨46335476962547127745412669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30890317975031418496941779 46335476962547127745412669)
  ·
    refine ⟨17375803860955172904529751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46335476962547127745412669 17375803860955172904529751)
    ·
      refine ⟨26063705791432759356794627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17375803860955172904529751 26063705791432759356794627)
      ·
        refine ⟨39095558687149139035191941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26063705791432759356794627 39095558687149139035191941)
        ·
          refine ⟨7330417253840463569098489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39095558687149139035191941 7330417253840463569098489)
          ·
            refine ⟨5497812940380347676823867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7330417253840463569098489 5497812940380347676823867)
            ·
              refine ⟨8246719410570521515235801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497812940380347676823867 8246719410570521515235801)
              ·
                refine ⟨6185039557927891136426851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8246719410570521515235801 6185039557927891136426851)
                ·
                  refine ⟨9277559336891836704640277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6185039557927891136426851 9277559336891836704640277)
                  ·
                    refine ⟨434885593916804845530013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9277559336891836704640277 434885593916804845530013)
                    ·
                      rfl

theorem cell22_1270405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_1270405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270405 prefixEnd_1270405 := by exact prefixLift 1270405
  have htrace : WordTrace (prefixWord ++ tailWord_1270405) baseStart_1270405 baseEnd_1270405 := by
    simpa [prefixWord, tailWord_1270405, baseEnd_1270405] using wordTrace_append hprefix tailTrace_1270405
  have hstable : (prefixWord ++ tailWord_1270405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270405).length < 2 ^ (prefixWord ++ tailWord_1270405).sum := by decide
  have hdescent : baseEnd_1270405 < baseStart_1270405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270450 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1270450 : Nat := 118140960795 + 1270450 * 2 ^ 59
def prefixEnd_1270450 : Nat := 4983230072969 + 3 ^ 40 * 1270450 * 2
def baseEnd_1270450 : Nat := 434900998336439728154875

theorem tailTrace_1270450 : CollatzResearch.WordTrace tailWord_1270450 prefixEnd_1270450 434900998336439728154875 := by
  unfold tailWord_1270450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584279561846025107700201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30891412164922733620533869 11584279561846025107700201)
  ·
    refine ⟨8688209671384518830775151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11584279561846025107700201 8688209671384518830775151)
    ·
      refine ⟨13032314507076778246162727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8688209671384518830775151 13032314507076778246162727)
      ·
        refine ⟨19548471760615167369244091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13032314507076778246162727 19548471760615167369244091)
        ·
          refine ⟨29322707640922751053866137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19548471760615167369244091 29322707640922751053866137)
          ·
            refine ⟨21992030730692063290399603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29322707640922751053866137 21992030730692063290399603)
            ·
              refine ⟨32988046096038094935599405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21992030730692063290399603 32988046096038094935599405)
              ·
                refine ⟨12370517286014285600849777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32988046096038094935599405 12370517286014285600849777)
                ·
                  refine ⟨9277887964510714200637333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12370517286014285600849777 9277887964510714200637333)
                  ·
                    refine ⟨434900998336439728154875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9277887964510714200637333 434900998336439728154875)
                    ·
                      rfl

theorem cell22_1270450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1270450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270450 prefixEnd_1270450 := by exact prefixLift 1270450
  have htrace : WordTrace (prefixWord ++ tailWord_1270450) baseStart_1270450 baseEnd_1270450 := by
    simpa [prefixWord, tailWord_1270450, baseEnd_1270450] using wordTrace_append hprefix tailTrace_1270450
  have hstable : (prefixWord ++ tailWord_1270450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270450).length < 2 ^ (prefixWord ++ tailWord_1270450).sum := by decide
  have hdescent : baseEnd_1270450 < baseStart_1270450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270499 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 5]
def baseStart_1270499 : Nat := 118140960795 + 1270499 * 2 ^ 59
def prefixEnd_1270499 : Nat := 4983230072969 + 3 ^ 40 * 1270499 * 2
def baseEnd_1270499 : Nat := 144972590679273311226575

theorem tailTrace_1270499 : CollatzResearch.WordTrace tailWord_1270499 prefixEnd_1270499 144972590679273311226575 := by
  unfold tailWord_1270499
  simp only [CollatzResearch.WordTrace]
  refine ⟨46338905424206581799334551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30892603616137721199556367 46338905424206581799334551)
  ·
    refine ⟨69508358136309872699001827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46338905424206581799334551 69508358136309872699001827)
    ·
      refine ⟨104262537204464809048502741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69508358136309872699001827 104262537204464809048502741)
      ·
        refine ⟨2443653215729643962074283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 104262537204464809048502741 2443653215729643962074283)
        ·
          refine ⟨3665479823594465943111425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443653215729643962074283 3665479823594465943111425)
          ·
            refine ⟨2749109867695849457333569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3665479823594465943111425 2749109867695849457333569)
            ·
              refine ⟨2061832400771887093000177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749109867695849457333569 2061832400771887093000177)
              ·
                refine ⟨1546374300578915319750133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061832400771887093000177 1546374300578915319750133)
                ·
                  refine ⟨144972590679273311226575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1546374300578915319750133 144972590679273311226575)
                  ·
                    rfl

theorem cell22_1270499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 5].length) (baseStart_1270499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270499 prefixEnd_1270499 := by exact prefixLift 1270499
  have htrace : WordTrace (prefixWord ++ tailWord_1270499) baseStart_1270499 baseEnd_1270499 := by
    simpa [prefixWord, tailWord_1270499, baseEnd_1270499] using wordTrace_append hprefix tailTrace_1270499
  have hstable : (prefixWord ++ tailWord_1270499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270499).length < 2 ^ (prefixWord ++ tailWord_1270499).sum := by decide
  have hdescent : baseEnd_1270499 < baseStart_1270499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270559 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 4, 3]
def baseStart_1270559 : Nat := 118140960795 + 1270559 * 2 ^ 59
def prefixEnd_1270559 : Nat := 4983230072969 + 3 ^ 40 * 1270559 * 2
def baseEnd_1270559 : Nat := 434938311263999777179541

theorem tailTrace_1270559 : CollatzResearch.WordTrace tailWord_1270559 prefixEnd_1270559 434938311263999777179541 := by
  unfold tailWord_1270559
  simp only [CollatzResearch.WordTrace]
  refine ⟨46341093803989212046518731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30894062535992808031012487 46341093803989212046518731)
  ·
    refine ⟨69511640705983818069778097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46341093803989212046518731 69511640705983818069778097)
    ·
      refine ⟨52133730529487863552333573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69511640705983818069778097 52133730529487863552333573)
      ·
        refine ⟨9775074474278974416062545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52133730529487863552333573 9775074474278974416062545)
        ·
          refine ⟨7331305855709230812046909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9775074474278974416062545 7331305855709230812046909)
          ·
            refine ⟨2749239695890961554517591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7331305855709230812046909 2749239695890961554517591)
            ·
              refine ⟨4123859543836442331776387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749239695890961554517591 4123859543836442331776387)
              ·
                refine ⟨6185789315754663497664581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123859543836442331776387 6185789315754663497664581)
                ·
                  refine ⟨1159835496703999405812109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6185789315754663497664581 1159835496703999405812109)
                  ·
                    refine ⟨434938311263999777179541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159835496703999405812109 434938311263999777179541)
                    ·
                      rfl

theorem cell22_1270559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 3].length) (baseStart_1270559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270559 prefixEnd_1270559 := by exact prefixLift 1270559
  have htrace : WordTrace (prefixWord ++ tailWord_1270559) baseStart_1270559 baseEnd_1270559 := by
    simpa [prefixWord, tailWord_1270559, baseEnd_1270559] using wordTrace_append hprefix tailTrace_1270559
  have hstable : (prefixWord ++ tailWord_1270559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270559).length < 2 ^ (prefixWord ++ tailWord_1270559).sum := by decide
  have hdescent : baseEnd_1270559 < baseStart_1270559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270574 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1270574 : Nat := 118140960795 + 1270574 * 2 ^ 59
def prefixEnd_1270574 : Nat := 4983230072969 + 3 ^ 40 * 1270574 * 2
def baseEnd_1270574 : Nat := 434943446070544738054495

theorem tailTrace_1270574 : CollatzResearch.WordTrace tailWord_1270574 prefixEnd_1270574 434943446070544738054495 := by
  unfold tailWord_1270574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792705112366858701039347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30894427265956579738876517 5792705112366858701039347)
  ·
    refine ⟨8689057668550288051559021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5792705112366858701039347 8689057668550288051559021)
    ·
      refine ⟨3258396625706358019334633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8689057668550288051559021 3258396625706358019334633)
      ·
        refine ⟨2443797469279768514500975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3258396625706358019334633 2443797469279768514500975)
        ·
          refine ⟨3665696203919652771751463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443797469279768514500975 3665696203919652771751463)
          ·
            refine ⟨5498544305879479157627195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665696203919652771751463 5498544305879479157627195)
            ·
              refine ⟨8247816458819218736440793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5498544305879479157627195 8247816458819218736440793)
              ·
                refine ⟨6185862344114414052330595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8247816458819218736440793 6185862344114414052330595)
                ·
                  refine ⟨9278793516171621078495893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6185862344114414052330595 9278793516171621078495893)
                  ·
                    refine ⟨434943446070544738054495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9278793516171621078495893 434943446070544738054495)
                    ·
                      rfl

theorem cell22_1270574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1270574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270574 prefixEnd_1270574 := by exact prefixLift 1270574
  have htrace : WordTrace (prefixWord ++ tailWord_1270574) baseStart_1270574 baseEnd_1270574 := by
    simpa [prefixWord, tailWord_1270574, baseEnd_1270574] using wordTrace_append hprefix tailTrace_1270574
  have hstable : (prefixWord ++ tailWord_1270574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270574).length < 2 ^ (prefixWord ++ tailWord_1270574).sum := by decide
  have hdescent : baseEnd_1270574 < baseStart_1270574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270589 : List Nat := [1, 4, 1, 4, 2, 1, 1, 8]
def baseStart_1270589 : Nat := 118140960795 + 1270589 * 2 ^ 59
def prefixEnd_1270589 : Nat := 4983230072969 + 3 ^ 40 * 1270589 * 2
def baseEnd_1270589 : Nat := 48327620097454410992161

theorem tailTrace_1270589 : CollatzResearch.WordTrace tailWord_1270589 prefixEnd_1270589 48327620097454410992161 := by
  unfold tailWord_1270589
  simp only [CollatzResearch.WordTrace]
  refine ⟨46342187993880527170110821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30894791995920351446740547 46342187993880527170110821)
  ·
    refine ⟨8689160248852598844395779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46342187993880527170110821 8689160248852598844395779)
    ·
      refine ⟨13033740373278898266593669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8689160248852598844395779 13033740373278898266593669)
      ·
        refine ⟨2443826319989793424986313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13033740373278898266593669 2443826319989793424986313)
        ·
          refine ⟨1832869739992345068739735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2443826319989793424986313 1832869739992345068739735)
          ·
            refine ⟨2749304609988517603109603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832869739992345068739735 2749304609988517603109603)
            ·
              refine ⟨4123956914982776404664405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749304609988517603109603 4123956914982776404664405)
              ·
                refine ⟨48327620097454410992161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4123956914982776404664405 48327620097454410992161)
                ·
                  rfl

theorem cell22_1270589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 8].length) (baseStart_1270589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270589 prefixEnd_1270589 := by exact prefixLift 1270589
  have htrace : WordTrace (prefixWord ++ tailWord_1270589) baseStart_1270589 baseEnd_1270589 := by
    simpa [prefixWord, tailWord_1270589, baseEnd_1270589] using wordTrace_append hprefix tailTrace_1270589
  have hstable : (prefixWord ++ tailWord_1270589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270589).length < 2 ^ (prefixWord ++ tailWord_1270589).sum := by decide
  have hdescent : baseEnd_1270589 < baseStart_1270589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270617 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 7]
def baseStart_1270617 : Nat := 118140960795 + 1270617 * 2 ^ 59
def prefixEnd_1270617 : Nat := 4983230072969 + 3 ^ 40 * 1270617 * 2
def baseEnd_1270617 : Nat := 144986055283102319743121

theorem tailTrace_1270617 : CollatzResearch.WordTrace tailWord_1270617 prefixEnd_1270617 144986055283102319743121 := by
  unfold tailWord_1270617
  simp only [CollatzResearch.WordTrace]
  refine ⟨46343209237779087952130105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30895472825186058634753403 46343209237779087952130105)
  ·
    refine ⟨34757406928334315964097579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46343209237779087952130105 34757406928334315964097579)
    ·
      refine ⟨52136110392501473946146369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34757406928334315964097579 52136110392501473946146369)
      ·
        refine ⟨39102082794376105459609777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52136110392501473946146369 39102082794376105459609777)
        ·
          refine ⟨29326562095782079094707333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39102082794376105459609777 29326562095782079094707333)
          ·
            refine ⟨5498730392959139830257625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29326562095782079094707333 5498730392959139830257625)
            ·
              refine ⟨4124047794719354872693219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5498730392959139830257625 4124047794719354872693219)
              ·
                refine ⟨6186071692079032309039829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124047794719354872693219 6186071692079032309039829)
                ·
                  refine ⟨144986055283102319743121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6186071692079032309039829 144986055283102319743121)
                  ·
                    rfl

theorem cell22_1270617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_1270617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270617 prefixEnd_1270617 := by exact prefixLift 1270617
  have htrace : WordTrace (prefixWord ++ tailWord_1270617) baseStart_1270617 baseEnd_1270617 := by
    simpa [prefixWord, tailWord_1270617, baseEnd_1270617] using wordTrace_append hprefix tailTrace_1270617
  have hstable : (prefixWord ++ tailWord_1270617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270617).length < 2 ^ (prefixWord ++ tailWord_1270617).sum := by decide
  have hdescent : baseEnd_1270617 < baseStart_1270617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270709 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1270709 : Nat := 118140960795 + 1270709 * 2 ^ 59
def prefixEnd_1270709 : Nat := 4983230072969 + 3 ^ 40 * 1270709 * 2
def baseEnd_1270709 : Nat := 434989659329449385929081

theorem tailTrace_1270709 : CollatzResearch.WordTrace tailWord_1270709 prefixEnd_1270709 434989659329449385929081 := by
  unfold tailWord_1270709
  simp only [CollatzResearch.WordTrace]
  refine ⟨46346564753445787664479181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30897709835630525109652787 46346564753445787664479181)
  ·
    refine ⟨17379961782542170374179693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46346564753445787664479181 17379961782542170374179693)
    ·
      refine ⟨6517485668453313890317385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17379961782542170374179693 6517485668453313890317385)
      ·
        refine ⟨4888114251339985417738039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6517485668453313890317385 4888114251339985417738039)
        ·
          refine ⟨7332171377009978126607059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4888114251339985417738039 7332171377009978126607059)
          ·
            refine ⟨10998257065514967189910589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7332171377009978126607059 10998257065514967189910589)
            ·
              refine ⟨4124346399568112696216471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10998257065514967189910589 4124346399568112696216471)
              ·
                refine ⟨6186519599352169044324707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124346399568112696216471 6186519599352169044324707)
                ·
                  refine ⟨9279779399028253566487061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6186519599352169044324707 9279779399028253566487061)
                  ·
                    refine ⟨434989659329449385929081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9279779399028253566487061 434989659329449385929081)
                    ·
                      rfl

theorem cell22_1270709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1270709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270709 prefixEnd_1270709 := by exact prefixLift 1270709
  have htrace : WordTrace (prefixWord ++ tailWord_1270709) baseStart_1270709 baseEnd_1270709 := by
    simpa [prefixWord, tailWord_1270709, baseEnd_1270709] using wordTrace_append hprefix tailTrace_1270709
  have hstable : (prefixWord ++ tailWord_1270709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270709).length < 2 ^ (prefixWord ++ tailWord_1270709).sum := by decide
  have hdescent : baseEnd_1270709 < baseStart_1270709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270769 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 7]
def baseStart_1270769 : Nat := 118140960795 + 1270769 * 2 ^ 59
def prefixEnd_1270769 : Nat := 4983230072969 + 3 ^ 40 * 1270769 * 2
def baseEnd_1270769 : Nat := 145003399518543076476299

theorem tailTrace_1270769 : CollatzResearch.WordTrace tailWord_1270769 prefixEnd_1270769 145003399518543076476299 := by
  unfold tailWord_1270769
  simp only [CollatzResearch.WordTrace]
  refine ⟨46348753133228417911663361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30899168755485611941108907 46348753133228417911663361)
  ·
    refine ⟨34761564849921313433747521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46348753133228417911663361 34761564849921313433747521)
    ·
      refine ⟨26071173637440985075310641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34761564849921313433747521 26071173637440985075310641)
      ·
        refine ⟨19553380228080738806482981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26071173637440985075310641 19553380228080738806482981)
        ·
          refine ⟨3666258792765138526215559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19553380228080738806482981 3666258792765138526215559)
          ·
            refine ⟨5499388189147707789323339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666258792765138526215559 5499388189147707789323339)
            ·
              refine ⟨8249082283721561683985009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5499388189147707789323339 8249082283721561683985009)
              ·
                refine ⟨6186811712791171262988757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8249082283721561683985009 6186811712791171262988757)
                ·
                  refine ⟨145003399518543076476299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6186811712791171262988757 145003399518543076476299)
                  ·
                    rfl

theorem cell22_1270769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_1270769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270769 prefixEnd_1270769 := by exact prefixLift 1270769
  have htrace : WordTrace (prefixWord ++ tailWord_1270769) baseStart_1270769 baseEnd_1270769 := by
    simpa [prefixWord, tailWord_1270769, baseEnd_1270769] using wordTrace_append hprefix tailTrace_1270769
  have hstable : (prefixWord ++ tailWord_1270769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270769).length < 2 ^ (prefixWord ++ tailWord_1270769).sum := by decide
  have hdescent : baseEnd_1270769 < baseStart_1270769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270833 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 1, 4]
def baseStart_1270833 : Nat := 118140960795 + 1270833 * 2 ^ 59
def prefixEnd_1270833 : Nat := 4983230072969 + 3 ^ 40 * 1270833 * 2
def baseEnd_1270833 : Nat := 435032107063554395828701

theorem tailTrace_1270833 : CollatzResearch.WordTrace tailWord_1270833 prefixEnd_1270833 435032107063554395828701 := by
  unfold tailWord_1270833
  simp only [CollatzResearch.WordTrace]
  refine ⟨46351087404996556841993153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30900724936664371227995435 46351087404996556841993153)
  ·
    refine ⟨34763315553747417631494865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46351087404996556841993153 34763315553747417631494865)
    ·
      refine ⟨26072486665310563223621149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34763315553747417631494865 26072486665310563223621149)
      ·
        refine ⟨9777182499491461208857931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26072486665310563223621149 9777182499491461208857931)
        ·
          refine ⟨14665773749237191813286897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9777182499491461208857931 14665773749237191813286897)
          ·
            refine ⟨10999330311927893859965173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14665773749237191813286897 10999330311927893859965173)
            ·
              refine ⟨1031187216743240049371735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10999330311927893859965173 1031187216743240049371735)
              ·
                refine ⟨1546780825114860074057603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031187216743240049371735 1546780825114860074057603)
                ·
                  refine ⟨2320171237672290111086405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546780825114860074057603 2320171237672290111086405)
                  ·
                    refine ⟨435032107063554395828701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2320171237672290111086405 435032107063554395828701)
                    ·
                      rfl

theorem cell22_1270833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_1270833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270833 prefixEnd_1270833 := by exact prefixLift 1270833
  have htrace : WordTrace (prefixWord ++ tailWord_1270833) baseStart_1270833 baseEnd_1270833 := by
    simpa [prefixWord, tailWord_1270833, baseEnd_1270833] using wordTrace_append hprefix tailTrace_1270833
  have hstable : (prefixWord ++ tailWord_1270833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270833).length < 2 ^ (prefixWord ++ tailWord_1270833).sum := by decide
  have hdescent : baseEnd_1270833 < baseStart_1270833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270874 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_1270874 : Nat := 118140960795 + 1270874 * 2 ^ 59
def prefixEnd_1270874 : Nat := 4983230072969 + 3 ^ 40 * 1270874 * 2
def baseEnd_1270874 : Nat := 435046142201443955553575

theorem tailTrace_1270874 : CollatzResearch.WordTrace tailWord_1270874 prefixEnd_1270874 435046142201443955553575 := by
  unfold tailWord_1270874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11588145699462005211058919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30901721865232013896157117 11588145699462005211058919)
  ·
    refine ⟨17382218549193007816588379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11588145699462005211058919 17382218549193007816588379)
    ·
      refine ⟨26073327823789511724882569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17382218549193007816588379 26073327823789511724882569)
      ·
        refine ⟨19554995867842133793661927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26073327823789511724882569 19554995867842133793661927)
        ·
          refine ⟨29332493801763200690492891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19554995867842133793661927 29332493801763200690492891)
          ·
            refine ⟨43998740702644801035739337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29332493801763200690492891 43998740702644801035739337)
            ·
              refine ⟨32999055526983600776804503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43998740702644801035739337 32999055526983600776804503)
              ·
                refine ⟨49498583290475401165206755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32999055526983600776804503 49498583290475401165206755)
                ·
                  refine ⟨74247874935713101747810133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49498583290475401165206755 74247874935713101747810133)
                  ·
                    refine ⟨435046142201443955553575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74247874935713101747810133 435046142201443955553575)
                    ·
                      rfl

theorem cell22_1270874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_1270874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270874 prefixEnd_1270874 := by exact prefixLift 1270874
  have htrace : WordTrace (prefixWord ++ tailWord_1270874) baseStart_1270874 baseEnd_1270874 := by
    simpa [prefixWord, tailWord_1270874, baseEnd_1270874] using wordTrace_append hprefix tailTrace_1270874
  have hstable : (prefixWord ++ tailWord_1270874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270874).length < 2 ^ (prefixWord ++ tailWord_1270874).sum := by decide
  have hdescent : baseEnd_1270874 < baseStart_1270874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270908 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_1270908 : Nat := 118140960795 + 1270908 * 2 ^ 59
def prefixEnd_1270908 : Nat := 4983230072969 + 3 ^ 40 * 1270908 * 2
def baseEnd_1270908 : Nat := 435057781096279200203471

theorem tailTrace_1270908 : CollatzResearch.WordTrace tailWord_1270908 prefixEnd_1270908 435057781096279200203471 := by
  unfold tailWord_1270908
  simp only [CollatzResearch.WordTrace]
  refine ⟨23176911439862422325486689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30902548586483229767315585 23176911439862422325486689)
  ·
    refine ⟨17382683579896816744115017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23176911439862422325486689 17382683579896816744115017)
    ·
      refine ⟨13037012684922612558086263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17382683579896816744115017 13037012684922612558086263)
      ·
        refine ⟨19555519027383918837129395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13037012684922612558086263 19555519027383918837129395)
        ·
          refine ⟨29333278541075878255694093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19555519027383918837129395 29333278541075878255694093)
          ·
            refine ⟨10999979452903454345885285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29333278541075878255694093 10999979452903454345885285)
            ·
              refine ⟨2062496147419397689853491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10999979452903454345885285 2062496147419397689853491)
              ·
                refine ⟨3093744221129096534780237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062496147419397689853491 3093744221129096534780237)
                ·
                  refine ⟨1160154082923411200542589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3093744221129096534780237 1160154082923411200542589)
                  ·
                    refine ⟨435057781096279200203471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1160154082923411200542589 435057781096279200203471)
                    ·
                      rfl

theorem cell22_1270908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_1270908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270908 prefixEnd_1270908 := by exact prefixLift 1270908
  have htrace : WordTrace (prefixWord ++ tailWord_1270908) baseStart_1270908 baseEnd_1270908 := by
    simpa [prefixWord, tailWord_1270908, baseEnd_1270908] using wordTrace_append hprefix tailTrace_1270908
  have hstable : (prefixWord ++ tailWord_1270908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270908).length < 2 ^ (prefixWord ++ tailWord_1270908).sum := by decide
  have hdescent : baseEnd_1270908 < baseStart_1270908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1270981 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_1270981 : Nat := 118140960795 + 1270981 * 2 ^ 59
def prefixEnd_1270981 : Nat := 4983230072969 + 3 ^ 40 * 1270981 * 2
def baseEnd_1270981 : Nat := 435082770488131343128247

theorem tailTrace_1270981 : CollatzResearch.WordTrace tailWord_1270981 prefixEnd_1270981 435082770488131343128247 := by
  unfold tailWord_1270981
  simp only [CollatzResearch.WordTrace]
  refine ⟨46356485408460378118380797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30904323605640252078920531 46356485408460378118380797)
  ·
    refine ⟨17383682028172641794392799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46356485408460378118380797 17383682028172641794392799)
    ·
      refine ⟨26075523042258962691589199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17383682028172641794392799 26075523042258962691589199)
      ·
        refine ⟨39113284563388444037383799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26075523042258962691589199 39113284563388444037383799)
        ·
          refine ⟨58669926845082666056075699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39113284563388444037383799 58669926845082666056075699)
          ·
            refine ⟨88004890267623999084113549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58669926845082666056075699 88004890267623999084113549)
            ·
              refine ⟨33001833850358999656542581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88004890267623999084113549 33001833850358999656542581)
              ·
                refine ⟨3093921923471156217800867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33001833850358999656542581 3093921923471156217800867)
                ·
                  refine ⟨4640882885206734326701301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093921923471156217800867 4640882885206734326701301)
                  ·
                    refine ⟨435082770488131343128247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4640882885206734326701301 435082770488131343128247)
                    ·
                      rfl

theorem cell22_1270981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_1270981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1270981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1270981 prefixEnd_1270981 := by exact prefixLift 1270981
  have htrace : WordTrace (prefixWord ++ tailWord_1270981) baseStart_1270981 baseEnd_1270981 := by
    simpa [prefixWord, tailWord_1270981, baseEnd_1270981] using wordTrace_append hprefix tailTrace_1270981
  have hstable : (prefixWord ++ tailWord_1270981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1270981).length < 2 ^ (prefixWord ++ tailWord_1270981).sum := by decide
  have hdescent : baseEnd_1270981 < baseStart_1270981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1270981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271043 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 5, 3]
def baseStart_1271043 : Nat := 118140960795 + 1271043 * 2 ^ 59
def prefixEnd_1271043 : Nat := 4983230072969 + 3 ^ 40 * 1271043 * 2
def baseEnd_1271043 : Nat := 435103994355183848078057

theorem tailTrace_1271043 : CollatzResearch.WordTrace tailWord_1271043 prefixEnd_1271043 435103994355183848078057 := by
  unfold tailWord_1271043
  simp only [CollatzResearch.WordTrace]
  refine ⟨46358746734235762707137783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30905831156157175138091855 46358746734235762707137783)
  ·
    refine ⟨69538120101353644060706675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46358746734235762707137783 69538120101353644060706675)
    ·
      refine ⟨104307180152030466091060013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69538120101353644060706675 104307180152030466091060013)
      ·
        refine ⟨39115192557011424784147505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104307180152030466091060013 39115192557011424784147505)
        ·
          refine ⟨29336394417758568588110629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39115192557011424784147505 29336394417758568588110629)
          ·
            refine ⟨5500573953329731610270743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29336394417758568588110629 5500573953329731610270743)
            ·
              refine ⟨8250860929994597415406115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500573953329731610270743 8250860929994597415406115)
              ·
                refine ⟨12376291394991896123109173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8250860929994597415406115 12376291394991896123109173)
                ·
                  refine ⟨1160277318280490261541485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12376291394991896123109173 1160277318280490261541485)
                  ·
                    refine ⟨435103994355183848078057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1160277318280490261541485 435103994355183848078057)
                    ·
                      rfl

theorem cell22_1271043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 3].length) (baseStart_1271043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271043 prefixEnd_1271043 := by exact prefixLift 1271043
  have htrace : WordTrace (prefixWord ++ tailWord_1271043) baseStart_1271043 baseEnd_1271043 := by
    simpa [prefixWord, tailWord_1271043, baseEnd_1271043] using wordTrace_append hprefix tailTrace_1271043
  have hstable : (prefixWord ++ tailWord_1271043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271043).length < 2 ^ (prefixWord ++ tailWord_1271043).sum := by decide
  have hdescent : baseEnd_1271043 < baseStart_1271043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271077 : List Nat := [1, 3, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_1271077 : Nat := 118140960795 + 1271077 * 2 ^ 59
def prefixEnd_1271077 : Nat := 4983230072969 + 3 ^ 40 * 1271077 * 2
def baseEnd_1271077 : Nat := 435115633250019092727953

theorem tailTrace_1271077 : CollatzResearch.WordTrace tailWord_1271077 prefixEnd_1271077 435115633250019092727953 := by
  unfold tailWord_1271077
  simp only [CollatzResearch.WordTrace]
  refine ⟨46359986816112586513875485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30906657877408391009250323 46359986816112586513875485)
  ·
    refine ⟨17384995056042219942703307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46359986816112586513875485 17384995056042219942703307)
    ·
      refine ⟨26077492584063329914054961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17384995056042219942703307 26077492584063329914054961)
      ·
        refine ⟨19558119438047497435541221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26077492584063329914054961 19558119438047497435541221)
        ·
          refine ⟨3667147394633905769163979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19558119438047497435541221 3667147394633905769163979)
          ·
            refine ⟨5500721091950858653745969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667147394633905769163979 5500721091950858653745969)
            ·
              refine ⟨4125540818963143990309477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500721091950858653745969 4125540818963143990309477)
              ·
                refine ⟨773538903555589498183027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4125540818963143990309477 773538903555589498183027)
                ·
                  refine ⟨1160308355333384247274541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773538903555589498183027 1160308355333384247274541)
                  ·
                    refine ⟨435115633250019092727953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1160308355333384247274541 435115633250019092727953)
                    ·
                      rfl

theorem cell22_1271077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_1271077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271077 prefixEnd_1271077 := by exact prefixLift 1271077
  have htrace : WordTrace (prefixWord ++ tailWord_1271077) baseStart_1271077 baseEnd_1271077 := by
    simpa [prefixWord, tailWord_1271077, baseEnd_1271077] using wordTrace_append hprefix tailTrace_1271077
  have hstable : (prefixWord ++ tailWord_1271077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271077).length < 2 ^ (prefixWord ++ tailWord_1271077).sum := by decide
  have hdescent : baseEnd_1271077 < baseStart_1271077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271165 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_1271165 : Nat := 118140960795 + 1271165 * 2 ^ 59
def prefixEnd_1271165 : Nat := 4983230072969 + 3 ^ 40 * 1271165 * 2
def baseEnd_1271165 : Nat := 435145757448416196527683

theorem tailTrace_1271165 : CollatzResearch.WordTrace tailWord_1271165 prefixEnd_1271165 435145757448416196527683 := by
  unfold tailWord_1271165
  simp only [CollatzResearch.WordTrace]
  refine ⟨46363196439793777543078949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30908797626529185028719299 46363196439793777543078949)
  ·
    refine ⟨8693099332461333289327303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46363196439793777543078949 8693099332461333289327303)
    ·
      refine ⟨13039648998691999933990955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8693099332461333289327303 13039648998691999933990955)
      ·
        refine ⟨19559473498037999900986433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13039648998691999933990955 19559473498037999900986433)
        ·
          refine ⟨14669605123528499925739825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19559473498037999900986433 14669605123528499925739825)
          ·
            refine ⟨11002203842646374944304869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14669605123528499925739825 11002203842646374944304869)
            ·
              refine ⟨2062913220496195302057163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11002203842646374944304869 2062913220496195302057163)
              ·
                refine ⟨3094369830744292953085745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062913220496195302057163 3094369830744292953085745)
                ·
                  refine ⟨2320777373058219714814309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3094369830744292953085745 2320777373058219714814309)
                  ·
                    refine ⟨435145757448416196527683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2320777373058219714814309 435145757448416196527683)
                    ·
                      rfl

theorem cell22_1271165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_1271165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271165 prefixEnd_1271165 := by exact prefixLift 1271165
  have htrace : WordTrace (prefixWord ++ tailWord_1271165) baseStart_1271165 baseEnd_1271165 := by
    simpa [prefixWord, tailWord_1271165, baseEnd_1271165] using wordTrace_append hprefix tailTrace_1271165
  have hstable : (prefixWord ++ tailWord_1271165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271165).length < 2 ^ (prefixWord ++ tailWord_1271165).sum := by decide
  have hdescent : baseEnd_1271165 < baseStart_1271165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271193 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_1271193 : Nat := 118140960795 + 1271193 * 2 ^ 59
def prefixEnd_1271193 : Nat := 4983230072969 + 3 ^ 40 * 1271193 * 2
def baseEnd_1271193 : Nat := 435155342420633456827597

theorem tailTrace_1271193 : CollatzResearch.WordTrace tailWord_1271193 prefixEnd_1271193 435155342420633456827597 := by
  unfold tailWord_1271193
  simp only [CollatzResearch.WordTrace]
  refine ⟨46364217683692338325098233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30909478455794892216732155 46364217683692338325098233)
  ·
    refine ⟨34773163262769253743823675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46364217683692338325098233 34773163262769253743823675)
    ·
      refine ⟨52159744894153880615735513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34773163262769253743823675 52159744894153880615735513)
      ·
        refine ⟨39119808670615410461801635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52159744894153880615735513 39119808670615410461801635)
        ·
          refine ⟨58679713005923115692702453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39119808670615410461801635 58679713005923115692702453)
          ·
            refine ⟨5501223094305292096190855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58679713005923115692702453 5501223094305292096190855)
            ·
              refine ⟨8251834641457938144286283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501223094305292096190855 8251834641457938144286283)
              ·
                refine ⟨12377751962186907216429425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8251834641457938144286283 12377751962186907216429425)
                ·
                  refine ⟨9283313971640180412322069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12377751962186907216429425 9283313971640180412322069)
                  ·
                    refine ⟨435155342420633456827597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9283313971640180412322069 435155342420633456827597)
                    ·
                      rfl

theorem cell22_1271193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_1271193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271193 prefixEnd_1271193 := by exact prefixLift 1271193
  have htrace : WordTrace (prefixWord ++ tailWord_1271193) baseStart_1271193 baseEnd_1271193 := by
    simpa [prefixWord, tailWord_1271193, baseEnd_1271193] using wordTrace_append hprefix tailTrace_1271193
  have hstable : (prefixWord ++ tailWord_1271193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271193).length < 2 ^ (prefixWord ++ tailWord_1271193).sum := by decide
  have hdescent : baseEnd_1271193 < baseStart_1271193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271223 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 1, 7]
def baseStart_1271223 : Nat := 118140960795 + 1271223 * 2 ^ 59
def prefixEnd_1271223 : Nat := 4983230072969 + 3 ^ 40 * 1271223 * 2
def baseEnd_1271223 : Nat := 435165612033723378577505

theorem tailTrace_1271223 : CollatzResearch.WordTrace tailWord_1271223 prefixEnd_1271223 435165612033723378577505 := by
  unfold tailWord_1271223
  simp only [CollatzResearch.WordTrace]
  refine ⟨46365311873583653448690323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30910207915722435632460215 46365311873583653448690323)
  ·
    refine ⟨69547967810375480173035485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46365311873583653448690323 69547967810375480173035485)
    ·
      refine ⟨26080487928890805064888307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69547967810375480173035485 26080487928890805064888307)
      ·
        refine ⟨39120731893336207597332461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26080487928890805064888307 39120731893336207597332461)
        ·
          refine ⟨14670274460001077848999673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39120731893336207597332461 14670274460001077848999673)
          ·
            refine ⟨11002705845000808386749755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14670274460001077848999673 11002705845000808386749755)
            ·
              refine ⟨16504058767501212580124633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11002705845000808386749755 16504058767501212580124633)
              ·
                refine ⟨12378044075625909435093475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16504058767501212580124633 12378044075625909435093475)
                ·
                  refine ⟨18567066113438864152640213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12378044075625909435093475 18567066113438864152640213)
                  ·
                    refine ⟨435165612033723378577505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18567066113438864152640213 435165612033723378577505)
                    ·
                      rfl

theorem cell22_1271223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_1271223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271223 prefixEnd_1271223 := by exact prefixLift 1271223
  have htrace : WordTrace (prefixWord ++ tailWord_1271223) baseStart_1271223 baseEnd_1271223 := by
    simpa [prefixWord, tailWord_1271223, baseEnd_1271223] using wordTrace_append hprefix tailTrace_1271223
  have hstable : (prefixWord ++ tailWord_1271223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271223).length < 2 ^ (prefixWord ++ tailWord_1271223).sum := by decide
  have hdescent : baseEnd_1271223 < baseStart_1271223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271229 : List Nat := [1, 4, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_1271229 : Nat := 118140960795 + 1271229 * 2 ^ 59
def prefixEnd_1271229 : Nat := 4983230072969 + 3 ^ 40 * 1271229 * 2
def baseEnd_1271229 : Nat := 435167665956341362927487

theorem tailTrace_1271229 : CollatzResearch.WordTrace tailWord_1271229 prefixEnd_1271229 435167665956341362927487 := by
  unfold tailWord_1271229
  simp only [CollatzResearch.WordTrace]
  refine ⟨46365530711561916473408741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30910353807707944315605827 46365530711561916473408741)
  ·
    refine ⟨8693537008417859338764139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46365530711561916473408741 8693537008417859338764139)
    ·
      refine ⟨13040305512626789008146209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8693537008417859338764139 13040305512626789008146209)
      ·
        refine ⟨9780229134470091756109657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13040305512626789008146209 9780229134470091756109657)
        ·
          refine ⟨7335171850852568817082243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9780229134470091756109657 7335171850852568817082243)
          ·
            refine ⟨11002757776278853225623365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7335171850852568817082243 11002757776278853225623365)
            ·
              refine ⟨2063017083052284979804381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11002757776278853225623365 2063017083052284979804381)
              ·
                refine ⟨773631406144606867426643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2063017083052284979804381 773631406144606867426643)
                ·
                  refine ⟨1160447109216910301139965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773631406144606867426643 1160447109216910301139965)
                  ·
                    refine ⟨435167665956341362927487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1160447109216910301139965 435167665956341362927487)
                    ·
                      rfl

theorem cell22_1271229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_1271229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271229 prefixEnd_1271229 := by exact prefixLift 1271229
  have htrace : WordTrace (prefixWord ++ tailWord_1271229) baseStart_1271229 baseEnd_1271229 := by
    simpa [prefixWord, tailWord_1271229, baseEnd_1271229] using wordTrace_append hprefix tailTrace_1271229
  have hstable : (prefixWord ++ tailWord_1271229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271229).length < 2 ^ (prefixWord ++ tailWord_1271229).sum := by decide
  have hdescent : baseEnd_1271229 < baseStart_1271229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271242 : List Nat := [3, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_1271242 : Nat := 118140960795 + 1271242 * 2 ^ 59
def prefixEnd_1271242 : Nat := 4983230072969 + 3 ^ 40 * 1271242 * 2
def baseEnd_1271242 : Nat := 145057372040671220784149

theorem tailTrace_1271242 : CollatzResearch.WordTrace tailWord_1271242 prefixEnd_1271242 145057372040671220784149 := by
  unfold tailWord_1271242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11591501215128704923407995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30910669907009879795754653 11591501215128704923407995)
  ·
    refine ⟨17387251822693057385111993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11591501215128704923407995 17387251822693057385111993)
    ·
      refine ⟨13040438867019793038833995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17387251822693057385111993 13040438867019793038833995)
      ·
        refine ⟨19560658300529689558250993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13040438867019793038833995 19560658300529689558250993)
        ·
          refine ⟨14670493725397267168688245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19560658300529689558250993 14670493725397267168688245)
          ·
            refine ⟨1375358786755993797064523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14670493725397267168688245 1375358786755993797064523)
            ·
              refine ⟨2063038180133990695596785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375358786755993797064523 2063038180133990695596785)
              ·
                refine ⟨1547278635100493021697589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2063038180133990695596785 1547278635100493021697589)
                ·
                  refine ⟨145057372040671220784149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1547278635100493021697589 145057372040671220784149)
                  ·
                    rfl

theorem cell22_1271242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_1271242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271242 prefixEnd_1271242 := by exact prefixLift 1271242
  have htrace : WordTrace (prefixWord ++ tailWord_1271242) baseStart_1271242 baseEnd_1271242 := by
    simpa [prefixWord, tailWord_1271242, baseEnd_1271242] using wordTrace_append hprefix tailTrace_1271242
  have hstable : (prefixWord ++ tailWord_1271242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271242).length < 2 ^ (prefixWord ++ tailWord_1271242).sum := by decide
  have hdescent : baseEnd_1271242 < baseStart_1271242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271272 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1271272 : Nat := 118140960795 + 1271272 * 2 ^ 59
def prefixEnd_1271272 : Nat := 4983230072969 + 3 ^ 40 * 1271272 * 2
def baseEnd_1271272 : Nat := 435182385735103584102355

theorem tailTrace_1271272 : CollatzResearch.WordTrace tailWord_1271272 prefixEnd_1271272 435182385735103584102355 := by
  unfold tailWord_1271272
  simp only [CollatzResearch.WordTrace]
  refine ⟨23183549525203067408612035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30911399366937423211482713 23183549525203067408612035)
  ·
    refine ⟨34775324287804601112918053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23183549525203067408612035 34775324287804601112918053)
    ·
      refine ⟨6520373303963362708672135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34775324287804601112918053 6520373303963362708672135)
      ·
        refine ⟨9780559955945044063008203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6520373303963362708672135 9780559955945044063008203)
        ·
          refine ⟨14670839933917566094512305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9780559955945044063008203 14670839933917566094512305)
          ·
            refine ⟨11003129950438174570884229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14670839933917566094512305 11003129950438174570884229)
            ·
              refine ⟨2063086865707157732040793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11003129950438174570884229 2063086865707157732040793)
              ·
                refine ⟨1547315149280368299030595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2063086865707157732040793 1547315149280368299030595)
                ·
                  refine ⟨2320972723920552448545893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547315149280368299030595 2320972723920552448545893)
                  ·
                    refine ⟨435182385735103584102355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2320972723920552448545893 435182385735103584102355)
                    ·
                      rfl

theorem cell22_1271272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1271272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271272 prefixEnd_1271272 := by exact prefixLift 1271272
  have htrace : WordTrace (prefixWord ++ tailWord_1271272) baseStart_1271272 baseEnd_1271272 := by
    simpa [prefixWord, tailWord_1271272, baseEnd_1271272] using wordTrace_append hprefix tailTrace_1271272
  have hstable : (prefixWord ++ tailWord_1271272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271272).length < 2 ^ (prefixWord ++ tailWord_1271272).sum := by decide
  have hdescent : baseEnd_1271272 < baseStart_1271272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271315 : List Nat := [1, 1, 1, 2, 1, 7, 2, 7]
def baseStart_1271315 : Nat := 118140960795 + 1271315 * 2 ^ 59
def prefixEnd_1271315 : Nat := 4983230072969 + 3 ^ 40 * 1271315 * 2
def baseEnd_1271315 : Nat := 48355233945985089475247

theorem tailTrace_1271315 : CollatzResearch.WordTrace tailWord_1271315 prefixEnd_1271315 48355233945985089475247 := by
  unfold tailWord_1271315
  simp only [CollatzResearch.WordTrace]
  refine ⟨46368667389250353161039399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30912444926166902107359599 46368667389250353161039399)
  ·
    refine ⟨69553001083875529741559099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46368667389250353161039399 69553001083875529741559099)
    ·
      refine ⟨104329501625813294612338649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69553001083875529741559099 104329501625813294612338649)
      ·
        refine ⟨78247126219359970959253987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104329501625813294612338649 78247126219359970959253987)
        ·
          refine ⟨117370689329039956438880981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78247126219359970959253987 117370689329039956438880981)
          ·
            refine ⟨2750875531149373979036273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 117370689329039956438880981 2750875531149373979036273)
            ·
              refine ⟨2063156648362030484277205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2750875531149373979036273 2063156648362030484277205)
              ·
                refine ⟨48355233945985089475247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2063156648362030484277205 48355233945985089475247)
                ·
                  rfl

theorem cell22_1271315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 7].length) (baseStart_1271315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271315 prefixEnd_1271315 := by exact prefixLift 1271315
  have htrace : WordTrace (prefixWord ++ tailWord_1271315) baseStart_1271315 baseEnd_1271315 := by
    simpa [prefixWord, tailWord_1271315, baseEnd_1271315] using wordTrace_append hprefix tailTrace_1271315
  have hstable : (prefixWord ++ tailWord_1271315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271315).length < 2 ^ (prefixWord ++ tailWord_1271315).sum := by decide
  have hdescent : baseEnd_1271315 < baseStart_1271315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271330 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1271330 : Nat := 118140960795 + 1271330 * 2 ^ 59
def prefixEnd_1271330 : Nat := 4983230072969 + 3 ^ 40 * 1271330 * 2
def baseEnd_1271330 : Nat := 435202240320410766152177

theorem tailTrace_1271330 : CollatzResearch.WordTrace tailWord_1271330 prefixEnd_1271330 435202240320410766152177 := by
  unfold tailWord_1271330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592303621049002680708861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30912809656130673815223629 11592303621049002680708861)
  ·
    refine ⟨4347113857893376005265823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11592303621049002680708861 4347113857893376005265823)
    ·
      refine ⟨6520670786840064007898735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4347113857893376005265823 6520670786840064007898735)
      ·
        refine ⟨9781006180260096011848103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6520670786840064007898735 9781006180260096011848103)
        ·
          refine ⟨14671509270390144017772155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9781006180260096011848103 14671509270390144017772155)
          ·
            refine ⟨22007263905585216026658233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14671509270390144017772155 22007263905585216026658233)
            ·
              refine ⟨16505447929188912019993675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22007263905585216026658233 16505447929188912019993675)
              ·
                refine ⟨24758171893783368029990513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16505447929188912019993675 24758171893783368029990513)
                ·
                  refine ⟨18568628920337526022492885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24758171893783368029990513 18568628920337526022492885)
                  ·
                    refine ⟨435202240320410766152177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18568628920337526022492885 435202240320410766152177)
                    ·
                      rfl

theorem cell22_1271330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1271330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271330 prefixEnd_1271330 := by exact prefixLift 1271330
  have htrace : WordTrace (prefixWord ++ tailWord_1271330) baseStart_1271330 baseEnd_1271330 := by
    simpa [prefixWord, tailWord_1271330, baseEnd_1271330] using wordTrace_append hprefix tailTrace_1271330
  have hstable : (prefixWord ++ tailWord_1271330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271330).length < 2 ^ (prefixWord ++ tailWord_1271330).sum := by decide
  have hdescent : baseEnd_1271330 < baseStart_1271330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271366 : List Nat := [6, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1271366 : Nat := 118140960795 + 1271366 * 2 ^ 59
def prefixEnd_1271366 : Nat := 4983230072969 + 3 ^ 40 * 1271366 * 2
def baseEnd_1271366 : Nat := 48357173761790963583563

theorem tailTrace_1271366 : CollatzResearch.WordTrace tailWord_1271366 prefixEnd_1271366 48357173761790963583563 := by
  unfold tailWord_1271366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449078984752049652223311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30913685008043725914097301 1449078984752049652223311)
  ·
    refine ⟨2173618477128074478334967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449078984752049652223311 2173618477128074478334967)
    ·
      refine ⟨3260427715692111717502451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173618477128074478334967 3260427715692111717502451)
      ·
        refine ⟨4890641573538167576253677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260427715692111717502451 4890641573538167576253677)
        ·
          refine ⟨1833990590076812841095129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4890641573538167576253677 1833990590076812841095129)
          ·
            refine ⟨1375492942557609630821347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1833990590076812841095129 1375492942557609630821347)
            ·
              refine ⟨2063239413836414446232021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375492942557609630821347 2063239413836414446232021)
              ·
                refine ⟨48357173761790963583563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2063239413836414446232021 48357173761790963583563)
                ·
                  rfl

theorem cell22_1271366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1271366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271366 prefixEnd_1271366 := by exact prefixLift 1271366
  have htrace : WordTrace (prefixWord ++ tailWord_1271366) baseStart_1271366 baseEnd_1271366 := by
    simpa [prefixWord, tailWord_1271366, baseEnd_1271366] using wordTrace_append hprefix tailTrace_1271366
  have hstable : (prefixWord ++ tailWord_1271366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271366).length < 2 ^ (prefixWord ++ tailWord_1271366).sum := by decide
  have hdescent : baseEnd_1271366 < baseStart_1271366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271435 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 3, 6]
def baseStart_1271435 : Nat := 118140960795 + 1271435 * 2 ^ 59
def prefixEnd_1271435 : Nat := 4983230072969 + 3 ^ 40 * 1271435 * 2
def baseEnd_1271435 : Nat := 435238183966225492276855

theorem tailTrace_1271435 : CollatzResearch.WordTrace tailWord_1271435 prefixEnd_1271435 435238183966225492276855 := by
  unfold tailWord_1271435
  simp only [CollatzResearch.WordTrace]
  refine ⟨46373044148815613655407759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30915362765877075770271839 46373044148815613655407759)
  ·
    refine ⟨69559566223223420483111639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46373044148815613655407759 69559566223223420483111639)
    ·
      refine ⟨104339349334835130724667459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69559566223223420483111639 104339349334835130724667459)
      ·
        refine ⟨156509024002252696087001189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104339349334835130724667459 156509024002252696087001189)
        ·
          refine ⟨29345442000422380516312723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156509024002252696087001189 29345442000422380516312723)
          ·
            refine ⟨44018163000633570774469085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29345442000422380516312723 44018163000633570774469085)
            ·
              refine ⟨16506811125237589040425907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44018163000633570774469085 16506811125237589040425907)
              ·
                refine ⟨24760216687856383560638861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16506811125237589040425907 24760216687856383560638861)
                ·
                  refine ⟨9285081257946143835239573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24760216687856383560638861 9285081257946143835239573)
                  ·
                    refine ⟨435238183966225492276855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9285081257946143835239573 435238183966225492276855)
                    ·
                      rfl

theorem cell22_1271435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_1271435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271435 prefixEnd_1271435 := by exact prefixLift 1271435
  have htrace : WordTrace (prefixWord ++ tailWord_1271435) baseStart_1271435 baseEnd_1271435 := by
    simpa [prefixWord, tailWord_1271435, baseEnd_1271435] using wordTrace_append hprefix tailTrace_1271435
  have hstable : (prefixWord ++ tailWord_1271435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271435).length < 2 ^ (prefixWord ++ tailWord_1271435).sum := by decide
  have hdescent : baseEnd_1271435 < baseStart_1271435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271456 : List Nat := [2, 1, 1, 4, 3, 3, 1, 3, 4]
def baseStart_1271456 : Nat := 118140960795 + 1271456 * 2 ^ 59
def prefixEnd_1271456 : Nat := 4983230072969 + 3 ^ 40 * 1271456 * 2
def baseEnd_1271456 : Nat := 145081790898462812500597

theorem tailTrace_1271456 : CollatzResearch.WordTrace tailWord_1271456 prefixEnd_1271456 145081790898462812500597 := by
  unfold tailWord_1271456
  simp only [CollatzResearch.WordTrace]
  refine ⟨23186905040869767120961111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30915873387826356161281481 23186905040869767120961111)
  ·
    refine ⟨34780357561304650681441667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23186905040869767120961111 34780357561304650681441667)
    ·
      refine ⟨52170536341956976022162501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34780357561304650681441667 52170536341956976022162501)
      ·
        refine ⟨9781975564116933004155469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52170536341956976022162501 9781975564116933004155469)
        ·
          refine ⟨3668240836543849876558301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9781975564116933004155469 3668240836543849876558301)
          ·
            refine ⟨1375590313703943703709363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3668240836543849876558301 1375590313703943703709363)
            ·
              refine ⟨2063385470555915555564045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375590313703943703709363 2063385470555915555564045)
              ·
                refine ⟨773769551458468333336517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2063385470555915555564045 773769551458468333336517)
                ·
                  refine ⟨145081790898462812500597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 773769551458468333336517 145081790898462812500597)
                  ·
                    rfl

theorem cell22_1271456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 4].length) (baseStart_1271456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271456 prefixEnd_1271456 := by exact prefixLift 1271456
  have htrace : WordTrace (prefixWord ++ tailWord_1271456) baseStart_1271456 baseEnd_1271456 := by
    simpa [prefixWord, tailWord_1271456, baseEnd_1271456] using wordTrace_append hprefix tailTrace_1271456
  have hstable : (prefixWord ++ tailWord_1271456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271456).length < 2 ^ (prefixWord ++ tailWord_1271456).sum := by decide
  have hdescent : baseEnd_1271456 < baseStart_1271456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271465 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_1271465 : Nat := 118140960795 + 1271465 * 2 ^ 59
def prefixEnd_1271465 : Nat := 4983230072969 + 3 ^ 40 * 1271465 * 2
def baseEnd_1271465 : Nat := 435248453579315414026763

theorem tailTrace_1271465 : CollatzResearch.WordTrace tailWord_1271465 prefixEnd_1271465 435248453579315414026763 := by
  unfold tailWord_1271465
  simp only [CollatzResearch.WordTrace]
  refine ⟨46374138338706928778999849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30916092225804619185999899 46374138338706928778999849)
  ·
    refine ⟨34780603754030196584249887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46374138338706928778999849 34780603754030196584249887)
    ·
      refine ⟨52170905631045294876374831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34780603754030196584249887 52170905631045294876374831)
      ·
        refine ⟨78256358446567942314562247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52170905631045294876374831 78256358446567942314562247)
        ·
          refine ⟨117384537669851913471843371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78256358446567942314562247 117384537669851913471843371)
          ·
            refine ⟨176076806504777870207765057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117384537669851913471843371 176076806504777870207765057)
            ·
              refine ⟨132057604878583402655823793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176076806504777870207765057 132057604878583402655823793)
              ·
                refine ⟨99043203658937551991867845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132057604878583402655823793 99043203658937551991867845)
                ·
                  refine ⟨18570600686050790998475221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99043203658937551991867845 18570600686050790998475221)
                  ·
                    refine ⟨435248453579315414026763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18570600686050790998475221 435248453579315414026763)
                    ·
                      rfl

theorem cell22_1271465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_1271465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271465 prefixEnd_1271465 := by exact prefixLift 1271465
  have htrace : WordTrace (prefixWord ++ tailWord_1271465) baseStart_1271465 baseEnd_1271465 := by
    simpa [prefixWord, tailWord_1271465, baseEnd_1271465] using wordTrace_append hprefix tailTrace_1271465
  have hstable : (prefixWord ++ tailWord_1271465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271465).length < 2 ^ (prefixWord ++ tailWord_1271465).sum := by decide
  have hdescent : baseEnd_1271465 < baseStart_1271465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271469 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1271469 : Nat := 118140960795 + 1271469 * 2 ^ 59
def prefixEnd_1271469 : Nat := 4983230072969 + 3 ^ 40 * 1271469 * 2
def baseEnd_1271469 : Nat := 435249822861060736926751

theorem tailTrace_1271469 : CollatzResearch.WordTrace tailWord_1271469 prefixEnd_1271469 435249822861060736926751 := by
  unfold tailWord_1271469
  simp only [CollatzResearch.WordTrace]
  refine ⟨46374284230692437462145461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30916189487128291641430307 46374284230692437462145461)
  ·
    refine ⟨4347589146627416012076137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46374284230692437462145461 4347589146627416012076137)
    ·
      refine ⟨3260691859970562009057103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4347589146627416012076137 3260691859970562009057103)
      ·
        refine ⟨4891037789955843013585655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260691859970562009057103 4891037789955843013585655)
        ·
          refine ⟨7336556684933764520378483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891037789955843013585655 7336556684933764520378483)
          ·
            refine ⟨11004835027400646780567725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7336556684933764520378483 11004835027400646780567725)
            ·
              refine ⟨4126813135275242542712897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11004835027400646780567725 4126813135275242542712897)
              ·
                refine ⟨3095109851456431907034673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4126813135275242542712897 3095109851456431907034673)
                ·
                  refine ⟨2321332388592323930276005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3095109851456431907034673 2321332388592323930276005)
                  ·
                    refine ⟨435249822861060736926751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2321332388592323930276005 435249822861060736926751)
                    ·
                      rfl

theorem cell22_1271469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1271469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271469 prefixEnd_1271469 := by exact prefixLift 1271469
  have htrace : WordTrace (prefixWord ++ tailWord_1271469) baseStart_1271469 baseEnd_1271469 := by
    simpa [prefixWord, tailWord_1271469, baseEnd_1271469] using wordTrace_append hprefix tailTrace_1271469
  have hstable : (prefixWord ++ tailWord_1271469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271469).length < 2 ^ (prefixWord ++ tailWord_1271469).sum := by decide
  have hdescent : baseEnd_1271469 < baseStart_1271469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271533 : List Nat := [1, 5, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_1271533 : Nat := 118140960795 + 1271533 * 2 ^ 59
def prefixEnd_1271533 : Nat := 4983230072969 + 3 ^ 40 * 1271533 * 2
def baseEnd_1271533 : Nat := 435271731368985903326555

theorem tailTrace_1271533 : CollatzResearch.WordTrace tailWord_1271533 prefixEnd_1271533 435271731368985903326555 := by
  unfold tailWord_1271533
  simp only [CollatzResearch.WordTrace]
  refine ⟨46376618502460576392475253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30917745668307050928316835 46376618502460576392475253)
  ·
    refine ⟨4347807984605679036794555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46376618502460576392475253 4347807984605679036794555)
    ·
      refine ⟨6521711976908518555191833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4347807984605679036794555 6521711976908518555191833)
      ·
        refine ⟨4891283982681388916393875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6521711976908518555191833 4891283982681388916393875)
        ·
          refine ⟨7336925974022083374590813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4891283982681388916393875 7336925974022083374590813)
          ·
            refine ⟨2751347240258281265471555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7336925974022083374590813 2751347240258281265471555)
            ·
              refine ⟨4127020860387421898207333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751347240258281265471555 4127020860387421898207333)
              ·
                refine ⟨773816411322641605913875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4127020860387421898207333 773816411322641605913875)
                ·
                  refine ⟨1160724616983962408870813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773816411322641605913875 1160724616983962408870813)
                  ·
                    refine ⟨435271731368985903326555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1160724616983962408870813 435271731368985903326555)
                    ·
                      rfl

theorem cell22_1271533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_1271533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271533 prefixEnd_1271533 := by exact prefixLift 1271533
  have htrace : WordTrace (prefixWord ++ tailWord_1271533) baseStart_1271533 baseEnd_1271533 := by
    simpa [prefixWord, tailWord_1271533, baseEnd_1271533] using wordTrace_append hprefix tailTrace_1271533
  have hstable : (prefixWord ++ tailWord_1271533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271533).length < 2 ^ (prefixWord ++ tailWord_1271533).sum := by decide
  have hdescent : baseEnd_1271533 < baseStart_1271533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271576 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 1, 4]
def baseStart_1271576 : Nat := 118140960795 + 1271576 * 2 ^ 59
def prefixEnd_1271576 : Nat := 4983230072969 + 3 ^ 40 * 1271576 * 2
def baseEnd_1271576 : Nat := 435286451147748124501423

theorem tailTrace_1271576 : CollatzResearch.WordTrace tailWord_1271576 prefixEnd_1271576 435286451147748124501423 := by
  unfold tailWord_1271576
  simp only [CollatzResearch.WordTrace]
  refine ⟨23189093420652397368145291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30918791227536529824193721 23189093420652397368145291)
  ·
    refine ⟨34783640130978596052217937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23189093420652397368145291 34783640130978596052217937)
    ·
      refine ⟨26087730098233947039163453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34783640130978596052217937 26087730098233947039163453)
      ·
        refine ⟨9782898786837730139686295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26087730098233947039163453 9782898786837730139686295)
        ·
          refine ⟨14674348180256595209529443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9782898786837730139686295 14674348180256595209529443)
          ·
            refine ⟨22011522270384892814294165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14674348180256595209529443 22011522270384892814294165)
            ·
              refine ⟨1031790106424291850670039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22011522270384892814294165 1031790106424291850670039)
              ·
                refine ⟨1547685159636437776005059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031790106424291850670039 1547685159636437776005059)
                ·
                  refine ⟨2321527739454656664007589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547685159636437776005059 2321527739454656664007589)
                  ·
                    refine ⟨435286451147748124501423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2321527739454656664007589 435286451147748124501423)
                    ·
                      rfl

theorem cell22_1271576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_1271576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271576 prefixEnd_1271576 := by exact prefixLift 1271576
  have htrace : WordTrace (prefixWord ++ tailWord_1271576) baseStart_1271576 baseEnd_1271576 := by
    simpa [prefixWord, tailWord_1271576, baseEnd_1271576] using wordTrace_append hprefix tailTrace_1271576
  have hstable : (prefixWord ++ tailWord_1271576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271576).length < 2 ^ (prefixWord ++ tailWord_1271576).sum := by decide
  have hdescent : baseEnd_1271576 < baseStart_1271576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271619 : List Nat := [1, 1, 1, 3, 1, 5, 4, 6]
def baseStart_1271619 : Nat := 118140960795 + 1271619 * 2 ^ 59
def prefixEnd_1271619 : Nat := 4983230072969 + 3 ^ 40 * 1271619 * 2
def baseEnd_1271619 : Nat := 48366796769612260630699

theorem tailTrace_1271619 : CollatzResearch.WordTrace tailWord_1271619 prefixEnd_1271619 48366796769612260630699 := by
  unfold tailWord_1271619
  simp only [CollatzResearch.WordTrace]
  refine ⟨46379755180149013080105911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30919836786766008720070607 46379755180149013080105911)
  ·
    refine ⟨69569632770223519620158867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46379755180149013080105911 69569632770223519620158867)
    ·
      refine ⟨104354449155335279430238301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69569632770223519620158867 104354449155335279430238301)
      ·
        refine ⟨39132918433250729786339363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104354449155335279430238301 39132918433250729786339363)
        ·
          refine ⟨58699377649876094679509045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39132918433250729786339363 58699377649876094679509045)
          ·
            refine ⟨5503066654675883876203973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58699377649876094679509045 5503066654675883876203973)
            ·
              refine ⟨1031824997751728226788245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5503066654675883876203973 1031824997751728226788245)
              ·
                refine ⟨48366796769612260630699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1031824997751728226788245 48366796769612260630699)
                ·
                  rfl

theorem cell22_1271619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 6].length) (baseStart_1271619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271619 prefixEnd_1271619 := by exact prefixLift 1271619
  have htrace : WordTrace (prefixWord ++ tailWord_1271619) baseStart_1271619 baseEnd_1271619 := by
    simpa [prefixWord, tailWord_1271619, baseEnd_1271619] using wordTrace_append hprefix tailTrace_1271619
  have hstable : (prefixWord ++ tailWord_1271619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271619).length < 2 ^ (prefixWord ++ tailWord_1271619).sum := by decide
  have hdescent : baseEnd_1271619 < baseStart_1271619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271632 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_1271632 : Nat := 118140960795 + 1271632 * 2 ^ 59
def prefixEnd_1271632 : Nat := 4983230072969 + 3 ^ 40 * 1271632 * 2
def baseEnd_1271632 : Nat := 435305621092182645101251

theorem tailTrace_1271632 : CollatzResearch.WordTrace tailWord_1271632 prefixEnd_1271632 435305621092182645101251 := by
  unfold tailWord_1271632
  simp only [CollatzResearch.WordTrace]
  refine ⟨23190114664550958150164575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30920152886067944200219433 23190114664550958150164575)
  ·
    refine ⟨34785171996826437225246863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23190114664550958150164575 34785171996826437225246863)
    ·
      refine ⟨52177757995239655837870295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34785171996826437225246863 52177757995239655837870295)
      ·
        refine ⟨78266636992859483756805443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52177757995239655837870295 78266636992859483756805443)
        ·
          refine ⟨117399955489289225635208165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78266636992859483756805443 117399955489289225635208165)
          ·
            refine ⟨22012491654241729806601531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117399955489289225635208165 22012491654241729806601531)
            ·
              refine ⟨33018737481362594709902297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22012491654241729806601531 33018737481362594709902297)
              ·
                refine ⟨24764053111021946032426723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33018737481362594709902297 24764053111021946032426723)
                ·
                  refine ⟨37146079666532919048640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24764053111021946032426723 37146079666532919048640085)
                  ·
                    refine ⟨435305621092182645101251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37146079666532919048640085 435305621092182645101251)
                    ·
                      rfl

theorem cell22_1271632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_1271632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271632 prefixEnd_1271632 := by exact prefixLift 1271632
  have htrace : WordTrace (prefixWord ++ tailWord_1271632) baseStart_1271632 baseEnd_1271632 := by
    simpa [prefixWord, tailWord_1271632, baseEnd_1271632] using wordTrace_append hprefix tailTrace_1271632
  have hstable : (prefixWord ++ tailWord_1271632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271632).length < 2 ^ (prefixWord ++ tailWord_1271632).sum := by decide
  have hdescent : baseEnd_1271632 < baseStart_1271632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271698 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1271698 : Nat := 118140960795 + 1271698 * 2 ^ 59
def prefixEnd_1271698 : Nat := 4983230072969 + 3 ^ 40 * 1271698 * 2
def baseEnd_1271698 : Nat := 145109404746993490983683

theorem tailTrace_1271698 : CollatzResearch.WordTrace tailWord_1271698 prefixEnd_1271698 145109404746993490983683 := by
  unfold tailWord_1271698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595659136715702393057937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30921757697908539714821165 11595659136715702393057937)
  ·
    refine ⟨8696744352536776794793453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11595659136715702393057937 8696744352536776794793453)
    ·
      refine ⟨3261279132201291298047545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8696744352536776794793453 3261279132201291298047545)
      ·
        refine ⟨2445959349150968473535659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3261279132201291298047545 2445959349150968473535659)
        ·
          refine ⟨3668939023726452710303489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2445959349150968473535659 3668939023726452710303489)
          ·
            refine ⟨2751704267794839532727617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3668939023726452710303489 2751704267794839532727617)
            ·
              refine ⟨2063778200846129649545713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751704267794839532727617 2063778200846129649545713)
              ·
                refine ⟨1547833650634597237159285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2063778200846129649545713 1547833650634597237159285)
                ·
                  refine ⟨145109404746993490983683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1547833650634597237159285 145109404746993490983683)
                  ·
                    rfl

theorem cell22_1271698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1271698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271698 prefixEnd_1271698 := by exact prefixLift 1271698
  have htrace : WordTrace (prefixWord ++ tailWord_1271698) baseStart_1271698 baseEnd_1271698 := by
    simpa [prefixWord, tailWord_1271698, baseEnd_1271698] using wordTrace_append hprefix tailTrace_1271698
  have hstable : (prefixWord ++ tailWord_1271698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271698).length < 2 ^ (prefixWord ++ tailWord_1271698).sum := by decide
  have hdescent : baseEnd_1271698 < baseStart_1271698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271741 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_1271741 : Nat := 118140960795 + 1271741 * 2 ^ 59
def prefixEnd_1271741 : Nat := 4983230072969 + 3 ^ 40 * 1271741 * 2
def baseEnd_1271741 : Nat := 435342934019742694125917

theorem tailTrace_1271741 : CollatzResearch.WordTrace tailWord_1271741 prefixEnd_1271741 435342934019742694125917 := by
  unfold tailWord_1271741
  simp only [CollatzResearch.WordTrace]
  refine ⟨46384204885707027916047077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30922803257138018610698051 46384204885707027916047077)
  ·
    refine ⟨8697038416070067734258827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46384204885707027916047077 8697038416070067734258827)
    ·
      refine ⟨13045557624105101601388241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8697038416070067734258827 13045557624105101601388241)
      ·
        refine ⟨9784168218078826201041181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13045557624105101601388241 9784168218078826201041181)
        ·
          refine ⟨3669063081779559825390443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9784168218078826201041181 3669063081779559825390443)
          ·
            refine ⟨5503594622669339738085665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669063081779559825390443 5503594622669339738085665)
            ·
              refine ⟨4127695967002004803564249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5503594622669339738085665 4127695967002004803564249)
              ·
                refine ⟨3095771975251503602673187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127695967002004803564249 3095771975251503602673187)
                ·
                  refine ⟨4643657962877255404009781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095771975251503602673187 4643657962877255404009781)
                  ·
                    refine ⟨435342934019742694125917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4643657962877255404009781 435342934019742694125917)
                    ·
                      rfl

theorem cell22_1271741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_1271741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271741 prefixEnd_1271741 := by exact prefixLift 1271741
  have htrace : WordTrace (prefixWord ++ tailWord_1271741) baseStart_1271741 baseEnd_1271741 := by
    simpa [prefixWord, tailWord_1271741, baseEnd_1271741] using wordTrace_append hprefix tailTrace_1271741
  have hstable : (prefixWord ++ tailWord_1271741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271741).length < 2 ^ (prefixWord ++ tailWord_1271741).sum := by decide
  have hdescent : baseEnd_1271741 < baseStart_1271741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271775 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 2, 3]
def baseStart_1271775 : Nat := 118140960795 + 1271775 * 2 ^ 59
def prefixEnd_1271775 : Nat := 4983230072969 + 3 ^ 40 * 1271775 * 2
def baseEnd_1271775 : Nat := 435354572914577938775813

theorem tailTrace_1271775 : CollatzResearch.WordTrace tailWord_1271775 prefixEnd_1271775 435354572914577938775813 := by
  unfold tailWord_1271775
  simp only [CollatzResearch.WordTrace]
  refine ⟨46385444967583851722784779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30923629978389234481856519 46385444967583851722784779)
  ·
    refine ⟨69578167451375777584177169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46385444967583851722784779 69578167451375777584177169)
    ·
      refine ⟨52183625588531833188132877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69578167451375777584177169 52183625588531833188132877)
      ·
        refine ⟨19568859595699437445549829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52183625588531833188132877 19568859595699437445549829)
        ·
          refine ⟨3669161174193644521040593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19568859595699437445549829 3669161174193644521040593)
          ·
            refine ⟨2751870880645233390780445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3669161174193644521040593 2751870880645233390780445)
            ·
              refine ⟨1031951580241962521542667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2751870880645233390780445 1031951580241962521542667)
              ·
                refine ⟨1547927370362943782314001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031951580241962521542667 1547927370362943782314001)
                ·
                  refine ⟨1160945527772207836735501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1547927370362943782314001 1160945527772207836735501)
                  ·
                    refine ⟨435354572914577938775813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1160945527772207836735501 435354572914577938775813)
                    ·
                      rfl

theorem cell22_1271775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 3].length) (baseStart_1271775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271775 prefixEnd_1271775 := by exact prefixLift 1271775
  have htrace : WordTrace (prefixWord ++ tailWord_1271775) baseStart_1271775 baseEnd_1271775 := by
    simpa [prefixWord, tailWord_1271775, baseEnd_1271775] using wordTrace_append hprefix tailTrace_1271775
  have hstable : (prefixWord ++ tailWord_1271775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271775).length < 2 ^ (prefixWord ++ tailWord_1271775).sum := by decide
  have hdescent : baseEnd_1271775 < baseStart_1271775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271816 : List Nat := [2, 1, 3, 2, 1, 2, 2, 4, 5]
def baseStart_1271816 : Nat := 118140960795 + 1271816 * 2 ^ 59
def prefixEnd_1271816 : Nat := 4983230072969 + 3 ^ 40 * 1271816 * 2
def baseEnd_1271816 : Nat := 145122869350822499500229

theorem tailTrace_1271816 : CollatzResearch.WordTrace tailWord_1271816 prefixEnd_1271816 145122869350822499500229 := by
  unfold tailWord_1271816
  simp only [CollatzResearch.WordTrace]
  refine ⟨23193470180217657862513651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30924626906956877150018201 23193470180217657862513651)
  ·
    refine ⟨34790205270326486793770477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23193470180217657862513651 34790205270326486793770477)
    ·
      refine ⟨13046326976372432547663929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34790205270326486793770477 13046326976372432547663929)
      ·
        refine ⟨9784745232279324410747947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13046326976372432547663929 9784745232279324410747947)
        ·
          refine ⟨14677117848418986616121921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9784745232279324410747947 14677117848418986616121921)
          ·
            refine ⟨11007838386314239962091441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14677117848418986616121921 11007838386314239962091441)
            ·
              refine ⟨8255878789735679971568581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11007838386314239962091441 8255878789735679971568581)
              ·
                refine ⟨1547977273075439994669109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8255878789735679971568581 1547977273075439994669109)
                ·
                  refine ⟨145122869350822499500229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1547977273075439994669109 145122869350822499500229)
                  ·
                    rfl

theorem cell22_1271816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_1271816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271816 prefixEnd_1271816 := by exact prefixLift 1271816
  have htrace : WordTrace (prefixWord ++ tailWord_1271816) baseStart_1271816 baseEnd_1271816 := by
    simpa [prefixWord, tailWord_1271816, baseEnd_1271816] using wordTrace_append hprefix tailTrace_1271816
  have hstable : (prefixWord ++ tailWord_1271816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271816).length < 2 ^ (prefixWord ++ tailWord_1271816).sum := by decide
  have hdescent : baseEnd_1271816 < baseStart_1271816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271893 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1271893 : Nat := 118140960795 + 1271893 * 2 ^ 59
def prefixEnd_1271893 : Nat := 4983230072969 + 3 ^ 40 * 1271893 * 2
def baseEnd_1271893 : Nat := 435394966726064964325451

theorem tailTrace_1271893 : CollatzResearch.WordTrace tailWord_1271893 prefixEnd_1271893 435394966726064964325451 := by
  unfold tailWord_1271893
  simp only [CollatzResearch.WordTrace]
  refine ⟨46389748781156357875580333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30926499187437571917053555 46389748781156357875580333)
  ·
    refine ⟨17396155792933634203342625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46389748781156357875580333 17396155792933634203342625)
    ·
      refine ⟨13047116844700225652506969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17396155792933634203342625 13047116844700225652506969)
      ·
        refine ⟨9785337633525169239380227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13047116844700225652506969 9785337633525169239380227)
        ·
          refine ⟨14678006450287753859070341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9785337633525169239380227 14678006450287753859070341)
          ·
            refine ⟨2752126209428953848575689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14678006450287753859070341 2752126209428953848575689)
            ·
              refine ⟨2064094657071715386431767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2752126209428953848575689 2064094657071715386431767)
              ·
                refine ⟨3096141985607573079647651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064094657071715386431767 3096141985607573079647651)
                ·
                  refine ⟨4644212978411359619471477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096141985607573079647651 4644212978411359619471477)
                  ·
                    refine ⟨435394966726064964325451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4644212978411359619471477 435394966726064964325451)
                    ·
                      rfl

theorem cell22_1271893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1271893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271893 prefixEnd_1271893 := by exact prefixLift 1271893
  have htrace : WordTrace (prefixWord ++ tailWord_1271893) baseStart_1271893 baseEnd_1271893 := by
    simpa [prefixWord, tailWord_1271893, baseEnd_1271893] using wordTrace_append hprefix tailTrace_1271893
  have hstable : (prefixWord ++ tailWord_1271893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271893).length < 2 ^ (prefixWord ++ tailWord_1271893).sum := by decide
  have hdescent : baseEnd_1271893 < baseStart_1271893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271908 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_1271908 : Nat := 118140960795 + 1271908 * 2 ^ 59
def prefixEnd_1271908 : Nat := 4983230072969 + 3 ^ 40 * 1271908 * 2
def baseEnd_1271908 : Nat := 435400101532609925200405

theorem tailTrace_1271908 : CollatzResearch.WordTrace tailWord_1271908 prefixEnd_1271908 435400101532609925200405 := by
  unfold tailWord_1271908
  simp only [CollatzResearch.WordTrace]
  refine ⟨23195147938051007718688189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30926863917401343624917585 23195147938051007718688189)
  ·
    refine ⟨8698180476769127894508071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23195147938051007718688189 8698180476769127894508071)
    ·
      refine ⟨13047270715153691841762107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8698180476769127894508071 13047270715153691841762107)
      ·
        refine ⟨19570906072730537762643161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13047270715153691841762107 19570906072730537762643161)
        ·
          refine ⟨14678179554547903321982371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19570906072730537762643161 14678179554547903321982371)
          ·
            refine ⟨22017269331821854982973557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14678179554547903321982371 22017269331821854982973557)
            ·
              refine ⟨2064118999858298904653771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22017269331821854982973557 2064118999858298904653771)
              ·
                refine ⟨3096178499787448356980657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064118999858298904653771 3096178499787448356980657)
                ·
                  refine ⟨2322133874840586267735493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096178499787448356980657 2322133874840586267735493)
                  ·
                    refine ⟨435400101532609925200405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2322133874840586267735493 435400101532609925200405)
                    ·
                      rfl

theorem cell22_1271908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_1271908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271908 prefixEnd_1271908 := by exact prefixLift 1271908
  have htrace : WordTrace (prefixWord ++ tailWord_1271908) baseStart_1271908 baseEnd_1271908 := by
    simpa [prefixWord, tailWord_1271908, baseEnd_1271908] using wordTrace_append hprefix tailTrace_1271908
  have hstable : (prefixWord ++ tailWord_1271908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271908).length < 2 ^ (prefixWord ++ tailWord_1271908).sum := by decide
  have hdescent : baseEnd_1271908 < baseStart_1271908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271914 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_1271914 : Nat := 118140960795 + 1271914 * 2 ^ 59
def prefixEnd_1271914 : Nat := 4983230072969 + 3 ^ 40 * 1271914 * 2
def baseEnd_1271914 : Nat := 435402155455227909550387

theorem tailTrace_1271914 : CollatzResearch.WordTrace tailWord_1271914 prefixEnd_1271914 435402155455227909550387 := by
  unfold tailWord_1271914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11597628678520069615523699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30927009809386852308063197 11597628678520069615523699)
  ·
    refine ⟨17396443017780104423285549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11597628678520069615523699 17396443017780104423285549)
    ·
      refine ⟨6523666131667539158732081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17396443017780104423285549 6523666131667539158732081)
      ·
        refine ⟨4892749598750654369049061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6523666131667539158732081 4892749598750654369049061)
        ·
          refine ⟨917390549765747694196699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4892749598750654369049061 917390549765747694196699)
          ·
            refine ⟨1376085824648621541295049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917390549765747694196699 1376085824648621541295049)
            ·
              refine ⟨1032064368486466155971287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376085824648621541295049 1032064368486466155971287)
              ·
                refine ⟨1548096552729699233956931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032064368486466155971287 1548096552729699233956931)
                ·
                  refine ⟨2322144829094548850935397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548096552729699233956931 2322144829094548850935397)
                  ·
                    refine ⟨435402155455227909550387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2322144829094548850935397 435402155455227909550387)
                    ·
                      rfl

theorem cell22_1271914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_1271914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271914 prefixEnd_1271914 := by exact prefixLift 1271914
  have htrace : WordTrace (prefixWord ++ tailWord_1271914) baseStart_1271914 baseEnd_1271914 := by
    simpa [prefixWord, tailWord_1271914, baseEnd_1271914] using wordTrace_append hprefix tailTrace_1271914
  have hstable : (prefixWord ++ tailWord_1271914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271914).length < 2 ^ (prefixWord ++ tailWord_1271914).sum := by decide
  have hdescent : baseEnd_1271914 < baseStart_1271914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1271989 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1271989 : Nat := 118140960795 + 1271989 * 2 ^ 59
def prefixEnd_1271989 : Nat := 4983230072969 + 3 ^ 40 * 1271989 * 2
def baseEnd_1271989 : Nat := 435427829487952713925157

theorem tailTrace_1271989 : CollatzResearch.WordTrace tailWord_1271989 prefixEnd_1271989 435427829487952713925157 := by
  unfold tailWord_1271989
  simp only [CollatzResearch.WordTrace]
  refine ⟨46393250188808566271075021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30928833459205710847383347 46393250188808566271075021)
  ·
    refine ⟨17397468820803212351653133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46393250188808566271075021 17397468820803212351653133)
    ·
      refine ⟨6524050807801204631869925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17397468820803212351653133 6524050807801204631869925)
      ·
        refine ⟨1223259526462725868475611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6524050807801204631869925 1223259526462725868475611)
        ·
          refine ⟨1834889289694088802713417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223259526462725868475611 1834889289694088802713417)
          ·
            refine ⟨1376166967270566602035063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1834889289694088802713417 1376166967270566602035063)
            ·
              refine ⟨2064250450905849903052595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376166967270566602035063 2064250450905849903052595)
              ·
                refine ⟨3096375676358774854578893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064250450905849903052595 3096375676358774854578893)
                ·
                  refine ⟨1161140878634540570467085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3096375676358774854578893 1161140878634540570467085)
                  ·
                    refine ⟨435427829487952713925157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161140878634540570467085 435427829487952713925157)
                    ·
                      rfl

theorem cell22_1271989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1271989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1271989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1271989 prefixEnd_1271989 := by exact prefixLift 1271989
  have htrace : WordTrace (prefixWord ++ tailWord_1271989) baseStart_1271989 baseEnd_1271989 := by
    simpa [prefixWord, tailWord_1271989, baseEnd_1271989] using wordTrace_append hprefix tailTrace_1271989
  have hstable : (prefixWord ++ tailWord_1271989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1271989).length < 2 ^ (prefixWord ++ tailWord_1271989).sum := by decide
  have hdescent : baseEnd_1271989 < baseStart_1271989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1271989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272043 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 2, 4]
def baseStart_1272043 : Nat := 118140960795 + 1272043 * 2 ^ 59
def prefixEnd_1272043 : Nat := 4983230072969 + 3 ^ 40 * 1272043 * 2
def baseEnd_1272043 : Nat := 435446314791514573074991

theorem tailTrace_1272043 : CollatzResearch.WordTrace tailWord_1272043 prefixEnd_1272043 435446314791514573074991 := by
  unfold tailWord_1272043
  simp only [CollatzResearch.WordTrace]
  refine ⟨46395219730612933493540783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30930146487075288995693855 46395219730612933493540783)
  ·
    refine ⟨69592829595919400240311175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46395219730612933493540783 69592829595919400240311175)
    ·
      refine ⟨104389244393879100360466763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69592829595919400240311175 104389244393879100360466763)
      ·
        refine ⟨156583866590818650540700145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104389244393879100360466763 156583866590818650540700145)
        ·
          refine ⟨117437899943113987905525109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156583866590818650540700145 117437899943113987905525109)
          ·
            refine ⟨11009803119666936366142979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117437899943113987905525109 11009803119666936366142979)
            ·
              refine ⟨16514704679500404549214469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11009803119666936366142979 16514704679500404549214469)
              ·
                refine ⟨3096507127406325852977713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16514704679500404549214469 3096507127406325852977713)
                ·
                  refine ⟨2322380345554744389733285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096507127406325852977713 2322380345554744389733285)
                  ·
                    refine ⟨435446314791514573074991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2322380345554744389733285 435446314791514573074991)
                    ·
                      rfl

theorem cell22_1272043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 4].length) (baseStart_1272043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272043 prefixEnd_1272043 := by exact prefixLift 1272043
  have htrace : WordTrace (prefixWord ++ tailWord_1272043) baseStart_1272043 baseEnd_1272043 := by
    simpa [prefixWord, tailWord_1272043, baseEnd_1272043] using wordTrace_append hprefix tailTrace_1272043
  have hstable : (prefixWord ++ tailWord_1272043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272043).length < 2 ^ (prefixWord ++ tailWord_1272043).sum := by decide
  have hdescent : baseEnd_1272043 < baseStart_1272043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272047 : List Nat := [1, 1, 2, 1, 6, 1, 4, 2, 4]
def baseStart_1272047 : Nat := 118140960795 + 1272047 * 2 ^ 59
def prefixEnd_1272047 : Nat := 4983230072969 + 3 ^ 40 * 1272047 * 2
def baseEnd_1272047 : Nat := 145149228024419965324993

theorem tailTrace_1272047 : CollatzResearch.WordTrace tailWord_1272047 prefixEnd_1272047 145149228024419965324993 := by
  unfold tailWord_1272047
  simp only [CollatzResearch.WordTrace]
  refine ⟨46395365622598442176686395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30930243748398961451124263 46395365622598442176686395)
  ·
    refine ⟨69593048433897663265029593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46395365622598442176686395 69593048433897663265029593)
    ·
      refine ⟨52194786325423247448772195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69593048433897663265029593 52194786325423247448772195)
      ·
        refine ⟨78292179488134871173158293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52194786325423247448772195 78292179488134871173158293)
        ·
          refine ⟨3669945913506322086241795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78292179488134871173158293 3669945913506322086241795)
          ·
            refine ⟨5504918870259483129362693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669945913506322086241795 5504918870259483129362693)
            ·
              refine ⟨1032172288173653086755505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5504918870259483129362693 1032172288173653086755505)
              ·
                refine ⟨774129216130239815066629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032172288173653086755505 774129216130239815066629)
                ·
                  refine ⟨145149228024419965324993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 774129216130239815066629 145149228024419965324993)
                  ·
                    rfl

theorem cell22_1272047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 4].length) (baseStart_1272047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272047 prefixEnd_1272047 := by exact prefixLift 1272047
  have htrace : WordTrace (prefixWord ++ tailWord_1272047) baseStart_1272047 baseEnd_1272047 := by
    simpa [prefixWord, tailWord_1272047, baseEnd_1272047] using wordTrace_append hprefix tailTrace_1272047
  have hstable : (prefixWord ++ tailWord_1272047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272047).length < 2 ^ (prefixWord ++ tailWord_1272047).sum := by decide
  have hdescent : baseEnd_1272047 < baseStart_1272047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272058 : List Nat := [3, 1, 1, 1, 1, 5, 3, 7]
def baseStart_1272058 : Nat := 118140960795 + 1272058 * 2 ^ 59
def prefixEnd_1272058 : Nat := 4983230072969 + 3 ^ 40 * 1272058 * 2
def baseEnd_1272058 : Nat := 48383494399784392661105

theorem tailTrace_1272058 : CollatzResearch.WordTrace tailWord_1272058 prefixEnd_1272058 48383494399784392661105 := by
  unfold tailWord_1272058
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598941706389647763834207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30930511217039060703557885 11598941706389647763834207)
  ·
    refine ⟨17398412559584471645751311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11598941706389647763834207 17398412559584471645751311)
    ·
      refine ⟨26097618839376707468626967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17398412559584471645751311 26097618839376707468626967)
      ·
        refine ⟨39146428259065061202940451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26097618839376707468626967 39146428259065061202940451)
        ·
          refine ⟨58719642388597591804410677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39146428259065061202940451 58719642388597591804410677)
          ·
            refine ⟨5504966473931024231663501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58719642388597591804410677 5504966473931024231663501)
            ·
              refine ⟨2064362427724134086873813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5504966473931024231663501 2064362427724134086873813)
              ·
                refine ⟨48383494399784392661105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2064362427724134086873813 48383494399784392661105)
                ·
                  rfl

theorem cell22_1272058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_1272058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272058 prefixEnd_1272058 := by exact prefixLift 1272058
  have htrace : WordTrace (prefixWord ++ tailWord_1272058) baseStart_1272058 baseEnd_1272058 := by
    simpa [prefixWord, tailWord_1272058, baseEnd_1272058] using wordTrace_append hprefix tailTrace_1272058
  have hstable : (prefixWord ++ tailWord_1272058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272058).length < 2 ^ (prefixWord ++ tailWord_1272058).sum := by decide
  have hdescent : baseEnd_1272058 < baseStart_1272058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272062 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1272062 : Nat := 118140960795 + 1272062 * 2 ^ 59
def prefixEnd_1272062 : Nat := 4983230072969 + 3 ^ 40 * 1272062 * 2
def baseEnd_1272062 : Nat := 435452818879804856849933

theorem tailTrace_1272062 : CollatzResearch.WordTrace tailWord_1272062 prefixEnd_1272062 435452818879804856849933 := by
  unfold tailWord_1272062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799489089693012467310305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30930608478362733158988293 5799489089693012467310305)
  ·
    refine ⟨4349616817269759350482729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5799489089693012467310305 4349616817269759350482729)
    ·
      refine ⟨3262212612952319512862047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4349616817269759350482729 3262212612952319512862047)
      ·
        refine ⟨4893318919428479269293071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262212612952319512862047 4893318919428479269293071)
        ·
          refine ⟨7339978379142718903939607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893318919428479269293071 7339978379142718903939607)
          ·
            refine ⟨11009967568714078355909411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7339978379142718903939607 11009967568714078355909411)
            ·
              refine ⟨16514951353071117533864117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11009967568714078355909411 16514951353071117533864117)
              ·
                refine ⟨1548276689350417268799761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16514951353071117533864117 1548276689350417268799761)
                ·
                  refine ⟨1161207517012812951599821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1548276689350417268799761 1161207517012812951599821)
                  ·
                    refine ⟨435452818879804856849933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161207517012812951599821 435452818879804856849933)
                    ·
                      rfl

theorem cell22_1272062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1272062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272062 prefixEnd_1272062 := by exact prefixLift 1272062
  have htrace : WordTrace (prefixWord ++ tailWord_1272062) baseStart_1272062 baseEnd_1272062 := by
    simpa [prefixWord, tailWord_1272062, baseEnd_1272062] using wordTrace_append hprefix tailTrace_1272062
  have hstable : (prefixWord ++ tailWord_1272062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272062).length < 2 ^ (prefixWord ++ tailWord_1272062).sum := by decide
  have hdescent : baseEnd_1272062 < baseStart_1272062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272165 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 6]
def baseStart_1272165 : Nat := 118140960795 + 1272165 * 2 ^ 59
def prefixEnd_1272165 : Nat := 4983230072969 + 3 ^ 40 * 1272165 * 2
def baseEnd_1272165 : Nat := 145162692628248973841539

theorem tailTrace_1272165 : CollatzResearch.WordTrace tailWord_1272165 prefixEnd_1272165 145162692628248973841539 := by
  unfold tailWord_1272165
  simp only [CollatzResearch.WordTrace]
  refine ⟨46399669436170948329481949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30933112957447298886321299 46399669436170948329481949)
  ·
    refine ⟨17399876038564105623555731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46399669436170948329481949 17399876038564105623555731)
    ·
      refine ⟨26099814057846158435333597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17399876038564105623555731 26099814057846158435333597)
      ·
        refine ⟨9787430271692309413250099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26099814057846158435333597 9787430271692309413250099)
        ·
          refine ⟨14681145407538464119875149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9787430271692309413250099 14681145407538464119875149)
          ·
            refine ⟨5505429527826924044953181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14681145407538464119875149 5505429527826924044953181)
            ·
              refine ⟨2064536072935096516857443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5505429527826924044953181 2064536072935096516857443)
              ·
                refine ⟨3096804109402644775286165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064536072935096516857443 3096804109402644775286165)
                ·
                  refine ⟨145162692628248973841539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3096804109402644775286165 145162692628248973841539)
                  ·
                    rfl

theorem cell22_1272165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_1272165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272165 prefixEnd_1272165 := by exact prefixLift 1272165
  have htrace : WordTrace (prefixWord ++ tailWord_1272165) baseStart_1272165 baseEnd_1272165 := by
    simpa [prefixWord, tailWord_1272165, baseEnd_1272165] using wordTrace_append hprefix tailTrace_1272165
  have hstable : (prefixWord ++ tailWord_1272165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272165).length < 2 ^ (prefixWord ++ tailWord_1272165).sum := by decide
  have hdescent : baseEnd_1272165 < baseStart_1272165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272208 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_1272208 : Nat := 118140960795 + 1272208 * 2 ^ 59
def prefixEnd_1272208 : Nat := 4983230072969 + 3 ^ 40 * 1272208 * 2
def baseEnd_1272208 : Nat := 435502797663509142699485

theorem tailTrace_1272208 : CollatzResearch.WordTrace tailWord_1272208 prefixEnd_1272208 435502797663509142699485 := by
  unfold tailWord_1272208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23200618887507583336648639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30934158516676777782198185 23200618887507583336648639)
  ·
    refine ⟨34800928331261375004972959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23200618887507583336648639 34800928331261375004972959)
    ·
      refine ⟨52201392496892062507459439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34800928331261375004972959 52201392496892062507459439)
      ·
        refine ⟨78302088745338093761189159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52201392496892062507459439 78302088745338093761189159)
        ·
          refine ⟨117453133118007140641783739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78302088745338093761189159 117453133118007140641783739)
          ·
            refine ⟨176179699677010710962675609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117453133118007140641783739 176179699677010710962675609)
            ·
              refine ⟨132134774757758033222006707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176179699677010710962675609 132134774757758033222006707)
              ·
                refine ⟨198202162136637049833010061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132134774757758033222006707 198202162136637049833010061)
                ·
                  refine ⟨74325810801238893687378773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198202162136637049833010061 74325810801238893687378773)
                  ·
                    refine ⟨435502797663509142699485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74325810801238893687378773 435502797663509142699485)
                    ·
                      rfl

theorem cell22_1272208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_1272208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272208 prefixEnd_1272208 := by exact prefixLift 1272208
  have htrace : WordTrace (prefixWord ++ tailWord_1272208) baseStart_1272208 baseEnd_1272208 := by
    simpa [prefixWord, tailWord_1272208, baseEnd_1272208] using wordTrace_append hprefix tailTrace_1272208
  have hstable : (prefixWord ++ tailWord_1272208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272208).length < 2 ^ (prefixWord ++ tailWord_1272208).sum := by decide
  have hdescent : baseEnd_1272208 < baseStart_1272208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272216 : List Nat := [2, 1, 2, 5, 1, 3, 2, 2, 4]
def baseStart_1272216 : Nat := 118140960795 + 1272216 * 2 ^ 59
def prefixEnd_1272216 : Nat := 4983230072969 + 3 ^ 40 * 1272216 * 2
def baseEnd_1272216 : Nat := 145168512075666596166487

theorem tailTrace_1272216 : CollatzResearch.WordTrace tailWord_1272216 prefixEnd_1272216 145168512075666596166487 := by
  unfold tailWord_1272216
  simp only [CollatzResearch.WordTrace]
  refine ⟨23200764779493092019794251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30934353039324122693059001 23200764779493092019794251)
  ·
    refine ⟨34801147169239638029691377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23200764779493092019794251 34801147169239638029691377)
    ·
      refine ⟨26100860376929728522268533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34801147169239638029691377 26100860376929728522268533)
      ·
        refine ⟨2446955660337162048962675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26100860376929728522268533 2446955660337162048962675)
        ·
          refine ⟨3670433490505743073444013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446955660337162048962675 3670433490505743073444013)
          ·
            refine ⟨1376412558939653652541505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3670433490505743073444013 1376412558939653652541505)
            ·
              refine ⟨1032309419204740239406129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1376412558939653652541505 1032309419204740239406129)
              ·
                refine ⟨774232064403555179554597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032309419204740239406129 774232064403555179554597)
                ·
                  refine ⟨145168512075666596166487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 774232064403555179554597 145168512075666596166487)
                  ·
                    rfl

theorem cell22_1272216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 4].length) (baseStart_1272216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272216 prefixEnd_1272216 := by exact prefixLift 1272216
  have htrace : WordTrace (prefixWord ++ tailWord_1272216) baseStart_1272216 baseEnd_1272216 := by
    simpa [prefixWord, tailWord_1272216, baseEnd_1272216] using wordTrace_append hprefix tailTrace_1272216
  have hstable : (prefixWord ++ tailWord_1272216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272216).length < 2 ^ (prefixWord ++ tailWord_1272216).sum := by decide
  have hdescent : baseEnd_1272216 < baseStart_1272216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272242 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_1272242 : Nat := 118140960795 + 1272242 * 2 ^ 59
def prefixEnd_1272242 : Nat := 4983230072969 + 3 ^ 40 * 1272242 * 2
def baseEnd_1272242 : Nat := 435514436558344387349381

theorem tailTrace_1272242 : CollatzResearch.WordTrace tailWord_1272242 prefixEnd_1272242 435514436558344387349381 := by
  unfold tailWord_1272242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11600619464222997620008745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30934985237927993653356653 11600619464222997620008745)
  ·
    refine ⟨8700464598167248215006559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11600619464222997620008745 8700464598167248215006559)
    ·
      refine ⟨13050696897250872322509839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8700464598167248215006559 13050696897250872322509839)
      ·
        refine ⟨19576045345876308483764759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13050696897250872322509839 19576045345876308483764759)
        ·
          refine ⟨29364068018814462725647139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19576045345876308483764759 29364068018814462725647139)
          ·
            refine ⟨44046102028221694088470709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29364068018814462725647139 44046102028221694088470709)
            ·
              refine ⟨4129322065145783820794129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44046102028221694088470709 4129322065145783820794129)
              ·
                refine ⟨3096991548859337865595597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4129322065145783820794129 3096991548859337865595597)
                ·
                  refine ⟨1161371830822251699598349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3096991548859337865595597 1161371830822251699598349)
                  ·
                    refine ⟨435514436558344387349381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161371830822251699598349 435514436558344387349381)
                    ·
                      rfl

theorem cell22_1272242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_1272242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272242 prefixEnd_1272242 := by exact prefixLift 1272242
  have htrace : WordTrace (prefixWord ++ tailWord_1272242) baseStart_1272242 baseEnd_1272242 := by
    simpa [prefixWord, tailWord_1272242, baseEnd_1272242] using wordTrace_append hprefix tailTrace_1272242
  have hstable : (prefixWord ++ tailWord_1272242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272242).length < 2 ^ (prefixWord ++ tailWord_1272242).sum := by decide
  have hdescent : baseEnd_1272242 < baseStart_1272242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272276 : List Nat := [2, 4, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_1272276 : Nat := 118140960795 + 1272276 * 2 ^ 59
def prefixEnd_1272276 : Nat := 4983230072969 + 3 ^ 40 * 1272276 * 2
def baseEnd_1272276 : Nat := 435526075453179631999277

theorem tailTrace_1272276 : CollatzResearch.WordTrace tailWord_1272276 prefixEnd_1272276 435526075453179631999277 := by
  unfold tailWord_1272276
  simp only [CollatzResearch.WordTrace]
  refine ⟨23201858969384407143386341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30935811959179209524515121 23201858969384407143386341)
  ·
    refine ⟨4350348556759576339384939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23201858969384407143386341 4350348556759576339384939)
    ·
      refine ⟨6525522835139364509077409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4350348556759576339384939 6525522835139364509077409)
      ·
        refine ⟨4894142126354523381808057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6525522835139364509077409 4894142126354523381808057)
        ·
          refine ⟨3670606594765892536356043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4894142126354523381808057 3670606594765892536356043)
          ·
            refine ⟨5505909892148838804534065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670606594765892536356043 5505909892148838804534065)
            ·
              refine ⟨4129432419111629103400549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5505909892148838804534065 4129432419111629103400549)
              ·
                refine ⟨774268578583430456887603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4129432419111629103400549 774268578583430456887603)
                ·
                  refine ⟨1161402867875145685331405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774268578583430456887603 1161402867875145685331405)
                  ·
                    refine ⟨435526075453179631999277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161402867875145685331405 435526075453179631999277)
                    ·
                      rfl

theorem cell22_1272276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_1272276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272276 prefixEnd_1272276 := by exact prefixLift 1272276
  have htrace : WordTrace (prefixWord ++ tailWord_1272276) baseStart_1272276 baseEnd_1272276 := by
    simpa [prefixWord, tailWord_1272276, baseEnd_1272276] using wordTrace_append hprefix tailTrace_1272276
  have hstable : (prefixWord ++ tailWord_1272276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272276).length < 2 ^ (prefixWord ++ tailWord_1272276).sum := by decide
  have hdescent : baseEnd_1272276 < baseStart_1272276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272300 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 6]
def baseStart_1272300 : Nat := 118140960795 + 1272300 * 2 ^ 59
def prefixEnd_1272300 : Nat := 4983230072969 + 3 ^ 40 * 1272300 * 2
def baseEnd_1272300 : Nat := 145178097047883856466401

theorem tailTrace_1272300 : CollatzResearch.WordTrace tailWord_1272300 prefixEnd_1272300 145178097047883856466401 := by
  unfold tailWord_1272300
  simp only [CollatzResearch.WordTrace]
  refine ⟨23202296645340933192823177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30936395527121244257097569 23202296645340933192823177)
  ·
    refine ⟨17401722484005699894617383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23202296645340933192823177 17401722484005699894617383)
    ·
      refine ⟨26102583726008549841926075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17401722484005699894617383 26102583726008549841926075)
      ·
        refine ⟨39153875589012824762889113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26102583726008549841926075 39153875589012824762889113)
        ·
          refine ⟨29365406691759618572166835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39153875589012824762889113 29365406691759618572166835)
          ·
            refine ⟨44048110037639427858250253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29365406691759618572166835 44048110037639427858250253)
            ·
              refine ⟨16518041264114785446843845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44048110037639427858250253 16518041264114785446843845)
              ·
                refine ⟨3097132737021522271283221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16518041264114785446843845 3097132737021522271283221)
                ·
                  refine ⟨145178097047883856466401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3097132737021522271283221 145178097047883856466401)
                  ·
                    rfl

theorem cell22_1272300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_1272300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272300 prefixEnd_1272300 := by exact prefixLift 1272300
  have htrace : WordTrace (prefixWord ++ tailWord_1272300) baseStart_1272300 baseEnd_1272300 := by
    simpa [prefixWord, tailWord_1272300, baseEnd_1272300] using wordTrace_append hprefix tailTrace_1272300
  have hstable : (prefixWord ++ tailWord_1272300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272300).length < 2 ^ (prefixWord ++ tailWord_1272300).sum := by decide
  have hdescent : baseEnd_1272300 < baseStart_1272300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272334 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_1272334 : Nat := 118140960795 + 1272334 * 2 ^ 59
def prefixEnd_1272334 : Nat := 4983230072969 + 3 ^ 40 * 1272334 * 2
def baseEnd_1272334 : Nat := 145181976679495604683033

theorem tailTrace_1272334 : CollatzResearch.WordTrace tailWord_1272334 prefixEnd_1272334 145181976679495604683033 := by
  unfold tailWord_1272334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800729171569836274048007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30937222248372460128256037 5800729171569836274048007)
  ·
    refine ⟨8701093757354754411072011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5800729171569836274048007 8701093757354754411072011)
    ·
      refine ⟨13051640636032131616608017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8701093757354754411072011 13051640636032131616608017)
      ·
        refine ⟨9788730477024098712456013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13051640636032131616608017 9788730477024098712456013)
        ·
          refine ⟨3670773928884037017171005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9788730477024098712456013 3670773928884037017171005)
          ·
            refine ⟨1376540223331513881439127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3670773928884037017171005 1376540223331513881439127)
            ·
              refine ⟨2064810334997270822158691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376540223331513881439127 2064810334997270822158691)
              ·
                refine ⟨3097215502495906233238037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064810334997270822158691 3097215502495906233238037)
                ·
                  refine ⟨145181976679495604683033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3097215502495906233238037 145181976679495604683033)
                  ·
                    rfl

theorem cell22_1272334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_1272334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272334 prefixEnd_1272334 := by exact prefixLift 1272334
  have htrace : WordTrace (prefixWord ++ tailWord_1272334) baseStart_1272334 baseEnd_1272334 := by
    simpa [prefixWord, tailWord_1272334, baseEnd_1272334] using wordTrace_append hprefix tailTrace_1272334
  have hstable : (prefixWord ++ tailWord_1272334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272334).length < 2 ^ (prefixWord ++ tailWord_1272334).sum := by decide
  have hdescent : baseEnd_1272334 < baseStart_1272334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272362 : List Nat := [3, 1, 4, 1, 1, 2, 2, 8]
def baseStart_1272362 : Nat := 118140960795 + 1272362 * 2 ^ 59
def prefixEnd_1272362 : Nat := 4983230072969 + 3 ^ 40 * 1272362 * 2
def baseEnd_1272362 : Nat := 48395057223411563816557

theorem tailTrace_1272362 : CollatzResearch.WordTrace tailWord_1272362 prefixEnd_1272362 48395057223411563816557 := by
  unfold tailWord_1272362
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601713654114312743600835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30937903077638167316268893 11601713654114312743600835)
  ·
    refine ⟨17402570481171469115401253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11601713654114312743600835 17402570481171469115401253)
    ·
      refine ⟨3262981965219650459137735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17402570481171469115401253 3262981965219650459137735)
      ·
        refine ⟨4894472947829475688706603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262981965219650459137735 4894472947829475688706603)
        ·
          refine ⟨7341709421744213533059905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894472947829475688706603 7341709421744213533059905)
          ·
            refine ⟨5506282066308160149794929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7341709421744213533059905 5506282066308160149794929)
            ·
              refine ⟨4129711549731120112346197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5506282066308160149794929 4129711549731120112346197)
              ·
                refine ⟨48395057223411563816557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4129711549731120112346197 48395057223411563816557)
                ·
                  rfl

theorem cell22_1272362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_1272362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272362 prefixEnd_1272362 := by exact prefixLift 1272362
  have htrace : WordTrace (prefixWord ++ tailWord_1272362) baseStart_1272362 baseEnd_1272362 := by
    simpa [prefixWord, tailWord_1272362, baseEnd_1272362] using wordTrace_append hprefix tailTrace_1272362
  have hstable : (prefixWord ++ tailWord_1272362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272362).length < 2 ^ (prefixWord ++ tailWord_1272362).sum := by decide
  have hdescent : baseEnd_1272362 < baseStart_1272362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272407 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 5]
def baseStart_1272407 : Nat := 118140960795 + 1272407 * 2 ^ 59
def prefixEnd_1272407 : Nat := 4983230072969 + 3 ^ 40 * 1272407 * 2
def baseEnd_1272407 : Nat := 145190306476779652324625

theorem tailTrace_1272407 : CollatzResearch.WordTrace tailWord_1272407 prefixEnd_1272407 145190306476779652324625 := by
  unfold tailWord_1272407
  simp only [CollatzResearch.WordTrace]
  refine ⟨46408495901294223659791475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30938997267529482439860983 46408495901294223659791475)
  ·
    refine ⟨69612743851941335489687213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46408495901294223659791475 69612743851941335489687213)
    ·
      refine ⟨26104778944478000808632705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69612743851941335489687213 26104778944478000808632705)
      ·
        refine ⟨19578584208358500606474529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26104778944478000808632705 19578584208358500606474529)
        ·
          refine ⟨14683938156268875454855897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19578584208358500606474529 14683938156268875454855897)
          ·
            refine ⟨11012953617201656591141923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14683938156268875454855897 11012953617201656591141923)
            ·
              refine ⟨16519430425802484886712885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11012953617201656591141923 16519430425802484886712885)
              ·
                refine ⟨1548696602418982958129333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16519430425802484886712885 1548696602418982958129333)
                ·
                  refine ⟨145190306476779652324625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1548696602418982958129333 145190306476779652324625)
                  ·
                    rfl

theorem cell22_1272407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 5].length) (baseStart_1272407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272407 prefixEnd_1272407 := by exact prefixLift 1272407
  have htrace : WordTrace (prefixWord ++ tailWord_1272407) baseStart_1272407 baseEnd_1272407 := by
    simpa [prefixWord, tailWord_1272407, baseEnd_1272407] using wordTrace_append hprefix tailTrace_1272407
  have hstable : (prefixWord ++ tailWord_1272407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272407).length < 2 ^ (prefixWord ++ tailWord_1272407).sum := by decide
  have hdescent : baseEnd_1272407 < baseStart_1272407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272484 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_1272484 : Nat := 118140960795 + 1272484 * 2 ^ 59
def prefixEnd_1272484 : Nat := 4983230072969 + 3 ^ 40 * 1272484 * 2
def baseEnd_1272484 : Nat := 435597278103936422798639

theorem tailTrace_1272484 : CollatzResearch.WordTrace tailWord_1272484 prefixEnd_1272484 435597278103936422798639 := by
  unfold tailWord_1272484
  simp only [CollatzResearch.WordTrace]
  refine ⟨23205652161007632905172253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30940869548010177206896337 23205652161007632905172253)
  ·
    refine ⟨8702119560377862339439595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23205652161007632905172253 8702119560377862339439595)
    ·
      refine ⟨13053179340566793509159393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8702119560377862339439595 13053179340566793509159393)
      ·
        refine ⟨9789884505425095131869545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13053179340566793509159393 9789884505425095131869545)
        ·
          refine ⟨7342413379068821348902159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9789884505425095131869545 7342413379068821348902159)
          ·
            refine ⟨11013620068603232023353239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7342413379068821348902159 11013620068603232023353239)
            ·
              refine ⟨16520430102904848035029859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11013620068603232023353239 16520430102904848035029859)
              ·
                refine ⟨24780645154357272052544789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16520430102904848035029859 24780645154357272052544789)
                ·
                  refine ⟨1161592741610497127463037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24780645154357272052544789 1161592741610497127463037)
                  ·
                    refine ⟨435597278103936422798639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161592741610497127463037 435597278103936422798639)
                    ·
                      rfl

theorem cell22_1272484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_1272484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272484 prefixEnd_1272484 := by exact prefixLift 1272484
  have htrace : WordTrace (prefixWord ++ tailWord_1272484) baseStart_1272484 baseEnd_1272484 := by
    simpa [prefixWord, tailWord_1272484, baseEnd_1272484] using wordTrace_append hprefix tailTrace_1272484
  have hstable : (prefixWord ++ tailWord_1272484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272484).length < 2 ^ (prefixWord ++ tailWord_1272484).sum := by decide
  have hdescent : baseEnd_1272484 < baseStart_1272484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272499 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 2, 4]
def baseStart_1272499 : Nat := 118140960795 + 1272499 * 2 ^ 59
def prefixEnd_1272499 : Nat := 4983230072969 + 3 ^ 40 * 1272499 * 2
def baseEnd_1272499 : Nat := 435602412910481383673593

theorem tailTrace_1272499 : CollatzResearch.WordTrace tailWord_1272499 prefixEnd_1272499 435602412910481383673593 := by
  unfold tailWord_1272499
  simp only [CollatzResearch.WordTrace]
  refine ⟨46411851416960923372140551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30941234277973948914760367 46411851416960923372140551)
  ·
    refine ⟨69617777125441385058210827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46411851416960923372140551 69617777125441385058210827)
    ·
      refine ⟨104426665688162077587316241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69617777125441385058210827 104426665688162077587316241)
      ·
        refine ⟨78319999266121558190487181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104426665688162077587316241 78319999266121558190487181)
        ·
          refine ⟨29369999724795584321432693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78319999266121558190487181 29369999724795584321432693)
          ·
            refine ⟨2753437474199586030134315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29369999724795584321432693 2753437474199586030134315)
            ·
              refine ⟨4130156211299379045201473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753437474199586030134315 4130156211299379045201473)
              ·
                refine ⟨3097617158474534283901105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4130156211299379045201473 3097617158474534283901105)
                ·
                  refine ⟨2323212868855900712925829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097617158474534283901105 2323212868855900712925829)
                  ·
                    refine ⟨435602412910481383673593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2323212868855900712925829 435602412910481383673593)
                    ·
                      rfl

theorem cell22_1272499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 4].length) (baseStart_1272499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272499 prefixEnd_1272499 := by exact prefixLift 1272499
  have htrace : WordTrace (prefixWord ++ tailWord_1272499) baseStart_1272499 baseEnd_1272499 := by
    simpa [prefixWord, tailWord_1272499, baseEnd_1272499] using wordTrace_append hprefix tailTrace_1272499
  have hstable : (prefixWord ++ tailWord_1272499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272499).length < 2 ^ (prefixWord ++ tailWord_1272499).sum := by decide
  have hdescent : baseEnd_1272499 < baseStart_1272499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272501 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 4, 3]
def baseStart_1272501 : Nat := 118140960795 + 1272501 * 2 ^ 59
def prefixEnd_1272501 : Nat := 4983230072969 + 3 ^ 40 * 1272501 * 2
def baseEnd_1272501 : Nat := 435603097551354045123587

theorem tailTrace_1272501 : CollatzResearch.WordTrace tailWord_1272501 prefixEnd_1272501 435603097551354045123587 := by
  unfold tailWord_1272501
  simp only [CollatzResearch.WordTrace]
  refine ⟨46411924362953677713713357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30941282908635785142475571 46411924362953677713713357)
  ·
    refine ⟨17404471636107629142642509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46411924362953677713713357 17404471636107629142642509)
    ·
      refine ⟨6526676863540360928490941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17404471636107629142642509 6526676863540360928490941)
      ·
        refine ⟨2447503823827635348184103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6526676863540360928490941 2447503823827635348184103)
        ·
          refine ⟨3671255735741453022276155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447503823827635348184103 3671255735741453022276155)
          ·
            refine ⟨5506883603612179533414233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671255735741453022276155 5506883603612179533414233)
            ·
              refine ⟨4130162702709134650060675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5506883603612179533414233 4130162702709134650060675)
              ·
                refine ⟨6195244054063701975091013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130162702709134650060675 6195244054063701975091013)
                ·
                  refine ⟨1161608260136944120329565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6195244054063701975091013 1161608260136944120329565)
                  ·
                    refine ⟨435603097551354045123587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161608260136944120329565 435603097551354045123587)
                    ·
                      rfl

theorem cell22_1272501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_1272501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272501 prefixEnd_1272501 := by exact prefixLift 1272501
  have htrace : WordTrace (prefixWord ++ tailWord_1272501) baseStart_1272501 baseEnd_1272501 := by
    simpa [prefixWord, tailWord_1272501, baseEnd_1272501] using wordTrace_append hprefix tailTrace_1272501
  have hstable : (prefixWord ++ tailWord_1272501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272501).length < 2 ^ (prefixWord ++ tailWord_1272501).sum := by decide
  have hdescent : baseEnd_1272501 < baseStart_1272501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272503 : List Nat := [1, 1, 3, 1, 6, 1, 3, 2, 4]
def baseStart_1272503 : Nat := 118140960795 + 1272503 * 2 ^ 59
def prefixEnd_1272503 : Nat := 4983230072969 + 3 ^ 40 * 1272503 * 2
def baseEnd_1272503 : Nat := 145201260730742235524527

theorem tailTrace_1272503 : CollatzResearch.WordTrace tailWord_1272503 prefixEnd_1272503 145201260730742235524527 := by
  unfold tailWord_1272503
  simp only [CollatzResearch.WordTrace]
  refine ⟨46411997308946432055286163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30941331539297621370190775 46411997308946432055286163)
  ·
    refine ⟨69617995963419648082929245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46411997308946432055286163 69617995963419648082929245)
    ·
      refine ⟨26106748486282368031098467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69617995963419648082929245 26106748486282368031098467)
      ·
        refine ⟨39160122729423552046647701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26106748486282368031098467 39160122729423552046647701)
        ·
          refine ⟨1835630752941729002186611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39160122729423552046647701 1835630752941729002186611)
          ·
            refine ⟨2753446129412593503279917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835630752941729002186611 2753446129412593503279917)
            ·
              refine ⟨1032542298529722563729969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2753446129412593503279917 1032542298529722563729969)
              ·
                refine ⟨774406723897291922797477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032542298529722563729969 774406723897291922797477)
                ·
                  refine ⟨145201260730742235524527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 774406723897291922797477 145201260730742235524527)
                  ·
                    rfl

theorem cell22_1272503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 4].length) (baseStart_1272503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272503 prefixEnd_1272503 := by exact prefixLift 1272503
  have htrace : WordTrace (prefixWord ++ tailWord_1272503) baseStart_1272503 baseEnd_1272503 := by
    simpa [prefixWord, tailWord_1272503, baseEnd_1272503] using wordTrace_append hprefix tailTrace_1272503
  have hstable : (prefixWord ++ tailWord_1272503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272503).length < 2 ^ (prefixWord ++ tailWord_1272503).sum := by decide
  have hdescent : baseEnd_1272503 < baseStart_1272503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272529 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 5, 3]
def baseStart_1272529 : Nat := 118140960795 + 1272529 * 2 ^ 59
def prefixEnd_1272529 : Nat := 4983230072969 + 3 ^ 40 * 1272529 * 2
def baseEnd_1272529 : Nat := 435612682523571305423501

theorem tailTrace_1272529 : CollatzResearch.WordTrace tailWord_1272529 prefixEnd_1272529 435612682523571305423501 := by
  unfold tailWord_1272529
  simp only [CollatzResearch.WordTrace]
  refine ⟨46412945606852238495732641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30941963737901492330488427 46412945606852238495732641)
  ·
    refine ⟨34809709205139178871799481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46412945606852238495732641 34809709205139178871799481)
    ·
      refine ⟨26107281903854384153849611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34809709205139178871799481 26107281903854384153849611)
      ·
        refine ⟨39160922855781576230774417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26107281903854384153849611 39160922855781576230774417)
        ·
          refine ⟨29370692141836182173080813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39160922855781576230774417 29370692141836182173080813)
          ·
            refine ⟨11014009553188568314905305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29370692141836182173080813 11014009553188568314905305)
            ·
              refine ⟨8260507164891426236178979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11014009553188568314905305 8260507164891426236178979)
              ·
                refine ⟨12390760747337139354268469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8260507164891426236178979 12390760747337139354268469)
                ·
                  refine ⟨1161633820062856814462669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12390760747337139354268469 1161633820062856814462669)
                  ·
                    refine ⟨435612682523571305423501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161633820062856814462669 435612682523571305423501)
                    ·
                      rfl

theorem cell22_1272529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_1272529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272529 prefixEnd_1272529 := by exact prefixLift 1272529
  have htrace : WordTrace (prefixWord ++ tailWord_1272529) baseStart_1272529 baseEnd_1272529 := by
    simpa [prefixWord, tailWord_1272529, baseEnd_1272529] using wordTrace_append hprefix tailTrace_1272529
  have hstable : (prefixWord ++ tailWord_1272529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272529).length < 2 ^ (prefixWord ++ tailWord_1272529).sum := by decide
  have hdescent : baseEnd_1272529 < baseStart_1272529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272533 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_1272533 : Nat := 118140960795 + 1272533 * 2 ^ 59
def prefixEnd_1272533 : Nat := 4983230072969 + 3 ^ 40 * 1272533 * 2
def baseEnd_1272533 : Nat := 435614051805316628323489

theorem tailTrace_1272533 : CollatzResearch.WordTrace tailWord_1272533 prefixEnd_1272533 435614051805316628323489 := by
  unfold tailWord_1272533
  simp only [CollatzResearch.WordTrace]
  refine ⟨46413091498837747178878253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30942060999225164785918835 46413091498837747178878253)
  ·
    refine ⟨17404909312064155192079345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46413091498837747178878253 17404909312064155192079345)
    ·
      refine ⟨13053681984048116394059509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17404909312064155192079345 13053681984048116394059509)
      ·
        refine ⟨1223782686004510911943079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13053681984048116394059509 1223782686004510911943079)
        ·
          refine ⟨1835674029006766367914619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223782686004510911943079 1835674029006766367914619)
          ·
            refine ⟨2753511043510149551871929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835674029006766367914619 2753511043510149551871929)
            ·
              refine ⟨2065133282632612163903947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2753511043510149551871929 2065133282632612163903947)
              ·
                refine ⟨3097699923948918245855921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065133282632612163903947 3097699923948918245855921)
                ·
                  refine ⟨2323274942961688684391941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097699923948918245855921 2323274942961688684391941)
                  ·
                    refine ⟨435614051805316628323489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2323274942961688684391941 435614051805316628323489)
                    ·
                      rfl

theorem cell22_1272533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_1272533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272533 prefixEnd_1272533 := by exact prefixLift 1272533
  have htrace : WordTrace (prefixWord ++ tailWord_1272533) baseStart_1272533 baseEnd_1272533 := by
    simpa [prefixWord, tailWord_1272533, baseEnd_1272533] using wordTrace_append hprefix tailTrace_1272533
  have hstable : (prefixWord ++ tailWord_1272533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272533).length < 2 ^ (prefixWord ++ tailWord_1272533).sum := by decide
  have hdescent : baseEnd_1272533 < baseStart_1272533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272559 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 5]
def baseStart_1272559 : Nat := 118140960795 + 1272559 * 2 ^ 59
def prefixEnd_1272559 : Nat := 4983230072969 + 3 ^ 40 * 1272559 * 2
def baseEnd_1272559 : Nat := 145207650712220409057803

theorem tailTrace_1272559 : CollatzResearch.WordTrace tailWord_1272559 prefixEnd_1272559 145207650712220409057803 := by
  unfold tailWord_1272559
  simp only [CollatzResearch.WordTrace]
  refine ⟨46414039796743553619324731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30942693197829035746216487 46414039796743553619324731)
  ·
    refine ⟨69621059695115330428987097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46414039796743553619324731 69621059695115330428987097)
    ·
      refine ⟨52215794771336497821740323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69621059695115330428987097 52215794771336497821740323)
      ·
        refine ⟨78323692157004746732610485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52215794771336497821740323 78323692157004746732610485)
        ·
          refine ⟨7342846139719195006182233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78323692157004746732610485 7342846139719195006182233)
          ·
            refine ⟨5507134604789396254636675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7342846139719195006182233 5507134604789396254636675)
            ·
              refine ⟨8260701907184094381955013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5507134604789396254636675 8260701907184094381955013)
              ·
                refine ⟨1548881607597017696616565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8260701907184094381955013 1548881607597017696616565)
                ·
                  refine ⟨145207650712220409057803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1548881607597017696616565 145207650712220409057803)
                  ·
                    rfl

theorem cell22_1272559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 5].length) (baseStart_1272559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272559 prefixEnd_1272559 := by exact prefixLift 1272559
  have htrace : WordTrace (prefixWord ++ tailWord_1272559) baseStart_1272559 baseEnd_1272559 := by
    simpa [prefixWord, tailWord_1272559, baseEnd_1272559] using wordTrace_append hprefix tailTrace_1272559
  have hstable : (prefixWord ++ tailWord_1272559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272559).length < 2 ^ (prefixWord ++ tailWord_1272559).sum := by decide
  have hdescent : baseEnd_1272559 < baseStart_1272559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272565 : List Nat := [1, 3, 6, 1, 1, 2, 1, 7]
def baseStart_1272565 : Nat := 118140960795 + 1272565 * 2 ^ 59
def prefixEnd_1272565 : Nat := 4983230072969 + 3 ^ 40 * 1272565 * 2
def baseEnd_1272565 : Nat := 48402778451031023502599

theorem tailTrace_1272565 : CollatzResearch.WordTrace tailWord_1272565 prefixEnd_1272565 48402778451031023502599 := by
  unfold tailWord_1272565
  simp only [CollatzResearch.WordTrace]
  refine ⟨46414258634721816644043149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30942839089814544429362099 46414258634721816644043149)
  ·
    refine ⟨17405346988020681241516181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46414258634721816644043149 17405346988020681241516181)
    ·
      refine ⟨815875640063469433196071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17405346988020681241516181 815875640063469433196071)
      ·
        refine ⟨1223813460095204149794107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815875640063469433196071 1223813460095204149794107)
        ·
          refine ⟨1835720190142806224691161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223813460095204149794107 1835720190142806224691161)
          ·
            refine ⟨1376790142607104668518371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1835720190142806224691161 1376790142607104668518371)
            ·
              refine ⟨2065185213910657002777557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376790142607104668518371 2065185213910657002777557)
              ·
                refine ⟨48402778451031023502599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2065185213910657002777557 48402778451031023502599)
                ·
                  rfl

theorem cell22_1272565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 7].length) (baseStart_1272565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272565 prefixEnd_1272565 := by exact prefixLift 1272565
  have htrace : WordTrace (prefixWord ++ tailWord_1272565) baseStart_1272565 baseEnd_1272565 := by
    simpa [prefixWord, tailWord_1272565, baseEnd_1272565] using wordTrace_append hprefix tailTrace_1272565
  have hstable : (prefixWord ++ tailWord_1272565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272565).length < 2 ^ (prefixWord ++ tailWord_1272565).sum := by decide
  have hdescent : baseEnd_1272565 < baseStart_1272565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272649 : List Nat := [1, 2, 1, 1, 2, 6, 1, 8]
def baseStart_1272649 : Nat := 118140960795 + 1272649 * 2 ^ 59
def prefixEnd_1272649 : Nat := 4983230072969 + 3 ^ 40 * 1272649 * 2
def baseEnd_1272649 : Nat := 48405973441770110269237

theorem tailTrace_1272649 : CollatzResearch.WordTrace tailWord_1272649 prefixEnd_1272649 48405973441770110269237 := by
  unfold tailWord_1272649
  simp only [CollatzResearch.WordTrace]
  refine ⟨46417322366417498990101001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30944881577611665993400667 46417322366417498990101001)
  ·
    refine ⟨34812991774813124242575751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46417322366417498990101001 34812991774813124242575751)
    ·
      refine ⟨52219487662219686363863627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34812991774813124242575751 52219487662219686363863627)
      ·
        refine ⟨78329231493329529545795441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52219487662219686363863627 78329231493329529545795441)
        ·
          refine ⟨58746923619997147159346581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78329231493329529545795441 58746923619997147159346581)
          ·
            refine ⟨2753762044687366273094371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58746923619997147159346581 2753762044687366273094371)
            ·
              refine ⟨4130643067031049409641557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753762044687366273094371 4130643067031049409641557)
              ·
                refine ⟨48405973441770110269237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4130643067031049409641557 48405973441770110269237)
                ·
                  rfl

theorem cell22_1272649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 8].length) (baseStart_1272649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272649 prefixEnd_1272649 := by exact prefixLift 1272649
  have htrace : WordTrace (prefixWord ++ tailWord_1272649) baseStart_1272649 baseEnd_1272649 := by
    simpa [prefixWord, tailWord_1272649, baseEnd_1272649] using wordTrace_append hprefix tailTrace_1272649
  have hstable : (prefixWord ++ tailWord_1272649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272649).length < 2 ^ (prefixWord ++ tailWord_1272649).sum := by decide
  have hdescent : baseEnd_1272649 < baseStart_1272649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272668 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1272668 : Nat := 118140960795 + 1272668 * 2 ^ 59
def prefixEnd_1272668 : Nat := 4983230072969 + 3 ^ 40 * 1272668 * 2
def baseEnd_1272668 : Nat := 435660265064221276198075

theorem tailTrace_1272668 : CollatzResearch.WordTrace tailWord_1272668 prefixEnd_1272668 435660265064221276198075 := by
  unfold tailWord_1272668
  simp only [CollatzResearch.WordTrace]
  refine ⟨23209007676674332617521329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30945343568899110156695105 23209007676674332617521329)
  ·
    refine ⟨17406755757505749463140997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23209007676674332617521329 17406755757505749463140997)
    ·
      refine ⟨3263766704532328024338937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17406755757505749463140997 3263766704532328024338937)
      ·
        refine ⟨2447825028399246018254203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3263766704532328024338937 2447825028399246018254203)
        ·
          refine ⟨3671737542598869027381305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447825028399246018254203 3671737542598869027381305)
          ·
            refine ⟨2753803156949151770535979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3671737542598869027381305 2753803156949151770535979)
            ·
              refine ⟨4130704735423727655803969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753803156949151770535979 4130704735423727655803969)
              ·
                refine ⟨3098028551567795741852977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4130704735423727655803969 3098028551567795741852977)
                ·
                  refine ⟨2323521413675846806389733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3098028551567795741852977 2323521413675846806389733)
                  ·
                    refine ⟨435660265064221276198075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2323521413675846806389733 435660265064221276198075)
                    ·
                      rfl

theorem cell22_1272668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1272668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272668 prefixEnd_1272668 := by exact prefixLift 1272668
  have htrace : WordTrace (prefixWord ++ tailWord_1272668) baseStart_1272668 baseEnd_1272668 := by
    simpa [prefixWord, tailWord_1272668, baseEnd_1272668] using wordTrace_append hprefix tailTrace_1272668
  have hstable : (prefixWord ++ tailWord_1272668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272668).length < 2 ^ (prefixWord ++ tailWord_1272668).sum := by decide
  have hdescent : baseEnd_1272668 < baseStart_1272668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272732 : List Nat := [2, 2, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_1272732 : Nat := 118140960795 + 1272732 * 2 ^ 59
def prefixEnd_1272732 : Nat := 4983230072969 + 3 ^ 40 * 1272732 * 2
def baseEnd_1272732 : Nat := 435682173572146442597879

theorem tailTrace_1272732 : CollatzResearch.WordTrace tailWord_1272732 prefixEnd_1272732 435682173572146442597879 := by
  unfold tailWord_1272732
  simp only [CollatzResearch.WordTrace]
  refine ⟨23210174812558402082686225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30946899750077869443581633 23210174812558402082686225)
  ·
    refine ⟨17407631109418801562014669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23210174812558402082686225 17407631109418801562014669)
    ·
      refine ⟨6527861666032050585755501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17407631109418801562014669 6527861666032050585755501)
      ·
        refine ⟨2447948124762018969658313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6527861666032050585755501 2447948124762018969658313)
        ·
          refine ⟨1835961093571514227243735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2447948124762018969658313 1835961093571514227243735)
          ·
            refine ⟨2753941640357271340865603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835961093571514227243735 2753941640357271340865603)
            ·
              refine ⟨4130912460535907011298405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753941640357271340865603 4130912460535907011298405)
              ·
                refine ⟨774546086350482564618451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4130912460535907011298405 774546086350482564618451)
                ·
                  refine ⟨1161819129525723846927677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774546086350482564618451 1161819129525723846927677)
                  ·
                    refine ⟨435682173572146442597879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161819129525723846927677 435682173572146442597879)
                    ·
                      rfl

theorem cell22_1272732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_1272732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272732 prefixEnd_1272732 := by exact prefixLift 1272732
  have htrace : WordTrace (prefixWord ++ tailWord_1272732) baseStart_1272732 baseEnd_1272732 := by
    simpa [prefixWord, tailWord_1272732, baseEnd_1272732] using wordTrace_append hprefix tailTrace_1272732
  have hstable : (prefixWord ++ tailWord_1272732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272732).length < 2 ^ (prefixWord ++ tailWord_1272732).sum := by decide
  have hdescent : baseEnd_1272732 < baseStart_1272732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272743 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1272743 : Nat := 118140960795 + 1272743 * 2 ^ 59
def prefixEnd_1272743 : Nat := 4983230072969 + 3 ^ 40 * 1272743 * 2
def baseEnd_1272743 : Nat := 435685939096946080572845

theorem tailTrace_1272743 : CollatzResearch.WordTrace tailWord_1272743 prefixEnd_1272743 435685939096946080572845 := by
  unfold tailWord_1272743
  simp only [CollatzResearch.WordTrace]
  refine ⟨46420750828076953044022883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30947167218717968696015255 46420750828076953044022883)
  ·
    refine ⟨69631126242115429566034325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46420750828076953044022883 69631126242115429566034325)
    ·
      refine ⟨3263959042599160760907859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69631126242115429566034325 3263959042599160760907859)
      ·
        refine ⟨4895938563898741141361789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3263959042599160760907859 4895938563898741141361789)
        ·
          refine ⟨1835976961462027928010671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4895938563898741141361789 1835976961462027928010671)
          ·
            refine ⟨2753965442193041892016007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835976961462027928010671 2753965442193041892016007)
            ·
              refine ⟨4130948163289562838024011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753965442193041892016007 4130948163289562838024011)
              ·
                refine ⟨6196422244934344257036017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130948163289562838024011 6196422244934344257036017)
                ·
                  refine ⟨4647316683700758192777013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6196422244934344257036017 4647316683700758192777013)
                  ·
                    refine ⟨435685939096946080572845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4647316683700758192777013 435685939096946080572845)
                    ·
                      rfl

theorem cell22_1272743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1272743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272743 prefixEnd_1272743 := by exact prefixLift 1272743
  have htrace : WordTrace (prefixWord ++ tailWord_1272743) baseStart_1272743 baseEnd_1272743 := by
    simpa [prefixWord, tailWord_1272743, baseEnd_1272743] using wordTrace_append hprefix tailTrace_1272743
  have hstable : (prefixWord ++ tailWord_1272743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272743).length < 2 ^ (prefixWord ++ tailWord_1272743).sum := by decide
  have hdescent : baseEnd_1272743 < baseStart_1272743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272771 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 6, 3]
def baseStart_1272771 : Nat := 118140960795 + 1272771 * 2 ^ 59
def prefixEnd_1272771 : Nat := 4983230072969 + 3 ^ 40 * 1272771 * 2
def baseEnd_1272771 : Nat := 435695524069163340872759

theorem tailTrace_1272771 : CollatzResearch.WordTrace tailWord_1272771 prefixEnd_1272771 435695524069163340872759 := by
  unfold tailWord_1272771
  simp only [CollatzResearch.WordTrace]
  refine ⟨46421772071975513826042167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30947848047983675884028111 46421772071975513826042167)
  ·
    refine ⟨69632658107963270739063251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46421772071975513826042167 69632658107963270739063251)
    ·
      refine ⟨104448987161944906108594877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69632658107963270739063251 104448987161944906108594877)
      ·
        refine ⟨39168370185729339790723079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104448987161944906108594877 39168370185729339790723079)
        ·
          refine ⟨58752555278594009686084619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39168370185729339790723079 58752555278594009686084619)
          ·
            refine ⟨88128832917891014529126929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58752555278594009686084619 88128832917891014529126929)
            ·
              refine ⟨66096624688418260896845197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88128832917891014529126929 66096624688418260896845197)
              ·
                refine ⟨24786234258156847836316949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66096624688418260896845197 24786234258156847836316949)
                ·
                  refine ⟨1161854730851102242327357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24786234258156847836316949 1161854730851102242327357)
                  ·
                    refine ⟨435695524069163340872759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161854730851102242327357 435695524069163340872759)
                    ·
                      rfl

theorem cell22_1272771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 3].length) (baseStart_1272771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272771 prefixEnd_1272771 := by exact prefixLift 1272771
  have htrace : WordTrace (prefixWord ++ tailWord_1272771) baseStart_1272771 baseEnd_1272771 := by
    simpa [prefixWord, tailWord_1272771, baseEnd_1272771] using wordTrace_append hprefix tailTrace_1272771
  have hstable : (prefixWord ++ tailWord_1272771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272771).length < 2 ^ (prefixWord ++ tailWord_1272771).sum := by decide
  have hdescent : baseEnd_1272771 < baseStart_1272771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272790 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1272790 : Nat := 118140960795 + 1272790 * 2 ^ 59
def prefixEnd_1272790 : Nat := 4983230072969 + 3 ^ 40 * 1272790 * 2
def baseEnd_1272790 : Nat := 145234009385817874882567

theorem tailTrace_1272790 : CollatzResearch.WordTrace tailWord_1272790 prefixEnd_1272790 145234009385817874882567 := by
  unfold tailWord_1272790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901404066181667504436489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30948310039271120047322549 2901404066181667504436489)
  ·
    refine ⟨2176053049636250628327367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2901404066181667504436489 2176053049636250628327367)
    ·
      refine ⟨3264079574454375942491051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176053049636250628327367 3264079574454375942491051)
      ·
        refine ⟨4896119361681563913736577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264079574454375942491051 4896119361681563913736577)
        ·
          refine ⟨3672089521261172935302433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4896119361681563913736577 3672089521261172935302433)
          ·
            refine ⟨2754067140945879701476825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672089521261172935302433 2754067140945879701476825)
            ·
              refine ⟨2065550355709409776107619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754067140945879701476825 2065550355709409776107619)
              ·
                refine ⟨3098325533564114664161429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065550355709409776107619 3098325533564114664161429)
                ·
                  refine ⟨145234009385817874882567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3098325533564114664161429 145234009385817874882567)
                  ·
                    rfl

theorem cell22_1272790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1272790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272790 prefixEnd_1272790 := by exact prefixLift 1272790
  have htrace : WordTrace (prefixWord ++ tailWord_1272790) baseStart_1272790 baseEnd_1272790 := by
    simpa [prefixWord, tailWord_1272790, baseEnd_1272790] using wordTrace_append hprefix tailTrace_1272790
  have hstable : (prefixWord ++ tailWord_1272790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272790).length < 2 ^ (prefixWord ++ tailWord_1272790).sum := by decide
  have hdescent : baseEnd_1272790 < baseStart_1272790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272863 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 5]
def baseStart_1272863 : Nat := 118140960795 + 1272863 * 2 ^ 59
def prefixEnd_1272863 : Nat := 4983230072969 + 3 ^ 40 * 1272863 * 2
def baseEnd_1272863 : Nat := 145242339183101922524159

theorem tailTrace_1272863 : CollatzResearch.WordTrace tailWord_1272863 prefixEnd_1272863 145242339183101922524159 := by
  unfold tailWord_1272863
  simp only [CollatzResearch.WordTrace]
  refine ⟨46425127587642213538391243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30950085058428142358927495 46425127587642213538391243)
  ·
    refine ⟨69637691381463320307586865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46425127587642213538391243 69637691381463320307586865)
    ·
      refine ⟨52228268536097490230690149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69637691381463320307586865 52228268536097490230690149)
      ·
        refine ⟨9792800350518279418254403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52228268536097490230690149 9792800350518279418254403)
        ·
          refine ⟨14689200525777419127381605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9792800350518279418254403 14689200525777419127381605)
          ·
            refine ⟨2754225098583266086384051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14689200525777419127381605 2754225098583266086384051)
            ·
              refine ⟨4131337647874899129576077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754225098583266086384051 4131337647874899129576077)
              ·
                refine ⟨1549251617953087173591029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4131337647874899129576077 1549251617953087173591029)
                ·
                  refine ⟨145242339183101922524159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1549251617953087173591029 145242339183101922524159)
                  ·
                    rfl

theorem cell22_1272863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 5].length) (baseStart_1272863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272863 prefixEnd_1272863 := by exact prefixLift 1272863
  have htrace : WordTrace (prefixWord ++ tailWord_1272863) baseStart_1272863 baseEnd_1272863 := by
    simpa [prefixWord, tailWord_1272863, baseEnd_1272863] using wordTrace_append hprefix tailTrace_1272863
  have hstable : (prefixWord ++ tailWord_1272863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272863).length < 2 ^ (prefixWord ++ tailWord_1272863).sum := by decide
  have hdescent : baseEnd_1272863 < baseStart_1272863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272942 : List Nat := [4, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_1272942 : Nat := 118140960795 + 1272942 * 2 ^ 59
def prefixEnd_1272942 : Nat := 4983230072969 + 3 ^ 40 * 1272942 * 2
def baseEnd_1272942 : Nat := 145251353621258631615745

theorem tailTrace_1272942 : CollatzResearch.WordTrace tailWord_1272942 prefixEnd_1272942 145251353621258631615745 := by
  unfold tailWord_1272942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803501119294501253814635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30952005969570673353678053 5803501119294501253814635)
  ·
    refine ⟨8705251678941751880721953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5803501119294501253814635 8705251678941751880721953)
    ·
      refine ⟨6528938759206313910541465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8705251678941751880721953 6528938759206313910541465)
      ·
        refine ⟨4896704069404735432906099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6528938759206313910541465 4896704069404735432906099)
        ·
          refine ⟨7345056104107103149359149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4896704069404735432906099 7345056104107103149359149)
          ·
            refine ⟨2754396039040163681009681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7345056104107103149359149 2754396039040163681009681)
            ·
              refine ⟨2065797029280122760757261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754396039040163681009681 2065797029280122760757261)
              ·
                refine ⟨774673885980046035283973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2065797029280122760757261 774673885980046035283973)
                ·
                  refine ⟨145251353621258631615745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 774673885980046035283973 145251353621258631615745)
                  ·
                    rfl

theorem cell22_1272942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_1272942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272942 prefixEnd_1272942 := by exact prefixLift 1272942
  have htrace : WordTrace (prefixWord ++ tailWord_1272942) baseStart_1272942 baseEnd_1272942 := by
    simpa [prefixWord, tailWord_1272942, baseEnd_1272942] using wordTrace_append hprefix tailTrace_1272942
  have hstable : (prefixWord ++ tailWord_1272942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272942).length < 2 ^ (prefixWord ++ tailWord_1272942).sum := by decide
  have hdescent : baseEnd_1272942 < baseStart_1272942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272953 : List Nat := [1, 2, 1, 3, 5, 1, 9]
def baseStart_1272953 : Nat := 118140960795 + 1272953 * 2 ^ 59
def prefixEnd_1272953 : Nat := 4983230072969 + 3 ^ 40 * 1272953 * 2
def baseEnd_1272953 : Nat := 16139178755132427141563

theorem tailTrace_1272953 : CollatzResearch.WordTrace tailWord_1272953 prefixEnd_1272953 16139178755132427141563 := by
  unfold tailWord_1272953
  simp only [CollatzResearch.WordTrace]
  refine ⟨46428410157316158909167513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30952273438210772606111675 46428410157316158909167513)
  ·
    refine ⟨34821307617987119181875635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46428410157316158909167513 34821307617987119181875635)
    ·
      refine ⟨52231961426980678772813453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34821307617987119181875635 52231961426980678772813453)
      ·
        refine ⟨19586985535117754539805045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52231961426980678772813453 19586985535117754539805045)
        ·
          refine ⟨1836279893917289488106723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19586985535117754539805045 1836279893917289488106723)
          ·
            refine ⟨2754419840875934232160085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836279893917289488106723 2754419840875934232160085)
            ·
              refine ⟨16139178755132427141563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2754419840875934232160085 16139178755132427141563)
              ·
                rfl

theorem cell22_1272953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 9].length) (baseStart_1272953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272953 prefixEnd_1272953 := by exact prefixLift 1272953
  have htrace : WordTrace (prefixWord ++ tailWord_1272953) baseStart_1272953 baseEnd_1272953 := by
    simpa [prefixWord, tailWord_1272953, baseEnd_1272953] using wordTrace_append hprefix tailTrace_1272953
  have hstable : (prefixWord ++ tailWord_1272953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272953).length < 2 ^ (prefixWord ++ tailWord_1272953).sum := by decide
  have hdescent : baseEnd_1272953 < baseStart_1272953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1272974 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_1272974 : Nat := 118140960795 + 1272974 * 2 ^ 59
def prefixEnd_1272974 : Nat := 4983230072969 + 3 ^ 40 * 1272974 * 2
def baseEnd_1272974 : Nat := 435765015117738478047137

theorem tailTrace_1272974 : CollatzResearch.WordTrace tailWord_1272974 prefixEnd_1272974 435765015117738478047137 := by
  unfold tailWord_1272974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803647011280009936960247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30952784060160052997121317 5803647011280009936960247)
  ·
    refine ⟨8705470516920014905440371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5803647011280009936960247 8705470516920014905440371)
    ·
      refine ⟨13058205775380022358160557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8705470516920014905440371 13058205775380022358160557)
      ·
        refine ⟨4896827165767508384310209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13058205775380022358160557 4896827165767508384310209)
        ·
          refine ⟨3672620374325631288232657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4896827165767508384310209 3672620374325631288232657)
          ·
            refine ⟨2754465280744223466174493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672620374325631288232657 2754465280744223466174493)
            ·
              refine ⟨1032924480279083799815435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2754465280744223466174493 1032924480279083799815435)
              ·
                refine ⟨1549386720418625699723153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032924480279083799815435 1549386720418625699723153)
                ·
                  refine ⟨1162040040313969274792365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1549386720418625699723153 1162040040313969274792365)
                  ·
                    refine ⟨435765015117738478047137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162040040313969274792365 435765015117738478047137)
                    ·
                      rfl

theorem cell22_1272974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_1272974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1272974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1272974 prefixEnd_1272974 := by exact prefixLift 1272974
  have htrace : WordTrace (prefixWord ++ tailWord_1272974) baseStart_1272974 baseEnd_1272974 := by
    simpa [prefixWord, tailWord_1272974, baseEnd_1272974] using wordTrace_append hprefix tailTrace_1272974
  have hstable : (prefixWord ++ tailWord_1272974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1272974).length < 2 ^ (prefixWord ++ tailWord_1272974).sum := by decide
  have hdescent : baseEnd_1272974 < baseStart_1272974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1272974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273073 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_1273073 : Nat := 118140960795 + 1273073 * 2 ^ 59
def prefixEnd_1273073 : Nat := 4983230072969 + 3 ^ 40 * 1273073 * 2
def baseEnd_1273073 : Nat := 435798904840935219821833

theorem tailTrace_1273073 : CollatzResearch.WordTrace tailWord_1273073 prefixEnd_1273073 435798904840935219821833 := by
  unfold tailWord_1273073
  simp only [CollatzResearch.WordTrace]
  refine ⟨46432786916881419403535873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30955191277920946269023915 46432786916881419403535873)
  ·
    refine ⟨34824590187661064552651905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46432786916881419403535873 34824590187661064552651905)
    ·
      refine ⟨26118442640745798414488929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34824590187661064552651905 26118442640745798414488929)
      ·
        refine ⟨19588831980559348810866697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26118442640745798414488929 19588831980559348810866697)
        ·
          refine ⟨14691623985419511608150023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19588831980559348810866697 14691623985419511608150023)
          ·
            refine ⟨22037435978129267412225035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14691623985419511608150023 22037435978129267412225035)
            ·
              refine ⟨33056153967193901118337553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22037435978129267412225035 33056153967193901118337553)
              ·
                refine ⟨24792115475395425838753165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33056153967193901118337553 24792115475395425838753165)
                ·
                  refine ⟨9297043303273284689532437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24792115475395425838753165 9297043303273284689532437)
                  ·
                    refine ⟨435798904840935219821833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9297043303273284689532437 435798904840935219821833)
                    ·
                      rfl

theorem cell22_1273073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1273073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273073 prefixEnd_1273073 := by exact prefixLift 1273073
  have htrace : WordTrace (prefixWord ++ tailWord_1273073) baseStart_1273073 baseEnd_1273073 := by
    simpa [prefixWord, tailWord_1273073, baseEnd_1273073] using wordTrace_append hprefix tailTrace_1273073
  have hstable : (prefixWord ++ tailWord_1273073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273073).length < 2 ^ (prefixWord ++ tailWord_1273073).sum := by decide
  have hdescent : baseEnd_1273073 < baseStart_1273073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273092 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_1273092 : Nat := 118140960795 + 1273092 * 2 ^ 59
def prefixEnd_1273092 : Nat := 4983230072969 + 3 ^ 40 * 1273092 * 2
def baseEnd_1273092 : Nat := 435805408929225503596775

theorem tailTrace_1273092 : CollatzResearch.WordTrace tailWord_1273092 prefixEnd_1273092 435805408929225503596775 := by
  unfold tailWord_1273092
  simp only [CollatzResearch.WordTrace]
  refine ⟨23216739951906292824238765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30955653269208390432318353 23216739951906292824238765)
  ·
    refine ⟨8706277481964859809089537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23216739951906292824238765 8706277481964859809089537)
    ·
      refine ⟨6529708111473644856817153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8706277481964859809089537 6529708111473644856817153)
      ·
        refine ⟨4897281083605233642612865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6529708111473644856817153 4897281083605233642612865)
        ·
          refine ⟨3672960812703925231959649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4897281083605233642612865 3672960812703925231959649)
          ·
            refine ⟨2754720609527943923969737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672960812703925231959649 2754720609527943923969737)
            ·
              refine ⟨2066040457145957942977303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754720609527943923969737 2066040457145957942977303)
              ·
                refine ⟨3099060685718936914465955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066040457145957942977303 3099060685718936914465955)
                ·
                  refine ⟨4648591028578405371698933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099060685718936914465955 4648591028578405371698933)
                  ·
                    refine ⟨435805408929225503596775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4648591028578405371698933 435805408929225503596775)
                    ·
                      rfl

theorem cell22_1273092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_1273092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273092 prefixEnd_1273092 := by exact prefixLift 1273092
  have htrace : WordTrace (prefixWord ++ tailWord_1273092) baseStart_1273092 baseEnd_1273092 := by
    simpa [prefixWord, tailWord_1273092, baseEnd_1273092] using wordTrace_append hprefix tailTrace_1273092
  have hstable : (prefixWord ++ tailWord_1273092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273092).length < 2 ^ (prefixWord ++ tailWord_1273092).sum := by decide
  have hdescent : baseEnd_1273092 < baseStart_1273092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273105 : List Nat := [1, 2, 2, 1, 1, 4, 5, 6]
def baseStart_1273105 : Nat := 118140960795 + 1273105 * 2 ^ 59
def prefixEnd_1273105 : Nat := 4983230072969 + 3 ^ 40 * 1273105 * 2
def baseEnd_1273105 : Nat := 48423317677210867002415

theorem tailTrace_1273105 : CollatzResearch.WordTrace tailWord_1273105 prefixEnd_1273105 48423317677210867002415 := by
  unfold tailWord_1273105
  simp only [CollatzResearch.WordTrace]
  refine ⟨46433954052765488868700769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30955969368510325912467179 46433954052765488868700769)
  ·
    refine ⟨34825465539574116651525577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46433954052765488868700769 34825465539574116651525577)
    ·
      refine ⟨26119099154680587488644183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34825465539574116651525577 26119099154680587488644183)
      ·
        refine ⟨39178648732020881232966275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26119099154680587488644183 39178648732020881232966275)
        ·
          refine ⟨58767973098031321849449413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39178648732020881232966275 58767973098031321849449413)
          ·
            refine ⟨11018994955880872846771765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58767973098031321849449413 11018994955880872846771765)
            ·
              refine ⟨1033030777113831829384853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11018994955880872846771765 1033030777113831829384853)
              ·
                refine ⟨48423317677210867002415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1033030777113831829384853 48423317677210867002415)
                ·
                  rfl

theorem cell22_1273105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 6].length) (baseStart_1273105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273105 prefixEnd_1273105 := by exact prefixLift 1273105
  have htrace : WordTrace (prefixWord ++ tailWord_1273105) baseStart_1273105 baseEnd_1273105 := by
    simpa [prefixWord, tailWord_1273105, baseEnd_1273105] using wordTrace_append hprefix tailTrace_1273105
  have hstable : (prefixWord ++ tailWord_1273105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273105).length < 2 ^ (prefixWord ++ tailWord_1273105).sum := by decide
  have hdescent : baseEnd_1273105 < baseStart_1273105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273137 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 3, 3]
def baseStart_1273137 : Nat := 118140960795 + 1273137 * 2 ^ 59
def prefixEnd_1273137 : Nat := 4983230072969 + 3 ^ 40 * 1273137 * 2
def baseEnd_1273137 : Nat := 435820813348860386221637

theorem tailTrace_1273137 : CollatzResearch.WordTrace tailWord_1273137 prefixEnd_1273137 435820813348860386221637 := by
  unfold tailWord_1273137
  simp only [CollatzResearch.WordTrace]
  refine ⟨46435121188649558333865665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30956747459099705555910443 46435121188649558333865665)
  ·
    refine ⟨34826340891487168750399249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46435121188649558333865665 34826340891487168750399249)
    ·
      refine ⟨26119755668615376562799437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34826340891487168750399249 26119755668615376562799437)
      ·
        refine ⟨9794908375730766211049789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26119755668615376562799437 9794908375730766211049789)
        ·
          refine ⟨3673090640899037329143671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9794908375730766211049789 3673090640899037329143671)
          ·
            refine ⟨5509635961348555993715507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673090640899037329143671 5509635961348555993715507)
            ·
              refine ⟨8264453942022833990573261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5509635961348555993715507 8264453942022833990573261)
              ·
                refine ⟨3099170228258562746464973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8264453942022833990573261 3099170228258562746464973)
                ·
                  refine ⟨1162188835596961029924365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3099170228258562746464973 1162188835596961029924365)
                  ·
                    refine ⟨435820813348860386221637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162188835596961029924365 435820813348860386221637)
                    ·
                      rfl

theorem cell22_1273137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_1273137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273137 prefixEnd_1273137 := by exact prefixLift 1273137
  have htrace : WordTrace (prefixWord ++ tailWord_1273137) baseStart_1273137 baseEnd_1273137 := by
    simpa [prefixWord, tailWord_1273137, baseEnd_1273137] using wordTrace_append hprefix tailTrace_1273137
  have hstable : (prefixWord ++ tailWord_1273137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273137).length < 2 ^ (prefixWord ++ tailWord_1273137).sum := by decide
  have hdescent : baseEnd_1273137 < baseStart_1273137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273240 : List Nat := [2, 1, 2, 5, 12]
def baseStart_1273240 : Nat := 118140960795 + 1273240 * 2 ^ 59
def prefixEnd_1273240 : Nat := 4983230072969 + 3 ^ 40 * 1273240 * 2
def baseEnd_1273240 : Nat := 1793646388287252884347

theorem tailTrace_1273240 : CollatzResearch.WordTrace tailWord_1273240 prefixEnd_1273240 1793646388287252884347 := by
  unfold tailWord_1273240
  simp only [CollatzResearch.WordTrace]
  refine ⟨23219438953638203462432587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30959251938184271283243449 23219438953638203462432587)
  ·
    refine ⟨34829158430457305193648881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23219438953638203462432587 34829158430457305193648881)
    ·
      refine ⟨26121868822842978895236661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34829158430457305193648881 26121868822842978895236661)
      ·
        refine ⟨2448925202141529271428437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26121868822842978895236661 2448925202141529271428437)
        ·
          refine ⟨1793646388287252884347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2448925202141529271428437 1793646388287252884347)
          ·
            rfl

theorem cell22_1273240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 12].length) (baseStart_1273240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273240 prefixEnd_1273240 := by exact prefixLift 1273240
  have htrace : WordTrace (prefixWord ++ tailWord_1273240) baseStart_1273240 baseEnd_1273240 := by
    simpa [prefixWord, tailWord_1273240, baseEnd_1273240] using wordTrace_append hprefix tailTrace_1273240
  have hstable : (prefixWord ++ tailWord_1273240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273240).length < 2 ^ (prefixWord ++ tailWord_1273240).sum := by decide
  have hdescent : baseEnd_1273240 < baseStart_1273240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273242 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_1273242 : Nat := 118140960795 + 1273242 * 2 ^ 59
def prefixEnd_1273242 : Nat := 4983230072969 + 3 ^ 40 * 1273242 * 2
def baseEnd_1273242 : Nat := 435856756994675112346315

theorem tailTrace_1273242 : CollatzResearch.WordTrace tailWord_1273242 prefixEnd_1273242 435856756994675112346315 := by
  unfold tailWord_1273242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11609737713317290316609495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30959300568846107510958653 11609737713317290316609495)
  ·
    refine ⟨17414606569975935474914243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11609737713317290316609495 17414606569975935474914243)
    ·
      refine ⟨26121909854963903212371365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17414606569975935474914243 26121909854963903212371365)
      ·
        refine ⟨4897858097805731852319631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26121909854963903212371365 4897858097805731852319631)
        ·
          refine ⟨7346787146708597778479447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897858097805731852319631 7346787146708597778479447)
          ·
            refine ⟨11020180720062896667719171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7346787146708597778479447 11020180720062896667719171)
            ·
              refine ⟨16530271080094345001578757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11020180720062896667719171 16530271080094345001578757)
              ·
                refine ⟨3099425827517689687796017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16530271080094345001578757 3099425827517689687796017)
                ·
                  refine ⟨2324569370638267265847013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099425827517689687796017 2324569370638267265847013)
                  ·
                    refine ⟨435856756994675112346315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2324569370638267265847013 435856756994675112346315)
                    ·
                      rfl

theorem cell22_1273242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_1273242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273242 prefixEnd_1273242 := by exact prefixLift 1273242
  have htrace : WordTrace (prefixWord ++ tailWord_1273242) baseStart_1273242 baseEnd_1273242 := by
    simpa [prefixWord, tailWord_1273242, baseEnd_1273242] using wordTrace_append hprefix tailTrace_1273242
  have hstable : (prefixWord ++ tailWord_1273242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273242).length < 2 ^ (prefixWord ++ tailWord_1273242).sum := by decide
  have hdescent : baseEnd_1273242 < baseStart_1273242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273261 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1273261 : Nat := 118140960795 + 1273261 * 2 ^ 59
def prefixEnd_1273261 : Nat := 4983230072969 + 3 ^ 40 * 1273261 * 2
def baseEnd_1273261 : Nat := 435863261082965396121257

theorem tailTrace_1273261 : CollatzResearch.WordTrace tailWord_1273261 prefixEnd_1273261 435863261082965396121257 := by
  unfold tailWord_1273261
  simp only [CollatzResearch.WordTrace]
  refine ⟨46439643840200327511379637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30959762560133551674253091 46439643840200327511379637)
  ·
    refine ⟨4353716610018780704191841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46439643840200327511379637 4353716610018780704191841)
    ·
      refine ⟨3265287457514085528143881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4353716610018780704191841 3265287457514085528143881)
      ·
        refine ⟨2448965593135564146107911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3265287457514085528143881 2448965593135564146107911)
        ·
          refine ⟨3673448389703346219161867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448965593135564146107911 3673448389703346219161867)
          ·
            refine ⟨5510172584555019328742801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673448389703346219161867 5510172584555019328742801)
            ·
              refine ⟨4132629438416264496557101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510172584555019328742801 4132629438416264496557101)
              ·
                refine ⟨1549736039406099186208913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4132629438416264496557101 1549736039406099186208913)
                ·
                  refine ⟨1162302029554574389656685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1549736039406099186208913 1162302029554574389656685)
                  ·
                    refine ⟨435863261082965396121257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162302029554574389656685 435863261082965396121257)
                    ·
                      rfl

theorem cell22_1273261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1273261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273261 prefixEnd_1273261 := by exact prefixLift 1273261
  have htrace : WordTrace (prefixWord ++ tailWord_1273261) baseStart_1273261 baseEnd_1273261 := by
    simpa [prefixWord, tailWord_1273261, baseEnd_1273261] using wordTrace_append hprefix tailTrace_1273261
  have hstable : (prefixWord ++ tailWord_1273261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273261).length < 2 ^ (prefixWord ++ tailWord_1273261).sum := by decide
  have hdescent : baseEnd_1273261 < baseStart_1273261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273272 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 5, 3]
def baseStart_1273272 : Nat := 118140960795 + 1273272 * 2 ^ 59
def prefixEnd_1273272 : Nat := 4983230072969 + 3 ^ 40 * 1273272 * 2
def baseEnd_1273272 : Nat := 435867026607765034096223

theorem tailTrace_1273272 : CollatzResearch.WordTrace tailWord_1273272 prefixEnd_1273272 435867026607765034096223 := by
  unfold tailWord_1273272
  simp only [CollatzResearch.WordTrace]
  refine ⟨23220022521580238195015035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30960030028773650926686713 23220022521580238195015035)
  ·
    refine ⟨34830033782370357292522553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23220022521580238195015035 34830033782370357292522553)
    ·
      refine ⟨26122525336777767969391915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34830033782370357292522553 26122525336777767969391915)
      ·
        refine ⟨39183788005166651954087873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26122525336777767969391915 39183788005166651954087873)
        ·
          refine ⟨29387841003874988965565905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39183788005166651954087873 29387841003874988965565905)
          ·
            refine ⟨22040880752906241724174429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29387841003874988965565905 22040880752906241724174429)
            ·
              refine ⟨8265330282339840646565411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22040880752906241724174429 8265330282339840646565411)
              ·
                refine ⟨12397995423509760969848117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8265330282339840646565411 12397995423509760969848117)
                ·
                  refine ⟨1162312070954040090923261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12397995423509760969848117 1162312070954040090923261)
                  ·
                    refine ⟨435867026607765034096223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162312070954040090923261 435867026607765034096223)
                    ·
                      rfl

theorem cell22_1273272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_1273272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273272 prefixEnd_1273272 := by exact prefixLift 1273272
  have htrace : WordTrace (prefixWord ++ tailWord_1273272) baseStart_1273272 baseEnd_1273272 := by
    simpa [prefixWord, tailWord_1273272, baseEnd_1273272] using wordTrace_append hprefix tailTrace_1273272
  have hstable : (prefixWord ++ tailWord_1273272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273272).length < 2 ^ (prefixWord ++ tailWord_1273272).sum := by decide
  have hdescent : baseEnd_1273272 < baseStart_1273272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273276 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_1273276 : Nat := 118140960795 + 1273276 * 2 ^ 59
def prefixEnd_1273276 : Nat := 4983230072969 + 3 ^ 40 * 1273276 * 2
def baseEnd_1273276 : Nat := 435868395889510356996211

theorem tailTrace_1273276 : CollatzResearch.WordTrace tailWord_1273276 prefixEnd_1273276 435868395889510356996211 := by
  unfold tailWord_1273276
  simp only [CollatzResearch.WordTrace]
  refine ⟨23220095467572992536587841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30960127290097323382117121 23220095467572992536587841)
  ·
    refine ⟨17415071600679744402440881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23220095467572992536587841 17415071600679744402440881)
    ·
      refine ⟨13061303700509808301830661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17415071600679744402440881 13061303700509808301830661)
      ·
        refine ⟨2448994443845589056593249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13061303700509808301830661 2448994443845589056593249)
        ·
          refine ⟨1836745832884191792444937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2448994443845589056593249 1836745832884191792444937)
          ·
            refine ⟨1377559374663143844333703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836745832884191792444937 1377559374663143844333703)
            ·
              refine ⟨2066339061994715766500555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377559374663143844333703 2066339061994715766500555)
              ·
                refine ⟨3099508592992073649750833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066339061994715766500555 3099508592992073649750833)
                ·
                  refine ⟨2324631444744055237313125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099508592992073649750833 2324631444744055237313125)
                  ·
                    refine ⟨435868395889510356996211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2324631444744055237313125 435868395889510356996211)
                    ·
                      rfl

theorem cell22_1273276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_1273276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273276 prefixEnd_1273276 := by exact prefixLift 1273276
  have htrace : WordTrace (prefixWord ++ tailWord_1273276) baseStart_1273276 baseEnd_1273276 := by
    simpa [prefixWord, tailWord_1273276, baseEnd_1273276] using wordTrace_append hprefix tailTrace_1273276
  have hstable : (prefixWord ++ tailWord_1273276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273276).length < 2 ^ (prefixWord ++ tailWord_1273276).sum := by decide
  have hdescent : baseEnd_1273276 < baseStart_1273276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273306 : List Nat := [3, 1, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_1273306 : Nat := 118140960795 + 1273306 * 2 ^ 59
def prefixEnd_1273306 : Nat := 4983230072969 + 3 ^ 40 * 1273306 * 2
def baseEnd_1273306 : Nat := 435878665502600278746119

theorem tailTrace_1273306 : CollatzResearch.WordTrace tailWord_1273306 prefixEnd_1273306 435878665502600278746119 := by
  unfold tailWord_1273306
  simp only [CollatzResearch.WordTrace]
  refine ⟨11610321281259325049191943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30960856750024866797845181 11610321281259325049191943)
  ·
    refine ⟨17415481921888987573787915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11610321281259325049191943 17415481921888987573787915)
    ·
      refine ⟨26123222882833481360681873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17415481921888987573787915 26123222882833481360681873)
      ·
        refine ⟨19592417162125111020511405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26123222882833481360681873 19592417162125111020511405)
        ·
          refine ⟨7347156435796916632691777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19592417162125111020511405 7347156435796916632691777)
          ·
            refine ⟨5510367326847687474518833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7347156435796916632691777 5510367326847687474518833)
            ·
              refine ⟨4132775495135765605889125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510367326847687474518833 4132775495135765605889125)
              ·
                refine ⟨774895405337956051104211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4132775495135765605889125 774895405337956051104211)
                ·
                  refine ⟨1162343108006934076656317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774895405337956051104211 1162343108006934076656317)
                  ·
                    refine ⟨435878665502600278746119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162343108006934076656317 435878665502600278746119)
                    ·
                      rfl

theorem cell22_1273306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_1273306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273306 prefixEnd_1273306 := by exact prefixLift 1273306
  have htrace : WordTrace (prefixWord ++ tailWord_1273306) baseStart_1273306 baseEnd_1273306 := by
    simpa [prefixWord, tailWord_1273306, baseEnd_1273306] using wordTrace_append hprefix tailTrace_1273306
  have hstable : (prefixWord ++ tailWord_1273306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273306).length < 2 ^ (prefixWord ++ tailWord_1273306).sum := by decide
  have hdescent : baseEnd_1273306 < baseStart_1273306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273357 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1273357 : Nat := 118140960795 + 1273357 * 2 ^ 59
def prefixEnd_1273357 : Nat := 4983230072969 + 3 ^ 40 * 1273357 * 2
def baseEnd_1273357 : Nat := 435896123844853145720963

theorem tailTrace_1273357 : CollatzResearch.WordTrace tailWord_1273357 prefixEnd_1273357 435896123844853145720963 := by
  unfold tailWord_1273357
  simp only [CollatzResearch.WordTrace]
  refine ⟨46443145247852535906874325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30962096831901690604582883 46443145247852535906874325)
  ·
    refine ⟨1088511216746543810317367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 46443145247852535906874325 1088511216746543810317367)
    ·
      refine ⟨1632766825119815715476051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1088511216746543810317367 1632766825119815715476051)
      ·
        refine ⟨2449150237679723573214077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632766825119815715476051 2449150237679723573214077)
        ·
          refine ⟨918431339129896339955279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2449150237679723573214077 918431339129896339955279)
          ·
            refine ⟨1377647008694844509932919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918431339129896339955279 1377647008694844509932919)
            ·
              refine ⟨2066470513042266764899379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377647008694844509932919 2066470513042266764899379)
              ·
                refine ⟨3099705769563400147349069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066470513042266764899379 3099705769563400147349069)
                ·
                  refine ⟨1162389663586275055255901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3099705769563400147349069 1162389663586275055255901)
                  ·
                    refine ⟨435896123844853145720963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162389663586275055255901 435896123844853145720963)
                    ·
                      rfl

theorem cell22_1273357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1273357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273357 prefixEnd_1273357 := by exact prefixLift 1273357
  have htrace : WordTrace (prefixWord ++ tailWord_1273357) baseStart_1273357 baseEnd_1273357 := by
    simpa [prefixWord, tailWord_1273357, baseEnd_1273357] using wordTrace_append hprefix tailTrace_1273357
  have hstable : (prefixWord ++ tailWord_1273357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273357).length < 2 ^ (prefixWord ++ tailWord_1273357).sum := by decide
  have hdescent : baseEnd_1273357 < baseStart_1273357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273415 : List Nat := [1, 1, 4, 1, 6, 1, 2, 2, 4]
def baseStart_1273415 : Nat := 118140960795 + 1273415 * 2 ^ 59
def prefixEnd_1273415 : Nat := 4983230072969 + 3 ^ 40 * 1273415 * 2
def baseEnd_1273415 : Nat := 145305326143386775923595

theorem tailTrace_1273415 : CollatzResearch.WordTrace tailWord_1273415 prefixEnd_1273415 145305326143386775923595 := by
  unfold tailWord_1273415
  simp only [CollatzResearch.WordTrace]
  refine ⟨46445260681642411812485699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30963507121094941208323799 46445260681642411812485699)
  ·
    refine ⟨69667891022463617718728549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46445260681642411812485699 69667891022463617718728549)
    ·
      refine ⟨13062729566711928322261603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69667891022463617718728549 13062729566711928322261603)
      ·
        refine ⟨19594094350067892483392405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13062729566711928322261603 19594094350067892483392405)
        ·
          refine ⟨918473172659432460159019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19594094350067892483392405 918473172659432460159019)
          ·
            refine ⟨1377709758989148690238529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918473172659432460159019 1377709758989148690238529)
            ·
              refine ⟨1033282319241861517678897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377709758989148690238529 1033282319241861517678897)
              ·
                refine ⟨774961739431396138259173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033282319241861517678897 774961739431396138259173)
                ·
                  refine ⟨145305326143386775923595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 774961739431396138259173 145305326143386775923595)
                  ·
                    rfl

theorem cell22_1273415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 4].length) (baseStart_1273415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273415 prefixEnd_1273415 := by exact prefixLift 1273415
  have htrace : WordTrace (prefixWord ++ tailWord_1273415) baseStart_1273415 baseEnd_1273415 := by
    simpa [prefixWord, tailWord_1273415, baseEnd_1273415] using wordTrace_append hprefix tailTrace_1273415
  have hstable : (prefixWord ++ tailWord_1273415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273415).length < 2 ^ (prefixWord ++ tailWord_1273415).sum := by decide
  have hdescent : baseEnd_1273415 < baseStart_1273415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273424 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 3, 3]
def baseStart_1273424 : Nat := 118140960795 + 1273424 * 2 ^ 59
def prefixEnd_1273424 : Nat := 4983230072969 + 3 ^ 40 * 1273424 * 2
def baseEnd_1273424 : Nat := 435919059314087304295757

theorem tailTrace_1273424 : CollatzResearch.WordTrace tailWord_1273424 prefixEnd_1273424 435919059314087304295757 := by
  unfold tailWord_1273424
  simp only [CollatzResearch.WordTrace]
  refine ⟨23222794469304903174781663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30963725959073204233042217 23222794469304903174781663)
  ·
    refine ⟨34834191703957354762172495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23222794469304903174781663 34834191703957354762172495)
    ·
      refine ⟨52251287555936032143258743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34834191703957354762172495 52251287555936032143258743)
      ·
        refine ⟨78376931333904048214888115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52251287555936032143258743 78376931333904048214888115)
        ·
          refine ⟨117565397000856072322332173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78376931333904048214888115 117565397000856072322332173)
          ·
            refine ⟨44087023875321027120874565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117565397000856072322332173 44087023875321027120874565)
            ·
              refine ⟨8266316976622692585163981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44087023875321027120874565 8266316976622692585163981)
              ·
                refine ⟨3099868866233509719436493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8266316976622692585163981 3099868866233509719436493)
                ·
                  refine ⟨1162450824837566144788685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3099868866233509719436493 1162450824837566144788685)
                  ·
                    refine ⟨435919059314087304295757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162450824837566144788685 435919059314087304295757)
                    ·
                      rfl

theorem cell22_1273424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_1273424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273424 prefixEnd_1273424 := by exact prefixLift 1273424
  have htrace : WordTrace (prefixWord ++ tailWord_1273424) baseStart_1273424 baseEnd_1273424 := by
    simpa [prefixWord, tailWord_1273424, baseEnd_1273424] using wordTrace_append hprefix tailTrace_1273424
  have hstable : (prefixWord ++ tailWord_1273424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273424).length < 2 ^ (prefixWord ++ tailWord_1273424).sum := by decide
  have hdescent : baseEnd_1273424 < baseStart_1273424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273430 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1273430 : Nat := 118140960795 + 1273430 * 2 ^ 59
def prefixEnd_1273430 : Nat := 4983230072969 + 3 ^ 40 * 1273430 * 2
def baseEnd_1273430 : Nat := 435921113236705288645739

theorem tailTrace_1273430 : CollatzResearch.WordTrace tailWord_1273430 prefixEnd_1273430 435921113236705288645739 := by
  unfold tailWord_1273430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902862986036754335892609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30963871851058712916187829 2902862986036754335892609)
  ·
    refine ⟨2177147239527565751919457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2902862986036754335892609 2177147239527565751919457)
    ·
      refine ⟨1632860429645674313939593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2177147239527565751919457 1632860429645674313939593)
      ·
        refine ⟨1224645322234255735454695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1632860429645674313939593 1224645322234255735454695)
        ·
          refine ⟨1836967983351383603182043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1224645322234255735454695 1836967983351383603182043)
          ·
            refine ⟨2755451975027075404773065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836967983351383603182043 2755451975027075404773065)
            ·
              refine ⟨2066588981270306553579799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755451975027075404773065 2066588981270306553579799)
              ·
                refine ⟨3099883471905459830369699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066588981270306553579799 3099883471905459830369699)
                ·
                  refine ⟨4649825207858189745554549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099883471905459830369699 4649825207858189745554549)
                  ·
                    refine ⟨435921113236705288645739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4649825207858189745554549 435921113236705288645739)
                    ·
                      rfl

theorem cell22_1273430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1273430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273430 prefixEnd_1273430 := by exact prefixLift 1273430
  have htrace : WordTrace (prefixWord ++ tailWord_1273430) baseStart_1273430 baseEnd_1273430 := by
    simpa [prefixWord, tailWord_1273430, baseEnd_1273430] using wordTrace_append hprefix tailTrace_1273430
  have hstable : (prefixWord ++ tailWord_1273430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273430).length < 2 ^ (prefixWord ++ tailWord_1273430).sum := by decide
  have hdescent : baseEnd_1273430 < baseStart_1273430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273452 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1273452 : Nat := 118140960795 + 1273452 * 2 ^ 59
def prefixEnd_1273452 : Nat := 4983230072969 + 3 ^ 40 * 1273452 * 2
def baseEnd_1273452 : Nat := 435928644286304564595671

theorem tailTrace_1273452 : CollatzResearch.WordTrace tailWord_1273452 prefixEnd_1273452 435928644286304564595671 := by
  unfold tailWord_1273452
  simp only [CollatzResearch.WordTrace]
  refine ⟨23223305091254183565791305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30964406788338911421055073 23223305091254183565791305)
  ·
    refine ⟨17417478818440637674343479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23223305091254183565791305 17417478818440637674343479)
    ·
      refine ⟨26126218227660956511515219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17417478818440637674343479 26126218227660956511515219)
      ·
        refine ⟨39189327341491434767272829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26126218227660956511515219 39189327341491434767272829)
        ·
          refine ⟨14695997753059288037727311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39189327341491434767272829 14695997753059288037727311)
          ·
            refine ⟨22043996629588932056590967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14695997753059288037727311 22043996629588932056590967)
            ·
              refine ⟨33065994944383398084886451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22043996629588932056590967 33065994944383398084886451)
              ·
                refine ⟨49598992416575097127329677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33065994944383398084886451 49598992416575097127329677)
                ·
                  refine ⟨18599622156215661422748629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49598992416575097127329677 18599622156215661422748629)
                  ·
                    refine ⟨435928644286304564595671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18599622156215661422748629 435928644286304564595671)
                    ·
                      rfl

theorem cell22_1273452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1273452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273452 prefixEnd_1273452 := by exact prefixLift 1273452
  have htrace : WordTrace (prefixWord ++ tailWord_1273452) baseStart_1273452 baseEnd_1273452 := by
    simpa [prefixWord, tailWord_1273452, baseEnd_1273452] using wordTrace_append hprefix tailTrace_1273452
  have hstable : (prefixWord ++ tailWord_1273452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273452).length < 2 ^ (prefixWord ++ tailWord_1273452).sum := by decide
  have hdescent : baseEnd_1273452 < baseStart_1273452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273458 : List Nat := [3, 2, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_1273458 : Nat := 118140960795 + 1273458 * 2 ^ 59
def prefixEnd_1273458 : Nat := 4983230072969 + 3 ^ 40 * 1273458 * 2
def baseEnd_1273458 : Nat := 435930698208922548945653

theorem tailTrace_1273458 : CollatzResearch.WordTrace tailWord_1273458 prefixEnd_1273458 435930698208922548945653 := by
  unfold tailWord_1273458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11611707255121657539075257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30964552680324420104200685 11611707255121657539075257)
  ·
    refine ⟨8708780441341243154306443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11611707255121657539075257 8708780441341243154306443)
    ·
      refine ⟨13063170662011864731459665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8708780441341243154306443 13063170662011864731459665)
      ·
        refine ⟨9797377996508898548594749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13063170662011864731459665 9797377996508898548594749)
        ·
          refine ⟨3674016748690836955723031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9797377996508898548594749 3674016748690836955723031)
          ·
            refine ⟨5511025123036255433584547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674016748690836955723031 5511025123036255433584547)
            ·
              refine ⟨8266537684554383150376821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511025123036255433584547 8266537684554383150376821)
              ·
                refine ⟨774987907926973420347827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8266537684554383150376821 774987907926973420347827)
                ·
                  refine ⟨1162481861890460130521741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774987907926973420347827 1162481861890460130521741)
                  ·
                    refine ⟨435930698208922548945653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162481861890460130521741 435930698208922548945653)
                    ·
                      rfl

theorem cell22_1273458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_1273458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273458 prefixEnd_1273458 := by exact prefixLift 1273458
  have htrace : WordTrace (prefixWord ++ tailWord_1273458) baseStart_1273458 baseEnd_1273458 := by
    simpa [prefixWord, tailWord_1273458, baseEnd_1273458] using wordTrace_append hprefix tailTrace_1273458
  have hstable : (prefixWord ++ tailWord_1273458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273458).length < 2 ^ (prefixWord ++ tailWord_1273458).sum := by decide
  have hdescent : baseEnd_1273458 < baseStart_1273458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273469 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_1273469 : Nat := 118140960795 + 1273469 * 2 ^ 59
def prefixEnd_1273469 : Nat := 4983230072969 + 3 ^ 40 * 1273469 * 2
def baseEnd_1273469 : Nat := 435934463733722186920619

theorem tailTrace_1273469 : CollatzResearch.WordTrace tailWord_1273469 prefixEnd_1273469 435934463733722186920619 := by
  unfold tailWord_1273469
  simp only [CollatzResearch.WordTrace]
  refine ⟨46447230223446779034951461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30964820148964519356634307 46447230223446779034951461)
  ·
    refine ⟨8708855666896271069053399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46447230223446779034951461 8708855666896271069053399)
    ·
      refine ⟨13063283500344406603580099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8708855666896271069053399 13063283500344406603580099)
      ·
        refine ⟨19594925250516609905370149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13063283500344406603580099 19594925250516609905370149)
        ·
          refine ⟨3674048484471864357256903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19594925250516609905370149 3674048484471864357256903)
          ·
            refine ⟨5511072726707796535885355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674048484471864357256903 5511072726707796535885355)
            ·
              refine ⟨8266609090061694803828033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511072726707796535885355 8266609090061694803828033)
              ·
                refine ⟨6199956817546271102871025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8266609090061694803828033 6199956817546271102871025)
                ·
                  refine ⟨4649967613159703327153269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6199956817546271102871025 4649967613159703327153269)
                  ·
                    refine ⟨435934463733722186920619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4649967613159703327153269 435934463733722186920619)
                    ·
                      rfl

theorem cell22_1273469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_1273469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273469 prefixEnd_1273469 := by exact prefixLift 1273469
  have htrace : WordTrace (prefixWord ++ tailWord_1273469) baseStart_1273469 baseEnd_1273469 := by
    simpa [prefixWord, tailWord_1273469, baseEnd_1273469] using wordTrace_append hprefix tailTrace_1273469
  have hstable : (prefixWord ++ tailWord_1273469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273469).length < 2 ^ (prefixWord ++ tailWord_1273469).sum := by decide
  have hdescent : baseEnd_1273469 < baseStart_1273469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273529 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 4, 4]
def baseStart_1273529 : Nat := 118140960795 + 1273529 * 2 ^ 59
def prefixEnd_1273529 : Nat := 4983230072969 + 3 ^ 40 * 1273529 * 2
def baseEnd_1273529 : Nat := 435955002959902030420435

theorem tailTrace_1273529 : CollatzResearch.WordTrace tailWord_1273529 prefixEnd_1273529 435955002959902030420435 := by
  unfold tailWord_1273529
  simp only [CollatzResearch.WordTrace]
  refine ⟨46449418603229409282135641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30966279068819606188090427 46449418603229409282135641)
  ·
    refine ⟨34837063952422056961601731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46449418603229409282135641 34837063952422056961601731)
    ·
      refine ⟨52255595928633085442402597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34837063952422056961601731 52255595928633085442402597)
      ·
        refine ⟨9797924236618703520450487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52255595928633085442402597 9797924236618703520450487)
        ·
          refine ⟨14696886354928055280675731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9797924236618703520450487 14696886354928055280675731)
          ·
            refine ⟨22045329532392082921013597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14696886354928055280675731 22045329532392082921013597)
            ·
              refine ⟨8266998574647031095380099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22045329532392082921013597 8266998574647031095380099)
              ·
                refine ⟨12400497861970546643070149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8266998574647031095380099 12400497861970546643070149)
                ·
                  refine ⟨2325093349119477495575653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12400497861970546643070149 2325093349119477495575653)
                  ·
                    refine ⟨435955002959902030420435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2325093349119477495575653 435955002959902030420435)
                    ·
                      rfl

theorem cell22_1273529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_1273529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273529 prefixEnd_1273529 := by exact prefixLift 1273529
  have htrace : WordTrace (prefixWord ++ tailWord_1273529) baseStart_1273529 baseEnd_1273529 := by
    simpa [prefixWord, tailWord_1273529, baseEnd_1273529] using wordTrace_append hprefix tailTrace_1273529
  have hstable : (prefixWord ++ tailWord_1273529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273529).length < 2 ^ (prefixWord ++ tailWord_1273529).sum := by decide
  have hdescent : baseEnd_1273529 < baseStart_1273529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273533 : List Nat := [1, 4, 1, 2, 1, 2, 5, 2, 4]
def baseStart_1273533 : Nat := 118140960795 + 1273533 * 2 ^ 59
def prefixEnd_1273533 : Nat := 4983230072969 + 3 ^ 40 * 1273533 * 2
def baseEnd_1273533 : Nat := 145318790747215784440141

theorem tailTrace_1273533 : CollatzResearch.WordTrace tailWord_1273533 prefixEnd_1273533 145318790747215784440141 := by
  unfold tailWord_1273533
  simp only [CollatzResearch.WordTrace]
  refine ⟨46449564495214917965281253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30966376330143278643520835 46449564495214917965281253)
  ·
    refine ⟨8709293342852797118490235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46449564495214917965281253 8709293342852797118490235)
    ·
      refine ⟨13063940014279195677735353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8709293342852797118490235 13063940014279195677735353)
      ·
        refine ⟨9797955010709396758301515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13063940014279195677735353 9797955010709396758301515)
        ·
          refine ⟨14696932516064095137452273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9797955010709396758301515 14696932516064095137452273)
          ·
            refine ⟨11022699387048071353089205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14696932516064095137452273 11022699387048071353089205)
            ·
              refine ⟨1033378067535756689352113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11022699387048071353089205 1033378067535756689352113)
              ·
                refine ⟨775033550651817517014085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033378067535756689352113 775033550651817517014085)
                ·
                  refine ⟨145318790747215784440141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775033550651817517014085 145318790747215784440141)
                  ·
                    rfl

theorem cell22_1273533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_1273533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273533 prefixEnd_1273533 := by exact prefixLift 1273533
  have htrace : WordTrace (prefixWord ++ tailWord_1273533) baseStart_1273533 baseEnd_1273533 := by
    simpa [prefixWord, tailWord_1273533, baseEnd_1273533] using wordTrace_append hprefix tailTrace_1273533
  have hstable : (prefixWord ++ tailWord_1273533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273533).length < 2 ^ (prefixWord ++ tailWord_1273533).sum := by decide
  have hdescent : baseEnd_1273533 < baseStart_1273533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273544 : List Nat := [2, 1, 3, 1, 2, 2, 4, 7]
def baseStart_1273544 : Nat := 118140960795 + 1273544 * 2 ^ 59
def prefixEnd_1273544 : Nat := 4983230072969 + 3 ^ 40 * 1273544 * 2
def baseEnd_1273544 : Nat := 48440015307382999032821

theorem tailTrace_1273544 : CollatzResearch.WordTrace tailWord_1273544 prefixEnd_1273544 48440015307382999032821 := by
  unfold tailWord_1273544
  simp only [CollatzResearch.WordTrace]
  refine ⟨23224982849087533421965843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30966643798783377895954457 23224982849087533421965843)
  ·
    refine ⟨34837474273631300132948765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23224982849087533421965843 34837474273631300132948765)
    ·
      refine ⟨13064052852611737549855787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34837474273631300132948765 13064052852611737549855787)
      ·
        refine ⟨19596079278917606324783681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13064052852611737549855787 19596079278917606324783681)
        ·
          refine ⟨14697059459188204743587761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19596079278917606324783681 14697059459188204743587761)
          ·
            refine ⟨11022794594391153557690821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14697059459188204743587761 11022794594391153557690821)
            ·
              refine ⟨2066773986448341292067029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11022794594391153557690821 2066773986448341292067029)
              ·
                refine ⟨48440015307382999032821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2066773986448341292067029 48440015307382999032821)
                ·
                  rfl

theorem cell22_1273544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 7].length) (baseStart_1273544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273544 prefixEnd_1273544 := by exact prefixLift 1273544
  have htrace : WordTrace (prefixWord ++ tailWord_1273544) baseStart_1273544 baseEnd_1273544 := by
    simpa [prefixWord, tailWord_1273544, baseEnd_1273544] using wordTrace_append hprefix tailTrace_1273544
  have hstable : (prefixWord ++ tailWord_1273544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273544).length < 2 ^ (prefixWord ++ tailWord_1273544).sum := by decide
  have hdescent : baseEnd_1273544 < baseStart_1273544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273681 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_1273681 : Nat := 118140960795 + 1273681 * 2 ^ 59
def prefixEnd_1273681 : Nat := 4983230072969 + 3 ^ 40 * 1273681 * 2
def baseEnd_1273681 : Nat := 436007035666224300619969

theorem tailTrace_1273681 : CollatzResearch.WordTrace tailWord_1273681 prefixEnd_1273681 436007035666224300619969 := by
  unfold tailWord_1273681
  simp only [CollatzResearch.WordTrace]
  refine ⟨46454962498678739241668897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30969974999119159494445931 46454962498678739241668897)
  ·
    refine ⟨34841221874009054431251673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46454962498678739241668897 34841221874009054431251673)
    ·
      refine ⟨26130916405506790823438755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34841221874009054431251673 26130916405506790823438755)
      ·
        refine ⟨39196374608260186235158133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26130916405506790823438755 39196374608260186235158133)
        ·
          refine ⟨3674660119524392459546075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39196374608260186235158133 3674660119524392459546075)
          ·
            refine ⟨5511990179286588689319113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674660119524392459546075 5511990179286588689319113)
            ·
              refine ⟨4133992634464941516989335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5511990179286588689319113 4133992634464941516989335)
              ·
                refine ⟨6200988951697412275484003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133992634464941516989335 6200988951697412275484003)
                ·
                  refine ⟨9301483427546118413226005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6200988951697412275484003 9301483427546118413226005)
                  ·
                    refine ⟨436007035666224300619969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9301483427546118413226005 436007035666224300619969)
                    ·
                      rfl

theorem cell22_1273681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_1273681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273681 prefixEnd_1273681 := by exact prefixLift 1273681
  have htrace : WordTrace (prefixWord ++ tailWord_1273681) baseStart_1273681 baseEnd_1273681 := by
    simpa [prefixWord, tailWord_1273681, baseEnd_1273681] using wordTrace_append hprefix tailTrace_1273681
  have hstable : (prefixWord ++ tailWord_1273681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273681).length < 2 ^ (prefixWord ++ tailWord_1273681).sum := by decide
  have hdescent : baseEnd_1273681 < baseStart_1273681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273685 : List Nat := [1, 3, 2, 2, 2, 4, 1, 3, 4]
def baseStart_1273685 : Nat := 118140960795 + 1273685 * 2 ^ 59
def prefixEnd_1273685 : Nat := 4983230072969 + 3 ^ 40 * 1273685 * 2
def baseEnd_1273685 : Nat := 145336134982656541173319

theorem tailTrace_1273685 : CollatzResearch.WordTrace tailWord_1273685 prefixEnd_1273685 145336134982656541173319 := by
  unfold tailWord_1273685
  simp only [CollatzResearch.WordTrace]
  refine ⟨46455108390664247924814509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30970072260442831949876339 46455108390664247924814509)
  ·
    refine ⟨17420665646499092971805441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46455108390664247924814509 17420665646499092971805441)
    ·
      refine ⟨13065499234874319728854081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17420665646499092971805441 13065499234874319728854081)
      ·
        refine ⟨9799124426155739796640561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13065499234874319728854081 9799124426155739796640561)
        ·
          refine ⟨7349343319616804847480421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9799124426155739796640561 7349343319616804847480421)
          ·
            refine ⟨1378001872428150908902579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7349343319616804847480421 1378001872428150908902579)
            ·
              refine ⟨2067002808642226363353869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378001872428150908902579 2067002808642226363353869)
              ·
                refine ⟨775126053240834886257701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067002808642226363353869 775126053240834886257701)
                ·
                  refine ⟨145336134982656541173319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775126053240834886257701 145336134982656541173319)
                  ·
                    rfl

theorem cell22_1273685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_1273685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273685 prefixEnd_1273685 := by exact prefixLift 1273685
  have htrace : WordTrace (prefixWord ++ tailWord_1273685) baseStart_1273685 baseEnd_1273685 := by
    simpa [prefixWord, tailWord_1273685, baseEnd_1273685] using wordTrace_append hprefix tailTrace_1273685
  have hstable : (prefixWord ++ tailWord_1273685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273685).length < 2 ^ (prefixWord ++ tailWord_1273685).sum := by decide
  have hdescent : baseEnd_1273685 < baseStart_1273685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273696 : List Nat := [2, 1, 1, 3, 3, 4, 8]
def baseStart_1273696 : Nat := 118140960795 + 1273696 * 2 ^ 59
def prefixEnd_1273696 : Nat := 4983230072969 + 3 ^ 40 * 1273696 * 2
def baseEnd_1273696 : Nat := 16148598906398861536849

theorem tailTrace_1273696 : CollatzResearch.WordTrace tailWord_1273696 prefixEnd_1273696 16148598906398861536849 := by
  unfold tailWord_1273696
  simp only [CollatzResearch.WordTrace]
  refine ⟨23227754796812198401732471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30970339729082931202309961 23227754796812198401732471)
  ·
    refine ⟨34841632195218297602598707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23227754796812198401732471 34841632195218297602598707)
    ·
      refine ⟨52262448292827446403898061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34841632195218297602598707 52262448292827446403898061)
      ·
        refine ⟨19598418109810292401461773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52262448292827446403898061 19598418109810292401461773)
        ·
          refine ⟨7349406791178859650548165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19598418109810292401461773 7349406791178859650548165)
          ·
            refine ⟨1378013773346036184477781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7349406791178859650548165 1378013773346036184477781)
            ·
              refine ⟨16148598906398861536849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1378013773346036184477781 16148598906398861536849)
              ·
                rfl

theorem cell22_1273696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 8].length) (baseStart_1273696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273696 prefixEnd_1273696 := by exact prefixLift 1273696
  have htrace : WordTrace (prefixWord ++ tailWord_1273696) baseStart_1273696 baseEnd_1273696 := by
    simpa [prefixWord, tailWord_1273696, baseEnd_1273696] using wordTrace_append hprefix tailTrace_1273696
  have hstable : (prefixWord ++ tailWord_1273696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273696).length < 2 ^ (prefixWord ++ tailWord_1273696).sum := by decide
  have hdescent : baseEnd_1273696 < baseStart_1273696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273698 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1273698 : Nat := 118140960795 + 1273698 * 2 ^ 59
def prefixEnd_1273698 : Nat := 4983230072969 + 3 ^ 40 * 1273698 * 2
def baseEnd_1273698 : Nat := 436012855113641922944917

theorem tailTrace_1273698 : CollatzResearch.WordTrace tailWord_1273698 prefixEnd_1273698 436012855113641922944917 := by
  unfold tailWord_1273698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11613895634904287786259437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30970388359744767430025165 11613895634904287786259437)
  ·
    refine ⟨4355210863089107919847289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11613895634904287786259437 4355210863089107919847289)
    ·
      refine ⟨3266408147316830939885467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4355210863089107919847289 3266408147316830939885467)
      ·
        refine ⟨4899612220975246409828201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3266408147316830939885467 4899612220975246409828201)
        ·
          refine ⟨3674709165731434807371151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4899612220975246409828201 3674709165731434807371151)
          ·
            refine ⟨5512063748597152211056727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674709165731434807371151 5512063748597152211056727)
            ·
              refine ⟨8268095622895728316585091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512063748597152211056727 8268095622895728316585091)
              ·
                refine ⟨12402143434343592474877637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8268095622895728316585091 12402143434343592474877637)
                ·
                  refine ⟨2325401893939423589039557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12402143434343592474877637 2325401893939423589039557)
                  ·
                    refine ⟨436012855113641922944917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2325401893939423589039557 436012855113641922944917)
                    ·
                      rfl

theorem cell22_1273698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1273698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273698 prefixEnd_1273698 := by exact prefixLift 1273698
  have htrace : WordTrace (prefixWord ++ tailWord_1273698) baseStart_1273698 baseEnd_1273698 := by
    simpa [prefixWord, tailWord_1273698, baseEnd_1273698] using wordTrace_append hprefix tailTrace_1273698
  have hstable : (prefixWord ++ tailWord_1273698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273698).length < 2 ^ (prefixWord ++ tailWord_1273698).sum := by decide
  have hdescent : baseEnd_1273698 < baseStart_1273698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273848 : List Nat := [2, 1, 2, 1, 1, 3, 6, 6]
def baseStart_1273848 : Nat := 118140960795 + 1273848 * 2 ^ 59
def prefixEnd_1273848 : Nat := 4983230072969 + 3 ^ 40 * 1273848 * 2
def baseEnd_1273848 : Nat := 48451578131010170188273

theorem tailTrace_1273848 : CollatzResearch.WordTrace tailWord_1273848 prefixEnd_1273848 48451578131010170188273 := by
  unfold tailWord_1273848
  simp only [CollatzResearch.WordTrace]
  refine ⟨23230526744536863381499099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30974035659382484508665465 23230526744536863381499099)
  ·
    refine ⟨34845790116805295072248649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23230526744536863381499099 34845790116805295072248649)
    ·
      refine ⟨26134342587603971304186487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34845790116805295072248649 26134342587603971304186487)
      ·
        refine ⟨39201513881405956956279731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26134342587603971304186487 39201513881405956956279731)
        ·
          refine ⟨58802270822108935434419597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39201513881405956956279731 58802270822108935434419597)
          ·
            refine ⟨22050851558290850787907349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58802270822108935434419597 22050851558290850787907349)
            ·
              refine ⟨1033633666794883630683157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22050851558290850787907349 1033633666794883630683157)
              ·
                refine ⟨48451578131010170188273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1033633666794883630683157 48451578131010170188273)
                ·
                  rfl

theorem cell22_1273848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 6].length) (baseStart_1273848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273848 prefixEnd_1273848 := by exact prefixLift 1273848
  have htrace : WordTrace (prefixWord ++ tailWord_1273848) baseStart_1273848 baseEnd_1273848 := by
    simpa [prefixWord, tailWord_1273848, baseEnd_1273848] using wordTrace_append hprefix tailTrace_1273848
  have hstable : (prefixWord ++ tailWord_1273848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273848).length < 2 ^ (prefixWord ++ tailWord_1273848).sum := by decide
  have hdescent : baseEnd_1273848 < baseStart_1273848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273854 : List Nat := [4, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_1273854 : Nat := 118140960795 + 1273854 * 2 ^ 59
def prefixEnd_1273854 : Nat := 4983230072969 + 3 ^ 40 * 1273854 * 2
def baseEnd_1273854 : Nat := 145355419033903172014813

theorem tailTrace_1273854 : CollatzResearch.WordTrace tailWord_1273854 prefixEnd_1273854 145355419033903172014813 := by
  unfold tailWord_1273854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5807659040881498723464577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30974181551367993191811077 5807659040881498723464577)
  ·
    refine ⟨4355744280661124042598433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5807659040881498723464577 4355744280661124042598433)
    ·
      refine ⟨3266808210495843031948825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4355744280661124042598433 3266808210495843031948825)
      ·
        refine ⟨2450106157871882273961619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3266808210495843031948825 2450106157871882273961619)
        ·
          refine ⟨3675159236807823410942429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450106157871882273961619 3675159236807823410942429)
          ·
            refine ⟨1378184713802933779103411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3675159236807823410942429 1378184713802933779103411)
            ·
              refine ⟨2067277070704400668655117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378184713802933779103411 2067277070704400668655117)
              ·
                refine ⟨775228901514150250745669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067277070704400668655117 775228901514150250745669)
                ·
                  refine ⟨145355419033903172014813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775228901514150250745669 145355419033903172014813)
                  ·
                    rfl

theorem cell22_1273854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_1273854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273854 prefixEnd_1273854 := by exact prefixLift 1273854
  have htrace : WordTrace (prefixWord ++ tailWord_1273854) baseStart_1273854 baseEnd_1273854 := by
    simpa [prefixWord, tailWord_1273854, baseEnd_1273854] using wordTrace_append hprefix tailTrace_1273854
  have hstable : (prefixWord ++ tailWord_1273854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273854).length < 2 ^ (prefixWord ++ tailWord_1273854).sum := by decide
  have hdescent : baseEnd_1273854 < baseStart_1273854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273942 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1273942 : Nat := 118140960795 + 1273942 * 2 ^ 59
def prefixEnd_1273942 : Nat := 4983230072969 + 3 ^ 40 * 1273942 * 2
def baseEnd_1273942 : Nat := 436096381300106619844169

theorem tailTrace_1273942 : CollatzResearch.WordTrace tailWord_1273942 prefixEnd_1273942 436096381300106619844169 := by
  unfold tailWord_1273942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904030121920823801057505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30976321300488787211280053 2904030121920823801057505)
  ·
    refine ⟨2178022591440617850793129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2904030121920823801057505 2178022591440617850793129)
    ·
      refine ⟨1633516943580463388094847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2178022591440617850793129 1633516943580463388094847)
      ·
        refine ⟨2450275415370695082142271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1633516943580463388094847 2450275415370695082142271)
        ·
          refine ⟨3675413123056042623213407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450275415370695082142271 3675413123056042623213407)
          ·
            refine ⟨5513119684584063934820111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675413123056042623213407 5513119684584063934820111)
            ·
              refine ⟨8269679526876095902230167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513119684584063934820111 8269679526876095902230167)
              ·
                refine ⟨12404519290314143853345251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8269679526876095902230167 12404519290314143853345251)
                ·
                  refine ⟨18606778935471215780017877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12404519290314143853345251 18606778935471215780017877)
                  ·
                    refine ⟨436096381300106619844169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18606778935471215780017877 436096381300106619844169)
                    ·
                      rfl

theorem cell22_1273942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1273942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273942 prefixEnd_1273942 := by exact prefixLift 1273942
  have htrace : WordTrace (prefixWord ++ tailWord_1273942) baseStart_1273942 baseEnd_1273942 := by
    simpa [prefixWord, tailWord_1273942, baseEnd_1273942] using wordTrace_append hprefix tailTrace_1273942
  have hstable : (prefixWord ++ tailWord_1273942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273942).length < 2 ^ (prefixWord ++ tailWord_1273942).sum := by decide
  have hdescent : baseEnd_1273942 < baseStart_1273942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273970 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1273970 : Nat := 118140960795 + 1273970 * 2 ^ 59
def prefixEnd_1273970 : Nat := 4983230072969 + 3 ^ 40 * 1273970 * 2
def baseEnd_1273970 : Nat := 436105966272323880144083

theorem tailTrace_1273970 : CollatzResearch.WordTrace tailWord_1273970 prefixEnd_1273970 436105966272323880144083 := by
  unfold tailWord_1273970
  simp only [CollatzResearch.WordTrace]
  refine ⟨11616375798657935399734841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30977002129754494399292909 11616375798657935399734841)
  ·
    refine ⟨8712281848993451549801131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11616375798657935399734841 8712281848993451549801131)
    ·
      refine ⟨13068422773490177324701697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8712281848993451549801131 13068422773490177324701697)
      ·
        refine ⟨9801317080117632993526273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13068422773490177324701697 9801317080117632993526273)
        ·
          refine ⟨7350987810088224745144705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9801317080117632993526273 7350987810088224745144705)
          ·
            refine ⟨5513240857566168558858529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7350987810088224745144705 5513240857566168558858529)
            ·
              refine ⟨4134930643174626419143897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513240857566168558858529 4134930643174626419143897)
              ·
                refine ⟨3101197982380969814357923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4134930643174626419143897 3101197982380969814357923)
                ·
                  refine ⟨4651796973571454721536885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101197982380969814357923 4651796973571454721536885)
                  ·
                    refine ⟨436105966272323880144083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4651796973571454721536885 436105966272323880144083)
                    ·
                      rfl

theorem cell22_1273970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1273970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273970 prefixEnd_1273970 := by exact prefixLift 1273970
  have htrace : WordTrace (prefixWord ++ tailWord_1273970) baseStart_1273970 baseEnd_1273970 := by
    simpa [prefixWord, tailWord_1273970, baseEnd_1273970] using wordTrace_append hprefix tailTrace_1273970
  have hstable : (prefixWord ++ tailWord_1273970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273970).length < 2 ^ (prefixWord ++ tailWord_1273970).sum := by decide
  have hdescent : baseEnd_1273970 < baseStart_1273970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273974 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_1273974 : Nat := 118140960795 + 1273974 * 2 ^ 59
def prefixEnd_1273974 : Nat := 4983230072969 + 3 ^ 40 * 1273974 * 2
def baseEnd_1273974 : Nat := 436107335554069203044071

theorem tailTrace_1273974 : CollatzResearch.WordTrace tailWord_1273974 prefixEnd_1273974 436107335554069203044071 := by
  unfold tailWord_1273974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904103067913578142630311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30977099391078166854723317 2904103067913578142630311)
  ·
    refine ⟨4356154601870367213945467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2904103067913578142630311 4356154601870367213945467)
    ·
      refine ⟨6534231902805550820918201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356154601870367213945467 6534231902805550820918201)
      ·
        refine ⟨4900673927104163115688651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6534231902805550820918201 4900673927104163115688651)
        ·
          refine ⟨7351010890656244673532977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4900673927104163115688651 7351010890656244673532977)
          ·
            refine ⟨5513258167992183505149733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7351010890656244673532977 5513258167992183505149733)
            ·
              refine ⟨1033735906498534407215575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5513258167992183505149733 1033735906498534407215575)
              ·
                refine ⟨1550603859747801610823363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033735906498534407215575 1550603859747801610823363)
                ·
                  refine ⟨2325905789621702416235045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550603859747801610823363 2325905789621702416235045)
                  ·
                    refine ⟨436107335554069203044071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2325905789621702416235045 436107335554069203044071)
                    ·
                      rfl

theorem cell22_1273974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_1273974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273974 prefixEnd_1273974 := by exact prefixLift 1273974
  have htrace : WordTrace (prefixWord ++ tailWord_1273974) baseStart_1273974 baseEnd_1273974 := by
    simpa [prefixWord, tailWord_1273974, baseEnd_1273974] using wordTrace_append hprefix tailTrace_1273974
  have hstable : (prefixWord ++ tailWord_1273974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273974).length < 2 ^ (prefixWord ++ tailWord_1273974).sum := by decide
  have hdescent : baseEnd_1273974 < baseStart_1273974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1273987 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 2, 3]
def baseStart_1273987 : Nat := 118140960795 + 1273987 * 2 ^ 59
def prefixEnd_1273987 : Nat := 4983230072969 + 3 ^ 40 * 1273987 * 2
def baseEnd_1273987 : Nat := 436111785719741502469031

theorem tailTrace_1273987 : CollatzResearch.WordTrace tailWord_1273987 prefixEnd_1273987 436111785719741502469031 := by
  unfold tailWord_1273987
  simp only [CollatzResearch.WordTrace]
  refine ⟨46466123235570153502308215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30977415490380102334872143 46466123235570153502308215)
  ·
    refine ⟨69699184853355230253462323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46466123235570153502308215 69699184853355230253462323)
    ·
      refine ⟨104548777280032845380193485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69699184853355230253462323 104548777280032845380193485)
      ·
        refine ⟨39205791480012317017572557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104548777280032845380193485 39205791480012317017572557)
        ·
          refine ⟨14702171805004618881589709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39205791480012317017572557 14702171805004618881589709)
          ·
            refine ⟨5513314426876732080596141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14702171805004618881589709 5513314426876732080596141)
            ·
              refine ⟨2067492910078774530223553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5513314426876732080596141 2067492910078774530223553)
              ·
                refine ⟨1550619682559080897667665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067492910078774530223553 1550619682559080897667665)
                ·
                  refine ⟨1162964761919310673250749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550619682559080897667665 1162964761919310673250749)
                  ·
                    refine ⟨436111785719741502469031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162964761919310673250749 436111785719741502469031)
                    ·
                      rfl

theorem cell22_1273987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 3].length) (baseStart_1273987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1273987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1273987 prefixEnd_1273987 := by exact prefixLift 1273987
  have htrace : WordTrace (prefixWord ++ tailWord_1273987) baseStart_1273987 baseEnd_1273987 := by
    simpa [prefixWord, tailWord_1273987, baseEnd_1273987] using wordTrace_append hprefix tailTrace_1273987
  have hstable : (prefixWord ++ tailWord_1273987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1273987).length < 2 ^ (prefixWord ++ tailWord_1273987).sum := by decide
  have hdescent : baseEnd_1273987 < baseStart_1273987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1273987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274017 : List Nat := [1, 2, 3, 3, 1, 4, 2, 6]
def baseStart_1274017 : Nat := 118140960795 + 1274017 * 2 ^ 59
def prefixEnd_1274017 : Nat := 4983230072969 + 3 ^ 40 * 1274017 * 2
def baseEnd_1274017 : Nat := 48458006148092380468771

theorem tailTrace_1274017 : CollatzResearch.WordTrace tailWord_1274017 prefixEnd_1274017 48458006148092380468771 := by
  unfold tailWord_1274017
  simp only [CollatzResearch.WordTrace]
  refine ⟨46467217425461468625900305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30978144950307645750600203 46467217425461468625900305)
  ·
    refine ⟨34850413069096101469425229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46467217425461468625900305 34850413069096101469425229)
    ·
      refine ⟨13068904900911038051034461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34850413069096101469425229 13068904900911038051034461)
      ·
        refine ⟨4900839337841639269137923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13068904900911038051034461 4900839337841639269137923)
        ·
          refine ⟨7351259006762458903706885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4900839337841639269137923 7351259006762458903706885)
          ·
            refine ⟨1378361063767961044445041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7351259006762458903706885 1378361063767961044445041)
            ·
              refine ⟨1033770797825970783333781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378361063767961044445041 1033770797825970783333781)
              ·
                refine ⟨48458006148092380468771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1033770797825970783333781 48458006148092380468771)
                ·
                  rfl

theorem cell22_1274017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 6].length) (baseStart_1274017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274017 prefixEnd_1274017 := by exact prefixLift 1274017
  have htrace : WordTrace (prefixWord ++ tailWord_1274017) baseStart_1274017 baseEnd_1274017 := by
    simpa [prefixWord, tailWord_1274017, baseEnd_1274017] using wordTrace_append hprefix tailTrace_1274017
  have hstable : (prefixWord ++ tailWord_1274017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274017).length < 2 ^ (prefixWord ++ tailWord_1274017).sum := by decide
  have hdescent : baseEnd_1274017 < baseStart_1274017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274045 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 5]
def baseStart_1274045 : Nat := 118140960795 + 1274045 * 2 ^ 59
def prefixEnd_1274045 : Nat := 4983230072969 + 3 ^ 40 * 1274045 * 2
def baseEnd_1274045 : Nat := 145377213435016228172951

theorem tailTrace_1274045 : CollatzResearch.WordTrace tailWord_1274045 prefixEnd_1274045 145377213435016228172951 := by
  unfold tailWord_1274045
  simp only [CollatzResearch.WordTrace]
  refine ⟨46468238669360029407919589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30978825779573352938613059 46468238669360029407919589)
  ·
    refine ⟨8712794750505005513984923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46468238669360029407919589 8712794750505005513984923)
    ·
      refine ⟨13069192125757508270977385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8712794750505005513984923 13069192125757508270977385)
      ·
        refine ⟨9801894094318131203233039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13069192125757508270977385 9801894094318131203233039)
        ·
          refine ⟨14702841141477196804849559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9801894094318131203233039 14702841141477196804849559)
          ·
            refine ⟨22054261712215795207274339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14702841141477196804849559 22054261712215795207274339)
            ·
              refine ⟨33081392568323692810911509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22054261712215795207274339 33081392568323692810911509)
              ·
                refine ⟨1550690276640173100511477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33081392568323692810911509 1550690276640173100511477)
                ·
                  refine ⟨145377213435016228172951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1550690276640173100511477 145377213435016228172951)
                  ·
                    rfl

theorem cell22_1274045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_1274045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274045 prefixEnd_1274045 := by exact prefixLift 1274045
  have htrace : WordTrace (prefixWord ++ tailWord_1274045) baseStart_1274045 baseEnd_1274045 := by
    simpa [prefixWord, tailWord_1274045, baseEnd_1274045] using wordTrace_append hprefix tailTrace_1274045
  have hstable : (prefixWord ++ tailWord_1274045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274045).length < 2 ^ (prefixWord ++ tailWord_1274045).sum := by decide
  have hdescent : baseEnd_1274045 < baseStart_1274045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274062 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_1274062 : Nat := 118140960795 + 1274062 * 2 ^ 59
def prefixEnd_1274062 : Nat := 4983230072969 + 3 ^ 40 * 1274062 * 2
def baseEnd_1274062 : Nat := 145379153250822102281267

theorem tailTrace_1274062 : CollatzResearch.WordTrace tailWord_1274062 prefixEnd_1274062 145379153250822102281267 := by
  unfold tailWord_1274062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808607338787305163911055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30979239140198960874192293 5808607338787305163911055)
  ·
    refine ⟨8712911008180957745866583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5808607338787305163911055 8712911008180957745866583)
    ·
      refine ⟨13069366512271436618799875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8712911008180957745866583 13069366512271436618799875)
      ·
        refine ⟨19604049768407154928199813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13069366512271436618799875 19604049768407154928199813)
        ·
          refine ⟨3675759331576341549037465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19604049768407154928199813 3675759331576341549037465)
          ·
            refine ⟨2756819498682256161778099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3675759331576341549037465 2756819498682256161778099)
            ·
              refine ⟨4135229248023384242667149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756819498682256161778099 4135229248023384242667149)
              ·
                refine ⟨1550710968008769091000181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4135229248023384242667149 1550710968008769091000181)
                ·
                  refine ⟨145379153250822102281267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1550710968008769091000181 145379153250822102281267)
                  ·
                    rfl

theorem cell22_1274062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_1274062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274062 prefixEnd_1274062 := by exact prefixLift 1274062
  have htrace : WordTrace (prefixWord ++ tailWord_1274062) baseStart_1274062 baseEnd_1274062 := by
    simpa [prefixWord, tailWord_1274062, baseEnd_1274062] using wordTrace_append hprefix tailTrace_1274062
  have hstable : (prefixWord ++ tailWord_1274062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274062).length < 2 ^ (prefixWord ++ tailWord_1274062).sum := by decide
  have hdescent : baseEnd_1274062 < baseStart_1274062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274141 : List Nat := [1, 4, 2, 3, 2, 1, 2, 3, 4]
def baseStart_1274141 : Nat := 118140960795 + 1274141 * 2 ^ 59
def prefixEnd_1274141 : Nat := 4983230072969 + 3 ^ 40 * 1274141 * 2
def baseEnd_1274141 : Nat := 145388167688978811372853

theorem tailTrace_1274141 : CollatzResearch.WordTrace tailWord_1274141 prefixEnd_1274141 145388167688978811372853 := by
  unfold tailWord_1274141
  simp only [CollatzResearch.WordTrace]
  refine ⟨46471740077012237803414277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30981160051341491868942851 46471740077012237803414277)
  ·
    refine ⟨8713451264439794588140177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46471740077012237803414277 8713451264439794588140177)
    ·
      refine ⟨6535088448329845941105133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8713451264439794588140177 6535088448329845941105133)
      ·
        refine ⟨2450658168123692227914425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6535088448329845941105133 2450658168123692227914425)
        ·
          refine ⟨1837993626092769170935819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2450658168123692227914425 1837993626092769170935819)
          ·
            refine ⟨2756990439139153756403729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837993626092769170935819 2756990439139153756403729)
            ·
              refine ⟨2067742829354365317302797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2756990439139153756403729 2067742829354365317302797)
              ·
                refine ⟨775403561007886993988549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067742829354365317302797 775403561007886993988549)
                ·
                  refine ⟨145388167688978811372853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775403561007886993988549 145388167688978811372853)
                  ·
                    rfl

theorem cell22_1274141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_1274141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274141 prefixEnd_1274141 := by exact prefixLift 1274141
  have htrace : WordTrace (prefixWord ++ tailWord_1274141) baseStart_1274141 baseEnd_1274141 := by
    simpa [prefixWord, tailWord_1274141, baseEnd_1274141] using wordTrace_append hprefix tailTrace_1274141
  have hstable : (prefixWord ++ tailWord_1274141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274141).length < 2 ^ (prefixWord ++ tailWord_1274141).sum := by decide
  have hdescent : baseEnd_1274141 < baseStart_1274141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274152 : List Nat := [2, 1, 5, 1, 3, 1, 9]
def baseStart_1274152 : Nat := 118140960795 + 1274152 * 2 ^ 59
def prefixEnd_1274152 : Nat := 4983230072969 + 3 ^ 40 * 1274152 * 2
def baseEnd_1274152 : Nat := 16154380318212447114575

theorem tailTrace_1274152 : CollatzResearch.WordTrace tailWord_1274152 prefixEnd_1274152 16154380318212447114575 := by
  unfold tailWord_1274152
  simp only [CollatzResearch.WordTrace]
  refine ⟨23236070639986193341032355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30981427519981591121376473 23236070639986193341032355)
  ·
    refine ⟨34854105959979290011548533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23236070639986193341032355 34854105959979290011548533)
    ·
      refine ⟨3267572433748058438582675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34854105959979290011548533 3267572433748058438582675)
      ·
        refine ⟨4901358650622087657874013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3267572433748058438582675 4901358650622087657874013)
        ·
          refine ⟨1838009493983282871702755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4901358650622087657874013 1838009493983282871702755)
          ·
            refine ⟨2757014240974924307554133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838009493983282871702755 2757014240974924307554133)
            ·
              refine ⟨16154380318212447114575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2757014240974924307554133 16154380318212447114575)
              ·
                rfl

theorem cell22_1274152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 9].length) (baseStart_1274152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274152 prefixEnd_1274152 := by exact prefixLift 1274152
  have htrace : WordTrace (prefixWord ++ tailWord_1274152) baseStart_1274152 baseEnd_1274152 := by
    simpa [prefixWord, tailWord_1274152, baseEnd_1274152] using wordTrace_append hprefix tailTrace_1274152
  have hstable : (prefixWord ++ tailWord_1274152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274152).length < 2 ^ (prefixWord ++ tailWord_1274152).sum := by decide
  have hdescent : baseEnd_1274152 < baseStart_1274152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274195 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 4, 5]
def baseStart_1274195 : Nat := 118140960795 + 1274195 * 2 ^ 59
def prefixEnd_1274195 : Nat := 4983230072969 + 3 ^ 40 * 1274195 * 2
def baseEnd_1274195 : Nat := 436182988370498293268393

theorem tailTrace_1274195 : CollatzResearch.WordTrace tailWord_1274195 prefixEnd_1274195 436182988370498293268393 := by
  unfold tailWord_1274195
  simp only [CollatzResearch.WordTrace]
  refine ⟨46473709618816605025880039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30982473079211070017253359 46473709618816605025880039)
  ·
    refine ⟨69710564428224907538820059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46473709618816605025880039 69710564428224907538820059)
    ·
      refine ⟨104565846642337361308230089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69710564428224907538820059 104565846642337361308230089)
      ·
        refine ⟨78424384981753020981172567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104565846642337361308230089 78424384981753020981172567)
        ·
          refine ⟨117636577472629531471758851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78424384981753020981172567 117636577472629531471758851)
          ·
            refine ⟨176454866208944297207638277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117636577472629531471758851 176454866208944297207638277)
            ·
              refine ⟨33085287414177055726432177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176454866208944297207638277 33085287414177055726432177)
              ·
                refine ⟨24813965560632791794824133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33085287414177055726432177 24813965560632791794824133)
                ·
                  refine ⟨4652618542618648461529525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24813965560632791794824133 4652618542618648461529525)
                  ·
                    refine ⟨436182988370498293268393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4652618542618648461529525 436182988370498293268393)
                    ·
                      rfl

theorem cell22_1274195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_1274195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274195 prefixEnd_1274195 := by exact prefixLift 1274195
  have htrace : WordTrace (prefixWord ++ tailWord_1274195) baseStart_1274195 baseEnd_1274195 := by
    simpa [prefixWord, tailWord_1274195, baseEnd_1274195] using wordTrace_append hprefix tailTrace_1274195
  have hstable : (prefixWord ++ tailWord_1274195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274195).length < 2 ^ (prefixWord ++ tailWord_1274195).sum := by decide
  have hdescent : baseEnd_1274195 < baseStart_1274195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274276 : List Nat := [2, 3, 1, 2, 1, 1, 6, 2, 4]
def baseStart_1274276 : Nat := 118140960795 + 1274276 * 2 ^ 59
def prefixEnd_1274276 : Nat := 4983230072969 + 3 ^ 40 * 1274276 * 2
def baseEnd_1274276 : Nat := 145403572108613693997715

theorem tailTrace_1274276 : CollatzResearch.WordTrace tailWord_1274276 prefixEnd_1274276 145403572108613693997715 := by
  unfold tailWord_1274276
  simp only [CollatzResearch.WordTrace]
  refine ⟨23238331965761577929789341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30984442621015437239719121 23238331965761577929789341)
  ·
    refine ⟨8714374487160591723671003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23238331965761577929789341 8714374487160591723671003)
    ·
      refine ⟨13071561730740887585506505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8714374487160591723671003 13071561730740887585506505)
      ·
        refine ⟨9803671298055665689129879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13071561730740887585506505 9803671298055665689129879)
        ·
          refine ⟨14705506947083498533694819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9803671298055665689129879 14705506947083498533694819)
          ·
            refine ⟨22058260420625247800542229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14705506947083498533694819 22058260420625247800542229)
            ·
              refine ⟨1033980957216808490650417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22058260420625247800542229 1033980957216808490650417)
              ·
                refine ⟨775485717912606367987813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033980957216808490650417 775485717912606367987813)
                ·
                  refine ⟨145403572108613693997715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775485717912606367987813 145403572108613693997715)
                  ·
                    rfl

theorem cell22_1274276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_1274276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274276 prefixEnd_1274276 := by exact prefixLift 1274276
  have htrace : WordTrace (prefixWord ++ tailWord_1274276) baseStart_1274276 baseEnd_1274276 := by
    simpa [prefixWord, tailWord_1274276, baseEnd_1274276] using wordTrace_append hprefix tailTrace_1274276
  have hstable : (prefixWord ++ tailWord_1274276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274276).length < 2 ^ (prefixWord ++ tailWord_1274276).sum := by decide
  have hdescent : baseEnd_1274276 < baseStart_1274276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274336 : List Nat := [2, 1, 1, 3, 1, 1, 3, 6, 1, 3]
def baseStart_1274336 : Nat := 118140960795 + 1274336 * 2 ^ 59
def prefixEnd_1274336 : Nat := 4983230072969 + 3 ^ 40 * 1274336 * 2
def baseEnd_1274336 : Nat := 436231255552020925492961

theorem tailTrace_1274336 : CollatzResearch.WordTrace tailWord_1274336 prefixEnd_1274336 436231255552020925492961 := by
  unfold tailWord_1274336
  simp only [CollatzResearch.WordTrace]
  refine ⟨23239426155652893053381431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30985901540870524071175241 23239426155652893053381431)
  ·
    refine ⟨34859139233479339580072147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23239426155652893053381431 34859139233479339580072147)
    ·
      refine ⟨52288708850219009370108221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34859139233479339580072147 52288708850219009370108221)
      ·
        refine ⟨19608265818832128513790583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52288708850219009370108221 19608265818832128513790583)
        ·
          refine ⟨29412398728248192770685875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19608265818832128513790583 29412398728248192770685875)
          ·
            refine ⟨44118598092372289156028813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29412398728248192770685875 44118598092372289156028813)
            ·
              refine ⟨16544474284639608433510805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44118598092372289156028813 16544474284639608433510805)
              ·
                refine ⟨775522232092481645320819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16544474284639608433510805 775522232092481645320819)
                ·
                  refine ⟨1163283348138722467981229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775522232092481645320819 1163283348138722467981229)
                  ·
                    refine ⟨436231255552020925492961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1163283348138722467981229 436231255552020925492961)
                    ·
                      rfl

theorem cell22_1274336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 3].length) (baseStart_1274336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274336 prefixEnd_1274336 := by exact prefixLift 1274336
  have htrace : WordTrace (prefixWord ++ tailWord_1274336) baseStart_1274336 baseEnd_1274336 := by
    simpa [prefixWord, tailWord_1274336, baseEnd_1274336] using wordTrace_append hprefix tailTrace_1274336
  have hstable : (prefixWord ++ tailWord_1274336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274336).length < 2 ^ (prefixWord ++ tailWord_1274336).sum := by decide
  have hdescent : baseEnd_1274336 < baseStart_1274336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274347 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 2, 5]
def baseStart_1274347 : Nat := 118140960795 + 1274347 * 2 ^ 59
def prefixEnd_1274347 : Nat := 4983230072969 + 3 ^ 40 * 1274347 * 2
def baseEnd_1274347 : Nat := 436235021076820563467927

theorem tailTrace_1274347 : CollatzResearch.WordTrace tailWord_1274347 prefixEnd_1274347 436235021076820563467927 := by
  unfold tailWord_1274347
  simp only [CollatzResearch.WordTrace]
  refine ⟨46479253514265934985413295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30986169009510623323608863 46479253514265934985413295)
  ·
    refine ⟨69718880271398902478119943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46479253514265934985413295 69718880271398902478119943)
    ·
      refine ⟨104578320407098353717179915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69718880271398902478119943 104578320407098353717179915)
      ·
        refine ⟨156867480610647530575769873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104578320407098353717179915 156867480610647530575769873)
        ·
          refine ⟨117650610457985647931827405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156867480610647530575769873 117650610457985647931827405)
          ·
            refine ⟨44118978921744617974435277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117650610457985647931827405 44118978921744617974435277)
            ·
              refine ⟨16544617095654231740413229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44118978921744617974435277 16544617095654231740413229)
              ·
                refine ⟨6204231410870336902654961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16544617095654231740413229 6204231410870336902654961)
                ·
                  refine ⟨4653173558152752676991221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6204231410870336902654961 4653173558152752676991221)
                  ·
                    refine ⟨436235021076820563467927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4653173558152752676991221 436235021076820563467927)
                    ·
                      rfl

theorem cell22_1274347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_1274347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274347 prefixEnd_1274347 := by exact prefixLift 1274347
  have htrace : WordTrace (prefixWord ++ tailWord_1274347) baseStart_1274347 baseEnd_1274347 := by
    simpa [prefixWord, tailWord_1274347, baseEnd_1274347] using wordTrace_append hprefix tailTrace_1274347
  have hstable : (prefixWord ++ tailWord_1274347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274347).length < 2 ^ (prefixWord ++ tailWord_1274347).sum := by decide
  have hdescent : baseEnd_1274347 < baseStart_1274347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274394 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_1274394 : Nat := 118140960795 + 1274394 * 2 ^ 59
def prefixEnd_1274394 : Nat := 4983230072969 + 3 ^ 40 * 1274394 * 2
def baseEnd_1274394 : Nat := 145417036712442702514261

theorem tailTrace_1274394 : CollatzResearch.WordTrace tailWord_1274394 prefixEnd_1274394 145417036712442702514261 := by
  unfold tailWord_1274394
  simp only [CollatzResearch.WordTrace]
  refine ⟨11620241936273915503093559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30987311830063774674916157 11620241936273915503093559)
  ·
    refine ⟨17430362904410873254640339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11620241936273915503093559 17430362904410873254640339)
    ·
      refine ⟨26145544356616309881960509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17430362904410873254640339 26145544356616309881960509)
      ·
        refine ⟨9804579133731116205735191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26145544356616309881960509 9804579133731116205735191)
        ·
          refine ⟨14706868700596674308602787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9804579133731116205735191 14706868700596674308602787)
          ·
            refine ⟨22060303050895011462904181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14706868700596674308602787 22060303050895011462904181)
            ·
              refine ⟨2068153411021407324647267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22060303050895011462904181 2068153411021407324647267)
              ·
                refine ⟨3102230116532110986970901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068153411021407324647267 3102230116532110986970901)
                ·
                  refine ⟨145417036712442702514261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3102230116532110986970901 145417036712442702514261)
                  ·
                    rfl

theorem cell22_1274394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_1274394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274394 prefixEnd_1274394 := by exact prefixLift 1274394
  have htrace : WordTrace (prefixWord ++ tailWord_1274394) baseStart_1274394 baseEnd_1274394 := by
    simpa [prefixWord, tailWord_1274394, baseEnd_1274394] using wordTrace_append hprefix tailTrace_1274394
  have hstable : (prefixWord ++ tailWord_1274394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274394).length < 2 ^ (prefixWord ++ tailWord_1274394).sum := by decide
  have hdescent : baseEnd_1274394 < baseStart_1274394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274400 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 5]
def baseStart_1274400 : Nat := 118140960795 + 1274400 * 2 ^ 59
def prefixEnd_1274400 : Nat := 4983230072969 + 3 ^ 40 * 1274400 * 2
def baseEnd_1274400 : Nat := 145417721353315363964255

theorem tailTrace_1274400 : CollatzResearch.WordTrace tailWord_1274400 prefixEnd_1274400 145417721353315363964255 := by
  unfold tailWord_1274400
  simp only [CollatzResearch.WordTrace]
  refine ⟨23240593291536962518546327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30987457722049283358061769 23240593291536962518546327)
  ·
    refine ⟨34860889937305443777819491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23240593291536962518546327 34860889937305443777819491)
    ·
      refine ⟨52291334905958165666729237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34860889937305443777819491 52291334905958165666729237)
      ·
        refine ⟨2451156323716789015627933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52291334905958165666729237 2451156323716789015627933)
        ·
          refine ⟨919183621393795880860475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2451156323716789015627933 919183621393795880860475)
          ·
            refine ⟨1378775432090693821290713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919183621393795880860475 1378775432090693821290713)
            ·
              refine ⟨1034081574068020365968035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378775432090693821290713 1034081574068020365968035)
              ·
                refine ⟨1551122361102030548952053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034081574068020365968035 1551122361102030548952053)
                ·
                  refine ⟨145417721353315363964255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551122361102030548952053 145417721353315363964255)
                  ·
                    rfl

theorem cell22_1274400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_1274400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274400 prefixEnd_1274400 := by exact prefixLift 1274400
  have htrace : WordTrace (prefixWord ++ tailWord_1274400) baseStart_1274400 baseEnd_1274400 := by
    simpa [prefixWord, tailWord_1274400, baseEnd_1274400] using wordTrace_append hprefix tailTrace_1274400
  have hstable : (prefixWord ++ tailWord_1274400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274400).length < 2 ^ (prefixWord ++ tailWord_1274400).sum := by decide
  have hdescent : baseEnd_1274400 < baseStart_1274400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274445 : List Nat := [1, 6, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1274445 : Nat := 118140960795 + 1274445 * 2 ^ 59
def prefixEnd_1274445 : Nat := 4983230072969 + 3 ^ 40 * 1274445 * 2
def baseEnd_1274445 : Nat := 145422856159860324839209

theorem tailTrace_1274445 : CollatzResearch.WordTrace tailWord_1274445 prefixEnd_1274445 145422856159860324839209 := by
  unfold tailWord_1274445
  simp only [CollatzResearch.WordTrace]
  refine ⟨46482827867910897722480789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30988551911940598481653859 46482827867910897722480789)
  ·
    refine ⟨2178882556308323330741287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46482827867910897722480789 2178882556308323330741287)
    ·
      refine ⟨3268323834462484996111931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2178882556308323330741287 3268323834462484996111931)
      ·
        refine ⟨4902485751693727494167897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3268323834462484996111931 4902485751693727494167897)
        ·
          refine ⟨3676864313770295620625923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4902485751693727494167897 3676864313770295620625923)
          ·
            refine ⟨5515296470655443430938885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3676864313770295620625923 5515296470655443430938885)
            ·
              refine ⟨1034118088247895643301041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5515296470655443430938885 1034118088247895643301041)
              ·
                refine ⟨775588566185921732475781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034118088247895643301041 775588566185921732475781)
                ·
                  refine ⟨145422856159860324839209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775588566185921732475781 145422856159860324839209)
                  ·
                    rfl

theorem cell22_1274445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1274445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274445 prefixEnd_1274445 := by exact prefixLift 1274445
  have htrace : WordTrace (prefixWord ++ tailWord_1274445) baseStart_1274445 baseEnd_1274445 := by
    simpa [prefixWord, tailWord_1274445, baseEnd_1274445] using wordTrace_append hprefix tailTrace_1274445
  have hstable : (prefixWord ++ tailWord_1274445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274445).length < 2 ^ (prefixWord ++ tailWord_1274445).sum := by decide
  have hdescent : baseEnd_1274445 < baseStart_1274445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274499 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 2, 5]
def baseStart_1274499 : Nat := 118140960795 + 1274499 * 2 ^ 59
def prefixEnd_1274499 : Nat := 4983230072969 + 3 ^ 40 * 1274499 * 2
def baseEnd_1274499 : Nat := 436287053783142833667461

theorem tailTrace_1274499 : CollatzResearch.WordTrace tailWord_1274499 prefixEnd_1274499 436287053783142833667461 := by
  unfold tailWord_1274499
  simp only [CollatzResearch.WordTrace]
  refine ⟨46484797409715264944946551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30989864939810176629964367 46484797409715264944946551)
  ·
    refine ⟨69727196114572897417419827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46484797409715264944946551 69727196114572897417419827)
    ·
      refine ⟨104590794171859346126129741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69727196114572897417419827 104590794171859346126129741)
      ·
        refine ⟨39221547814447254797298653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104590794171859346126129741 39221547814447254797298653)
        ·
          refine ⟨14708080430417720548986995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39221547814447254797298653 14708080430417720548986995)
          ·
            refine ⟨22062120645626580823480493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14708080430417720548986995 22062120645626580823480493)
            ·
              refine ⟨8273295242109967808805185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22062120645626580823480493 8273295242109967808805185)
              ·
                refine ⟨6204971431582475856603889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8273295242109967808805185 6204971431582475856603889)
                ·
                  refine ⟨4653728573686856892452917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6204971431582475856603889 4653728573686856892452917)
                  ·
                    refine ⟨436287053783142833667461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4653728573686856892452917 436287053783142833667461)
                    ·
                      rfl

theorem cell22_1274499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_1274499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274499 prefixEnd_1274499 := by exact prefixLift 1274499
  have htrace : WordTrace (prefixWord ++ tailWord_1274499) baseStart_1274499 baseEnd_1274499 := by
    simpa [prefixWord, tailWord_1274499, baseEnd_1274499] using wordTrace_append hprefix tailTrace_1274499
  have hstable : (prefixWord ++ tailWord_1274499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274499).length < 2 ^ (prefixWord ++ tailWord_1274499).sum := by decide
  have hdescent : baseEnd_1274499 < baseStart_1274499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274501 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 5]
def baseStart_1274501 : Nat := 118140960795 + 1274501 * 2 ^ 59
def prefixEnd_1274501 : Nat := 4983230072969 + 3 ^ 40 * 1274501 * 2
def baseEnd_1274501 : Nat := 145429246141338498372485

theorem tailTrace_1274501 : CollatzResearch.WordTrace tailWord_1274501 prefixEnd_1274501 145429246141338498372485 := by
  unfold tailWord_1274501
  simp only [CollatzResearch.WordTrace]
  refine ⟨46484870355708019286519357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30989913570472012857679571 46484870355708019286519357)
  ·
    refine ⟨17431826383390507232444759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46484870355708019286519357 17431826383390507232444759)
    ·
      refine ⟨26147739575085760848667139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17431826383390507232444759 26147739575085760848667139)
      ·
        refine ⟨39221609362628641273000709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26147739575085760848667139 39221609362628641273000709)
        ·
          refine ⟨7354051755492870238687633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39221609362628641273000709 7354051755492870238687633)
          ·
            refine ⟨5515538816619652679015725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7354051755492870238687633 5515538816619652679015725)
            ·
              refine ⟨2068327056232369754630897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5515538816619652679015725 2068327056232369754630897)
              ·
                refine ⟨1551245292174277315973173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068327056232369754630897 1551245292174277315973173)
                ·
                  refine ⟨145429246141338498372485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551245292174277315973173 145429246141338498372485)
                  ·
                    rfl

theorem cell22_1274501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_1274501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274501 prefixEnd_1274501 := by exact prefixLift 1274501
  have htrace : WordTrace (prefixWord ++ tailWord_1274501) baseStart_1274501 baseEnd_1274501 := by
    simpa [prefixWord, tailWord_1274501, baseEnd_1274501] using wordTrace_append hprefix tailTrace_1274501
  have hstable : (prefixWord ++ tailWord_1274501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274501).length < 2 ^ (prefixWord ++ tailWord_1274501).sum := by decide
  have hdescent : baseEnd_1274501 < baseStart_1274501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274544 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_1274544 : Nat := 118140960795 + 1274544 * 2 ^ 59
def prefixEnd_1274544 : Nat := 4983230072969 + 3 ^ 40 * 1274544 * 2
def baseEnd_1274544 : Nat := 436302458202777716292323

theorem tailTrace_1274544 : CollatzResearch.WordTrace tailWord_1274544 prefixEnd_1274544 436302458202777716292323 := by
  unfold tailWord_1274544
  simp only [CollatzResearch.WordTrace]
  refine ⟨23243219347276118815167343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30990959129701491753556457 23243219347276118815167343)
  ·
    refine ⟨34864829020914178222751015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23243219347276118815167343 34864829020914178222751015)
    ·
      refine ⟨52297243531371267334126523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34864829020914178222751015 52297243531371267334126523)
      ·
        refine ⟨78445865297056901001189785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52297243531371267334126523 78445865297056901001189785)
        ·
          refine ⟨58834398972792675750892339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78445865297056901001189785 58834398972792675750892339)
          ·
            refine ⟨88251598459189013626338509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58834398972792675750892339 88251598459189013626338509)
            ·
              refine ⟨33094349422195880109876941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88251598459189013626338509 33094349422195880109876941)
              ·
                refine ⟨12410381033323455041203853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33094349422195880109876941 12410381033323455041203853)
                ·
                  refine ⟨4653892887496295640451445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12410381033323455041203853 4653892887496295640451445)
                  ·
                    refine ⟨436302458202777716292323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4653892887496295640451445 436302458202777716292323)
                    ·
                      rfl

theorem cell22_1274544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_1274544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274544 prefixEnd_1274544 := by exact prefixLift 1274544
  have htrace : WordTrace (prefixWord ++ tailWord_1274544) baseStart_1274544 baseEnd_1274544 := by
    simpa [prefixWord, tailWord_1274544, baseEnd_1274544] using wordTrace_append hprefix tailTrace_1274544
  have hstable : (prefixWord ++ tailWord_1274544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274544).length < 2 ^ (prefixWord ++ tailWord_1274544).sum := by decide
  have hdescent : baseEnd_1274544 < baseStart_1274544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274593 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1274593 : Nat := 118140960795 + 1274593 * 2 ^ 59
def prefixEnd_1274593 : Nat := 4983230072969 + 3 ^ 40 * 1274593 * 2
def baseEnd_1274593 : Nat := 436319231904157921817173

theorem tailTrace_1274593 : CollatzResearch.WordTrace tailWord_1274593 prefixEnd_1274593 436319231904157921817173 := by
  unfold tailWord_1274593
  simp only [CollatzResearch.WordTrace]
  refine ⟨46488225871374718998868433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30992150580916479332578955 46488225871374718998868433)
  ·
    refine ⟨34866169403531039249151325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46488225871374718998868433 34866169403531039249151325)
    ·
      refine ⟨13074813526324139718431747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34866169403531039249151325 13074813526324139718431747)
      ·
        refine ⟨19612220289486209577647621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13074813526324139718431747 19612220289486209577647621)
        ·
          refine ⟨3677291304278664295808929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19612220289486209577647621 3677291304278664295808929)
          ·
            refine ⟨2757968478208998221856697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3677291304278664295808929 2757968478208998221856697)
            ·
              refine ⟨2068476358656748666392523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2757968478208998221856697 2068476358656748666392523)
              ·
                refine ⟨3102714537985122999588785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068476358656748666392523 3102714537985122999588785)
                ·
                  refine ⟨2327035903488842249691589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3102714537985122999588785 2327035903488842249691589)
                  ·
                    refine ⟨436319231904157921817173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2327035903488842249691589 436319231904157921817173)
                    ·
                      rfl

theorem cell22_1274593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1274593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274593 prefixEnd_1274593 := by exact prefixLift 1274593
  have htrace : WordTrace (prefixWord ++ tailWord_1274593) baseStart_1274593 baseEnd_1274593 := by
    simpa [prefixWord, tailWord_1274593, baseEnd_1274593] using wordTrace_append hprefix tailTrace_1274593
  have hstable : (prefixWord ++ tailWord_1274593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274593).length < 2 ^ (prefixWord ++ tailWord_1274593).sum := by decide
  have hdescent : baseEnd_1274593 < baseStart_1274593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274619 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 11]
def baseStart_1274619 : Nat := 118140960795 + 1274619 * 2 ^ 59
def prefixEnd_1274619 : Nat := 4983230072969 + 3 ^ 40 * 1274619 * 2
def baseEnd_1274619 : Nat := 145442710745167506889031

theorem tailTrace_1274619 : CollatzResearch.WordTrace tailWord_1274619 prefixEnd_1274619 145442710745167506889031 := by
  unfold tailWord_1274619
  simp only [CollatzResearch.WordTrace]
  refine ⟨46489174169280525439314911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30992782779520350292876607 46489174169280525439314911)
  ·
    refine ⟨69733761253920788158972367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46489174169280525439314911 69733761253920788158972367)
    ·
      refine ⟨104600641880881182238458551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69733761253920788158972367 104600641880881182238458551)
      ·
        refine ⟨156900962821321773357687827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104600641880881182238458551 156900962821321773357687827)
        ·
          refine ⟨235351444231982660036531741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156900962821321773357687827 235351444231982660036531741)
          ·
            refine ⟨88256791586993497513699403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235351444231982660036531741 88256791586993497513699403)
            ·
              refine ⟨132385187380490246270549105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88256791586993497513699403 132385187380490246270549105)
              ·
                refine ⟨99288890535367684702911829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132385187380490246270549105 99288890535367684702911829)
                ·
                  refine ⟨145442710745167506889031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 99288890535367684702911829 145442710745167506889031)
                  ·
                    rfl

theorem cell22_1274619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 11].length) (baseStart_1274619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274619 prefixEnd_1274619 := by exact prefixLift 1274619
  have htrace : WordTrace (prefixWord ++ tailWord_1274619) baseStart_1274619 baseEnd_1274619 := by
    simpa [prefixWord, tailWord_1274619, baseEnd_1274619] using wordTrace_append hprefix tailTrace_1274619
  have hstable : (prefixWord ++ tailWord_1274619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274619).length < 2 ^ (prefixWord ++ tailWord_1274619).sum := by decide
  have hdescent : baseEnd_1274619 < baseStart_1274619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274670 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_1274670 : Nat := 118140960795 + 1274670 * 2 ^ 59
def prefixEnd_1274670 : Nat := 4983230072969 + 3 ^ 40 * 1274670 * 2
def baseEnd_1274670 : Nat := 145448530192585129213979

theorem tailTrace_1274670 : CollatzResearch.WordTrace tailWord_1274670 prefixEnd_1274670 145448530192585129213979 := by
  unfold tailWord_1274670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811379286511970143677683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30994022861397174099614309 5811379286511970143677683)
  ·
    refine ⟨8717068929767955215516525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5811379286511970143677683 8717068929767955215516525)
    ·
      refine ⟨3268900848662983205818697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8717068929767955215516525 3268900848662983205818697)
      ·
        refine ⟨2451675636497237404364023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3268900848662983205818697 2451675636497237404364023)
        ·
          refine ⟨3677513454745856106546035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451675636497237404364023 3677513454745856106546035)
          ·
            refine ⟨5516270182118784159819053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677513454745856106546035 5516270182118784159819053)
            ·
              refine ⟨2068601318294544059932145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5516270182118784159819053 2068601318294544059932145)
              ·
                refine ⟨1551450988720908044949109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068601318294544059932145 1551450988720908044949109)
                ·
                  refine ⟨145448530192585129213979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551450988720908044949109 145448530192585129213979)
                  ·
                    rfl

theorem cell22_1274670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_1274670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274670 prefixEnd_1274670 := by exact prefixLift 1274670
  have htrace : WordTrace (prefixWord ++ tailWord_1274670) baseStart_1274670 baseEnd_1274670 := by
    simpa [prefixWord, tailWord_1274670, baseEnd_1274670] using wordTrace_append hprefix tailTrace_1274670
  have hstable : (prefixWord ++ tailWord_1274670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274670).length < 2 ^ (prefixWord ++ tailWord_1274670).sum := by decide
  have hdescent : baseEnd_1274670 < baseStart_1274670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274700 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_1274700 : Nat := 118140960795 + 1274700 * 2 ^ 59
def prefixEnd_1274700 : Nat := 4983230072969 + 3 ^ 40 * 1274700 * 2
def baseEnd_1274700 : Nat := 436355860190845309391845

theorem tailTrace_1274700 : CollatzResearch.WordTrace tailWord_1274700 prefixEnd_1274700 436355860190845309391845 := by
  unfold tailWord_1274700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23246064240993538136506777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30994752321324717515342369 23246064240993538136506777)
  ·
    refine ⟨17434548180745153602380083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23246064240993538136506777 17434548180745153602380083)
    ·
      refine ⟨26151822271117730403570125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17434548180745153602380083 26151822271117730403570125)
      ·
        refine ⟨9806933351669148901338797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26151822271117730403570125 9806933351669148901338797)
        ·
          refine ⟨3677600006875930838002049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9806933351669148901338797 3677600006875930838002049)
          ·
            refine ⟨2758200005156948128501537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3677600006875930838002049 2758200005156948128501537)
            ·
              refine ⟨2068650003867711096376153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2758200005156948128501537 2068650003867711096376153)
              ·
                refine ⟨1551487502900783322282115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2068650003867711096376153 1551487502900783322282115)
                ·
                  refine ⟨2327231254351174983423173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1551487502900783322282115 2327231254351174983423173)
                  ·
                    refine ⟨436355860190845309391845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2327231254351174983423173 436355860190845309391845)
                    ·
                      rfl

theorem cell22_1274700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_1274700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274700 prefixEnd_1274700 := by exact prefixLift 1274700
  have htrace : WordTrace (prefixWord ++ tailWord_1274700) baseStart_1274700 baseEnd_1274700 := by
    simpa [prefixWord, tailWord_1274700, baseEnd_1274700] using wordTrace_append hprefix tailTrace_1274700
  have hstable : (prefixWord ++ tailWord_1274700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274700).length < 2 ^ (prefixWord ++ tailWord_1274700).sum := by decide
  have hdescent : baseEnd_1274700 < baseStart_1274700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274713 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 4, 3]
def baseStart_1274713 : Nat := 118140960795 + 1274713 * 2 ^ 59
def prefixEnd_1274713 : Nat := 4983230072969 + 3 ^ 40 * 1274713 * 2
def baseEnd_1274713 : Nat := 436360310356517608816805

theorem tailTrace_1274713 : CollatzResearch.WordTrace tailWord_1274713 prefixEnd_1274713 436360310356517608816805 := by
  unfold tailWord_1274713
  simp only [CollatzResearch.WordTrace]
  refine ⟨46492602630939979493236793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30995068420626652995491195 46492602630939979493236793)
  ·
    refine ⟨34869451973204984619927595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46492602630939979493236793 34869451973204984619927595)
    ·
      refine ⟨52304177959807476929891393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34869451973204984619927595 52304177959807476929891393)
      ·
        refine ⟨39228133469855607697418545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52304177959807476929891393 39228133469855607697418545)
        ·
          refine ⟨29421100102391705773063909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39228133469855607697418545 29421100102391705773063909)
          ·
            refine ⟨5516456269198444832449483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29421100102391705773063909 5516456269198444832449483)
            ·
              refine ⟨8274684403797667248674225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5516456269198444832449483 8274684403797667248674225)
              ·
                refine ⟨6206013302848250436505669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8274684403797667248674225 6206013302848250436505669)
                ·
                  refine ⟨1163627494284046956844813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6206013302848250436505669 1163627494284046956844813)
                  ·
                    refine ⟨436360310356517608816805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1163627494284046956844813 436360310356517608816805)
                    ·
                      rfl

theorem cell22_1274713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_1274713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274713 prefixEnd_1274713 := by exact prefixLift 1274713
  have htrace : WordTrace (prefixWord ++ tailWord_1274713) baseStart_1274713 baseEnd_1274713 := by
    simpa [prefixWord, tailWord_1274713, baseEnd_1274713] using wordTrace_append hprefix tailTrace_1274713
  have hstable : (prefixWord ++ tailWord_1274713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274713).length < 2 ^ (prefixWord ++ tailWord_1274713).sum := by decide
  have hdescent : baseEnd_1274713 < baseStart_1274713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274728 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_1274728 : Nat := 118140960795 + 1274728 * 2 ^ 59
def prefixEnd_1274728 : Nat := 4983230072969 + 3 ^ 40 * 1274728 * 2
def baseEnd_1274728 : Nat := 436365445163062569691759

theorem tailTrace_1274728 : CollatzResearch.WordTrace tailWord_1274728 prefixEnd_1274728 436365445163062569691759 := by
  unfold tailWord_1274728
  simp only [CollatzResearch.WordTrace]
  refine ⟨23246574862942818527516419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30995433150590424703355225 23246574862942818527516419)
  ·
    refine ⟨34869862294414227791274629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23246574862942818527516419 34869862294414227791274629)
    ·
      refine ⟨6538099180202667710863993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34869862294414227791274629 6538099180202667710863993)
      ·
        refine ⟨4903574385152000783147995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6538099180202667710863993 4903574385152000783147995)
        ·
          refine ⟨7355361577728001174721993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4903574385152000783147995 7355361577728001174721993)
          ·
            refine ⟨5516521183296000881041495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7355361577728001174721993 5516521183296000881041495)
            ·
              refine ⟨8274781774944001321562243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5516521183296000881041495 8274781774944001321562243)
              ·
                refine ⟨12412172662416001982343365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8274781774944001321562243 12412172662416001982343365)
                ·
                  refine ⟨2327282374203000371689381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12412172662416001982343365 2327282374203000371689381)
                  ·
                    refine ⟨436365445163062569691759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2327282374203000371689381 436365445163062569691759)
                    ·
                      rfl

theorem cell22_1274728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_1274728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274728 prefixEnd_1274728 := by exact prefixLift 1274728
  have htrace : WordTrace (prefixWord ++ tailWord_1274728) baseStart_1274728 baseEnd_1274728 := by
    simpa [prefixWord, tailWord_1274728, baseEnd_1274728] using wordTrace_append hprefix tailTrace_1274728
  have hstable : (prefixWord ++ tailWord_1274728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274728).length < 2 ^ (prefixWord ++ tailWord_1274728).sum := by decide
  have hdescent : baseEnd_1274728 < baseStart_1274728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274771 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 7]
def baseStart_1274771 : Nat := 118140960795 + 1274771 * 2 ^ 59
def prefixEnd_1274771 : Nat := 4983230072969 + 3 ^ 40 * 1274771 * 2
def baseEnd_1274771 : Nat := 145460054980608263622209

theorem tailTrace_1274771 : CollatzResearch.WordTrace tailWord_1274771 prefixEnd_1274771 145460054980608263622209 := by
  unfold tailWord_1274771
  simp only [CollatzResearch.WordTrace]
  refine ⟨46494718064729855398848167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30996478709819903599232111 46494718064729855398848167)
  ·
    refine ⟨69742077097094783098272251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46494718064729855398848167 69742077097094783098272251)
    ·
      refine ⟨104613115645642174647408377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69742077097094783098272251 104613115645642174647408377)
      ·
        refine ⟨78459836734231630985556283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104613115645642174647408377 78459836734231630985556283)
        ·
          refine ⟨117689755101347446478334425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78459836734231630985556283 117689755101347446478334425)
          ·
            refine ⟨88267316326010584858750819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117689755101347446478334425 88267316326010584858750819)
            ·
              refine ⟨132400974489015877288126229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88267316326010584858750819 132400974489015877288126229)
              ·
                refine ⟨6206295679172619247880917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132400974489015877288126229 6206295679172619247880917)
                ·
                  refine ⟨145460054980608263622209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6206295679172619247880917 145460054980608263622209)
                  ·
                    rfl

theorem cell22_1274771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 7].length) (baseStart_1274771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274771 prefixEnd_1274771 := by exact prefixLift 1274771
  have htrace : WordTrace (prefixWord ++ tailWord_1274771) baseStart_1274771 baseEnd_1274771 := by
    simpa [prefixWord, tailWord_1274771, baseEnd_1274771] using wordTrace_append hprefix tailTrace_1274771
  have hstable : (prefixWord ++ tailWord_1274771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274771).length < 2 ^ (prefixWord ++ tailWord_1274771).sum := by decide
  have hdescent : baseEnd_1274771 < baseStart_1274771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274863 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 1, 6]
def baseStart_1274863 : Nat := 118140960795 + 1274863 * 2 ^ 59
def prefixEnd_1274863 : Nat := 4983230072969 + 3 ^ 40 * 1274863 * 2
def baseEnd_1274863 : Nat := 436411658421967217566345

theorem tailTrace_1274863 : CollatzResearch.WordTrace tailWord_1274863 prefixEnd_1274863 436411658421967217566345 := by
  unfold tailWord_1274863
  simp only [CollatzResearch.WordTrace]
  refine ⟨46498073580396555111197243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30998715720264370074131495 46498073580396555111197243)
  ·
    refine ⟨69747110370594832666795865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46498073580396555111197243 69747110370594832666795865)
    ·
      refine ⟨52310332777946124500096899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69747110370594832666795865 52310332777946124500096899)
      ·
        refine ⟨78465499166919186750145349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52310332777946124500096899 78465499166919186750145349)
        ·
          refine ⟨14712281093797347515652253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78465499166919186750145349 14712281093797347515652253)
          ·
            refine ⟨5517105410174005318369595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14712281093797347515652253 5517105410174005318369595)
            ·
              refine ⟨8275658115261007977554393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517105410174005318369595 8275658115261007977554393)
              ·
                refine ⟨6206743586445755983165795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8275658115261007977554393 6206743586445755983165795)
                ·
                  refine ⟨9310115379668633974748693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6206743586445755983165795 9310115379668633974748693)
                  ·
                    refine ⟨436411658421967217566345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9310115379668633974748693 436411658421967217566345)
                    ·
                      rfl

theorem cell22_1274863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_1274863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274863 prefixEnd_1274863 := by exact prefixLift 1274863
  have htrace : WordTrace (prefixWord ++ tailWord_1274863) baseStart_1274863 baseEnd_1274863 := by
    simpa [prefixWord, tailWord_1274863, baseEnd_1274863] using wordTrace_append hprefix tailTrace_1274863
  have hstable : (prefixWord ++ tailWord_1274863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274863).length < 2 ^ (prefixWord ++ tailWord_1274863).sum := by decide
  have hdescent : baseEnd_1274863 < baseStart_1274863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274865 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 1, 5]
def baseStart_1274865 : Nat := 118140960795 + 1274865 * 2 ^ 59
def prefixEnd_1274865 : Nat := 4983230072969 + 3 ^ 40 * 1274865 * 2
def baseEnd_1274865 : Nat := 436412343062839879016339

theorem tailTrace_1274865 : CollatzResearch.WordTrace tailWord_1274865 prefixEnd_1274865 436412343062839879016339 := by
  unfold tailWord_1274865
  simp only [CollatzResearch.WordTrace]
  refine ⟨46498146526389309452770049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30998764350926206301846699 46498146526389309452770049)
  ·
    refine ⟨34873609894791982089577537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46498146526389309452770049 34873609894791982089577537)
    ·
      refine ⟨26155207421093986567183153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34873609894791982089577537 26155207421093986567183153)
      ·
        refine ⟨19616405565820489925387365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26155207421093986567183153 19616405565820489925387365)
        ·
          refine ⟨3678076043591341861010131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19616405565820489925387365 3678076043591341861010131)
          ·
            refine ⟨5517114065387012791515197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678076043591341861010131 5517114065387012791515197)
            ·
              refine ⟨2068917774520129796818199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5517114065387012791515197 2068917774520129796818199)
              ·
                refine ⟨3103376661780194695227299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068917774520129796818199 3103376661780194695227299)
                ·
                  refine ⟨4655064992670292042840949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103376661780194695227299 4655064992670292042840949)
                  ·
                    refine ⟨436412343062839879016339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4655064992670292042840949 436412343062839879016339)
                    ·
                      rfl

theorem cell22_1274865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_1274865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274865 prefixEnd_1274865 := by exact prefixLift 1274865
  have htrace : WordTrace (prefixWord ++ tailWord_1274865) baseStart_1274865 baseEnd_1274865 := by
    simpa [prefixWord, tailWord_1274865, baseEnd_1274865] using wordTrace_append hprefix tailTrace_1274865
  have hstable : (prefixWord ++ tailWord_1274865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274865).length < 2 ^ (prefixWord ++ tailWord_1274865).sum := by decide
  have hdescent : baseEnd_1274865 < baseStart_1274865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274912 : List Nat := [2, 1, 1, 7, 1, 1, 2, 7]
def baseStart_1274912 : Nat := 118140960795 + 1274912 * 2 ^ 59
def prefixEnd_1274912 : Nat := 4983230072969 + 3 ^ 40 * 1274912 * 2
def baseEnd_1274912 : Nat := 48492048013705269232355

theorem tailTrace_1274912 : CollatzResearch.WordTrace tailWord_1274912 prefixEnd_1274912 48492048013705269232355 := by
  unfold tailWord_1274912
  simp only [CollatzResearch.WordTrace]
  refine ⟨23249930378609518239865495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30999907171479357653153993 23249930378609518239865495)
  ·
    refine ⟨34874895567914277359798243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23249930378609518239865495 34874895567914277359798243)
    ·
      refine ⟨52312343351871416039697365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34874895567914277359798243 52312343351871416039697365)
      ·
        refine ⟨1226070547309486313430407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 52312343351871416039697365 1226070547309486313430407)
        ·
          refine ⟨1839105820964229470145611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226070547309486313430407 1839105820964229470145611)
          ·
            refine ⟨2758658731446344205218417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839105820964229470145611 2758658731446344205218417)
            ·
              refine ⟨2068994048584758153913813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2758658731446344205218417 2068994048584758153913813)
              ·
                refine ⟨48492048013705269232355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2068994048584758153913813 48492048013705269232355)
                ·
                  rfl

theorem cell22_1274912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 7].length) (baseStart_1274912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274912 prefixEnd_1274912 := by exact prefixLift 1274912
  have htrace : WordTrace (prefixWord ++ tailWord_1274912) baseStart_1274912 baseEnd_1274912 := by
    simpa [prefixWord, tailWord_1274912, baseEnd_1274912] using wordTrace_append hprefix tailTrace_1274912
  have hstable : (prefixWord ++ tailWord_1274912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274912).length < 2 ^ (prefixWord ++ tailWord_1274912).sum := by decide
  have hdescent : baseEnd_1274912 < baseStart_1274912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274916 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_1274916 : Nat := 118140960795 + 1274916 * 2 ^ 59
def prefixEnd_1274916 : Nat := 4983230072969 + 3 ^ 40 * 1274916 * 2
def baseEnd_1274916 : Nat := 436429801405092745991183

theorem tailTrace_1274916 : CollatzResearch.WordTrace tailWord_1274916 prefixEnd_1274916 436429801405092745991183 := by
  unfold tailWord_1274916
  simp only [CollatzResearch.WordTrace]
  refine ⟨23250003324602272581438301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31000004432803030108584401 23250003324602272581438301)
  ·
    refine ⟨8718751246725852218039363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23250003324602272581438301 8718751246725852218039363)
    ·
      refine ⟨13078126870088778327059045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8718751246725852218039363 13078126870088778327059045)
      ·
        refine ⟨2452148788141645936323571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13078126870088778327059045 2452148788141645936323571)
        ·
          refine ⟨3678223182212468904485357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452148788141645936323571 3678223182212468904485357)
          ·
            refine ⟨1379333693329675839182009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3678223182212468904485357 1379333693329675839182009)
            ·
              refine ⟨1034500269997256879386507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1379333693329675839182009 1034500269997256879386507)
              ·
                refine ⟨1551750404995885319079761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034500269997256879386507 1551750404995885319079761)
                ·
                  refine ⟨1163812803746913989309821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1551750404995885319079761 1163812803746913989309821)
                  ·
                    refine ⟨436429801405092745991183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1163812803746913989309821 436429801405092745991183)
                    ·
                      rfl

theorem cell22_1274916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_1274916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274916 prefixEnd_1274916 := by exact prefixLift 1274916
  have htrace : WordTrace (prefixWord ++ tailWord_1274916) baseStart_1274916 baseEnd_1274916 := by
    simpa [prefixWord, tailWord_1274916, baseEnd_1274916] using wordTrace_append hprefix tailTrace_1274916
  have hstable : (prefixWord ++ tailWord_1274916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274916).length < 2 ^ (prefixWord ++ tailWord_1274916).sum := by decide
  have hdescent : baseEnd_1274916 < baseStart_1274916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274957 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 5]
def baseStart_1274957 : Nat := 118140960795 + 1274957 * 2 ^ 59
def prefixEnd_1274957 : Nat := 4983230072969 + 3 ^ 40 * 1274957 * 2
def baseEnd_1274957 : Nat := 145481278847660768572019

theorem tailTrace_1274957 : CollatzResearch.WordTrace tailWord_1274957 prefixEnd_1274957 145481278847660768572019 := by
  unfold tailWord_1274957
  simp only [CollatzResearch.WordTrace]
  refine ⟨46501502042056009165119125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31001001361370672776746083 46501502042056009165119125)
  ·
    refine ⟨2179757908221375429614959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46501502042056009165119125 2179757908221375429614959)
    ·
      refine ⟨3269636862332063144422439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2179757908221375429614959 3269636862332063144422439)
      ·
        refine ⟨4904455293498094716633659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269636862332063144422439 4904455293498094716633659)
        ·
          refine ⟨7356682940247142074950489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4904455293498094716633659 7356682940247142074950489)
          ·
            refine ⟨5517512205185356556212867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7356682940247142074950489 5517512205185356556212867)
            ·
              refine ⟨8276268307778034834319301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517512205185356556212867 8276268307778034834319301)
              ·
                refine ⟨1551800307708381531434869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8276268307778034834319301 1551800307708381531434869)
                ·
                  refine ⟨145481278847660768572019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1551800307708381531434869 145481278847660768572019)
                  ·
                    rfl

theorem cell22_1274957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_1274957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274957 prefixEnd_1274957 := by exact prefixLift 1274957
  have htrace : WordTrace (prefixWord ++ tailWord_1274957) baseStart_1274957 baseEnd_1274957 := by
    simpa [prefixWord, tailWord_1274957, baseEnd_1274957] using wordTrace_append hprefix tailTrace_1274957
  have hstable : (prefixWord ++ tailWord_1274957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274957).length < 2 ^ (prefixWord ++ tailWord_1274957).sum := by decide
  have hdescent : baseEnd_1274957 < baseStart_1274957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1274985 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 6]
def baseStart_1274985 : Nat := 118140960795 + 1274985 * 2 ^ 59
def prefixEnd_1274985 : Nat := 4983230072969 + 3 ^ 40 * 1274985 * 2
def baseEnd_1274985 : Nat := 145484473838399855338657

theorem tailTrace_1274985 : CollatzResearch.WordTrace tailWord_1274985 prefixEnd_1274985 145484473838399855338657 := by
  unfold tailWord_1274985
  simp only [CollatzResearch.WordTrace]
  refine ⟨46502523285954569947138409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31001682190636379964758939 46502523285954569947138409)
  ·
    refine ⟨34876892464465927460353807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46502523285954569947138409 34876892464465927460353807)
    ·
      refine ⟨52315338696698891190530711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34876892464465927460353807 52315338696698891190530711)
      ·
        refine ⟨78473008045048336785796067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52315338696698891190530711 78473008045048336785796067)
        ·
          refine ⟨117709512067572505178694101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78473008045048336785796067 117709512067572505178694101)
          ·
            refine ⟨2758816689083730590125643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 117709512067572505178694101 2758816689083730590125643)
            ·
              refine ⟨4138225033625595885188465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758816689083730590125643 4138225033625595885188465)
              ·
                refine ⟨3103668775219196913891349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4138225033625595885188465 3103668775219196913891349)
                ·
                  refine ⟨145484473838399855338657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3103668775219196913891349 145484473838399855338657)
                  ·
                    rfl

theorem cell22_1274985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 6].length) (baseStart_1274985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1274985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1274985 prefixEnd_1274985 := by exact prefixLift 1274985
  have htrace : WordTrace (prefixWord ++ tailWord_1274985) baseStart_1274985 baseEnd_1274985 := by
    simpa [prefixWord, tailWord_1274985, baseEnd_1274985] using wordTrace_append hprefix tailTrace_1274985
  have hstable : (prefixWord ++ tailWord_1274985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1274985).length < 2 ^ (prefixWord ++ tailWord_1274985).sum := by decide
  have hdescent : baseEnd_1274985 < baseStart_1274985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1274985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275000 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_1275000 : Nat := 118140960795 + 1275000 * 2 ^ 59
def prefixEnd_1275000 : Nat := 4983230072969 + 3 ^ 40 * 1275000 * 2
def baseEnd_1275000 : Nat := 436458556321744526890925

theorem tailTrace_1275000 : CollatzResearch.WordTrace tailWord_1275000 prefixEnd_1275000 436458556321744526890925 := by
  unfold tailWord_1275000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23251535190450113754467227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31002046920600151672622969 23251535190450113754467227)
  ·
    refine ⟨34877302785675170631700841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23251535190450113754467227 34877302785675170631700841)
    ·
      refine ⟨26157977089256377973775631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34877302785675170631700841 26157977089256377973775631)
      ·
        refine ⟨39236965633884566960663447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26157977089256377973775631 39236965633884566960663447)
        ·
          refine ⟨58855448450826850440995171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39236965633884566960663447 58855448450826850440995171)
          ·
            refine ⟨88283172676240275661492757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58855448450826850440995171 88283172676240275661492757)
            ·
              refine ⟨4138273719198762921632473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88283172676240275661492757 4138273719198762921632473)
              ·
                refine ⟨3103705289399072191224355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4138273719198762921632473 3103705289399072191224355)
                ·
                  refine ⟨4655557934098608286836533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103705289399072191224355 4655557934098608286836533)
                  ·
                    refine ⟨436458556321744526890925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4655557934098608286836533 436458556321744526890925)
                    ·
                      rfl

theorem cell22_1275000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_1275000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275000 prefixEnd_1275000 := by exact prefixLift 1275000
  have htrace : WordTrace (prefixWord ++ tailWord_1275000) baseStart_1275000 baseEnd_1275000 := by
    simpa [prefixWord, tailWord_1275000, baseEnd_1275000] using wordTrace_append hprefix tailTrace_1275000
  have hstable : (prefixWord ++ tailWord_1275000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275000).length < 2 ^ (prefixWord ++ tailWord_1275000).sum := by decide
  have hdescent : baseEnd_1275000 < baseStart_1275000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275015 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 4, 4]
def baseStart_1275015 : Nat := 118140960795 + 1275015 * 2 ^ 59
def prefixEnd_1275015 : Nat := 4983230072969 + 3 ^ 40 * 1275015 * 2
def baseEnd_1275015 : Nat := 436463691128289487765879

theorem tailTrace_1275015 : CollatzResearch.WordTrace tailWord_1275015 prefixEnd_1275015 436463691128289487765879 := by
  unfold tailWord_1275015
  simp only [CollatzResearch.WordTrace]
  refine ⟨46503617475845885070730499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31002411650563923380486999 46503617475845885070730499)
  ·
    refine ⟨69755426213768827606095749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46503617475845885070730499 69755426213768827606095749)
    ·
      refine ⟨13079142415081655176142953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69755426213768827606095749 13079142415081655176142953)
      ·
        refine ⟨9809356811311241382107215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13079142415081655176142953 9809356811311241382107215)
        ·
          refine ⟨14714035216966862073160823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9809356811311241382107215 14714035216966862073160823)
          ·
            refine ⟨22071052825450293109741235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14714035216966862073160823 22071052825450293109741235)
            ·
              refine ⟨33106579238175439664611853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22071052825450293109741235 33106579238175439664611853)
              ·
                refine ⟨12414967214315789874229445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33106579238175439664611853 12414967214315789874229445)
                ·
                  refine ⟨2327806352684210601418021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12414967214315789874229445 2327806352684210601418021)
                  ·
                    refine ⟨436463691128289487765879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2327806352684210601418021 436463691128289487765879)
                    ·
                      rfl

theorem cell22_1275015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_1275015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275015 prefixEnd_1275015 := by exact prefixLift 1275015
  have htrace : WordTrace (prefixWord ++ tailWord_1275015) baseStart_1275015 baseEnd_1275015 := by
    simpa [prefixWord, tailWord_1275015, baseEnd_1275015] using wordTrace_append hprefix tailTrace_1275015
  have hstable : (prefixWord ++ tailWord_1275015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275015).length < 2 ^ (prefixWord ++ tailWord_1275015).sum := by decide
  have hdescent : baseEnd_1275015 < baseStart_1275015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275017 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 4, 3]
def baseStart_1275017 : Nat := 118140960795 + 1275017 * 2 ^ 59
def prefixEnd_1275017 : Nat := 4983230072969 + 3 ^ 40 * 1275017 * 2
def baseEnd_1275017 : Nat := 436464375769162149215873

theorem tailTrace_1275017 : CollatzResearch.WordTrace tailWord_1275017 prefixEnd_1275017 436464375769162149215873 := by
  unfold tailWord_1275017
  simp only [CollatzResearch.WordTrace]
  refine ⟨46503690421838639412303305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31002460281225759608202203 46503690421838639412303305)
  ·
    refine ⟨34877767816378979559227479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46503690421838639412303305 34877767816378979559227479)
    ·
      refine ⟨52316651724568469338841219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34877767816378979559227479 52316651724568469338841219)
      ·
        refine ⟨78474977586852704008261829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52316651724568469338841219 78474977586852704008261829)
        ·
          refine ⟨14714058297534882001549093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78474977586852704008261829 14714058297534882001549093)
          ·
            refine ⟨2758885930787790375290455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14714058297534882001549093 2758885930787790375290455)
            ·
              refine ⟨4138328896181685562935683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758885930787790375290455 4138328896181685562935683)
              ·
                refine ⟨6207493344272528344403525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4138328896181685562935683 6207493344272528344403525)
                ·
                  refine ⟨1163905002051099064575661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6207493344272528344403525 1163905002051099064575661)
                  ·
                    refine ⟨436464375769162149215873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1163905002051099064575661 436464375769162149215873)
                    ·
                      rfl

theorem cell22_1275017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_1275017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275017 prefixEnd_1275017 := by exact prefixLift 1275017
  have htrace : WordTrace (prefixWord ++ tailWord_1275017) baseStart_1275017 baseEnd_1275017 := by
    simpa [prefixWord, tailWord_1275017, baseEnd_1275017] using wordTrace_append hprefix tailTrace_1275017
  have hstable : (prefixWord ++ tailWord_1275017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275017).length < 2 ^ (prefixWord ++ tailWord_1275017).sum := by decide
  have hdescent : baseEnd_1275017 < baseStart_1275017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275034 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_1275034 : Nat := 118140960795 + 1275034 * 2 ^ 59
def prefixEnd_1275034 : Nat := 4983230072969 + 3 ^ 40 * 1275034 * 2
def baseEnd_1275034 : Nat := 436470195216579771540821

theorem tailTrace_1275034 : CollatzResearch.WordTrace tailWord_1275034 prefixEnd_1275034 436470195216579771540821 := by
  unfold tailWord_1275034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11626077615694262828918039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31002873641851367543781437 11626077615694262828918039)
  ·
    refine ⟨17439116423541394243377059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11626077615694262828918039 17439116423541394243377059)
    ·
      refine ⟨26158674635312091365065589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17439116423541394243377059 26158674635312091365065589)
      ·
        refine ⟨2452375747060508565474899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26158674635312091365065589 2452375747060508565474899)
        ·
          refine ⟨3678563620590762848212349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452375747060508565474899 3678563620590762848212349)
          ·
            refine ⟨1379461357721536068079631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3678563620590762848212349 1379461357721536068079631)
            ·
              refine ⟨2069192036582304102119447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379461357721536068079631 2069192036582304102119447)
              ·
                refine ⟨3103788054873456153179171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069192036582304102119447 3103788054873456153179171)
                ·
                  refine ⟨4655682082310184229768757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103788054873456153179171 4655682082310184229768757)
                  ·
                    refine ⟨436470195216579771540821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4655682082310184229768757 436470195216579771540821)
                    ·
                      rfl

theorem cell22_1275034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_1275034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275034 prefixEnd_1275034 := by exact prefixLift 1275034
  have htrace : WordTrace (prefixWord ++ tailWord_1275034) baseStart_1275034 baseEnd_1275034 := by
    simpa [prefixWord, tailWord_1275034, baseEnd_1275034] using wordTrace_append hprefix tailTrace_1275034
  have hstable : (prefixWord ++ tailWord_1275034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275034).length < 2 ^ (prefixWord ++ tailWord_1275034).sum := by decide
  have hdescent : baseEnd_1275034 < baseStart_1275034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275047 : List Nat := [1, 1, 6, 2, 1, 2, 1, 8]
def baseStart_1275047 : Nat := 118140960795 + 1275047 * 2 ^ 59
def prefixEnd_1275047 : Nat := 4983230072969 + 3 ^ 40 * 1275047 * 2
def baseEnd_1275047 : Nat := 48497182820250230107309

theorem tailTrace_1275047 : CollatzResearch.WordTrace tailWord_1275047 prefixEnd_1275047 48497182820250230107309 := by
  unfold tailWord_1275047
  simp only [CollatzResearch.WordTrace]
  refine ⟨46504784611729954535895395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31003189741153303023930263 46504784611729954535895395)
  ·
    refine ⟨69757176917594931803843093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46504784611729954535895395 69757176917594931803843093)
    ·
      refine ⟨3269867668012262428305145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69757176917594931803843093 3269867668012262428305145)
      ·
        refine ⟨2452400751009196821228859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3269867668012262428305145 2452400751009196821228859)
        ·
          refine ⟨3678601126513795231843289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452400751009196821228859 3678601126513795231843289)
          ·
            refine ⟨2758950844885346423882467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3678601126513795231843289 2758950844885346423882467)
            ·
              refine ⟨4138426267328019635823701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758950844885346423882467 4138426267328019635823701)
              ·
                refine ⟨48497182820250230107309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4138426267328019635823701 48497182820250230107309)
                ·
                  rfl

theorem cell22_1275047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 8].length) (baseStart_1275047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275047 prefixEnd_1275047 := by exact prefixLift 1275047
  have htrace : WordTrace (prefixWord ++ tailWord_1275047) baseStart_1275047 baseEnd_1275047 := by
    simpa [prefixWord, tailWord_1275047, baseEnd_1275047] using wordTrace_append hprefix tailTrace_1275047
  have hstable : (prefixWord ++ tailWord_1275047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275047).length < 2 ^ (prefixWord ++ tailWord_1275047).sum := by decide
  have hdescent : baseEnd_1275047 < baseStart_1275047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275053 : List Nat := [1, 5, 2, 1, 4, 1, 1, 3, 4]
def baseStart_1275053 : Nat := 118140960795 + 1275053 * 2 ^ 59
def prefixEnd_1275053 : Nat := 4983230072969 + 3 ^ 40 * 1275053 * 2
def baseEnd_1275053 : Nat := 145492233101623351771921

theorem tailTrace_1275053 : CollatzResearch.WordTrace tailWord_1275053 prefixEnd_1275053 145492233101623351771921 := by
  unfold tailWord_1275053
  simp only [CollatzResearch.WordTrace]
  refine ⟨46505003449708217560613813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31003335633138811707075875 46505003449708217560613813)
  ·
    refine ⟨4359844073410145396307545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46505003449708217560613813 4359844073410145396307545)
    ·
      refine ⟨3269883055057609047230659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4359844073410145396307545 3269883055057609047230659)
      ·
        refine ⟨4904824582586413570845989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269883055057609047230659 4904824582586413570845989)
        ·
          refine ⟨919654609234952544533623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4904824582586413570845989 919654609234952544533623)
          ·
            refine ⟨1379481913852428816800435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919654609234952544533623 1379481913852428816800435)
            ·
              refine ⟨2069222870778643225200653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379481913852428816800435 2069222870778643225200653)
              ·
                refine ⟨775958576541991209450245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2069222870778643225200653 775958576541991209450245)
                ·
                  refine ⟨145492233101623351771921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 775958576541991209450245 145492233101623351771921)
                  ·
                    rfl

theorem cell22_1275053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_1275053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275053 prefixEnd_1275053 := by exact prefixLift 1275053
  have htrace : WordTrace (prefixWord ++ tailWord_1275053) baseStart_1275053 baseEnd_1275053 := by
    simpa [prefixWord, tailWord_1275053, baseEnd_1275053] using wordTrace_append hprefix tailTrace_1275053
  have hstable : (prefixWord ++ tailWord_1275053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275053).length < 2 ^ (prefixWord ++ tailWord_1275053).sum := by decide
  have hdescent : baseEnd_1275053 < baseStart_1275053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275079 : List Nat := [1, 1, 4, 1, 1, 1, 1, 8, 1, 3]
def baseStart_1275079 : Nat := 118140960795 + 1275079 * 2 ^ 59
def prefixEnd_1275079 : Nat := 4983230072969 + 3 ^ 40 * 1275079 * 2
def baseEnd_1275079 : Nat := 436485599636214654165683

theorem tailTrace_1275079 : CollatzResearch.WordTrace tailWord_1275079 prefixEnd_1275079 436485599636214654165683 := by
  unfold tailWord_1275079
  simp only [CollatzResearch.WordTrace]
  refine ⟨46505951747614024001060291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31003967831742682667373527 46505951747614024001060291)
  ·
    refine ⟨69758927621421036001590437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46505951747614024001060291 69758927621421036001590437)
    ·
      refine ⟨13079798929016444250298207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69758927621421036001590437 13079798929016444250298207)
      ·
        refine ⟨19619698393524666375447311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13079798929016444250298207 19619698393524666375447311)
        ·
          refine ⟨29429547590286999563170967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19619698393524666375447311 29429547590286999563170967)
          ·
            refine ⟨44144321385430499344756451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29429547590286999563170967 44144321385430499344756451)
            ·
              refine ⟨66216482078145749017134677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44144321385430499344756451 66216482078145749017134677)
              ·
                refine ⟨775974399353270496294547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 66216482078145749017134677 775974399353270496294547)
                ·
                  refine ⟨1163961599029905744441821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775974399353270496294547 1163961599029905744441821)
                  ·
                    refine ⟨436485599636214654165683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1163961599029905744441821 436485599636214654165683)
                    ·
                      rfl

theorem cell22_1275079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_1275079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275079 prefixEnd_1275079 := by exact prefixLift 1275079
  have htrace : WordTrace (prefixWord ++ tailWord_1275079) baseStart_1275079 baseEnd_1275079 := by
    simpa [prefixWord, tailWord_1275079, baseEnd_1275079] using wordTrace_append hprefix tailTrace_1275079
  have hstable : (prefixWord ++ tailWord_1275079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275079).length < 2 ^ (prefixWord ++ tailWord_1275079).sum := by decide
  have hdescent : baseEnd_1275079 < baseStart_1275079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275186 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_1275186 : Nat := 118140960795 + 1275186 * 2 ^ 59
def prefixEnd_1275186 : Nat := 4983230072969 + 3 ^ 40 * 1275186 * 2
def baseEnd_1275186 : Nat := 436522227922902041740355

theorem tailTrace_1275186 : CollatzResearch.WordTrace tailWord_1275186 prefixEnd_1275186 436522227922902041740355 := by
  unfold tailWord_1275186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11627463589556595318801353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31006569572150920850136941 11627463589556595318801353)
  ·
    refine ⟨8720597692167446489101015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11627463589556595318801353 8720597692167446489101015)
    ·
      refine ⟨13080896538251169733651523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8720597692167446489101015 13080896538251169733651523)
      ·
        refine ⟨19621344807376754600477285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13080896538251169733651523 19621344807376754600477285)
        ·
          refine ⟨3679002151383141487589491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19621344807376754600477285 3679002151383141487589491)
          ·
            refine ⟨5518503227074712231384237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679002151383141487589491 5518503227074712231384237)
            ·
              refine ⟨2069438710153017086769089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5518503227074712231384237 2069438710153017086769089)
              ·
                refine ⟨1552079032614762815076817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069438710153017086769089 1552079032614762815076817)
                ·
                  refine ⟨1164059274461072111307613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1552079032614762815076817 1164059274461072111307613)
                  ·
                    refine ⟨436522227922902041740355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164059274461072111307613 436522227922902041740355)
                    ·
                      rfl

theorem cell22_1275186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_1275186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275186 prefixEnd_1275186 := by exact prefixLift 1275186
  have htrace : WordTrace (prefixWord ++ tailWord_1275186) baseStart_1275186 baseEnd_1275186 := by
    simpa [prefixWord, tailWord_1275186, baseEnd_1275186] using wordTrace_append hprefix tailTrace_1275186
  have hstable : (prefixWord ++ tailWord_1275186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275186).length < 2 ^ (prefixWord ++ tailWord_1275186).sum := by decide
  have hdescent : baseEnd_1275186 < baseStart_1275186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275214 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1275214 : Nat := 118140960795 + 1275214 * 2 ^ 59
def prefixEnd_1275214 : Nat := 4983230072969 + 3 ^ 40 * 1275214 * 2
def baseEnd_1275214 : Nat := 436531812895119302040269

theorem tailTrace_1275214 : CollatzResearch.WordTrace tailWord_1275214 prefixEnd_1275214 436531812895119302040269 := by
  unfold tailWord_1275214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5813859450265617757153087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31007250401416628038149797 5813859450265617757153087)
  ·
    refine ⟨8720789175398426635729631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5813859450265617757153087 8720789175398426635729631)
    ·
      refine ⟨13081183763097639953594447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8720789175398426635729631 13081183763097639953594447)
      ·
        refine ⟨19621775644646459930391671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13081183763097639953594447 19621775644646459930391671)
        ·
          refine ⟨29432663466969689895587507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19621775644646459930391671 29432663466969689895587507)
          ·
            refine ⟨44148995200454534843381261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29432663466969689895587507 44148995200454534843381261)
            ·
              refine ⟨16555873200170450566267973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44148995200454534843381261 16555873200170450566267973)
              ·
                refine ⟨3104226225031959481175245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16555873200170450566267973 3104226225031959481175245)
                ·
                  refine ⟨1164084834386984805440717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3104226225031959481175245 1164084834386984805440717)
                  ·
                    refine ⟨436531812895119302040269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164084834386984805440717 436531812895119302040269)
                    ·
                      rfl

theorem cell22_1275214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1275214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275214 prefixEnd_1275214 := by exact prefixLift 1275214
  have htrace : WordTrace (prefixWord ++ tailWord_1275214) baseStart_1275214 baseEnd_1275214 := by
    simpa [prefixWord, tailWord_1275214, baseEnd_1275214] using wordTrace_append hprefix tailTrace_1275214
  have hstable : (prefixWord ++ tailWord_1275214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275214).length < 2 ^ (prefixWord ++ tailWord_1275214).sum := by decide
  have hdescent : baseEnd_1275214 < baseStart_1275214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275248 : List Nat := [2, 1, 1, 1, 4, 2, 5, 2, 1, 3]
def baseStart_1275248 : Nat := 118140960795 + 1275248 * 2 ^ 59
def prefixEnd_1275248 : Nat := 4983230072969 + 3 ^ 40 * 1275248 * 2
def baseEnd_1275248 : Nat := 436543451789954546690165

theorem tailTrace_1275248 : CollatzResearch.WordTrace tailWord_1275248 prefixEnd_1275248 436543451789954546690165 := by
  unfold tailWord_1275248
  simp only [CollatzResearch.WordTrace]
  refine ⟨23256057842000882931981199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31008077122667843909308265 23256057842000882931981199)
  ·
    refine ⟨34884086763001324397971799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23256057842000882931981199 34884086763001324397971799)
    ·
      refine ⟨52326130144501986596957699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34884086763001324397971799 52326130144501986596957699)
      ·
        refine ⟨78489195216752979895436549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52326130144501986596957699 78489195216752979895436549)
        ·
          refine ⟨14716724103141183730394353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78489195216752979895436549 14716724103141183730394353)
          ·
            refine ⟨11037543077355887797795765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14716724103141183730394353 11037543077355887797795765)
            ·
              refine ⟨1034769663502114481043353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11037543077355887797795765 1034769663502114481043353)
              ·
                refine ⟨776077247626585860782515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034769663502114481043353 776077247626585860782515)
                ·
                  refine ⟨1164115871439878791173773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776077247626585860782515 1164115871439878791173773)
                  ·
                    refine ⟨436543451789954546690165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164115871439878791173773 436543451789954546690165)
                    ·
                      rfl

theorem cell22_1275248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 3].length) (baseStart_1275248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275248 prefixEnd_1275248 := by exact prefixLift 1275248
  have htrace : WordTrace (prefixWord ++ tailWord_1275248) baseStart_1275248 baseEnd_1275248 := by
    simpa [prefixWord, tailWord_1275248, baseEnd_1275248] using wordTrace_append hprefix tailTrace_1275248
  have hstable : (prefixWord ++ tailWord_1275248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275248).length < 2 ^ (prefixWord ++ tailWord_1275248).sum := by decide
  have hdescent : baseEnd_1275248 < baseStart_1275248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275321 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 1, 5]
def baseStart_1275321 : Nat := 118140960795 + 1275321 * 2 ^ 59
def prefixEnd_1275321 : Nat := 4983230072969 + 3 ^ 40 * 1275321 * 2
def baseEnd_1275321 : Nat := 436568441181806689614941

theorem tailTrace_1275321 : CollatzResearch.WordTrace tailWord_1275321 prefixEnd_1275321 436568441181806689614941 := by
  unfold tailWord_1275321
  simp only [CollatzResearch.WordTrace]
  refine ⟨46514778212737299331369817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31009852141824866220913211 46514778212737299331369817)
  ·
    refine ⟨34886083659552974498527363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46514778212737299331369817 34886083659552974498527363)
    ·
      refine ⟨52329125489329461747791045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34886083659552974498527363 52329125489329461747791045)
      ·
        refine ⟨9811711029249274077710821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52329125489329461747791045 9811711029249274077710821)
        ·
          refine ⟨1839695817984238889570779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9811711029249274077710821 1839695817984238889570779)
          ·
            refine ⟨2759543726976358334356169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839695817984238889570779 2759543726976358334356169)
            ·
              refine ⟨2069657795232268750767127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2759543726976358334356169 2069657795232268750767127)
              ·
                refine ⟨3104486692848403126150691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069657795232268750767127 3104486692848403126150691)
                ·
                  refine ⟨4656730039272604689226037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104486692848403126150691 4656730039272604689226037)
                  ·
                    refine ⟨436568441181806689614941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4656730039272604689226037 436568441181806689614941)
                    ·
                      rfl

theorem cell22_1275321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_1275321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275321 prefixEnd_1275321 := by exact prefixLift 1275321
  have htrace : WordTrace (prefixWord ++ tailWord_1275321) baseStart_1275321 baseEnd_1275321 := by
    simpa [prefixWord, tailWord_1275321, baseEnd_1275321] using wordTrace_append hprefix tailTrace_1275321
  have hstable : (prefixWord ++ tailWord_1275321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275321).length < 2 ^ (prefixWord ++ tailWord_1275321).sum := by decide
  have hdescent : baseEnd_1275321 < baseStart_1275321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275443 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 1, 4]
def baseStart_1275443 : Nat := 118140960795 + 1275443 * 2 ^ 59
def prefixEnd_1275443 : Nat := 4983230072969 + 3 ^ 40 * 1275443 * 2
def baseEnd_1275443 : Nat := 436610204275039038064567

theorem tailTrace_1275443 : CollatzResearch.WordTrace tailWord_1275443 prefixEnd_1275443 436610204275039038064567 := by
  unfold tailWord_1275443
  simp only [CollatzResearch.WordTrace]
  refine ⟨46519227918295314167310983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31012818612196876111540655 46519227918295314167310983)
  ·
    refine ⟨69778841877442971250966475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46519227918295314167310983 69778841877442971250966475)
    ·
      refine ⟨104668262816164456876449713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69778841877442971250966475 104668262816164456876449713)
      ·
        refine ⟨78501197112123342657337285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104668262816164456876449713 78501197112123342657337285)
        ·
          refine ⟨14718974458523126748250741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78501197112123342657337285 14718974458523126748250741)
          ·
            refine ⟨1379903855486543132648507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14718974458523126748250741 1379903855486543132648507)
            ·
              refine ⟨2069855783229814698972761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379903855486543132648507 2069855783229814698972761)
              ·
                refine ⟨1552391837422361024229571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069855783229814698972761 1552391837422361024229571)
                ·
                  refine ⟨2328587756133541536344357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552391837422361024229571 2328587756133541536344357)
                  ·
                    refine ⟨436610204275039038064567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2328587756133541536344357 436610204275039038064567)
                    ·
                      rfl

theorem cell22_1275443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 4].length) (baseStart_1275443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275443 prefixEnd_1275443 := by exact prefixLift 1275443
  have htrace : WordTrace (prefixWord ++ tailWord_1275443) baseStart_1275443 baseEnd_1275443 := by
    simpa [prefixWord, tailWord_1275443, baseEnd_1275443] using wordTrace_append hprefix tailTrace_1275443
  have hstable : (prefixWord ++ tailWord_1275443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275443).length < 2 ^ (prefixWord ++ tailWord_1275443).sum := by decide
  have hdescent : baseEnd_1275443 < baseStart_1275443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275473 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 2, 3]
def baseStart_1275473 : Nat := 118140960795 + 1275473 * 2 ^ 59
def prefixEnd_1275473 : Nat := 4983230072969 + 3 ^ 40 * 1275473 * 2
def baseEnd_1275473 : Nat := 436620473888128959814475

theorem tailTrace_1275473 : CollatzResearch.WordTrace tailWord_1275473 prefixEnd_1275473 436620473888128959814475 := by
  unfold tailWord_1275473
  simp only [CollatzResearch.WordTrace]
  refine ⟨46520322108186629290903073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31013548072124419527268715 46520322108186629290903073)
  ·
    refine ⟨34890241581139971968177305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46520322108186629290903073 34890241581139971968177305)
    ·
      refine ⟨26167681185854978976132979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34890241581139971968177305 26167681185854978976132979)
      ·
        refine ⟨39251521778782468464199469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26167681185854978976132979 39251521778782468464199469)
        ·
          refine ⟨14719320667043425674074801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39251521778782468464199469 14719320667043425674074801)
          ·
            refine ⟨11039490500282569255556101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14719320667043425674074801 11039490500282569255556101)
            ·
              refine ⟨2069904468802981735416769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11039490500282569255556101 2069904468802981735416769)
              ·
                refine ⟨1552428351602236301562577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069904468802981735416769 1552428351602236301562577)
                ·
                  refine ⟨1164321263701677226171933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1552428351602236301562577 1164321263701677226171933)
                  ·
                    refine ⟨436620473888128959814475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164321263701677226171933 436620473888128959814475)
                    ·
                      rfl

theorem cell22_1275473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_1275473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275473 prefixEnd_1275473 := by exact prefixLift 1275473
  have htrace : WordTrace (prefixWord ++ tailWord_1275473) baseStart_1275473 baseEnd_1275473 := by
    simpa [prefixWord, tailWord_1275473, baseEnd_1275473] using wordTrace_append hprefix tailTrace_1275473
  have hstable : (prefixWord ++ tailWord_1275473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275473).length < 2 ^ (prefixWord ++ tailWord_1275473).sum := by decide
  have hdescent : baseEnd_1275473 < baseStart_1275473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275578 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_1275578 : Nat := 118140960795 + 1275578 * 2 ^ 59
def prefixEnd_1275578 : Nat := 4983230072969 + 3 ^ 40 * 1275578 * 2
def baseEnd_1275578 : Nat := 436656417533943685939153

theorem tailTrace_1275578 : CollatzResearch.WordTrace tailWord_1275578 prefixEnd_1275578 436656417533943685939153 := by
  unfold tailWord_1275578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11631037943201558055868847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31016101181870821482316925 11631037943201558055868847)
  ·
    refine ⟨17446556914802337083803271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11631037943201558055868847 17446556914802337083803271)
    ·
      refine ⟨26169835372203505625704907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17446556914802337083803271 26169835372203505625704907)
      ·
        refine ⟨39254753058305258438557361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26169835372203505625704907 39254753058305258438557361)
        ·
          refine ⟨29441064793728943828918021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39254753058305258438557361 29441064793728943828918021)
          ·
            refine ⟨5520199648824176967922129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29441064793728943828918021 5520199648824176967922129)
            ·
              refine ⟨4140149736618132725941597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5520199648824176967922129 4140149736618132725941597)
              ·
                refine ⟨1552556151231799772228099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4140149736618132725941597 1552556151231799772228099)
                ·
                  refine ⟨2328834226847699658342149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552556151231799772228099 2328834226847699658342149)
                  ·
                    refine ⟨436656417533943685939153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2328834226847699658342149 436656417533943685939153)
                    ·
                      rfl

theorem cell22_1275578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_1275578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275578 prefixEnd_1275578 := by exact prefixLift 1275578
  have htrace : WordTrace (prefixWord ++ tailWord_1275578) baseStart_1275578 baseEnd_1275578 := by
    simpa [prefixWord, tailWord_1275578, baseEnd_1275578] using wordTrace_append hprefix tailTrace_1275578
  have hstable : (prefixWord ++ tailWord_1275578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275578).length < 2 ^ (prefixWord ++ tailWord_1275578).sum := by decide
  have hdescent : baseEnd_1275578 < baseStart_1275578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275586 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1275586 : Nat := 118140960795 + 1275586 * 2 ^ 59
def prefixEnd_1275586 : Nat := 4983230072969 + 3 ^ 40 * 1275586 * 2
def baseEnd_1275586 : Nat := 436659156097434331739129

theorem tailTrace_1275586 : CollatzResearch.WordTrace tailWord_1275586 prefixEnd_1275586 436659156097434331739129 := by
  unfold tailWord_1275586
  simp only [CollatzResearch.WordTrace]
  refine ⟨11631110889194312397441653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31016295704518166393177741 11631110889194312397441653)
  ·
    refine ⟨1090416645861966787260155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11631110889194312397441653 1090416645861966787260155)
    ·
      refine ⟨1635624968792950180890233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090416645861966787260155 1635624968792950180890233)
      ·
        refine ⟨1226718726594712635667675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1635624968792950180890233 1226718726594712635667675)
        ·
          refine ⟨1840078089892068953501513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226718726594712635667675 1840078089892068953501513)
          ·
            refine ⟨1380058567419051715126135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1840078089892068953501513 1380058567419051715126135)
            ·
              refine ⟨2070087851128577572689203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380058567419051715126135 2070087851128577572689203)
              ·
                refine ⟨3105131776692866359033805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070087851128577572689203 3105131776692866359033805)
                ·
                  refine ⟨1164424416259824884637677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3105131776692866359033805 1164424416259824884637677)
                  ·
                    refine ⟨436659156097434331739129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164424416259824884637677 436659156097434331739129)
                    ·
                      rfl

theorem cell22_1275586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1275586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275586 prefixEnd_1275586 := by exact prefixLift 1275586
  have htrace : WordTrace (prefixWord ++ tailWord_1275586) baseStart_1275586 baseEnd_1275586 := by
    simpa [prefixWord, tailWord_1275586, baseEnd_1275586] using wordTrace_append hprefix tailTrace_1275586
  have hstable : (prefixWord ++ tailWord_1275586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275586).length < 2 ^ (prefixWord ++ tailWord_1275586).sum := by decide
  have hdescent : baseEnd_1275586 < baseStart_1275586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275621 : List Nat := [1, 3, 1, 4, 1, 1, 1, 10]
def baseStart_1275621 : Nat := 118140960795 + 1275621 * 2 ^ 59
def prefixEnd_1275621 : Nat := 4983230072969 + 3 ^ 40 * 1275621 * 2
def baseEnd_1275621 : Nat := 48519015256967323012669

theorem tailTrace_1275621 : CollatzResearch.WordTrace tailWord_1275621 prefixEnd_1275621 48519015256967323012669 := by
  unfold tailWord_1275621
  simp only [CollatzResearch.WordTrace]
  refine ⟨46525720111650450567290717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31017146741100300378193811 46525720111650450567290717)
  ·
    refine ⟨17447145041868918962734019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46525720111650450567290717 17447145041868918962734019)
    ·
      refine ⟨26170717562803378444101029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17447145041868918962734019 26170717562803378444101029)
      ·
        refine ⟨4907009543025633458268943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26170717562803378444101029 4907009543025633458268943)
        ·
          refine ⟨7360514314538450187403415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907009543025633458268943 7360514314538450187403415)
          ·
            refine ⟨11040771471807675281105123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7360514314538450187403415 11040771471807675281105123)
            ·
              refine ⟨16561157207711512921657685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11040771471807675281105123 16561157207711512921657685)
              ·
                refine ⟨48519015256967323012669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16561157207711512921657685 48519015256967323012669)
                ·
                  rfl

theorem cell22_1275621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 10].length) (baseStart_1275621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275621 prefixEnd_1275621 := by exact prefixLift 1275621
  have htrace : WordTrace (prefixWord ++ tailWord_1275621) baseStart_1275621 baseEnd_1275621 := by
    simpa [prefixWord, tailWord_1275621, baseEnd_1275621] using wordTrace_append hprefix tailTrace_1275621
  have hstable : (prefixWord ++ tailWord_1275621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275621).length < 2 ^ (prefixWord ++ tailWord_1275621).sum := by decide
  have hdescent : baseEnd_1275621 < baseStart_1275621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275651 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 2, 6]
def baseStart_1275651 : Nat := 118140960795 + 1275651 * 2 ^ 59
def prefixEnd_1275651 : Nat := 4983230072969 + 3 ^ 40 * 1275651 * 2
def baseEnd_1275651 : Nat := 436681406925795828863929

theorem tailTrace_1275651 : CollatzResearch.WordTrace tailWord_1275651 prefixEnd_1275651 436681406925795828863929 := by
  unfold tailWord_1275651
  simp only [CollatzResearch.WordTrace]
  refine ⟨46526814301541765690882807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31017876201027843793921871 46526814301541765690882807)
  ·
    refine ⟨69790221452312648536324211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46526814301541765690882807 69790221452312648536324211)
    ·
      refine ⟨104685332178468972804486317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69790221452312648536324211 104685332178468972804486317)
      ·
        refine ⟨39256999566925864801682369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104685332178468972804486317 39256999566925864801682369)
        ·
          refine ⟨29442749675194398601261777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39256999566925864801682369 29442749675194398601261777)
          ·
            refine ⟨22082062256395798950946333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29442749675194398601261777 22082062256395798950946333)
            ·
              refine ⟨8280773346148424606604875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22082062256395798950946333 8280773346148424606604875)
              ·
                refine ⟨12421160019222636909907313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8280773346148424606604875 12421160019222636909907313)
                ·
                  refine ⟨9315870014416977682430485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12421160019222636909907313 9315870014416977682430485)
                  ·
                    refine ⟨436681406925795828863929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9315870014416977682430485 436681406925795828863929)
                    ·
                      rfl

theorem cell22_1275651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 6].length) (baseStart_1275651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275651 prefixEnd_1275651 := by exact prefixLift 1275651
  have htrace : WordTrace (prefixWord ++ tailWord_1275651) baseStart_1275651 baseEnd_1275651 := by
    simpa [prefixWord, tailWord_1275651, baseEnd_1275651] using wordTrace_append hprefix tailTrace_1275651
  have hstable : (prefixWord ++ tailWord_1275651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275651).length < 2 ^ (prefixWord ++ tailWord_1275651).sum := by decide
  have hdescent : baseEnd_1275651 < baseStart_1275651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275655 : List Nat := [1, 1, 4, 4, 2, 2, 1, 7]
def baseStart_1275655 : Nat := 118140960795 + 1275655 * 2 ^ 59
def prefixEnd_1275655 : Nat := 4983230072969 + 3 ^ 40 * 1275655 * 2
def baseEnd_1275655 : Nat := 48520308467504572418213

theorem tailTrace_1275655 : CollatzResearch.WordTrace tailWord_1275655 prefixEnd_1275655 48520308467504572418213 := by
  unfold tailWord_1275655
  simp only [CollatzResearch.WordTrace]
  refine ⟨46526960193527274374028419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31017973462351516249352279 46526960193527274374028419)
  ·
    refine ⟨69790440290290911561042629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46526960193527274374028419 69790440290290911561042629)
    ·
      refine ⟨13085707554429545917695493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69790440290290911561042629 13085707554429545917695493)
      ·
        refine ⟨2453570166455539859567905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13085707554429545917695493 2453570166455539859567905)
        ·
          refine ⟨1840177624841654894675929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2453570166455539859567905 1840177624841654894675929)
          ·
            refine ⟨1380133218631241171006947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1840177624841654894675929 1380133218631241171006947)
            ·
              refine ⟨2070199827946861756510421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380133218631241171006947 2070199827946861756510421)
              ·
                refine ⟨48520308467504572418213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2070199827946861756510421 48520308467504572418213)
                ·
                  rfl

theorem cell22_1275655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 7].length) (baseStart_1275655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275655 prefixEnd_1275655 := by exact prefixLift 1275655
  have htrace : WordTrace (prefixWord ++ tailWord_1275655) baseStart_1275655 baseEnd_1275655 := by
    simpa [prefixWord, tailWord_1275655, baseEnd_1275655] using wordTrace_append hprefix tailTrace_1275655
  have hstable : (prefixWord ++ tailWord_1275655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275655).length < 2 ^ (prefixWord ++ tailWord_1275655).sum := by decide
  have hdescent : baseEnd_1275655 < baseStart_1275655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275698 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1275698 : Nat := 118140960795 + 1275698 * 2 ^ 59
def prefixEnd_1275698 : Nat := 4983230072969 + 3 ^ 40 * 1275698 * 2
def baseEnd_1275698 : Nat := 436697495986303372938785

theorem tailTrace_1275698 : CollatzResearch.WordTrace tailWord_1275698 prefixEnd_1275698 436697495986303372938785 := by
  unfold tailWord_1275698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11632132133092873179460937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31019019021580995145229165 11632132133092873179460937)
  ·
    refine ⟨8724099099819654884595703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11632132133092873179460937 8724099099819654884595703)
    ·
      refine ⟨13086148649729482326893555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724099099819654884595703 13086148649729482326893555)
      ·
        refine ⟨19629222974594223490340333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13086148649729482326893555 19629222974594223490340333)
        ·
          refine ⟨7360958615472833808877625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19629222974594223490340333 7360958615472833808877625)
          ·
            refine ⟨5520718961604625356658219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7360958615472833808877625 5520718961604625356658219)
            ·
              refine ⟨8281078442406938034987329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520718961604625356658219 8281078442406938034987329)
              ·
                refine ⟨6210808831805203526240497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8281078442406938034987329 6210808831805203526240497)
                ·
                  refine ⟨4658106623853902644680373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6210808831805203526240497 4658106623853902644680373)
                  ·
                    refine ⟨436697495986303372938785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4658106623853902644680373 436697495986303372938785)
                    ·
                      rfl

theorem cell22_1275698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1275698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275698 prefixEnd_1275698 := by exact prefixLift 1275698
  have htrace : WordTrace (prefixWord ++ tailWord_1275698) baseStart_1275698 baseEnd_1275698 := by
    simpa [prefixWord, tailWord_1275698, baseEnd_1275698] using wordTrace_append hprefix tailTrace_1275698
  have hstable : (prefixWord ++ tailWord_1275698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275698).length < 2 ^ (prefixWord ++ tailWord_1275698).sum := by decide
  have hdescent : baseEnd_1275698 < baseStart_1275698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275700 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1275700 : Nat := 118140960795 + 1275700 * 2 ^ 59
def prefixEnd_1275700 : Nat := 4983230072969 + 3 ^ 40 * 1275700 * 2
def baseEnd_1275700 : Nat := 145566060209058678129593

theorem tailTrace_1275700 : CollatzResearch.WordTrace tailWord_1275700 prefixEnd_1275700 145566060209058678129593 := by
  unfold tailWord_1275700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23264300739182123529708277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31019067652242831372944369 23264300739182123529708277)
  ·
    refine ⟨2181028194298324080910151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23264300739182123529708277 2181028194298324080910151)
    ·
      refine ⟨3271542291447486121365227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181028194298324080910151 3271542291447486121365227)
      ·
        refine ⟨4907313437171229182047841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3271542291447486121365227 4907313437171229182047841)
        ·
          refine ⟨3680485077878421886535881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4907313437171229182047841 3680485077878421886535881)
          ·
            refine ⟨2760363808408816414901911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3680485077878421886535881 2760363808408816414901911)
            ·
              refine ⟨4140545712613224622352867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760363808408816414901911 4140545712613224622352867)
              ·
                refine ⟨6210818568919836933529301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140545712613224622352867 6210818568919836933529301)
                ·
                  refine ⟨145566060209058678129593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6210818568919836933529301 145566060209058678129593)
                  ·
                    rfl

theorem cell22_1275700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1275700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275700 prefixEnd_1275700 := by exact prefixLift 1275700
  have htrace : WordTrace (prefixWord ++ tailWord_1275700) baseStart_1275700 baseEnd_1275700 := by
    simpa [prefixWord, tailWord_1275700, baseEnd_1275700] using wordTrace_append hprefix tailTrace_1275700
  have hstable : (prefixWord ++ tailWord_1275700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275700).length < 2 ^ (prefixWord ++ tailWord_1275700).sum := by decide
  have hdescent : baseEnd_1275700 < baseStart_1275700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275730 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1275730 : Nat := 118140960795 + 1275730 * 2 ^ 59
def prefixEnd_1275730 : Nat := 4983230072969 + 3 ^ 40 * 1275730 * 2
def baseEnd_1275730 : Nat := 436708450240265956138687

theorem tailTrace_1275730 : CollatzResearch.WordTrace tailWord_1275730 prefixEnd_1275730 436708450240265956138687 := by
  unfold tailWord_1275730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11632423917063890545752161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31019797112170374788672429 11632423917063890545752161)
  ·
    refine ⟨8724317937797917909314121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11632423917063890545752161 8724317937797917909314121)
    ·
      refine ⟨6543238453348438431985591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8724317937797917909314121 6543238453348438431985591)
      ·
        refine ⟨9814857680022657647978387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6543238453348438431985591 9814857680022657647978387)
        ·
          refine ⟨14722286520033986471967581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9814857680022657647978387 14722286520033986471967581)
          ·
            refine ⟨5520857445012744926987843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14722286520033986471967581 5520857445012744926987843)
            ·
              refine ⟨8281286167519117390481765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520857445012744926987843 8281286167519117390481765)
              ·
                refine ⟨1552741156409834510715331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8281286167519117390481765 1552741156409834510715331)
                ·
                  refine ⟨2329111734614751766072997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552741156409834510715331 2329111734614751766072997)
                  ·
                    refine ⟨436708450240265956138687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2329111734614751766072997 436708450240265956138687)
                    ·
                      rfl

theorem cell22_1275730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1275730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275730 prefixEnd_1275730 := by exact prefixLift 1275730
  have htrace : WordTrace (prefixWord ++ tailWord_1275730) baseStart_1275730 baseEnd_1275730 := by
    simpa [prefixWord, tailWord_1275730, baseEnd_1275730] using wordTrace_append hprefix tailTrace_1275730
  have hstable : (prefixWord ++ tailWord_1275730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275730).length < 2 ^ (prefixWord ++ tailWord_1275730).sum := by decide
  have hdescent : baseEnd_1275730 < baseStart_1275730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275760 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 2, 3]
def baseStart_1275760 : Nat := 118140960795 + 1275760 * 2 ^ 59
def prefixEnd_1275760 : Nat := 4983230072969 + 3 ^ 40 * 1275760 * 2
def baseEnd_1275760 : Nat := 436718719853355877888595

theorem tailTrace_1275760 : CollatzResearch.WordTrace tailWord_1275760 prefixEnd_1275760 436718719853355877888595 := by
  unfold tailWord_1275760
  simp only [CollatzResearch.WordTrace]
  refine ⟨23265394929073438653300367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31020526572097918204400489 23265394929073438653300367)
  ·
    refine ⟨34898092393610157979950551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23265394929073438653300367 34898092393610157979950551)
    ·
      refine ⟨52347138590415236969925827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34898092393610157979950551 52347138590415236969925827)
      ·
        refine ⟨78520707885622855454888741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52347138590415236969925827 78520707885622855454888741)
        ·
          refine ⟨14722632728554285397791639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78520707885622855454888741 14722632728554285397791639)
          ·
            refine ⟨22083949092831428096687459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14722632728554285397791639 22083949092831428096687459)
            ·
              refine ⟨33125923639247142145031189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22083949092831428096687459 33125923639247142145031189)
              ·
                refine ⟨1552777670589709788048337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33125923639247142145031189 1552777670589709788048337)
                ·
                  refine ⟨1164583252942282341036253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1552777670589709788048337 1164583252942282341036253)
                  ·
                    refine ⟨436718719853355877888595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164583252942282341036253 436718719853355877888595)
                    ·
                      rfl

theorem cell22_1275760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_1275760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275760 prefixEnd_1275760 := by exact prefixLift 1275760
  have htrace : WordTrace (prefixWord ++ tailWord_1275760) baseStart_1275760 baseEnd_1275760 := by
    simpa [prefixWord, tailWord_1275760, baseEnd_1275760] using wordTrace_append hprefix tailTrace_1275760
  have hstable : (prefixWord ++ tailWord_1275760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275760).length < 2 ^ (prefixWord ++ tailWord_1275760).sum := by decide
  have hdescent : baseEnd_1275760 < baseStart_1275760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275798 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1275798 : Nat := 118140960795 + 1275798 * 2 ^ 59
def prefixEnd_1275798 : Nat := 4983230072969 + 3 ^ 40 * 1275798 * 2
def baseEnd_1275798 : Nat := 436731728029936445438479

theorem tailTrace_1275798 : CollatzResearch.WordTrace tailWord_1275798 prefixEnd_1275798 436731728029936445438479 := by
  unfold tailWord_1275798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908260989500575612280253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31021450554672806530989365 2908260989500575612280253)
  ·
    refine ⟨1090597871062715854605095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2908260989500575612280253 1090597871062715854605095)
    ·
      refine ⟨1635896806594073781907643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090597871062715854605095 1635896806594073781907643)
      ·
        refine ⟨2453845209891110672861465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635896806594073781907643 2453845209891110672861465)
        ·
          refine ⟨1840383907418333004646099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2453845209891110672861465 1840383907418333004646099)
          ·
            refine ⟨2760575861127499506969149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840383907418333004646099 2760575861127499506969149)
            ·
              refine ⟨1035215947922812315113431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2760575861127499506969149 1035215947922812315113431)
              ·
                refine ⟨1552823921884218472670147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035215947922812315113431 1552823921884218472670147)
                ·
                  refine ⟨2329235882826327709005221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552823921884218472670147 2329235882826327709005221)
                  ·
                    refine ⟨436731728029936445438479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2329235882826327709005221 436731728029936445438479)
                    ·
                      rfl

theorem cell22_1275798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1275798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275798 prefixEnd_1275798 := by exact prefixLift 1275798
  have htrace : WordTrace (prefixWord ++ tailWord_1275798) baseStart_1275798 baseEnd_1275798 := by
    simpa [prefixWord, tailWord_1275798, baseEnd_1275798] using wordTrace_append hprefix tailTrace_1275798
  have hstable : (prefixWord ++ tailWord_1275798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275798).length < 2 ^ (prefixWord ++ tailWord_1275798).sum := by decide
  have hdescent : baseEnd_1275798 < baseStart_1275798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275863 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 8]
def baseStart_1275863 : Nat := 118140960795 + 1275863 * 2 ^ 59
def prefixEnd_1275863 : Nat := 4983230072969 + 3 ^ 40 * 1275863 * 2
def baseEnd_1275863 : Nat := 145584659619432647521093

theorem tailTrace_1275863 : CollatzResearch.WordTrace tailWord_1275863 prefixEnd_1275863 145584659619432647521093 := by
  unfold tailWord_1275863
  simp only [CollatzResearch.WordTrace]
  refine ⟨46534546576773725897600243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31023031051182483931733495 46534546576773725897600243)
  ·
    refine ⟨69801819865160588846400365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46534546576773725897600243 69801819865160588846400365)
    ·
      refine ⟨26175682449435220817400137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69801819865160588846400365 26175682449435220817400137)
      ·
        refine ⟨19631761837076415613050103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26175682449435220817400137 19631761837076415613050103)
        ·
          refine ⟨29447642755614623419575155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19631761837076415613050103 29447642755614623419575155)
          ·
            refine ⟨44171464133421935129362733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29447642755614623419575155 44171464133421935129362733)
            ·
              refine ⟨16564299050033225673511025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44171464133421935129362733 16564299050033225673511025)
              ·
                refine ⟨12423224287524919255133269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16564299050033225673511025 12423224287524919255133269)
                ·
                  refine ⟨145584659619432647521093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12423224287524919255133269 145584659619432647521093)
                  ·
                    rfl

theorem cell22_1275863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 8].length) (baseStart_1275863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275863 prefixEnd_1275863 := by exact prefixLift 1275863
  have htrace : WordTrace (prefixWord ++ tailWord_1275863) baseStart_1275863 baseEnd_1275863 := by
    simpa [prefixWord, tailWord_1275863, baseEnd_1275863] using wordTrace_append hprefix tailTrace_1275863
  have hstable : (prefixWord ++ tailWord_1275863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275863).length < 2 ^ (prefixWord ++ tailWord_1275863).sum := by decide
  have hdescent : baseEnd_1275863 < baseStart_1275863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275869 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 5]
def baseStart_1275869 : Nat := 118140960795 + 1275869 * 2 ^ 59
def prefixEnd_1275869 : Nat := 4983230072969 + 3 ^ 40 * 1275869 * 2
def baseEnd_1275869 : Nat := 145585344260305308971087

theorem tailTrace_1275869 : CollatzResearch.WordTrace tailWord_1275869 prefixEnd_1275869 145585344260305308971087 := by
  unfold tailWord_1275869
  simp only [CollatzResearch.WordTrace]
  refine ⟨46534765414751988922318661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31023176943167992614879107 46534765414751988922318661)
  ·
    refine ⟨8725268515265997922934749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46534765414751988922318661 8725268515265997922934749)
    ·
      refine ⟨3271975693224749221100531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8725268515265997922934749 3271975693224749221100531)
      ·
        refine ⟨4907963539837123831650797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3271975693224749221100531 4907963539837123831650797)
        ·
          refine ⟨1840486327438921436869049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4907963539837123831650797 1840486327438921436869049)
          ·
            refine ⟨1380364745579191077651787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1840486327438921436869049 1380364745579191077651787)
            ·
              refine ⟨2070547118368786616477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380364745579191077651787 2070547118368786616477681)
              ·
                refine ⟨1552910338776589962358261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2070547118368786616477681 1552910338776589962358261)
                ·
                  refine ⟨145585344260305308971087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1552910338776589962358261 145585344260305308971087)
                  ·
                    rfl

theorem cell22_1275869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_1275869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275869 prefixEnd_1275869 := by exact prefixLift 1275869
  have htrace : WordTrace (prefixWord ++ tailWord_1275869) baseStart_1275869 baseEnd_1275869 := by
    simpa [prefixWord, tailWord_1275869, baseEnd_1275869] using wordTrace_append hprefix tailTrace_1275869
  have hstable : (prefixWord ++ tailWord_1275869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275869).length < 2 ^ (prefixWord ++ tailWord_1275869).sum := by decide
  have hdescent : baseEnd_1275869 < baseStart_1275869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275946 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1275946 : Nat := 118140960795 + 1275946 * 2 ^ 59
def prefixEnd_1275946 : Nat := 4983230072969 + 3 ^ 40 * 1275946 * 2
def baseEnd_1275946 : Nat := 436782391454513392738025

theorem tailTrace_1275946 : CollatzResearch.WordTrace tailWord_1275946 prefixEnd_1275946 436782391454513392738025 := by
  unfold tailWord_1275946
  simp only [CollatzResearch.WordTrace]
  refine ⟨11634393458868257768217923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31025049223648687381914461 11634393458868257768217923)
  ·
    refine ⟨17451590188302386652326885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11634393458868257768217923 17451590188302386652326885)
    ·
      refine ⟨3272173160306697497311291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17451590188302386652326885 3272173160306697497311291)
      ·
        refine ⟨4908259740460046245966937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272173160306697497311291 4908259740460046245966937)
        ·
          refine ⟨3681194805345034684475203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4908259740460046245966937 3681194805345034684475203)
          ·
            refine ⟨5521792208017552026712805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681194805345034684475203 5521792208017552026712805)
            ·
              refine ⟨1035336039003291005008651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5521792208017552026712805 1035336039003291005008651)
              ·
                refine ⟨1553004058504936507512977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035336039003291005008651 1553004058504936507512977)
                ·
                  refine ⟨1164753043878702380634733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1553004058504936507512977 1164753043878702380634733)
                  ·
                    refine ⟨436782391454513392738025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164753043878702380634733 436782391454513392738025)
                    ·
                      rfl

theorem cell22_1275946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1275946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275946 prefixEnd_1275946 := by exact prefixLift 1275946
  have htrace : WordTrace (prefixWord ++ tailWord_1275946) baseStart_1275946 baseEnd_1275946 := by
    simpa [prefixWord, tailWord_1275946, baseEnd_1275946] using wordTrace_append hprefix tailTrace_1275946
  have hstable : (prefixWord ++ tailWord_1275946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275946).length < 2 ^ (prefixWord ++ tailWord_1275946).sum := by decide
  have hdescent : baseEnd_1275946 < baseStart_1275946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275957 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 3, 3]
def baseStart_1275957 : Nat := 118140960795 + 1275957 * 2 ^ 59
def prefixEnd_1275957 : Nat := 4983230072969 + 3 ^ 40 * 1275957 * 2
def baseEnd_1275957 : Nat := 436786156979313030712991

theorem tailTrace_1275957 : CollatzResearch.WordTrace tailWord_1275957 prefixEnd_1275957 436786156979313030712991 := by
  unfold tailWord_1275957
  simp only [CollatzResearch.WordTrace]
  refine ⟨46537975038433179951522125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31025316692288786634348083 46537975038433179951522125)
  ·
    refine ⟨17451740639412442481820797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46537975038433179951522125 17451740639412442481820797)
    ·
      refine ⟨6544402739779665930682799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17451740639412442481820797 6544402739779665930682799)
      ·
        refine ⟨9816604109669498896024199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6544402739779665930682799 9816604109669498896024199)
        ·
          refine ⟨14724906164504248344036299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9816604109669498896024199 14724906164504248344036299)
          ·
            refine ⟨22087359246756372516054449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14724906164504248344036299 22087359246756372516054449)
            ·
              refine ⟨16565519435067279387040837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22087359246756372516054449 16565519435067279387040837)
              ·
                refine ⟨3106034894075114885070157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16565519435067279387040837 3106034894075114885070157)
                ·
                  refine ⟨1164763085278168081901309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3106034894075114885070157 1164763085278168081901309)
                  ·
                    refine ⟨436786156979313030712991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164763085278168081901309 436786156979313030712991)
                    ·
                      rfl

theorem cell22_1275957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_1275957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275957 prefixEnd_1275957 := by exact prefixLift 1275957
  have htrace : WordTrace (prefixWord ++ tailWord_1275957) baseStart_1275957 baseEnd_1275957 := by
    simpa [prefixWord, tailWord_1275957, baseEnd_1275957] using wordTrace_append hprefix tailTrace_1275957
  have hstable : (prefixWord ++ tailWord_1275957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275957).length < 2 ^ (prefixWord ++ tailWord_1275957).sum := by decide
  have hdescent : baseEnd_1275957 < baseStart_1275957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275985 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1275985 : Nat := 118140960795 + 1275985 * 2 ^ 59
def prefixEnd_1275985 : Nat := 4983230072969 + 3 ^ 40 * 1275985 * 2
def baseEnd_1275985 : Nat := 436795741951530291012905

theorem tailTrace_1275985 : CollatzResearch.WordTrace tailWord_1275985 prefixEnd_1275985 436795741951530291012905 := by
  unfold tailWord_1275985
  simp only [CollatzResearch.WordTrace]
  refine ⟨46538996282331740733541409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31025997521554493822360939 46538996282331740733541409)
  ·
    refine ⟨34904247211748805550156057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46538996282331740733541409 34904247211748805550156057)
    ·
      refine ⟨26178185408811604162617043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34904247211748805550156057 26178185408811604162617043)
      ·
        refine ⟨39267278113217406243925565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26178185408811604162617043 39267278113217406243925565)
        ·
          refine ⟨14725229292456527341472087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39267278113217406243925565 14725229292456527341472087)
          ·
            refine ⟨22087843938684791012208131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14725229292456527341472087 22087843938684791012208131)
            ·
              refine ⟨33131765908027186518312197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22087843938684791012208131 33131765908027186518312197)
              ·
                refine ⟨6212206107755097472183537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33131765908027186518312197 6212206107755097472183537)
                ·
                  refine ⟨4659154580816323104137653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212206107755097472183537 4659154580816323104137653)
                  ·
                    refine ⟨436795741951530291012905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4659154580816323104137653 436795741951530291012905)
                    ·
                      rfl

theorem cell22_1275985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1275985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275985 prefixEnd_1275985 := by exact prefixLift 1275985
  have htrace : WordTrace (prefixWord ++ tailWord_1275985) baseStart_1275985 baseEnd_1275985 := by
    simpa [prefixWord, tailWord_1275985, baseEnd_1275985] using wordTrace_append hprefix tailTrace_1275985
  have hstable : (prefixWord ++ tailWord_1275985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275985).length < 2 ^ (prefixWord ++ tailWord_1275985).sum := by decide
  have hdescent : baseEnd_1275985 < baseStart_1275985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1275991 : List Nat := [1, 1, 3, 2, 2, 1, 6, 2, 1, 3]
def baseStart_1275991 : Nat := 118140960795 + 1275991 * 2 ^ 59
def prefixEnd_1275991 : Nat := 4983230072969 + 3 ^ 40 * 1275991 * 2
def baseEnd_1275991 : Nat := 436797795874148275362887

theorem tailTrace_1275991 : CollatzResearch.WordTrace tailWord_1275991 prefixEnd_1275991 436797795874148275362887 := by
  unfold tailWord_1275991
  simp only [CollatzResearch.WordTrace]
  refine ⟨46539215120310003758259827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31026143413540002505506551 46539215120310003758259827)
  ·
    refine ⟨69808822680465005637389741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46539215120310003758259827 69808822680465005637389741)
    ·
      refine ⟨26178308505174377114021153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69808822680465005637389741 26178308505174377114021153)
      ·
        refine ⟨19633731378880782835515865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26178308505174377114021153 19633731378880782835515865)
        ·
          refine ⟨14725298534160587126636899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19633731378880782835515865 14725298534160587126636899)
          ·
            refine ⟨22087947801240880689955349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14725298534160587126636899 22087947801240880689955349)
            ·
              refine ⟨1035372553183166282341657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22087947801240880689955349 1035372553183166282341657)
              ·
                refine ⟨776529414887374711756243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035372553183166282341657 776529414887374711756243)
                ·
                  refine ⟨1164794122331062067634365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776529414887374711756243 1164794122331062067634365)
                  ·
                    refine ⟨436797795874148275362887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164794122331062067634365 436797795874148275362887)
                    ·
                      rfl

theorem cell22_1275991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_1275991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1275991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1275991 prefixEnd_1275991 := by exact prefixLift 1275991
  have htrace : WordTrace (prefixWord ++ tailWord_1275991) baseStart_1275991 baseEnd_1275991 := by
    simpa [prefixWord, tailWord_1275991, baseEnd_1275991] using wordTrace_append hprefix tailTrace_1275991
  have hstable : (prefixWord ++ tailWord_1275991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1275991).length < 2 ^ (prefixWord ++ tailWord_1275991).sum := by decide
  have hdescent : baseEnd_1275991 < baseStart_1275991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1275991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276015 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 8]
def baseStart_1276015 : Nat := 118140960795 + 1276015 * 2 ^ 59
def prefixEnd_1276015 : Nat := 4983230072969 + 3 ^ 40 * 1276015 * 2
def baseEnd_1276015 : Nat := 145602003854873404254271

theorem tailTrace_1276015 : CollatzResearch.WordTrace tailWord_1276015 prefixEnd_1276015 145602003854873404254271 := by
  unfold tailWord_1276015
  simp only [CollatzResearch.WordTrace]
  refine ⟨46540090472223055857133499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31026726981482037238088999 46540090472223055857133499)
  ·
    refine ⟨69810135708334583785700249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46540090472223055857133499 69810135708334583785700249)
    ·
      refine ⟨52357601781250937839275187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69810135708334583785700249 52357601781250937839275187)
      ·
        refine ⟨78536402671876406758912781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52357601781250937839275187 78536402671876406758912781)
        ·
          refine ⟨29451151001953652534592293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78536402671876406758912781 29451151001953652534592293)
          ·
            refine ⟨5522090812866309850236055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29451151001953652534592293 5522090812866309850236055)
            ·
              refine ⟨8283136219299464775354083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522090812866309850236055 8283136219299464775354083)
              ·
                refine ⟨12424704328949197163031125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8283136219299464775354083 12424704328949197163031125)
                ·
                  refine ⟨145602003854873404254271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12424704328949197163031125 145602003854873404254271)
                  ·
                    rfl

theorem cell22_1276015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 8].length) (baseStart_1276015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276015 prefixEnd_1276015 := by exact prefixLift 1276015
  have htrace : WordTrace (prefixWord ++ tailWord_1276015) baseStart_1276015 baseEnd_1276015 := by
    simpa [prefixWord, tailWord_1276015, baseEnd_1276015] using wordTrace_append hprefix tailTrace_1276015
  have hstable : (prefixWord ++ tailWord_1276015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276015).length < 2 ^ (prefixWord ++ tailWord_1276015).sum := by decide
  have hdescent : baseEnd_1276015 < baseStart_1276015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276017 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 1, 4]
def baseStart_1276017 : Nat := 118140960795 + 1276017 * 2 ^ 59
def prefixEnd_1276017 : Nat := 4983230072969 + 3 ^ 40 * 1276017 * 2
def baseEnd_1276017 : Nat := 436806696205492874212807

theorem tailTrace_1276017 : CollatzResearch.WordTrace tailWord_1276017 prefixEnd_1276017 436806696205492874212807 := by
  unfold tailWord_1276017
  simp only [CollatzResearch.WordTrace]
  refine ⟨46540163418215810198706305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31026775612143873465804203 46540163418215810198706305)
  ·
    refine ⟨34905122563661857649029729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46540163418215810198706305 34905122563661857649029729)
    ·
      refine ⟨26178841922746393236772297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34905122563661857649029729 26178841922746393236772297)
      ·
        refine ⟨19634131442059794927579223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26178841922746393236772297 19634131442059794927579223)
        ·
          refine ⟨29451197163089692391368835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19634131442059794927579223 29451197163089692391368835)
          ·
            refine ⟨44176795744634538587053253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29451197163089692391368835 44176795744634538587053253)
            ·
              refine ⟨8283149202118975985072485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44176795744634538587053253 8283149202118975985072485)
              ·
                refine ⟨1553090475397307997201091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8283149202118975985072485 1553090475397307997201091)
                ·
                  refine ⟨2329635713095961995801637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553090475397307997201091 2329635713095961995801637)
                  ·
                    refine ⟨436806696205492874212807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2329635713095961995801637 436806696205492874212807)
                    ·
                      rfl

theorem cell22_1276017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_1276017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276017 prefixEnd_1276017 := by exact prefixLift 1276017
  have htrace : WordTrace (prefixWord ++ tailWord_1276017) baseStart_1276017 baseEnd_1276017 := by
    simpa [prefixWord, tailWord_1276017, baseEnd_1276017] using wordTrace_append hprefix tailTrace_1276017
  have hstable : (prefixWord ++ tailWord_1276017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276017).length < 2 ^ (prefixWord ++ tailWord_1276017).sum := by decide
  have hdescent : baseEnd_1276017 < baseStart_1276017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276064 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 1, 5]
def baseStart_1276064 : Nat := 118140960795 + 1276064 * 2 ^ 59
def prefixEnd_1276064 : Nat := 4983230072969 + 3 ^ 40 * 1276064 * 2
def baseEnd_1276064 : Nat := 436822785266000418287663

theorem tailTrace_1276064 : CollatzResearch.WordTrace tailWord_1276064 prefixEnd_1276064 436822785266000418287663 := by
  unfold tailWord_1276064
  simp only [CollatzResearch.WordTrace]
  refine ⟨23270938824522768612833623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31027918432697024817111497 23270938824522768612833623)
  ·
    refine ⟨34906408236784152919250435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23270938824522768612833623 34906408236784152919250435)
    ·
      refine ⟨52359612355176229378875653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34906408236784152919250435 52359612355176229378875653)
      ·
        refine ⟨9817427316595543008539185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52359612355176229378875653 9817427316595543008539185)
        ·
          refine ⟨7363070487446657256404389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9817427316595543008539185 7363070487446657256404389)
          ·
            refine ⟨1380575716396248235575823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7363070487446657256404389 1380575716396248235575823)
            ·
              refine ⟨2070863574594372353363735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380575716396248235575823 2070863574594372353363735)
              ·
                refine ⟨3106295361891558530045603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070863574594372353363735 3106295361891558530045603)
                ·
                  refine ⟨4659443042837337795068405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106295361891558530045603 4659443042837337795068405)
                  ·
                    refine ⟨436822785266000418287663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4659443042837337795068405 436822785266000418287663)
                    ·
                      rfl

theorem cell22_1276064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 1, 5].length) (baseStart_1276064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276064 prefixEnd_1276064 := by exact prefixLift 1276064
  have htrace : WordTrace (prefixWord ++ tailWord_1276064) baseStart_1276064 baseEnd_1276064 := by
    simpa [prefixWord, tailWord_1276064, baseEnd_1276064] using wordTrace_append hprefix tailTrace_1276064
  have hstable : (prefixWord ++ tailWord_1276064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276064).length < 2 ^ (prefixWord ++ tailWord_1276064).sum := by decide
  have hdescent : baseEnd_1276064 < baseStart_1276064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276094 : List Nat := [4, 2, 1, 1, 4, 2, 8]
def baseStart_1276094 : Nat := 118140960795 + 1276094 * 2 ^ 59
def prefixEnd_1276094 : Nat := 4983230072969 + 3 ^ 40 * 1276094 * 2
def baseEnd_1276094 : Nat := 16179002032558901482873

theorem tailTrace_1276094 : CollatzResearch.WordTrace tailWord_1276094 prefixEnd_1276094 16179002032558901482873 := by
  unfold tailWord_1276094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5817871479867106543657417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31028647892624568232839557 5817871479867106543657417)
  ·
    refine ⟨4363403609900329907743063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5817871479867106543657417 4363403609900329907743063)
    ·
      refine ⟨6545105414850494861614595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4363403609900329907743063 6545105414850494861614595)
      ·
        refine ⟨9817658122275742292421893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6545105414850494861614595 9817658122275742292421893)
        ·
          refine ⟨1840810897926701679829105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9817658122275742292421893 1840810897926701679829105)
          ·
            refine ⟨1380608173445026259871829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1840810897926701679829105 1380608173445026259871829)
            ·
              refine ⟨16179002032558901482873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1380608173445026259871829 16179002032558901482873)
              ·
                rfl

theorem cell22_1276094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 8].length) (baseStart_1276094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276094 prefixEnd_1276094 := by exact prefixLift 1276094
  have htrace : WordTrace (prefixWord ++ tailWord_1276094) baseStart_1276094 baseEnd_1276094 := by
    simpa [prefixWord, tailWord_1276094, baseEnd_1276094] using wordTrace_append hprefix tailTrace_1276094
  have hstable : (prefixWord ++ tailWord_1276094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276094).length < 2 ^ (prefixWord ++ tailWord_1276094).sum := by decide
  have hdescent : baseEnd_1276094 < baseStart_1276094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276098 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1276098 : Nat := 118140960795 + 1276098 * 2 ^ 59
def prefixEnd_1276098 : Nat := 4983230072969 + 3 ^ 40 * 1276098 * 2
def baseEnd_1276098 : Nat := 436834424160835662937559

theorem tailTrace_1276098 : CollatzResearch.WordTrace tailWord_1276098 prefixEnd_1276098 436834424160835662937559 := by
  unfold tailWord_1276098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635779432730590258101237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31028745153948240688269965 11635779432730590258101237)
  ·
    refine ⟨1090854321818492836696991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11635779432730590258101237 1090854321818492836696991)
    ·
      refine ⟨1636281482727739255045487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090854321818492836696991 1636281482727739255045487)
      ·
        refine ⟨2454422224091608882568231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636281482727739255045487 2454422224091608882568231)
        ·
          refine ⟨3681633336137413323852347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454422224091608882568231 3681633336137413323852347)
          ·
            refine ⟨5522450004206119985778521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681633336137413323852347 5522450004206119985778521)
            ·
              refine ⟨4141837503154589989333891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5522450004206119985778521 4141837503154589989333891)
              ·
                refine ⟨6212756254731884984000837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141837503154589989333891 6212756254731884984000837)
                ·
                  refine ⟨1164891797762228434500157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6212756254731884984000837 1164891797762228434500157)
                  ·
                    refine ⟨436834424160835662937559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164891797762228434500157 436834424160835662937559)
                    ·
                      rfl

theorem cell22_1276098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1276098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276098 prefixEnd_1276098 := by exact prefixLift 1276098
  have htrace : WordTrace (prefixWord ++ tailWord_1276098) baseStart_1276098 baseEnd_1276098 := by
    simpa [prefixWord, tailWord_1276098, baseEnd_1276098] using wordTrace_append hprefix tailTrace_1276098
  have hstable : (prefixWord ++ tailWord_1276098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276098).length < 2 ^ (prefixWord ++ tailWord_1276098).sum := by decide
  have hdescent : baseEnd_1276098 < baseStart_1276098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276130 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1276130 : Nat := 118140960795 + 1276130 * 2 ^ 59
def prefixEnd_1276130 : Nat := 4983230072969 + 3 ^ 40 * 1276130 * 2
def baseEnd_1276130 : Nat := 436845378414798246137461

theorem tailTrace_1276130 : CollatzResearch.WordTrace tailWord_1276130 prefixEnd_1276130 436845378414798246137461 := by
  unfold tailWord_1276130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11636071216701607624392461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31029523244537620331713229 11636071216701607624392461)
  ·
    refine ⟨4363526706263102859147173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11636071216701607624392461 4363526706263102859147173)
    ·
      refine ⟨818161257424331786090095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4363526706263102859147173 818161257424331786090095)
      ·
        refine ⟨1227241886136497679135143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818161257424331786090095 1227241886136497679135143)
        ·
          refine ⟨1840862829204746518702715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227241886136497679135143 1840862829204746518702715)
          ·
            refine ⟨2761294243807119778054073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840862829204746518702715 2761294243807119778054073)
            ·
              refine ⟨2070970682855339833540555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2761294243807119778054073 2070970682855339833540555)
              ·
                refine ⟨3106456024283009750310833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070970682855339833540555 3106456024283009750310833)
                ·
                  refine ⟨2329842018212257312733125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3106456024283009750310833 2329842018212257312733125)
                  ·
                    refine ⟨436845378414798246137461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2329842018212257312733125 436845378414798246137461)
                    ·
                      rfl

theorem cell22_1276130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1276130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276130 prefixEnd_1276130 := by exact prefixLift 1276130
  have htrace : WordTrace (prefixWord ++ tailWord_1276130) baseStart_1276130 baseEnd_1276130 := by
    simpa [prefixWord, tailWord_1276130, baseEnd_1276130] using wordTrace_append hprefix tailTrace_1276130
  have hstable : (prefixWord ++ tailWord_1276130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276130).length < 2 ^ (prefixWord ++ tailWord_1276130).sum := by decide
  have hdescent : baseEnd_1276130 < baseStart_1276130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276216 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 2, 3]
def baseStart_1276216 : Nat := 118140960795 + 1276216 * 2 ^ 59
def prefixEnd_1276216 : Nat := 4983230072969 + 3 ^ 40 * 1276216 * 2
def baseEnd_1276216 : Nat := 436874817972322688487197

theorem tailTrace_1276216 : CollatzResearch.WordTrace tailWord_1276216 prefixEnd_1276216 436874817972322688487197 := by
  unfold tailWord_1276216
  simp only [CollatzResearch.WordTrace]
  refine ⟨23273710772247433592600251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31031614362996578123467001 23273710772247433592600251)
  ·
    refine ⟨34910566158371150388900377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23273710772247433592600251 34910566158371150388900377)
    ·
      refine ⟨26182924618778362791675283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34910566158371150388900377 26182924618778362791675283)
      ·
        refine ⟨39274386928167544187512925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26182924618778362791675283 39274386928167544187512925)
        ·
          refine ⟨14727895098062829070317347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39274386928167544187512925 14727895098062829070317347)
          ·
            refine ⟨22091842647094243605476021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14727895098062829070317347 22091842647094243605476021)
            ·
              refine ⟨2071110248165085338013377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22091842647094243605476021 2071110248165085338013377)
              ·
                refine ⟨1553332686123814003510033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2071110248165085338013377 1553332686123814003510033)
                ·
                  refine ⟨1164999514592860502632525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1553332686123814003510033 1164999514592860502632525)
                  ·
                    refine ⟨436874817972322688487197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164999514592860502632525 436874817972322688487197)
                    ·
                      rfl

theorem cell22_1276216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_1276216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276216 prefixEnd_1276216 := by exact prefixLift 1276216
  have htrace : WordTrace (prefixWord ++ tailWord_1276216) baseStart_1276216 baseEnd_1276216 := by
    simpa [prefixWord, tailWord_1276216, baseEnd_1276216] using wordTrace_append hprefix tailTrace_1276216
  have hstable : (prefixWord ++ tailWord_1276216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276216).length < 2 ^ (prefixWord ++ tailWord_1276216).sum := by decide
  have hdescent : baseEnd_1276216 < baseStart_1276216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276252 : List Nat := [2, 2, 4, 3, 2, 1, 1, 3, 4]
def baseStart_1276252 : Nat := 118140960795 + 1276252 * 2 ^ 59
def prefixEnd_1276252 : Nat := 4983230072969 + 3 ^ 40 * 1276252 * 2
def baseEnd_1276252 : Nat := 145629047169343531529029

theorem tailTrace_1276252 : CollatzResearch.WordTrace tailWord_1276252 prefixEnd_1276252 145629047169343531529029 := by
  unfold tailWord_1276252
  simp only [CollatzResearch.WordTrace]
  refine ⟨23274367286182222666755505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31032489714909630222340673 23274367286182222666755505)
  ·
    refine ⟨17455775464636667000066629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23274367286182222666755505 17455775464636667000066629)
    ·
      refine ⟨3272957899619375062512493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17455775464636667000066629 3272957899619375062512493)
      ·
        refine ⟨1227359212357265648442185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3272957899619375062512493 1227359212357265648442185)
        ·
          refine ⟨920519409267949236331639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227359212357265648442185 920519409267949236331639)
          ·
            refine ⟨1380779113901923854497459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920519409267949236331639 1380779113901923854497459)
            ·
              refine ⟨2071168670852885781746189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380779113901923854497459 2071168670852885781746189)
              ·
                refine ⟨776688251569832168154821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2071168670852885781746189 776688251569832168154821)
                ·
                  refine ⟨145629047169343531529029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776688251569832168154821 145629047169343531529029)
                  ·
                    rfl

theorem cell22_1276252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_1276252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276252 prefixEnd_1276252 := by exact prefixLift 1276252
  have htrace : WordTrace (prefixWord ++ tailWord_1276252) baseStart_1276252 baseEnd_1276252 := by
    simpa [prefixWord, tailWord_1276252, baseEnd_1276252] using wordTrace_append hprefix tailTrace_1276252
  have hstable : (prefixWord ++ tailWord_1276252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276252).length < 2 ^ (prefixWord ++ tailWord_1276252).sum := by decide
  have hdescent : baseEnd_1276252 < baseStart_1276252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276274 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_1276274 : Nat := 118140960795 + 1276274 * 2 ^ 59
def prefixEnd_1276274 : Nat := 4983230072969 + 3 ^ 40 * 1276274 * 2
def baseEnd_1276274 : Nat := 145631557519209956845673

theorem tailTrace_1276274 : CollatzResearch.WordTrace tailWord_1276274 prefixEnd_1276274 145631557519209956845673 := by
  unfold tailWord_1276274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11637384244571185772702969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31033024652189828727207917 11637384244571185772702969)
  ·
    refine ⟨8728038183428389329527227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11637384244571185772702969 8728038183428389329527227)
    ·
      refine ⟨13092057275142583994290841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8728038183428389329527227 13092057275142583994290841)
      ·
        refine ⟨9819042956356937995718131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13092057275142583994290841 9819042956356937995718131)
        ·
          refine ⟨14728564434535406993577197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9819042956356937995718131 14728564434535406993577197)
          ·
            refine ⟨5523211662950777622591449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14728564434535406993577197 5523211662950777622591449)
            ·
              refine ⟨4142408747213083216943587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5523211662950777622591449 4142408747213083216943587)
              ·
                refine ⟨6213613120819624825415381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142408747213083216943587 6213613120819624825415381)
                ·
                  refine ⟨145631557519209956845673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6213613120819624825415381 145631557519209956845673)
                  ·
                    rfl

theorem cell22_1276274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_1276274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276274 prefixEnd_1276274 := by exact prefixLift 1276274
  have htrace : WordTrace (prefixWord ++ tailWord_1276274) baseStart_1276274 baseEnd_1276274 := by
    simpa [prefixWord, tailWord_1276274, baseEnd_1276274] using wordTrace_append hprefix tailTrace_1276274
  have hstable : (prefixWord ++ tailWord_1276274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276274).length < 2 ^ (prefixWord ++ tailWord_1276274).sum := by decide
  have hdescent : baseEnd_1276274 < baseStart_1276274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276291 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 5]
def baseStart_1276291 : Nat := 118140960795 + 1276291 * 2 ^ 59
def prefixEnd_1276291 : Nat := 4983230072969 + 3 ^ 40 * 1276291 * 2
def baseEnd_1276291 : Nat := 145633497335015830953989

theorem tailTrace_1276291 : CollatzResearch.WordTrace tailWord_1276291 prefixEnd_1276291 145633497335015830953989 := by
  unfold tailWord_1276291
  simp only [CollatzResearch.WordTrace]
  refine ⟨46550157019223154994180727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31033438012815436662787151 46550157019223154994180727)
  ·
    refine ⟨69825235528834732491271091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46550157019223154994180727 69825235528834732491271091)
    ·
      refine ⟨104737853293252098736906637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69825235528834732491271091 104737853293252098736906637)
      ·
        refine ⟨39276694984969537026339989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104737853293252098736906637 39276694984969537026339989)
        ·
          refine ⟨1841095077420447048109687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39276694984969537026339989 1841095077420447048109687)
          ·
            refine ⟨2761642616130670572164531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841095077420447048109687 2761642616130670572164531)
            ·
              refine ⟨4142463924196005858246797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761642616130670572164531 4142463924196005858246797)
              ·
                refine ⟨1553423971573502196842549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4142463924196005858246797 1553423971573502196842549)
                ·
                  refine ⟨145633497335015830953989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1553423971573502196842549 145633497335015830953989)
                  ·
                    rfl

theorem cell22_1276291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 5].length) (baseStart_1276291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276291 prefixEnd_1276291 := by exact prefixLift 1276291
  have htrace : WordTrace (prefixWord ++ tailWord_1276291) baseStart_1276291 baseEnd_1276291 := by
    simpa [prefixWord, tailWord_1276291, baseEnd_1276291] using wordTrace_append hprefix tailTrace_1276291
  have hstable : (prefixWord ++ tailWord_1276291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276291).length < 2 ^ (prefixWord ++ tailWord_1276291).sum := by decide
  have hdescent : baseEnd_1276291 < baseStart_1276291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276340 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1276340 : Nat := 118140960795 + 1276340 * 2 ^ 59
def prefixEnd_1276340 : Nat := 4983230072969 + 3 ^ 40 * 1276340 * 2
def baseEnd_1276340 : Nat := 436917265706427698386817

theorem tailTrace_1276340 : CollatzResearch.WordTrace tailWord_1276340 prefixEnd_1276340 436917265706427698386817 := by
  unfold tailWord_1276340
  simp only [CollatzResearch.WordTrace]
  refine ⟨23275972098022818181357237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31034629464030424241809649 23275972098022818181357237)
  ·
    refine ⟨2182122384189639204502241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23275972098022818181357237 2182122384189639204502241)
    ·
      refine ⟨1636591788142229403376681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2182122384189639204502241 1636591788142229403376681)
      ·
        refine ⟨1227443841106672052532511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1636591788142229403376681 1227443841106672052532511)
        ·
          refine ⟨1841165761660008078798767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227443841106672052532511 1841165761660008078798767)
          ·
            refine ⟨2761748642490012118198151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841165761660008078798767 2761748642490012118198151)
            ·
              refine ⟨4142622963735018177297227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761748642490012118198151 4142622963735018177297227)
              ·
                refine ⟨6213934445602527265945841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142622963735018177297227 6213934445602527265945841)
                ·
                  refine ⟨4660450834201895449459381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6213934445602527265945841 4660450834201895449459381)
                  ·
                    refine ⟨436917265706427698386817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4660450834201895449459381 436917265706427698386817)
                    ·
                      rfl

theorem cell22_1276340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1276340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276340 prefixEnd_1276340 := by exact prefixLift 1276340
  have htrace : WordTrace (prefixWord ++ tailWord_1276340) baseStart_1276340 baseEnd_1276340 := by
    simpa [prefixWord, tailWord_1276340, baseEnd_1276340] using wordTrace_append hprefix tailTrace_1276340
  have hstable : (prefixWord ++ tailWord_1276340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276340).length < 2 ^ (prefixWord ++ tailWord_1276340).sum := by decide
  have hdescent : baseEnd_1276340 < baseStart_1276340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276402 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_1276402 : Nat := 118140960795 + 1276402 * 2 ^ 59
def prefixEnd_1276402 : Nat := 4983230072969 + 3 ^ 40 * 1276402 * 2
def baseEnd_1276402 : Nat := 436938489573480203336627

theorem tailTrace_1276402 : CollatzResearch.WordTrace tailWord_1276402 prefixEnd_1276402 436938489573480203336627 := by
  unfold tailWord_1276402
  simp only [CollatzResearch.WordTrace]
  refine ⟨11638551380455255237867865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31036137014547347300980973 11638551380455255237867865)
  ·
    refine ⟨8728913535341441428400899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11638551380455255237867865 8728913535341441428400899)
    ·
      refine ⟨13093370303012162142601349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8728913535341441428400899 13093370303012162142601349)
      ·
        refine ⟨2455006931814780401737753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13093370303012162142601349 2455006931814780401737753)
        ·
          refine ⟨1841255198861085301303315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2455006931814780401737753 1841255198861085301303315)
          ·
            refine ⟨2761882798291627951954973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841255198861085301303315 2761882798291627951954973)
            ·
              refine ⟨1035706049359360481983115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2761882798291627951954973 1035706049359360481983115)
              ·
                refine ⟨1553559074039040722974673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035706049359360481983115 1553559074039040722974673)
                ·
                  refine ⟨1165169305529280542231005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1553559074039040722974673 1165169305529280542231005)
                  ·
                    refine ⟨436938489573480203336627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1165169305529280542231005 436938489573480203336627)
                    ·
                      rfl

theorem cell22_1276402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_1276402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276402 prefixEnd_1276402 := by exact prefixLift 1276402
  have htrace : WordTrace (prefixWord ++ tailWord_1276402) baseStart_1276402 baseEnd_1276402 := by
    simpa [prefixWord, tailWord_1276402, baseEnd_1276402] using wordTrace_append hprefix tailTrace_1276402
  have hstable : (prefixWord ++ tailWord_1276402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276402).length < 2 ^ (prefixWord ++ tailWord_1276402).sum := by decide
  have hdescent : baseEnd_1276402 < baseStart_1276402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276490 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_1276490 : Nat := 118140960795 + 1276490 * 2 ^ 59
def prefixEnd_1276490 : Nat := 4983230072969 + 3 ^ 40 * 1276490 * 2
def baseEnd_1276490 : Nat := 436968613771877307136357

theorem tailTrace_1276490 : CollatzResearch.WordTrace tailWord_1276490 prefixEnd_1276490 436968613771877307136357 := by
  unfold tailWord_1276490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11639353786375552995168731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31038276763668141320449949 11639353786375552995168731)
  ·
    refine ⟨17459030679563329492753097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11639353786375552995168731 17459030679563329492753097)
    ·
      refine ⟨13094273009672497119564823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17459030679563329492753097 13094273009672497119564823)
      ·
        refine ⟨19641409514508745679347235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13094273009672497119564823 19641409514508745679347235)
        ·
          refine ⟨29462114271763118519020853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19641409514508745679347235 29462114271763118519020853)
          ·
            refine ⟨2762073212977792361158205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29462114271763118519020853 2762073212977792361158205)
            ·
              refine ⟨1035777454866672135434327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2762073212977792361158205 1035777454866672135434327)
              ·
                refine ⟨1553666182300008203151491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035777454866672135434327 1553666182300008203151491)
                ·
                  refine ⟨2330499273450012304727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1553666182300008203151491 2330499273450012304727237)
                  ·
                    refine ⟨436968613771877307136357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2330499273450012304727237 436968613771877307136357)
                    ·
                      rfl

theorem cell22_1276490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_1276490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276490 prefixEnd_1276490 := by exact prefixLift 1276490
  have htrace : WordTrace (prefixWord ++ tailWord_1276490) baseStart_1276490 baseEnd_1276490 := by
    simpa [prefixWord, tailWord_1276490, baseEnd_1276490] using wordTrace_append hprefix tailTrace_1276490
  have hstable : (prefixWord ++ tailWord_1276490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276490).length < 2 ^ (prefixWord ++ tailWord_1276490).sum := by decide
  have hdescent : baseEnd_1276490 < baseStart_1276490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276520 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1276520 : Nat := 118140960795 + 1276520 * 2 ^ 59
def prefixEnd_1276520 : Nat := 4983230072969 + 3 ^ 40 * 1276520 * 2
def baseEnd_1276520 : Nat := 436978883384967228886265

theorem tailTrace_1276520 : CollatzResearch.WordTrace tailWord_1276520 prefixEnd_1276520 436978883384967228886265 := by
  unfold tailWord_1276520
  simp only [CollatzResearch.WordTrace]
  refine ⟨23279254667696763552133507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31039006223595684736178009 23279254667696763552133507)
  ·
    refine ⟨34918882001545145328200261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23279254667696763552133507 34918882001545145328200261)
    ·
      refine ⟨6547290375289714749037549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34918882001545145328200261 6547290375289714749037549)
      ·
        refine ⟨2455233890733643030889081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6547290375289714749037549 2455233890733643030889081)
        ·
          refine ⟨1841425418050232273166811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2455233890733643030889081 1841425418050232273166811)
          ·
            refine ⟨2762138127075348409750217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841425418050232273166811 2762138127075348409750217)
            ·
              refine ⟨2071603595306511307312663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762138127075348409750217 2071603595306511307312663)
              ·
                refine ⟨3107405392959766960968995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071603595306511307312663 3107405392959766960968995)
                ·
                  refine ⟨4661108089439650441453493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107405392959766960968995 4661108089439650441453493)
                  ·
                    refine ⟨436978883384967228886265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4661108089439650441453493 436978883384967228886265)
                    ·
                      rfl

theorem cell22_1276520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1276520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276520 prefixEnd_1276520 := by exact prefixLift 1276520
  have htrace : WordTrace (prefixWord ++ tailWord_1276520) baseStart_1276520 baseEnd_1276520 := by
    simpa [prefixWord, tailWord_1276520, baseEnd_1276520] using wordTrace_append hprefix tailTrace_1276520
  have hstable : (prefixWord ++ tailWord_1276520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276520).length < 2 ^ (prefixWord ++ tailWord_1276520).sum := by decide
  have hdescent : baseEnd_1276520 < baseStart_1276520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276554 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_1276554 : Nat := 118140960795 + 1276554 * 2 ^ 59
def prefixEnd_1276554 : Nat := 4983230072969 + 3 ^ 40 * 1276554 * 2
def baseEnd_1276554 : Nat := 436990522279802473536161

theorem tailTrace_1276554 : CollatzResearch.WordTrace tailWord_1276554 prefixEnd_1276554 436990522279802473536161 := by
  unfold tailWord_1276554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11639937354317587727751179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31039832944846900607336477 11639937354317587727751179)
  ·
    refine ⟨17459906031476381591626769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11639937354317587727751179 17459906031476381591626769)
    ·
      refine ⟨13094929523607286193720077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17459906031476381591626769 13094929523607286193720077)
      ·
        refine ⟨4910598571352732322645029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13094929523607286193720077 4910598571352732322645029)
        ·
          refine ⟨920737232128637310495943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4910598571352732322645029 920737232128637310495943)
          ·
            refine ⟨1381105848192955965743915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920737232128637310495943 1381105848192955965743915)
            ·
              refine ⟨2071658772289433948615873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381105848192955965743915 2071658772289433948615873)
              ·
                refine ⟨1553744079217075461461905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2071658772289433948615873 1553744079217075461461905)
                ·
                  refine ⟨1165308059412806596096429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1553744079217075461461905 1165308059412806596096429)
                  ·
                    refine ⟨436990522279802473536161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1165308059412806596096429 436990522279802473536161)
                    ·
                      rfl

theorem cell22_1276554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_1276554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276554 prefixEnd_1276554 := by exact prefixLift 1276554
  have htrace : WordTrace (prefixWord ++ tailWord_1276554) baseStart_1276554 baseEnd_1276554 := by
    simpa [prefixWord, tailWord_1276554, baseEnd_1276554] using wordTrace_append hprefix tailTrace_1276554
  have hstable : (prefixWord ++ tailWord_1276554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276554).length < 2 ^ (prefixWord ++ tailWord_1276554).sum := by decide
  have hdescent : baseEnd_1276554 < baseStart_1276554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276599 : List Nat := [1, 1, 3, 1, 6, 2, 1, 3, 1, 3]
def baseStart_1276599 : Nat := 118140960795 + 1276599 * 2 ^ 59
def prefixEnd_1276599 : Nat := 4983230072969 + 3 ^ 40 * 1276599 * 2
def baseEnd_1276599 : Nat := 437005926699437356161023

theorem tailTrace_1276599 : CollatzResearch.WordTrace tailWord_1276599 prefixEnd_1276599 437005926699437356161023 := by
  unfold tailWord_1276599
  simp only [CollatzResearch.WordTrace]
  refine ⟨46561390702107323596392851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31040927134738215730928567 46561390702107323596392851)
  ·
    refine ⟨69842086053160985394589277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46561390702107323596392851 69842086053160985394589277)
    ·
      refine ⟨26190782269935369522970979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69842086053160985394589277 26190782269935369522970979)
      ·
        refine ⟨39286173404903054284456469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26190782269935369522970979 39286173404903054284456469)
        ·
          refine ⟨1841539378354830669583897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39286173404903054284456469 1841539378354830669583897)
          ·
            refine ⟨1381154533766123002187923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1841539378354830669583897 1381154533766123002187923)
            ·
              refine ⟨2071731800649184503281885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381154533766123002187923 2071731800649184503281885)
              ·
                refine ⟨776899425243444188730707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2071731800649184503281885 776899425243444188730707)
                ·
                  refine ⟨1165349137865166283096061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776899425243444188730707 1165349137865166283096061)
                  ·
                    refine ⟨437005926699437356161023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1165349137865166283096061 437005926699437356161023)
                    ·
                      rfl

theorem cell22_1276599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_1276599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276599 prefixEnd_1276599 := by exact prefixLift 1276599
  have htrace : WordTrace (prefixWord ++ tailWord_1276599) baseStart_1276599 baseEnd_1276599 := by
    simpa [prefixWord, tailWord_1276599, baseEnd_1276599] using wordTrace_append hprefix tailTrace_1276599
  have hstable : (prefixWord ++ tailWord_1276599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276599).length < 2 ^ (prefixWord ++ tailWord_1276599).sum := by decide
  have hdescent : baseEnd_1276599 < baseStart_1276599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276629 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 5]
def baseStart_1276629 : Nat := 118140960795 + 1276629 * 2 ^ 59
def prefixEnd_1276629 : Nat := 4983230072969 + 3 ^ 40 * 1276629 * 2
def baseEnd_1276629 : Nat := 145672065437509092636977

theorem tailTrace_1276629 : CollatzResearch.WordTrace tailWord_1276629 prefixEnd_1276629 145672065437509092636977 := by
  unfold tailWord_1276629
  simp only [CollatzResearch.WordTrace]
  refine ⟨46562484891998638719984941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31041656594665759146656627 46562484891998638719984941)
  ·
    refine ⟨17460931834499489519994353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46562484891998638719984941 17460931834499489519994353)
    ·
      refine ⟨13095698875874617139995765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17460931834499489519994353 13095698875874617139995765)
      ·
        refine ⟨1227721769613245356874603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13095698875874617139995765 1227721769613245356874603)
        ·
          refine ⟨1841582654419868035311905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227721769613245356874603 1841582654419868035311905)
          ·
            refine ⟨1381186990814901026483929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1841582654419868035311905 1381186990814901026483929)
            ·
              refine ⟨1035890243111175769862947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1381186990814901026483929 1035890243111175769862947)
              ·
                refine ⟨1553835364666763654794421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035890243111175769862947 1553835364666763654794421)
                ·
                  refine ⟨145672065437509092636977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1553835364666763654794421 145672065437509092636977)
                  ·
                    rfl

theorem cell22_1276629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_1276629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276629 prefixEnd_1276629 := by exact prefixLift 1276629
  have htrace : WordTrace (prefixWord ++ tailWord_1276629) baseStart_1276629 baseEnd_1276629 := by
    simpa [prefixWord, tailWord_1276629, baseEnd_1276629] using wordTrace_append hprefix tailTrace_1276629
  have hstable : (prefixWord ++ tailWord_1276629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276629).length < 2 ^ (prefixWord ++ tailWord_1276629).sum := by decide
  have hdescent : baseEnd_1276629 < baseStart_1276629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276674 : List Nat := [3, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_1276674 : Nat := 118140960795 + 1276674 * 2 ^ 59
def prefixEnd_1276674 : Nat := 4983230072969 + 3 ^ 40 * 1276674 * 2
def baseEnd_1276674 : Nat := 145677200244054053511931

theorem tailTrace_1276674 : CollatzResearch.WordTrace tailWord_1276674 prefixEnd_1276674 145677200244054053511931 := by
  unfold tailWord_1276674
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641031544208902851343269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31042750784557074270248717 11641031544208902851343269)
  ·
    refine ⟨2182693414539169284626863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11641031544208902851343269 2182693414539169284626863)
    ·
      refine ⟨3274040121808753926940295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2182693414539169284626863 3274040121808753926940295)
      ·
        refine ⟨4911060182713130890410443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3274040121808753926940295 4911060182713130890410443)
        ·
          refine ⟨7366590274069696335615665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911060182713130890410443 7366590274069696335615665)
          ·
            refine ⟨5524942705552272251711749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7366590274069696335615665 5524942705552272251711749)
            ·
              refine ⟨1035926757291051047195953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5524942705552272251711749 1035926757291051047195953)
              ·
                refine ⟨776945067968288285396965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1035926757291051047195953 776945067968288285396965)
                ·
                  refine ⟨145677200244054053511931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 776945067968288285396965 145677200244054053511931)
                  ·
                    rfl

theorem cell22_1276674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_1276674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276674 prefixEnd_1276674 := by exact prefixLift 1276674
  have htrace : WordTrace (prefixWord ++ tailWord_1276674) baseStart_1276674 baseEnd_1276674 := by
    simpa [prefixWord, tailWord_1276674, baseEnd_1276674] using wordTrace_append hprefix tailTrace_1276674
  have hstable : (prefixWord ++ tailWord_1276674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276674).length < 2 ^ (prefixWord ++ tailWord_1276674).sum := by decide
  have hdescent : baseEnd_1276674 < baseStart_1276674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276698 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1276698 : Nat := 118140960795 + 1276698 * 2 ^ 59
def prefixEnd_1276698 : Nat := 4983230072969 + 3 ^ 40 * 1276698 * 2
def baseEnd_1276698 : Nat := 437039816422634097935719

theorem tailTrace_1276698 : CollatzResearch.WordTrace tailWord_1276698 prefixEnd_1276698 437039816422634097935719 := by
  unfold tailWord_1276698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641250382187165876061687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31043334352499109002831165 11641250382187165876061687)
  ·
    refine ⟨17461875573280748814092531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11641250382187165876061687 17461875573280748814092531)
    ·
      refine ⟨26192813359921123221138797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17461875573280748814092531 26192813359921123221138797)
      ·
        refine ⟨9822305009970421207927049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26192813359921123221138797 9822305009970421207927049)
        ·
          refine ⟨7366728757477815905945287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9822305009970421207927049 7366728757477815905945287)
          ·
            refine ⟨11050093136216723858917931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366728757477815905945287 11050093136216723858917931)
            ·
              refine ⟨16575139704325085788376897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11050093136216723858917931 16575139704325085788376897)
              ·
                refine ⟨12431354778243814341282673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16575139704325085788376897 12431354778243814341282673)
                ·
                  refine ⟨9323516083682860755962005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12431354778243814341282673 9323516083682860755962005)
                  ·
                    refine ⟨437039816422634097935719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9323516083682860755962005 437039816422634097935719)
                    ·
                      rfl

theorem cell22_1276698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1276698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276698 prefixEnd_1276698 := by exact prefixLift 1276698
  have htrace : WordTrace (prefixWord ++ tailWord_1276698) baseStart_1276698 baseEnd_1276698 := by
    simpa [prefixWord, tailWord_1276698, baseEnd_1276698] using wordTrace_append hprefix tailTrace_1276698
  have hstable : (prefixWord ++ tailWord_1276698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276698).length < 2 ^ (prefixWord ++ tailWord_1276698).sum := by decide
  have hdescent : baseEnd_1276698 < baseStart_1276698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276700 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1276700 : Nat := 118140960795 + 1276700 * 2 ^ 59
def prefixEnd_1276700 : Nat := 4983230072969 + 3 ^ 40 * 1276700 * 2
def baseEnd_1276700 : Nat := 437040501063506759385713

theorem tailTrace_1276700 : CollatzResearch.WordTrace tailWord_1276700 prefixEnd_1276700 437040501063506759385713 := by
  unfold tailWord_1276700
  simp only [CollatzResearch.WordTrace]
  refine ⟨23282537237370708922909777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31043382983160945230546369 23282537237370708922909777)
  ·
    refine ⟨17461902928028031692182333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23282537237370708922909777 17461902928028031692182333)
    ·
      refine ⟨6548213598010511884568375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17461902928028031692182333 6548213598010511884568375)
      ·
        refine ⟨9822320397015767826852563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6548213598010511884568375 9822320397015767826852563)
        ·
          refine ⟨14733480595523651740278845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9822320397015767826852563 14733480595523651740278845)
          ·
            refine ⟨5525055223321369402604567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14733480595523651740278845 5525055223321369402604567)
            ·
              refine ⟨8287582834982054103906851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525055223321369402604567 8287582834982054103906851)
              ·
                refine ⟨12431374252473081155860277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8287582834982054103906851 12431374252473081155860277)
                ·
                  refine ⟨1165441336169351358361901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12431374252473081155860277 1165441336169351358361901)
                  ·
                    refine ⟨437040501063506759385713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1165441336169351358361901 437040501063506759385713)
                    ·
                      rfl

theorem cell22_1276700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1276700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276700 prefixEnd_1276700 := by exact prefixLift 1276700
  have htrace : WordTrace (prefixWord ++ tailWord_1276700) baseStart_1276700 baseEnd_1276700 := by
    simpa [prefixWord, tailWord_1276700, baseEnd_1276700] using wordTrace_append hprefix tailTrace_1276700
  have hstable : (prefixWord ++ tailWord_1276700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276700).length < 2 ^ (prefixWord ++ tailWord_1276700).sum := by decide
  have hdescent : baseEnd_1276700 < baseStart_1276700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276728 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 4, 5]
def baseStart_1276728 : Nat := 118140960795 + 1276728 * 2 ^ 59
def prefixEnd_1276728 : Nat := 4983230072969 + 3 ^ 40 * 1276728 * 2
def baseEnd_1276728 : Nat := 437050086035724019685627

theorem tailTrace_1276728 : CollatzResearch.WordTrace tailWord_1276728 prefixEnd_1276728 437050086035724019685627 := by
  unfold tailWord_1276728
  simp only [CollatzResearch.WordTrace]
  refine ⟨23283047859319989313919419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31044063812426652418559225 23283047859319989313919419)
  ·
    refine ⟨34924571788979983970879129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23283047859319989313919419 34924571788979983970879129)
    ·
      refine ⟨26193428841734987978159347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34924571788979983970879129 26193428841734987978159347)
      ·
        refine ⟨39290143262602481967239021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26193428841734987978159347 39290143262602481967239021)
        ·
          refine ⟨14733803723475930737714633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39290143262602481967239021 14733803723475930737714633)
          ·
            refine ⟨11050352792606948053285975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14733803723475930737714633 11050352792606948053285975)
            ·
              refine ⟨16575529188910422079928963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11050352792606948053285975 16575529188910422079928963)
              ·
                refine ⟨24863293783365633119893445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16575529188910422079928963 24863293783365633119893445)
                ·
                  refine ⟨4661867584381056209980021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24863293783365633119893445 4661867584381056209980021)
                  ·
                    refine ⟨437050086035724019685627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4661867584381056209980021 437050086035724019685627)
                    ·
                      rfl

theorem cell22_1276728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_1276728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276728 prefixEnd_1276728 := by exact prefixLift 1276728
  have htrace : WordTrace (prefixWord ++ tailWord_1276728) baseStart_1276728 baseEnd_1276728 := by
    simpa [prefixWord, tailWord_1276728, baseEnd_1276728] using wordTrace_append hprefix tailTrace_1276728
  have hstable : (prefixWord ++ tailWord_1276728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276728).length < 2 ^ (prefixWord ++ tailWord_1276728).sum := by decide
  have hdescent : baseEnd_1276728 < baseStart_1276728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276730 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_1276730 : Nat := 118140960795 + 1276730 * 2 ^ 59
def prefixEnd_1276730 : Nat := 4983230072969 + 3 ^ 40 * 1276730 * 2
def baseEnd_1276730 : Nat := 145683590225532227045207

theorem tailTrace_1276730 : CollatzResearch.WordTrace tailWord_1276730 prefixEnd_1276730 145683590225532227045207 := by
  unfold tailWord_1276730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641542166158183242352911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31044112443088488646274429 11641542166158183242352911)
  ·
    refine ⟨17462313249237274863529367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11641542166158183242352911 17462313249237274863529367)
    ·
      refine ⟨26193469873855912295294051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17462313249237274863529367 26193469873855912295294051)
      ·
        refine ⟨39290204810783868442941077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26193469873855912295294051 39290204810783868442941077)
        ·
          refine ⟨1841728350505493833262863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39290204810783868442941077 1841728350505493833262863)
          ·
            refine ⟨2762592525758240749894295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841728350505493833262863 2762592525758240749894295)
            ·
              refine ⟨4143888788637361124841443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2762592525758240749894295 4143888788637361124841443)
              ·
                refine ⟨6215833182956041687262165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143888788637361124841443 6215833182956041687262165)
                ·
                  refine ⟨145683590225532227045207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6215833182956041687262165 145683590225532227045207)
                  ·
                    rfl

theorem cell22_1276730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_1276730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276730 prefixEnd_1276730 := by exact prefixLift 1276730
  have htrace : WordTrace (prefixWord ++ tailWord_1276730) baseStart_1276730 baseEnd_1276730 := by
    simpa [prefixWord, tailWord_1276730, baseEnd_1276730] using wordTrace_append hprefix tailTrace_1276730
  have hstable : (prefixWord ++ tailWord_1276730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276730).length < 2 ^ (prefixWord ++ tailWord_1276730).sum := by decide
  have hdescent : baseEnd_1276730 < baseStart_1276730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276734 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1276734 : Nat := 118140960795 + 1276734 * 2 ^ 59
def prefixEnd_1276734 : Nat := 4983230072969 + 3 ^ 40 * 1276734 * 2
def baseEnd_1276734 : Nat := 437052139958342004035609

theorem tailTrace_1276734 : CollatzResearch.WordTrace tailWord_1276734 prefixEnd_1276734 437052139958342004035609 := by
  unfold tailWord_1276734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5820789319577280206569657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31044209704412161101704837 5820789319577280206569657)
  ·
    refine ⟨4365591989682960154927243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5820789319577280206569657 4365591989682960154927243)
    ·
      refine ⟨6548387984524440232390865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4365591989682960154927243 6548387984524440232390865)
      ·
        refine ⟨4911290988393330174293149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548387984524440232390865 4911290988393330174293149)
        ·
          refine ⟨1841734120647498815359931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4911290988393330174293149 1841734120647498815359931)
          ·
            refine ⟨2762601180971248223039897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841734120647498815359931 2762601180971248223039897)
            ·
              refine ⟨2071950885728436167279923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2762601180971248223039897 2071950885728436167279923)
              ·
                refine ⟨3107926328592654250919885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2071950885728436167279923 3107926328592654250919885)
                ·
                  refine ⟨1165472373222245344094957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3107926328592654250919885 1165472373222245344094957)
                  ·
                    refine ⟨437052139958342004035609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1165472373222245344094957 437052139958342004035609)
                    ·
                      rfl

theorem cell22_1276734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1276734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276734 prefixEnd_1276734 := by exact prefixLift 1276734
  have htrace : WordTrace (prefixWord ++ tailWord_1276734) baseStart_1276734 baseEnd_1276734 := by
    simpa [prefixWord, tailWord_1276734, baseEnd_1276734] using wordTrace_append hprefix tailTrace_1276734
  have hstable : (prefixWord ++ tailWord_1276734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276734).length < 2 ^ (prefixWord ++ tailWord_1276734).sum := by decide
  have hdescent : baseEnd_1276734 < baseStart_1276734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276798 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_1276798 : Nat := 118140960795 + 1276798 * 2 ^ 59
def prefixEnd_1276798 : Nat := 4983230072969 + 3 ^ 40 * 1276798 * 2
def baseEnd_1276798 : Nat := 145691349488755723478471

theorem tailTrace_1276798 : CollatzResearch.WordTrace tailWord_1276798 prefixEnd_1276798 145691349488755723478471 := by
  unfold tailWord_1276798
  simp only [CollatzResearch.WordTrace]
  refine ⟨5821081103548297572860881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31045765885590920388591365 5821081103548297572860881)
  ·
    refine ⟨4365810827661223179645661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5821081103548297572860881 4365810827661223179645661)
    ·
      refine ⟨1637179060372958692367123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4365810827661223179645661 1637179060372958692367123)
      ·
        refine ⟨2455768590559438038550685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637179060372958692367123 2455768590559438038550685)
        ·
          refine ⟨920913221459789264456507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2455768590559438038550685 920913221459789264456507)
          ·
            refine ⟨1381369832189683896684761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920913221459789264456507 1381369832189683896684761)
            ·
              refine ⟨1036027374142262922513571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1381369832189683896684761 1036027374142262922513571)
              ·
                refine ⟨1554041061213394383770357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036027374142262922513571 1554041061213394383770357)
                ·
                  refine ⟨145691349488755723478471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1554041061213394383770357 145691349488755723478471)
                  ·
                    rfl

theorem cell22_1276798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_1276798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276798 prefixEnd_1276798 := by exact prefixLift 1276798
  have htrace : WordTrace (prefixWord ++ tailWord_1276798) baseStart_1276798 baseEnd_1276798 := by
    simpa [prefixWord, tailWord_1276798, baseEnd_1276798] using wordTrace_append hprefix tailTrace_1276798
  have hstable : (prefixWord ++ tailWord_1276798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276798).length < 2 ^ (prefixWord ++ tailWord_1276798).sum := by decide
  have hdescent : baseEnd_1276798 < baseStart_1276798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276820 : List Nat := [2, 4, 2, 1, 1, 1, 1, 10]
def baseStart_1276820 : Nat := 118140960795 + 1276820 * 2 ^ 59
def prefixEnd_1276820 : Nat := 4983230072969 + 3 ^ 40 * 1276820 * 2
def baseEnd_1276820 : Nat := 48564619946207382931705

theorem tailTrace_1276820 : CollatzResearch.WordTrace tailWord_1276820 prefixEnd_1276820 48564619946207382931705 := by
  unfold tailWord_1276820
  simp only [CollatzResearch.WordTrace]
  refine ⟨23284725617153339170093957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31046300822871118893458609 23284725617153339170093957)
  ·
    refine ⟨4365886053216251094392617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23284725617153339170093957 4365886053216251094392617)
    ·
      refine ⟨3274414539912188320794463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4365886053216251094392617 3274414539912188320794463)
      ·
        refine ⟨4911621809868282481191695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3274414539912188320794463 4911621809868282481191695)
        ·
          refine ⟨7367432714802423721787543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4911621809868282481191695 7367432714802423721787543)
          ·
            refine ⟨11051149072203635582681315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7367432714802423721787543 11051149072203635582681315)
            ·
              refine ⟨16576723608305453374021973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11051149072203635582681315 16576723608305453374021973)
              ·
                refine ⟨48564619946207382931705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16576723608305453374021973 48564619946207382931705)
                ·
                  rfl

theorem cell22_1276820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 10].length) (baseStart_1276820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276820 prefixEnd_1276820 := by exact prefixLift 1276820
  have htrace : WordTrace (prefixWord ++ tailWord_1276820) baseStart_1276820 baseEnd_1276820 := by
    simpa [prefixWord, tailWord_1276820, baseEnd_1276820] using wordTrace_append hprefix tailTrace_1276820
  have hstable : (prefixWord ++ tailWord_1276820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276820).length < 2 ^ (prefixWord ++ tailWord_1276820).sum := by decide
  have hdescent : baseEnd_1276820 < baseStart_1276820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276929 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1276929 : Nat := 118140960795 + 1276929 * 2 ^ 59
def prefixEnd_1276929 : Nat := 4983230072969 + 3 ^ 40 * 1276929 * 2
def baseEnd_1276929 : Nat := 437118892443426495410011

theorem tailTrace_1276929 : CollatzResearch.WordTrace tailWord_1276929 prefixEnd_1276929 437118892443426495410011 := by
  unfold tailWord_1276929
  simp only [CollatzResearch.WordTrace]
  refine ⟨46573426790911789955905841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31048951193941193303937227 46573426790911789955905841)
  ·
    refine ⟨34930070093183842466929381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46573426790911789955905841 34930070093183842466929381)
    ·
      refine ⟨6549388142471970462549259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34930070093183842466929381 6549388142471970462549259)
      ·
        refine ⟨9824082213707955693823889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6549388142471970462549259 9824082213707955693823889)
        ·
          refine ⟨7368061660280966770367917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9824082213707955693823889 7368061660280966770367917)
          ·
            refine ⟨2763023122605362538887969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7368061660280966770367917 2763023122605362538887969)
            ·
              refine ⟨2072267341954021904165977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2763023122605362538887969 2072267341954021904165977)
              ·
                refine ⟨1554200506465516428124483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072267341954021904165977 1554200506465516428124483)
                ·
                  refine ⟨2331300759698274642186725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554200506465516428124483 2331300759698274642186725)
                  ·
                    refine ⟨437118892443426495410011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2331300759698274642186725 437118892443426495410011)
                    ·
                      rfl

theorem cell22_1276929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1276929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276929 prefixEnd_1276929 := by exact prefixLift 1276929
  have htrace : WordTrace (prefixWord ++ tailWord_1276929) baseStart_1276929 baseEnd_1276929 := by
    simpa [prefixWord, tailWord_1276929, baseEnd_1276929] using wordTrace_append hprefix tailTrace_1276929
  have hstable : (prefixWord ++ tailWord_1276929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276929).length < 2 ^ (prefixWord ++ tailWord_1276929).sum := by decide
  have hdescent : baseEnd_1276929 < baseStart_1276929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1276961 : List Nat := [1, 2, 3, 2, 3, 2, 3, 2, 4]
def baseStart_1276961 : Nat := 118140960795 + 1276961 * 2 ^ 59
def prefixEnd_1276961 : Nat := 4983230072969 + 3 ^ 40 * 1276961 * 2
def baseEnd_1276961 : Nat := 145709948899129692869971

theorem tailTrace_1276961 : CollatzResearch.WordTrace tailWord_1276961 prefixEnd_1276961 145709948899129692869971 := by
  unfold tailWord_1276961
  simp only [CollatzResearch.WordTrace]
  refine ⟨46574593926795859421070737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31049729284530572947380491 46574593926795859421070737)
  ·
    refine ⟨34930945445096894565803053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46574593926795859421070737 34930945445096894565803053)
    ·
      refine ⟨13099104541911335462176145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34930945445096894565803053 13099104541911335462176145)
      ·
        refine ⟨9824328406433501596632109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13099104541911335462176145 9824328406433501596632109)
        ·
          refine ⟨3684123152412563098737041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9824328406433501596632109 3684123152412563098737041)
          ·
            refine ⟨2763092364309422324052781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3684123152412563098737041 2763092364309422324052781)
            ·
              refine ⟨1036159636616033371519793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2763092364309422324052781 1036159636616033371519793)
              ·
                refine ⟨777119727462025028639845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036159636616033371519793 777119727462025028639845)
                ·
                  refine ⟨145709948899129692869971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 777119727462025028639845 145709948899129692869971)
                  ·
                    rfl

theorem cell22_1276961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 4].length) (baseStart_1276961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1276961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1276961 prefixEnd_1276961 := by exact prefixLift 1276961
  have htrace : WordTrace (prefixWord ++ tailWord_1276961) baseStart_1276961 baseEnd_1276961 := by
    simpa [prefixWord, tailWord_1276961, baseEnd_1276961] using wordTrace_append hprefix tailTrace_1276961
  have hstable : (prefixWord ++ tailWord_1276961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1276961).length < 2 ^ (prefixWord ++ tailWord_1276961).sum := by decide
  have hdescent : baseEnd_1276961 < baseStart_1276961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1276961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277034 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_1277034 : Nat := 118140960795 + 1277034 * 2 ^ 59
def prefixEnd_1277034 : Nat := 4983230072969 + 3 ^ 40 * 1277034 * 2
def baseEnd_1277034 : Nat := 145718278696413740511563

theorem tailTrace_1277034 : CollatzResearch.WordTrace tailWord_1277034 prefixEnd_1277034 145718278696413740511563 := by
  unfold tailWord_1277034
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644314113882848222119539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31051504303687595258985437 11644314113882848222119539)
  ·
    refine ⟨17466471170824272333179309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11644314113882848222119539 17466471170824272333179309)
    ·
      refine ⟨6549926689059102124942241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17466471170824272333179309 6549926689059102124942241)
      ·
        refine ⟨4912445016794326593706681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6549926689059102124942241 4912445016794326593706681)
        ·
          refine ⟨3684333762595744945280011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4912445016794326593706681 3684333762595744945280011)
          ·
            refine ⟨5526500643893617417920017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684333762595744945280011 5526500643893617417920017)
            ·
              refine ⟨4144875482920213063440013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5526500643893617417920017 4144875482920213063440013)
              ·
                refine ⟨1554328306095079898790005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4144875482920213063440013 1554328306095079898790005)
                ·
                  refine ⟨145718278696413740511563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1554328306095079898790005 145718278696413740511563)
                  ·
                    rfl

theorem cell22_1277034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_1277034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277034 prefixEnd_1277034 := by exact prefixLift 1277034
  have htrace : WordTrace (prefixWord ++ tailWord_1277034) baseStart_1277034 baseEnd_1277034 := by
    simpa [prefixWord, tailWord_1277034, baseEnd_1277034] using wordTrace_append hprefix tailTrace_1277034
  have hstable : (prefixWord ++ tailWord_1277034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277034).length < 2 ^ (prefixWord ++ tailWord_1277034).sum := by decide
  have hdescent : baseEnd_1277034 < baseStart_1277034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277047 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 3, 4]
def baseStart_1277047 : Nat := 118140960795 + 1277047 * 2 ^ 59
def prefixEnd_1277047 : Nat := 4983230072969 + 3 ^ 40 * 1277047 * 2
def baseEnd_1277047 : Nat := 437159286254913520959649

theorem tailTrace_1277047 : CollatzResearch.WordTrace tailWord_1277047 prefixEnd_1277047 437159286254913520959649 := by
  unfold tailWord_1277047
  simp only [CollatzResearch.WordTrace]
  refine ⟨46577730604484296108701395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31051820402989530739134263 46577730604484296108701395)
  ·
    refine ⟨69866595906726444163052093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46577730604484296108701395 69866595906726444163052093)
    ·
      refine ⟨26199973465022416561144535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69866595906726444163052093 26199973465022416561144535)
      ·
        refine ⟨39299960197533624841716803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26199973465022416561144535 39299960197533624841716803)
        ·
          refine ⟨58949940296300437262575205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39299960197533624841716803 58949940296300437262575205)
          ·
            refine ⟨11053113805556331986732851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58949940296300437262575205 11053113805556331986732851)
            ·
              refine ⟨16579670708334497980099277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11053113805556331986732851 16579670708334497980099277)
              ·
                refine ⟨6217376515625436742537229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16579670708334497980099277 6217376515625436742537229)
                ·
                  refine ⟨2331516193359538778451461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6217376515625436742537229 2331516193359538778451461)
                  ·
                    refine ⟨437159286254913520959649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2331516193359538778451461 437159286254913520959649)
                    ·
                      rfl

theorem cell22_1277047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_1277047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277047 prefixEnd_1277047 := by exact prefixLift 1277047
  have htrace : WordTrace (prefixWord ++ tailWord_1277047) baseStart_1277047 baseEnd_1277047 := by
    simpa [prefixWord, tailWord_1277047, baseEnd_1277047] using wordTrace_append hprefix tailTrace_1277047
  have hstable : (prefixWord ++ tailWord_1277047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277047).length < 2 ^ (prefixWord ++ tailWord_1277047).sum := by decide
  have hdescent : baseEnd_1277047 < baseStart_1277047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277079 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 6]
def baseStart_1277079 : Nat := 118140960795 + 1277079 * 2 ^ 59
def prefixEnd_1277079 : Nat := 4983230072969 + 3 ^ 40 * 1277079 * 2
def baseEnd_1277079 : Nat := 145723413502958701386517

theorem tailTrace_1277079 : CollatzResearch.WordTrace tailWord_1277079 prefixEnd_1277079 145723413502958701386517 := by
  unfold tailWord_1277079
  simp only [CollatzResearch.WordTrace]
  refine ⟨46578897740368365573866291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31052598493578910382577527 46578897740368365573866291)
  ·
    refine ⟨69868346610552548360799437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46578897740368365573866291 69868346610552548360799437)
    ·
      refine ⟨26200629978957205635299789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69868346610552548360799437 26200629978957205635299789)
      ·
        refine ⟨9825236242108952113237421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26200629978957205635299789 9825236242108952113237421)
        ·
          refine ⟨3684463590790857042464033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9825236242108952113237421 3684463590790857042464033)
          ·
            refine ⟨2763347693093142781848025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3684463590790857042464033 2763347693093142781848025)
            ·
              refine ⟨2072510769819857086386019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2763347693093142781848025 2072510769819857086386019)
              ·
                refine ⟨3108766154729785629579029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072510769819857086386019 3108766154729785629579029)
                ·
                  refine ⟨145723413502958701386517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3108766154729785629579029 145723413502958701386517)
                  ·
                    rfl

theorem cell22_1277079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 6].length) (baseStart_1277079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277079 prefixEnd_1277079 := by exact prefixLift 1277079
  have htrace : WordTrace (prefixWord ++ tailWord_1277079) baseStart_1277079 baseEnd_1277079 := by
    simpa [prefixWord, tailWord_1277079, baseEnd_1277079] using wordTrace_append hprefix tailTrace_1277079
  have hstable : (prefixWord ++ tailWord_1277079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277079).length < 2 ^ (prefixWord ++ tailWord_1277079).sum := by decide
  have hdescent : baseEnd_1277079 < baseStart_1277079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277098 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1277098 : Nat := 118140960795 + 1277098 * 2 ^ 59
def prefixEnd_1277098 : Nat := 4983230072969 + 3 ^ 40 * 1277098 * 2
def baseEnd_1277098 : Nat := 437176744597166387934493

theorem tailTrace_1277098 : CollatzResearch.WordTrace tailWord_1277098 prefixEnd_1277098 437176744597166387934493 := by
  unfold tailWord_1277098
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644897681824882954701987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31053060484866354545871965 11644897681824882954701987)
  ·
    refine ⟨17467346522737324432052981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11644897681824882954701987 17467346522737324432052981)
    ·
      refine ⟨1637563736506624165504967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17467346522737324432052981 1637563736506624165504967)
      ·
        refine ⟨2456345604759936248257451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637563736506624165504967 2456345604759936248257451)
        ·
          refine ⟨3684518407139904372386177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456345604759936248257451 3684518407139904372386177)
          ·
            refine ⟨2763388805354928279289633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3684518407139904372386177 2763388805354928279289633)
            ·
              refine ⟨2072541604016196209467225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2763388805354928279289633 2072541604016196209467225)
              ·
                refine ⟨1554406203012147157100419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072541604016196209467225 1554406203012147157100419)
                ·
                  refine ⟨2331609304518220735650629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554406203012147157100419 2331609304518220735650629)
                  ·
                    refine ⟨437176744597166387934493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2331609304518220735650629 437176744597166387934493)
                    ·
                      rfl

theorem cell22_1277098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1277098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277098 prefixEnd_1277098 := by exact prefixLift 1277098
  have htrace : WordTrace (prefixWord ++ tailWord_1277098) baseStart_1277098 baseEnd_1277098 := by
    simpa [prefixWord, tailWord_1277098, baseEnd_1277098] using wordTrace_append hprefix tailTrace_1277098
  have hstable : (prefixWord ++ tailWord_1277098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277098).length < 2 ^ (prefixWord ++ tailWord_1277098).sum := by decide
  have hdescent : baseEnd_1277098 < baseStart_1277098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277137 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1277137 : Nat := 118140960795 + 1277137 * 2 ^ 59
def prefixEnd_1277137 : Nat := 4983230072969 + 3 ^ 40 * 1277137 * 2
def baseEnd_1277137 : Nat := 437190095094183286209373

theorem tailTrace_1277137 : CollatzResearch.WordTrace tailWord_1277137 prefixEnd_1277137 437190095094183286209373 := by
  unfold tailWord_1277137
  simp only [CollatzResearch.WordTrace]
  refine ⟨46581013174158241479477665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31054008782772160986318443 46581013174158241479477665)
  ·
    refine ⟨34935759880618681109608249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46581013174158241479477665 34935759880618681109608249)
    ·
      refine ⟨26201819910464010832206187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34935759880618681109608249 26201819910464010832206187)
      ·
        refine ⟨39302729865696016248309281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26201819910464010832206187 39302729865696016248309281)
        ·
          refine ⟨29477047399272012186231961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39302729865696016248309281 29477047399272012186231961)
          ·
            refine ⟨22107785549454009139673971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29477047399272012186231961 22107785549454009139673971)
            ·
              refine ⟨33161678324181013709510957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22107785549454009139673971 33161678324181013709510957)
              ·
                refine ⟨12435629371567880141066609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33161678324181013709510957 12435629371567880141066609)
                ·
                  refine ⟨9326722028675910105799957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12435629371567880141066609 9326722028675910105799957)
                  ·
                    refine ⟨437190095094183286209373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9326722028675910105799957 437190095094183286209373)
                    ·
                      rfl

theorem cell22_1277137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1277137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277137 prefixEnd_1277137 := by exact prefixLift 1277137
  have htrace : WordTrace (prefixWord ++ tailWord_1277137) baseStart_1277137 baseEnd_1277137 := by
    simpa [prefixWord, tailWord_1277137, baseEnd_1277137] using wordTrace_append hprefix tailTrace_1277137
  have hstable : (prefixWord ++ tailWord_1277137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277137).length < 2 ^ (prefixWord ++ tailWord_1277137).sum := by decide
  have hdescent : baseEnd_1277137 < baseStart_1277137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277233 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 1, 4]
def baseStart_1277233 : Nat := 118140960795 + 1277233 * 2 ^ 59
def prefixEnd_1277233 : Nat := 4983230072969 + 3 ^ 40 * 1277233 * 2
def baseEnd_1277233 : Nat := 437222957856071035809079

theorem tailTrace_1277233 : CollatzResearch.WordTrace tailWord_1277233 prefixEnd_1277233 437222957856071035809079 := by
  unfold tailWord_1277233
  simp only [CollatzResearch.WordTrace]
  refine ⟨46584514581810449874972353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31056343054540299916648235 46584514581810449874972353)
  ·
    refine ⟨34938385936357837406229265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46584514581810449874972353 34938385936357837406229265)
    ·
      refine ⟨26203789452268378054671949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34938385936357837406229265 26203789452268378054671949)
      ·
        refine ⟨9826421044600641770501981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26203789452268378054671949 9826421044600641770501981)
        ·
          refine ⟨3684907891725240663938243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9826421044600641770501981 3684907891725240663938243)
          ·
            refine ⟨5527361837587860995907365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684907891725240663938243 5527361837587860995907365)
            ·
              refine ⟨1036380344547723936732631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5527361837587860995907365 1036380344547723936732631)
              ·
                refine ⟨1554570516821585905098947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036380344547723936732631 1554570516821585905098947)
                ·
                  refine ⟨2331855775232378857648421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554570516821585905098947 2331855775232378857648421)
                  ·
                    refine ⟨437222957856071035809079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2331855775232378857648421 437222957856071035809079)
                    ·
                      rfl

theorem cell22_1277233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_1277233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277233 prefixEnd_1277233 := by exact prefixLift 1277233
  have htrace : WordTrace (prefixWord ++ tailWord_1277233) baseStart_1277233 baseEnd_1277233 := by
    simpa [prefixWord, tailWord_1277233, baseEnd_1277233] using wordTrace_append hprefix tailTrace_1277233
  have hstable : (prefixWord ++ tailWord_1277233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277233).length < 2 ^ (prefixWord ++ tailWord_1277233).sum := by decide
  have hdescent : baseEnd_1277233 < baseStart_1277233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277310 : List Nat := [4, 2, 3, 2, 1, 1, 2, 7]
def baseStart_1277310 : Nat := 118140960795 + 1277310 * 2 ^ 59
def prefixEnd_1277310 : Nat := 4983230072969 + 3 ^ 40 * 1277310 * 2
def baseEnd_1277310 : Nat := 48583257392185389070427

theorem tailTrace_1277310 : CollatzResearch.WordTrace tailWord_1277310 prefixEnd_1277310 48583257392185389070427 := by
  unfold tailWord_1277310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5823415375316436503190673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31058215335020994683683589 5823415375316436503190673)
  ·
    refine ⟨4367561531487327377393005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5823415375316436503190673 4367561531487327377393005)
    ·
      refine ⟨1637835574307747766522377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4367561531487327377393005 1637835574307747766522377)
      ·
        refine ⟨1228376680730810824891783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1637835574307747766522377 1228376680730810824891783)
        ·
          refine ⟨1842565021096216237337675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228376680730810824891783 1842565021096216237337675)
          ·
            refine ⟨2763847531644324356006513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842565021096216237337675 2763847531644324356006513)
            ·
              refine ⟨2072885648733243267004885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2763847531644324356006513 2072885648733243267004885)
              ·
                refine ⟨48583257392185389070427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2072885648733243267004885 48583257392185389070427)
                ·
                  rfl

theorem cell22_1277310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_1277310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277310 prefixEnd_1277310 := by exact prefixLift 1277310
  have htrace : WordTrace (prefixWord ++ tailWord_1277310) baseStart_1277310 baseEnd_1277310 := by
    simpa [prefixWord, tailWord_1277310, baseEnd_1277310] using wordTrace_append hprefix tailTrace_1277310
  have hstable : (prefixWord ++ tailWord_1277310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277310).length < 2 ^ (prefixWord ++ tailWord_1277310).sum := by decide
  have hdescent : baseEnd_1277310 < baseStart_1277310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277314 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1277314 : Nat := 118140960795 + 1277314 * 2 ^ 59
def prefixEnd_1277314 : Nat := 4983230072969 + 3 ^ 40 * 1277314 * 2
def baseEnd_1277314 : Nat := 437250685811413824533831

theorem tailTrace_1277314 : CollatzResearch.WordTrace tailWord_1277314 prefixEnd_1277314 437250685811413824533831 := by
  unfold tailWord_1277314
  simp only [CollatzResearch.WordTrace]
  refine ⟨11646867223629250177167749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31058312596344667139113997 11646867223629250177167749)
  ·
    refine ⟨2183787604430484408218953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11646867223629250177167749 2183787604430484408218953)
    ·
      refine ⟨1637840703322863306164215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2183787604430484408218953 1637840703322863306164215)
      ·
        refine ⟨2456761054984294959246323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637840703322863306164215 2456761054984294959246323)
        ·
          refine ⟨3685141582476442438869485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456761054984294959246323 3685141582476442438869485)
          ·
            refine ⟨1381928093428665914576057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3685141582476442438869485 1381928093428665914576057)
            ·
              refine ⟨1036446070071499435932043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1381928093428665914576057 1036446070071499435932043)
              ·
                refine ⟨1554669105107249153898065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036446070071499435932043 1554669105107249153898065)
                ·
                  refine ⟨1166001828830436865423549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554669105107249153898065 1166001828830436865423549)
                  ·
                    refine ⟨437250685811413824533831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1166001828830436865423549 437250685811413824533831)
                    ·
                      rfl

theorem cell22_1277314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1277314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277314 prefixEnd_1277314 := by exact prefixLift 1277314
  have htrace : WordTrace (prefixWord ++ tailWord_1277314) baseStart_1277314 baseEnd_1277314 := by
    simpa [prefixWord, tailWord_1277314, baseEnd_1277314] using wordTrace_append hprefix tailTrace_1277314
  have hstable : (prefixWord ++ tailWord_1277314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277314).length < 2 ^ (prefixWord ++ tailWord_1277314).sum := by decide
  have hdescent : baseEnd_1277314 < baseStart_1277314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277349 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 10]
def baseStart_1277349 : Nat := 118140960795 + 1277349 * 2 ^ 59
def prefixEnd_1277349 : Nat := 4983230072969 + 3 ^ 40 * 1277349 * 2
def baseEnd_1277349 : Nat := 145754222342228466636241

theorem tailTrace_1277349 : CollatzResearch.WordTrace tailWord_1277349 prefixEnd_1277349 145754222342228466636241 := by
  unfold tailWord_1277349
  simp only [CollatzResearch.WordTrace]
  refine ⟨46588745449390201686195101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31059163632926801124130067 46588745449390201686195101)
  ·
    refine ⟨17470779543521325632323163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46588745449390201686195101 17470779543521325632323163)
    ·
      refine ⟨26206169315281988448484745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17470779543521325632323163 26206169315281988448484745)
      ·
        refine ⟨19654626986461491336363559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26206169315281988448484745 19654626986461491336363559)
        ·
          refine ⟨29481940479692237004545339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19654626986461491336363559 29481940479692237004545339)
          ·
            refine ⟨44222910719538355506818009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29481940479692237004545339 44222910719538355506818009)
            ·
              refine ⟨33167183039653766630113507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44222910719538355506818009 33167183039653766630113507)
              ·
                refine ⟨49750774559480649945170261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33167183039653766630113507 49750774559480649945170261)
                ·
                  refine ⟨145754222342228466636241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 49750774559480649945170261 145754222342228466636241)
                  ·
                    rfl

theorem cell22_1277349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_1277349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277349 prefixEnd_1277349 := by exact prefixLift 1277349
  have htrace : WordTrace (prefixWord ++ tailWord_1277349) baseStart_1277349 baseEnd_1277349 := by
    simpa [prefixWord, tailWord_1277349, baseEnd_1277349] using wordTrace_append hprefix tailTrace_1277349
  have hstable : (prefixWord ++ tailWord_1277349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277349).length < 2 ^ (prefixWord ++ tailWord_1277349).sum := by decide
  have hdescent : baseEnd_1277349 < baseStart_1277349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277411 : List Nat := [1, 1, 1, 6, 2, 2, 9]
def baseStart_1277411 : Nat := 118140960795 + 1277411 * 2 ^ 59
def prefixEnd_1277411 : Nat := 4983230072969 + 3 ^ 40 * 1277411 * 2
def baseEnd_1277411 : Nat := 16195699662731033513279

theorem tailTrace_1277411 : CollatzResearch.WordTrace tailWord_1277411 prefixEnd_1277411 16195699662731033513279 := by
  unfold tailWord_1277411
  simp only [CollatzResearch.WordTrace]
  refine ⟨46591006775165586274952087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31060671183443724183301391 46591006775165586274952087)
  ·
    refine ⟨69886510162748379412428131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46591006775165586274952087 69886510162748379412428131)
    ·
      refine ⟨104829765244122569118642197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69886510162748379412428131 104829765244122569118642197)
      ·
        refine ⟨4913895245818245427436353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104829765244122569118642197 4913895245818245427436353)
        ·
          refine ⟨3685421434363684070577265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4913895245818245427436353 3685421434363684070577265)
          ·
            refine ⟨2764066075772763052932949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3685421434363684070577265 2764066075772763052932949)
            ·
              refine ⟨16195699662731033513279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2764066075772763052932949 16195699662731033513279)
              ·
                rfl

theorem cell22_1277411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 9].length) (baseStart_1277411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277411 prefixEnd_1277411 := by exact prefixLift 1277411
  have htrace : WordTrace (prefixWord ++ tailWord_1277411) baseStart_1277411 baseEnd_1277411 := by
    simpa [prefixWord, tailWord_1277411, baseEnd_1277411] using wordTrace_append hprefix tailTrace_1277411
  have hstable : (prefixWord ++ tailWord_1277411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277411).length < 2 ^ (prefixWord ++ tailWord_1277411).sum := by decide
  have hdescent : baseEnd_1277411 < baseStart_1277411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277415 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 2, 3]
def baseStart_1277415 : Nat := 118140960795 + 1277415 * 2 ^ 59
def prefixEnd_1277415 : Nat := 4983230072969 + 3 ^ 40 * 1277415 * 2
def baseEnd_1277415 : Nat := 437285260175483227758521

theorem tailTrace_1277415 : CollatzResearch.WordTrace tailWord_1277415 prefixEnd_1277415 437285260175483227758521 := by
  unfold tailWord_1277415
  simp only [CollatzResearch.WordTrace]
  refine ⟨46591152667151094958097699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31060768444767396638731799 46591152667151094958097699)
  ·
    refine ⟨69886729000726642437146549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46591152667151094958097699 69886729000726642437146549)
    ·
      refine ⟨6551880843818122728482489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69886729000726642437146549 6551880843818122728482489)
      ·
        refine ⟨4913910632863592046361867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6551880843818122728482489 4913910632863592046361867)
        ·
          refine ⟨7370865949295388069542801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913910632863592046361867 7370865949295388069542801)
          ·
            refine ⟨5528149461971541052157101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7370865949295388069542801 5528149461971541052157101)
            ·
              refine ⟨2073056048239327894558913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5528149461971541052157101 2073056048239327894558913)
              ·
                refine ⟨1554792036179495920919185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073056048239327894558913 1554792036179495920919185)
                ·
                  refine ⟨1166094027134621940689389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1554792036179495920919185 1166094027134621940689389)
                  ·
                    refine ⟨437285260175483227758521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1166094027134621940689389 437285260175483227758521)
                    ·
                      rfl

theorem cell22_1277415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_1277415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277415 prefixEnd_1277415 := by exact prefixLift 1277415
  have htrace : WordTrace (prefixWord ++ tailWord_1277415) baseStart_1277415 baseEnd_1277415 := by
    simpa [prefixWord, tailWord_1277415, baseEnd_1277415] using wordTrace_append hprefix tailTrace_1277415
  have hstable : (prefixWord ++ tailWord_1277415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277415).length < 2 ^ (prefixWord ++ tailWord_1277415).sum := by decide
  have hdescent : baseEnd_1277415 < baseStart_1277415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277471 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 4, 5]
def baseStart_1277471 : Nat := 118140960795 + 1277471 * 2 ^ 59
def prefixEnd_1277471 : Nat := 4983230072969 + 3 ^ 40 * 1277471 * 2
def baseEnd_1277471 : Nat := 437304430119917748358349

theorem tailTrace_1277471 : CollatzResearch.WordTrace tailWord_1277471 prefixEnd_1277471 437304430119917748358349 := by
  unfold tailWord_1277471
  simp only [CollatzResearch.WordTrace]
  refine ⟨46593195154948216522136267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31062130103298811014757511 46593195154948216522136267)
  ·
    refine ⟨69889792732422324783204401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46593195154948216522136267 69889792732422324783204401)
    ·
      refine ⟨52417344549316743587403301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69889792732422324783204401 52417344549316743587403301)
      ·
        refine ⟨9828252102996889422638119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52417344549316743587403301 9828252102996889422638119)
        ·
          refine ⟨14742378154495334133957179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9828252102996889422638119 14742378154495334133957179)
          ·
            refine ⟨22113567231743001200935769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14742378154495334133957179 22113567231743001200935769)
            ·
              refine ⟨16585175423807250900701827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22113567231743001200935769 16585175423807250900701827)
              ·
                refine ⟨24877763135710876351052741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16585175423807250900701827 24877763135710876351052741)
                ·
                  refine ⟨4664580587945789315822389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24877763135710876351052741 4664580587945789315822389)
                  ·
                    refine ⟨437304430119917748358349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4664580587945789315822389 437304430119917748358349)
                    ·
                      rfl

theorem cell22_1277471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_1277471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277471 prefixEnd_1277471 := by exact prefixLift 1277471
  have htrace : WordTrace (prefixWord ++ tailWord_1277471) baseStart_1277471 baseEnd_1277471 := by
    simpa [prefixWord, tailWord_1277471, baseEnd_1277471] using wordTrace_append hprefix tailTrace_1277471
  have hstable : (prefixWord ++ tailWord_1277471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277471).length < 2 ^ (prefixWord ++ tailWord_1277471).sum := by decide
  have hdescent : baseEnd_1277471 < baseStart_1277471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277503 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 3, 4]
def baseStart_1277503 : Nat := 118140960795 + 1277503 * 2 ^ 59
def prefixEnd_1277503 : Nat := 4983230072969 + 3 ^ 40 * 1277503 * 2
def baseEnd_1277503 : Nat := 437315384373880331558251

theorem tailTrace_1277503 : CollatzResearch.WordTrace tailWord_1277503 prefixEnd_1277503 437315384373880331558251 := by
  unfold tailWord_1277503
  simp only [CollatzResearch.WordTrace]
  refine ⟨46594362290832285987301163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31062908193888190658200775 46594362290832285987301163)
  ·
    refine ⟨69891543436248428980951745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46594362290832285987301163 69891543436248428980951745)
    ·
      refine ⟨52418657577186321735713809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69891543436248428980951745 52418657577186321735713809)
      ·
        refine ⟨39313993182889741301785357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52418657577186321735713809 39313993182889741301785357)
        ·
          refine ⟨14742747443583652988169509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39313993182889741301785357 14742747443583652988169509)
          ·
            refine ⟨2764265145671934935281783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14742747443583652988169509 2764265145671934935281783)
            ·
              refine ⟨4146397718507902402922675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764265145671934935281783 4146397718507902402922675)
              ·
                refine ⟨6219596577761853604384013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146397718507902402922675 6219596577761853604384013)
                ·
                  refine ⟨2332348716660695101644005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6219596577761853604384013 2332348716660695101644005)
                  ·
                    refine ⟨437315384373880331558251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332348716660695101644005 437315384373880331558251)
                    ·
                      rfl

theorem cell22_1277503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_1277503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277503 prefixEnd_1277503 := by exact prefixLift 1277503
  have htrace : WordTrace (prefixWord ++ tailWord_1277503) baseStart_1277503 baseEnd_1277503 := by
    simpa [prefixWord, tailWord_1277503, baseEnd_1277503] using wordTrace_append hprefix tailTrace_1277503
  have hstable : (prefixWord ++ tailWord_1277503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277503).length < 2 ^ (prefixWord ++ tailWord_1277503).sum := by decide
  have hdescent : baseEnd_1277503 < baseStart_1277503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277520 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 1, 4]
def baseStart_1277520 : Nat := 118140960795 + 1277520 * 2 ^ 59
def prefixEnd_1277520 : Nat := 4983230072969 + 3 ^ 40 * 1277520 * 2
def baseEnd_1277520 : Nat := 437321203821297953883199

theorem tailTrace_1277520 : CollatzResearch.WordTrace tailWord_1277520 prefixEnd_1277520 437321203821297953883199 := by
  unfold tailWord_1277520
  simp only [CollatzResearch.WordTrace]
  refine ⟨23297491165885348945335007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31063321554513798593780009 23297491165885348945335007)
  ·
    refine ⟨34946236748828023418002511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23297491165885348945335007 34946236748828023418002511)
    ·
      refine ⟨52419355123242035127003767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34946236748828023418002511 52419355123242035127003767)
      ·
        refine ⟨78629032684863052690505651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52419355123242035127003767 78629032684863052690505651)
        ·
          refine ⟨117943549027294579035758477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78629032684863052690505651 117943549027294579035758477)
          ·
            refine ⟨44228830885235467138409429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117943549027294579035758477 44228830885235467138409429)
            ·
              refine ⟨1036613223872706261056471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44228830885235467138409429 1036613223872706261056471)
              ·
                refine ⟨1554919835809059391584707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036613223872706261056471 1554919835809059391584707)
                ·
                  refine ⟨2332379753713589087377061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554919835809059391584707 2332379753713589087377061)
                  ·
                    refine ⟨437321203821297953883199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332379753713589087377061 437321203821297953883199)
                    ·
                      rfl

theorem cell22_1277520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 1, 4].length) (baseStart_1277520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277520 prefixEnd_1277520 := by exact prefixLift 1277520
  have htrace : WordTrace (prefixWord ++ tailWord_1277520) baseStart_1277520 baseEnd_1277520 := by
    simpa [prefixWord, tailWord_1277520, baseEnd_1277520] using wordTrace_append hprefix tailTrace_1277520
  have hstable : (prefixWord ++ tailWord_1277520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277520).length < 2 ^ (prefixWord ++ tailWord_1277520).sum := by decide
  have hdescent : baseEnd_1277520 < baseStart_1277520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277563 : List Nat := [1, 1, 1, 1, 1, 4, 7, 6]
def baseStart_1277563 : Nat := 118140960795 + 1277563 * 2 ^ 59
def prefixEnd_1277563 : Nat := 4983230072969 + 3 ^ 40 * 1277563 * 2
def baseEnd_1277563 : Nat := 48592880400006686117563

theorem tailTrace_1277563 : CollatzResearch.WordTrace tailWord_1277563 prefixEnd_1277563 48592880400006686117563 := by
  unfold tailWord_1277563
  simp only [CollatzResearch.WordTrace]
  refine ⟨46596550670614916234485343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31064367113743277489656895 46596550670614916234485343)
  ·
    refine ⟨69894826005922374351728015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46596550670614916234485343 69894826005922374351728015)
    ·
      refine ⟨104842239008883561527592023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69894826005922374351728015 104842239008883561527592023)
      ·
        refine ⟨157263358513325342291388035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104842239008883561527592023 157263358513325342291388035)
        ·
          refine ⟨235895037769988013437082053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157263358513325342291388035 235895037769988013437082053)
          ·
            refine ⟨44230319581872752519452885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235895037769988013437082053 44230319581872752519452885)
            ·
              refine ⟨1036648115200142637174677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 44230319581872752519452885 1036648115200142637174677)
              ·
                refine ⟨48592880400006686117563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1036648115200142637174677 48592880400006686117563)
                ·
                  rfl

theorem cell22_1277563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 6].length) (baseStart_1277563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277563 prefixEnd_1277563 := by exact prefixLift 1277563
  have htrace : WordTrace (prefixWord ++ tailWord_1277563) baseStart_1277563 baseEnd_1277563 := by
    simpa [prefixWord, tailWord_1277563, baseEnd_1277563] using wordTrace_append hprefix tailTrace_1277563
  have hstable : (prefixWord ++ tailWord_1277563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277563).length < 2 ^ (prefixWord ++ tailWord_1277563).sum := by decide
  have hdescent : baseEnd_1277563 < baseStart_1277563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277565 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_1277565 : Nat := 118140960795 + 1277565 * 2 ^ 59
def prefixEnd_1277565 : Nat := 4983230072969 + 3 ^ 40 * 1277565 * 2
def baseEnd_1277565 : Nat := 437336608240932836508061

theorem tailTrace_1277565 : CollatzResearch.WordTrace tailWord_1277565 prefixEnd_1277565 437336608240932836508061 := by
  unfold tailWord_1277565
  simp only [CollatzResearch.WordTrace]
  refine ⟨46596623616607670576058149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31064415744405113717372099 46596623616607670576058149)
  ·
    refine ⟨8736866928113938233010903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46596623616607670576058149 8736866928113938233010903)
    ·
      refine ⟨13105300392170907349516355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8736866928113938233010903 13105300392170907349516355)
      ·
        refine ⟨19657950588256361024274533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13105300392170907349516355 19657950588256361024274533)
        ·
          refine ⟨3685865735298067692051475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19657950588256361024274533 3685865735298067692051475)
          ·
            refine ⟨5528798602947101538077213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685865735298067692051475 5528798602947101538077213)
            ·
              refine ⟨2073299476105163076778955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5528798602947101538077213 2073299476105163076778955)
              ·
                refine ⟨3109949214157744615168433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073299476105163076778955 3109949214157744615168433)
                ·
                  refine ⟨2332461910618308461376325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3109949214157744615168433 2332461910618308461376325)
                  ·
                    refine ⟨437336608240932836508061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332461910618308461376325 437336608240932836508061)
                    ·
                      rfl

theorem cell22_1277565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_1277565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277565 prefixEnd_1277565 := by exact prefixLift 1277565
  have htrace : WordTrace (prefixWord ++ tailWord_1277565) baseStart_1277565 baseEnd_1277565 := by
    simpa [prefixWord, tailWord_1277565, baseEnd_1277565] using wordTrace_append hprefix tailTrace_1277565
  have hstable : (prefixWord ++ tailWord_1277565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277565).length < 2 ^ (prefixWord ++ tailWord_1277565).sum := by decide
  have hdescent : baseEnd_1277565 < baseStart_1277565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277614 : List Nat := [4, 1, 4, 1, 2, 2, 2, 6]
def baseStart_1277614 : Nat := 118140960795 + 1277614 * 2 ^ 59
def prefixEnd_1277614 : Nat := 4983230072969 + 3 ^ 40 * 1277614 * 2
def baseEnd_1277614 : Nat := 48594820215812560225879

theorem tailTrace_1277614 : CollatzResearch.WordTrace tailWord_1277614 prefixEnd_1277614 48594820215812560225879 := by
  unfold tailWord_1277614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824801349178768993073987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31065607195620101296394597 5824801349178768993073987)
  ·
    refine ⟨8737202023768153489610981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5824801349178768993073987 8737202023768153489610981)
    ·
      refine ⟨1638225379456528779302059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8737202023768153489610981 1638225379456528779302059)
      ·
        refine ⟨2457338069184793168953089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638225379456528779302059 2457338069184793168953089)
        ·
          refine ⟨1843003551888594876714817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457338069184793168953089 1843003551888594876714817)
          ·
            refine ⟨1382252663916446157536113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1843003551888594876714817 1382252663916446157536113)
            ·
              refine ⟨1036689497937334618152085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382252663916446157536113 1036689497937334618152085)
              ·
                refine ⟨48594820215812560225879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1036689497937334618152085 48594820215812560225879)
                ·
                  rfl

theorem cell22_1277614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_1277614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277614 prefixEnd_1277614 := by exact prefixLift 1277614
  have htrace : WordTrace (prefixWord ++ tailWord_1277614) baseStart_1277614 baseEnd_1277614 := by
    simpa [prefixWord, tailWord_1277614, baseEnd_1277614] using wordTrace_append hprefix tailTrace_1277614
  have hstable : (prefixWord ++ tailWord_1277614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277614).length < 2 ^ (prefixWord ++ tailWord_1277614).sum := by decide
  have hdescent : baseEnd_1277614 < baseStart_1277614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277672 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1277672 : Nat := 118140960795 + 1277672 * 2 ^ 59
def prefixEnd_1277672 : Nat := 4983230072969 + 3 ^ 40 * 1277672 * 2
def baseEnd_1277672 : Nat := 437373236527620224082733

theorem tailTrace_1277672 : CollatzResearch.WordTrace tailWord_1277672 prefixEnd_1277672 437373236527620224082733 := by
  unfold tailWord_1277672
  simp only [CollatzResearch.WordTrace]
  refine ⟨23300263113610013925101635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31067017484813351900135513 23300263113610013925101635)
  ·
    refine ⟨34950394670415020887652453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23300263113610013925101635 34950394670415020887652453)
    ·
      refine ⟨6553199000702816416434835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34950394670415020887652453 6553199000702816416434835)
      ·
        refine ⟨9829798501054224624652253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6553199000702816416434835 9829798501054224624652253)
        ·
          refine ⟨3686174437895334234244595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9829798501054224624652253 3686174437895334234244595)
          ·
            refine ⟨5529261656843001351366893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686174437895334234244595 5529261656843001351366893)
            ·
              refine ⟨2073473121316125506762585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5529261656843001351366893 2073473121316125506762585)
              ·
                refine ⟨1555104840987094130071939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073473121316125506762585 1555104840987094130071939)
                ·
                  refine ⟨2332657261480641195107909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555104840987094130071939 2332657261480641195107909)
                  ·
                    refine ⟨437373236527620224082733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332657261480641195107909 437373236527620224082733)
                    ·
                      rfl

theorem cell22_1277672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1277672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277672 prefixEnd_1277672 := by exact prefixLift 1277672
  have htrace : WordTrace (prefixWord ++ tailWord_1277672) baseStart_1277672 baseEnd_1277672 := by
    simpa [prefixWord, tailWord_1277672, baseEnd_1277672] using wordTrace_append hprefix tailTrace_1277672
  have hstable : (prefixWord ++ tailWord_1277672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277672).length < 2 ^ (prefixWord ++ tailWord_1277672).sum := by decide
  have hdescent : baseEnd_1277672 < baseStart_1277672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277683 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 1, 6]
def baseStart_1277683 : Nat := 118140960795 + 1277683 * 2 ^ 59
def prefixEnd_1277683 : Nat := 4983230072969 + 3 ^ 40 * 1277683 * 2
def baseEnd_1277683 : Nat := 437377002052419862057699

theorem tailTrace_1277683 : CollatzResearch.WordTrace tailWord_1277683 prefixEnd_1277683 437377002052419862057699 := by
  unfold tailWord_1277683
  simp only [CollatzResearch.WordTrace]
  refine ⟨46600927430180176728853703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31067284953453451152569135 46600927430180176728853703)
  ·
    refine ⟨69901391145270265093280555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46600927430180176728853703 69901391145270265093280555)
    ·
      refine ⟨104852086717905397639920833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69901391145270265093280555 104852086717905397639920833)
      ·
        refine ⟨78639065038429048229940625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104852086717905397639920833 78639065038429048229940625)
        ·
          refine ⟨58979298778821786172455469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78639065038429048229940625 58979298778821786172455469)
          ·
            refine ⟨22117237042058169814670801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58979298778821786172455469 22117237042058169814670801)
            ·
              refine ⟨16587927781543627361003101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22117237042058169814670801 16587927781543627361003101)
              ·
                refine ⟨6220472918078860260376163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16587927781543627361003101 6220472918078860260376163)
                ·
                  refine ⟨9330709377118290390564245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6220472918078860260376163 9330709377118290390564245)
                  ·
                    refine ⟨437377002052419862057699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9330709377118290390564245 437377002052419862057699)
                    ·
                      rfl

theorem cell22_1277683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_1277683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277683 prefixEnd_1277683 := by exact prefixLift 1277683
  have htrace : WordTrace (prefixWord ++ tailWord_1277683) baseStart_1277683 baseEnd_1277683 := by
    simpa [prefixWord, tailWord_1277683, baseEnd_1277683] using wordTrace_append hprefix tailTrace_1277683
  have hstable : (prefixWord ++ tailWord_1277683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277683).length < 2 ^ (prefixWord ++ tailWord_1277683).sum := by decide
  have hdescent : baseEnd_1277683 < baseStart_1277683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277713 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1277713 : Nat := 118140960795 + 1277713 * 2 ^ 59
def prefixEnd_1277713 : Nat := 4983230072969 + 3 ^ 40 * 1277713 * 2
def baseEnd_1277713 : Nat := 437387271665509783807607

theorem tailTrace_1277713 : CollatzResearch.WordTrace tailWord_1277713 prefixEnd_1277713 437387271665509783807607 := by
  unfold tailWord_1277713
  simp only [CollatzResearch.WordTrace]
  refine ⟨46602021620071491852445793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31068014413380994568297195 46602021620071491852445793)
  ·
    refine ⟨34951516215053618889334345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46602021620071491852445793 34951516215053618889334345)
    ·
      refine ⟨26213637161290214167000759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34951516215053618889334345 26213637161290214167000759)
      ·
        refine ⟨39320455741935321250501139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26213637161290214167000759 39320455741935321250501139)
        ·
          refine ⟨58980683612902981875751709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39320455741935321250501139 58980683612902981875751709)
          ·
            refine ⟨22117756354838618203406891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58980683612902981875751709 22117756354838618203406891)
            ·
              refine ⟨33176634532257927305110337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22117756354838618203406891 33176634532257927305110337)
              ·
                refine ⟨24882475899193445478832753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33176634532257927305110337 24882475899193445478832753)
                ·
                  refine ⟨18661856924395084109124565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24882475899193445478832753 18661856924395084109124565)
                  ·
                    refine ⟨437387271665509783807607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18661856924395084109124565 437387271665509783807607)
                    ·
                      rfl

theorem cell22_1277713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1277713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277713 prefixEnd_1277713 := by exact prefixLift 1277713
  have htrace : WordTrace (prefixWord ++ tailWord_1277713) baseStart_1277713 baseEnd_1277713 := by
    simpa [prefixWord, tailWord_1277713, baseEnd_1277713] using wordTrace_append hprefix tailTrace_1277713
  have hstable : (prefixWord ++ tailWord_1277713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277713).length < 2 ^ (prefixWord ++ tailWord_1277713).sum := by decide
  have hdescent : baseEnd_1277713 < baseStart_1277713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277732 : List Nat := [2, 3, 1, 3, 2, 2, 3, 6]
def baseStart_1277732 : Nat := 118140960795 + 1277732 * 2 ^ 59
def prefixEnd_1277732 : Nat := 4983230072969 + 3 ^ 40 * 1277732 * 2
def baseEnd_1277732 : Nat := 48599308417088896398061

theorem tailTrace_1277732 : CollatzResearch.WordTrace tailWord_1277732 prefixEnd_1277732 48599308417088896398061 := by
  unfold tailWord_1277732
  simp only [CollatzResearch.WordTrace]
  refine ⟨23301357303501329048693725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31068476404668438731591633 23301357303501329048693725)
  ·
    refine ⟨8738008988812998393260147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23301357303501329048693725 8738008988812998393260147)
    ·
      refine ⟨13107013483219497589890221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8738008988812998393260147 13107013483219497589890221)
      ·
        refine ⟨4915130056207311596208833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13107013483219497589890221 4915130056207311596208833)
        ·
          refine ⟨3686347542155483697156625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4915130056207311596208833 3686347542155483697156625)
          ·
            refine ⟨2764760656616612772867469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3686347542155483697156625 2764760656616612772867469)
            ·
              refine ⟨1036785246231229789825301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2764760656616612772867469 1036785246231229789825301)
              ·
                refine ⟨48599308417088896398061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1036785246231229789825301 48599308417088896398061)
                ·
                  rfl

theorem cell22_1277732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 6].length) (baseStart_1277732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277732 prefixEnd_1277732 := by exact prefixLift 1277732
  have htrace : WordTrace (prefixWord ++ tailWord_1277732) baseStart_1277732 baseEnd_1277732 := by
    simpa [prefixWord, tailWord_1277732, baseEnd_1277732] using wordTrace_append hprefix tailTrace_1277732
  have hstable : (prefixWord ++ tailWord_1277732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277732).length < 2 ^ (prefixWord ++ tailWord_1277732).sum := by decide
  have hdescent : baseEnd_1277732 < baseStart_1277732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277743 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 9]
def baseStart_1277743 : Nat := 118140960795 + 1277743 * 2 ^ 59
def prefixEnd_1277743 : Nat := 4983230072969 + 3 ^ 40 * 1277743 * 2
def baseEnd_1277743 : Nat := 145799180426199901852505

theorem tailTrace_1277743 : CollatzResearch.WordTrace tailWord_1277743 prefixEnd_1277743 145799180426199901852505 := by
  unfold tailWord_1277743
  simp only [CollatzResearch.WordTrace]
  refine ⟨46603115809962806976037883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31068743873308537984025255 46603115809962806976037883)
  ·
    refine ⟨69904673714944210464056825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46603115809962806976037883 69904673714944210464056825)
    ·
      refine ⟨52428505286208157848042619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69904673714944210464056825 52428505286208157848042619)
      ·
        refine ⟨78642757929312236772063929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52428505286208157848042619 78642757929312236772063929)
        ·
          refine ⟨58982068446984177579047947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78642757929312236772063929 58982068446984177579047947)
          ·
            refine ⟨88473102670476266368571921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58982068446984177579047947 88473102670476266368571921)
            ·
              refine ⟨66354827002857199776428941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88473102670476266368571921 66354827002857199776428941)
              ·
                refine ⟨24883060126071449916160853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66354827002857199776428941 24883060126071449916160853)
                ·
                  refine ⟨145799180426199901852505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24883060126071449916160853 145799180426199901852505)
                  ·
                    rfl

theorem cell22_1277743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 9].length) (baseStart_1277743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277743 prefixEnd_1277743 := by exact prefixLift 1277743
  have htrace : WordTrace (prefixWord ++ tailWord_1277743) baseStart_1277743 baseEnd_1277743 := by
    simpa [prefixWord, tailWord_1277743, baseEnd_1277743] using wordTrace_append hprefix tailTrace_1277743
  have hstable : (prefixWord ++ tailWord_1277743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277743).length < 2 ^ (prefixWord ++ tailWord_1277743).sum := by decide
  have hdescent : baseEnd_1277743 < baseStart_1277743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277753 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 2, 3]
def baseStart_1277753 : Nat := 118140960795 + 1277753 * 2 ^ 59
def prefixEnd_1277753 : Nat := 4983230072969 + 3 ^ 40 * 1277753 * 2
def baseEnd_1277753 : Nat := 437400964482963012807485

theorem tailTrace_1277753 : CollatzResearch.WordTrace tailWord_1277753 prefixEnd_1277753 437400964482963012807485 := by
  unfold tailWord_1277753
  simp only [CollatzResearch.WordTrace]
  refine ⟨46603480539926578683901913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31068987026617719122601275 46603480539926578683901913)
  ·
    refine ⟨34952610404944934012926435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46603480539926578683901913 34952610404944934012926435)
    ·
      refine ⟨52428915607417401019389653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34952610404944934012926435 52428915607417401019389653)
      ·
        refine ⟨1228802709548845336391945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 52428915607417401019389653 1228802709548845336391945)
        ·
          refine ⟨921602032161634002293959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1228802709548845336391945 921602032161634002293959)
          ·
            refine ⟨1382403048242451003440939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921602032161634002293959 1382403048242451003440939)
            ·
              refine ⟨2073604572363676505161409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382403048242451003440939 2073604572363676505161409)
              ·
                refine ⟨1555203429272757378871057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2073604572363676505161409 1555203429272757378871057)
                ·
                  refine ⟨1166402571954568034153293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555203429272757378871057 1166402571954568034153293)
                  ·
                    refine ⟨437400964482963012807485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1166402571954568034153293 437400964482963012807485)
                    ·
                      rfl

theorem cell22_1277753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 3].length) (baseStart_1277753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277753 prefixEnd_1277753 := by exact prefixLift 1277753
  have htrace : WordTrace (prefixWord ++ tailWord_1277753) baseStart_1277753 baseEnd_1277753 := by
    simpa [prefixWord, tailWord_1277753, baseEnd_1277753] using wordTrace_append hprefix tailTrace_1277753
  have hstable : (prefixWord ++ tailWord_1277753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277753).length < 2 ^ (prefixWord ++ tailWord_1277753).sum := by decide
  have hdescent : baseEnd_1277753 < baseStart_1277753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277805 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1277805 : Nat := 118140960795 + 1277805 * 2 ^ 59
def prefixEnd_1277805 : Nat := 4983230072969 + 3 ^ 40 * 1277805 * 2
def baseEnd_1277805 : Nat := 145806255048550736835775

theorem tailTrace_1277805 : CollatzResearch.WordTrace tailWord_1277805 prefixEnd_1277805 145806255048550736835775 := by
  unfold tailWord_1277805
  simp only [CollatzResearch.WordTrace]
  refine ⟨46605377135738191564794869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31070251423825461043196579 46605377135738191564794869)
  ·
    refine ⟨4369254106475455459199519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46605377135738191564794869 4369254106475455459199519)
    ·
      refine ⟨6553881159713183188799279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369254106475455459199519 6553881159713183188799279)
      ·
        refine ⟨9830821739569774783198919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6553881159713183188799279 9830821739569774783198919)
        ·
          refine ⟨14746232609354662174798379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830821739569774783198919 14746232609354662174798379)
          ·
            refine ⟨22119348914031993262197569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14746232609354662174798379 22119348914031993262197569)
            ·
              refine ⟨16589511685523994946648177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22119348914031993262197569 16589511685523994946648177)
              ·
                refine ⟨12442133764142996209986133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16589511685523994946648177 12442133764142996209986133)
                ·
                  refine ⟨145806255048550736835775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12442133764142996209986133 145806255048550736835775)
                  ·
                    rfl

theorem cell22_1277805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1277805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277805 prefixEnd_1277805 := by exact prefixLift 1277805
  have htrace : WordTrace (prefixWord ++ tailWord_1277805) baseStart_1277805 baseEnd_1277805 := by
    simpa [prefixWord, tailWord_1277805, baseEnd_1277805] using wordTrace_append hprefix tailTrace_1277805
  have hstable : (prefixWord ++ tailWord_1277805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277805).length < 2 ^ (prefixWord ++ tailWord_1277805).sum := by decide
  have hdescent : baseEnd_1277805 < baseStart_1277805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277835 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 6, 4]
def baseStart_1277835 : Nat := 118140960795 + 1277835 * 2 ^ 59
def prefixEnd_1277835 : Nat := 4983230072969 + 3 ^ 40 * 1277835 * 2
def baseEnd_1277835 : Nat := 437429034758742132257233

theorem tailTrace_1277835 : CollatzResearch.WordTrace tailWord_1277835 prefixEnd_1277835 437429034758742132257233 := by
  unfold tailWord_1277835
  simp only [CollatzResearch.WordTrace]
  refine ⟨46606471325629506688386959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31070980883753004458924639 46606471325629506688386959)
  ·
    refine ⟨69909706988444260032580439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46606471325629506688386959 69909706988444260032580439)
    ·
      refine ⟨104864560482666390048870659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69909706988444260032580439 104864560482666390048870659)
      ·
        refine ⟨157296840723999585073305989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104864560482666390048870659 157296840723999585073305989)
        ·
          refine ⟨29493157635749922201244873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157296840723999585073305989 29493157635749922201244873)
          ·
            refine ⟨22119868226812441650933655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29493157635749922201244873 22119868226812441650933655)
            ·
              refine ⟨33179802340218662476400483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22119868226812441650933655 33179802340218662476400483)
              ·
                refine ⟨49769703510327993714600725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33179802340218662476400483 49769703510327993714600725)
                ·
                  refine ⟨2332954852046624705371909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49769703510327993714600725 2332954852046624705371909)
                  ·
                    refine ⟨437429034758742132257233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2332954852046624705371909 437429034758742132257233)
                    ·
                      rfl

theorem cell22_1277835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 4].length) (baseStart_1277835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277835 prefixEnd_1277835 := by exact prefixLift 1277835
  have htrace : WordTrace (prefixWord ++ tailWord_1277835) baseStart_1277835 baseEnd_1277835 := by
    simpa [prefixWord, tailWord_1277835, baseEnd_1277835] using wordTrace_append hprefix tailTrace_1277835
  have hstable : (prefixWord ++ tailWord_1277835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277835).length < 2 ^ (prefixWord ++ tailWord_1277835).sum := by decide
  have hdescent : baseEnd_1277835 < baseStart_1277835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277880 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1277880 : Nat := 118140960795 + 1277880 * 2 ^ 59
def prefixEnd_1277880 : Nat := 4983230072969 + 3 ^ 40 * 1277880 * 2
def baseEnd_1277880 : Nat := 437444439178377014882095

theorem tailTrace_1277880 : CollatzResearch.WordTrace tailWord_1277880 prefixEnd_1277880 437444439178377014882095 := by
  unfold tailWord_1277880
  simp only [CollatzResearch.WordTrace]
  refine ⟨23304056305233239686887547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31072075073644319582516729 23304056305233239686887547)
  ·
    refine ⟨34956084457849859530331321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23304056305233239686887547 34956084457849859530331321)
    ·
      refine ⟨26217063343387394647748491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34956084457849859530331321 26217063343387394647748491)
      ·
        refine ⟨39325595015081091971622737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26217063343387394647748491 39325595015081091971622737)
        ·
          refine ⟨29494196261310818978717053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39325595015081091971622737 29494196261310818978717053)
          ·
            refine ⟨11060323597991557117018895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29494196261310818978717053 11060323597991557117018895)
            ·
              refine ⟨16590485396987335675528343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11060323597991557117018895 16590485396987335675528343)
              ·
                refine ⟨24885728095481003513292515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16590485396987335675528343 24885728095481003513292515)
                ·
                  refine ⟨37328592143221505269938773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24885728095481003513292515 37328592143221505269938773)
                  ·
                    refine ⟨437444439178377014882095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37328592143221505269938773 437444439178377014882095)
                    ·
                      rfl

theorem cell22_1277880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1277880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277880 prefixEnd_1277880 := by exact prefixLift 1277880
  have htrace : WordTrace (prefixWord ++ tailWord_1277880) baseStart_1277880 baseEnd_1277880 := by
    simpa [prefixWord, tailWord_1277880, baseEnd_1277880] using wordTrace_append hprefix tailTrace_1277880
  have hstable : (prefixWord ++ tailWord_1277880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277880).length < 2 ^ (prefixWord ++ tailWord_1277880).sum := by decide
  have hdescent : baseEnd_1277880 < baseStart_1277880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277895 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 9]
def baseStart_1277895 : Nat := 118140960795 + 1277895 * 2 ^ 59
def prefixEnd_1277895 : Nat := 4983230072969 + 3 ^ 40 * 1277895 * 2
def baseEnd_1277895 : Nat := 145816524661640658585683

theorem tailTrace_1277895 : CollatzResearch.WordTrace tailWord_1277895 prefixEnd_1277895 145816524661640658585683 := by
  unfold tailWord_1277895
  simp only [CollatzResearch.WordTrace]
  refine ⟨46608659705412136935571139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31072439803608091290380759 46608659705412136935571139)
  ·
    refine ⟨69912989558118205403356709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46608659705412136935571139 69912989558118205403356709)
    ·
      refine ⟨13108685542147163513129383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69912989558118205403356709 13108685542147163513129383)
      ·
        refine ⟨19663028313220745269694075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13108685542147163513129383 19663028313220745269694075)
        ·
          refine ⟨29494542469831117904541113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19663028313220745269694075 29494542469831117904541113)
          ·
            refine ⟨22120906852373338428405835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29494542469831117904541113 22120906852373338428405835)
            ·
              refine ⟨33181360278560007642608753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22120906852373338428405835 33181360278560007642608753)
              ·
                refine ⟨24886020208920005731956565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33181360278560007642608753 24886020208920005731956565)
                ·
                  refine ⟨145816524661640658585683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24886020208920005731956565 145816524661640658585683)
                  ·
                    rfl

theorem cell22_1277895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 9].length) (baseStart_1277895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277895 prefixEnd_1277895 := by exact prefixLift 1277895
  have htrace : WordTrace (prefixWord ++ tailWord_1277895) baseStart_1277895 baseEnd_1277895 := by
    simpa [prefixWord, tailWord_1277895, baseEnd_1277895] using wordTrace_append hprefix tailTrace_1277895
  have hstable : (prefixWord ++ tailWord_1277895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277895).length < 2 ^ (prefixWord ++ tailWord_1277895).sum := by decide
  have hdescent : baseEnd_1277895 < baseStart_1277895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277933 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_1277933 : Nat := 118140960795 + 1277933 * 2 ^ 59
def prefixEnd_1277933 : Nat := 4983230072969 + 3 ^ 40 * 1277933 * 2
def baseEnd_1277933 : Nat := 437462582161502543306933

theorem tailTrace_1277933 : CollatzResearch.WordTrace tailWord_1277933 prefixEnd_1277933 437462582161502543306933 := by
  unfold tailWord_1277933
  simp only [CollatzResearch.WordTrace]
  refine ⟨46610045679274469425454453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31073363786182979616969635 46610045679274469425454453)
  ·
    refine ⟨4369691782431981508636355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46610045679274469425454453 4369691782431981508636355)
    ·
      refine ⟨6554537673647972262954533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369691782431981508636355 6554537673647972262954533)
      ·
        refine ⟨1228975813808994799303975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6554537673647972262954533 1228975813808994799303975)
        ·
          refine ⟨1843463720713492198955963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228975813808994799303975 1843463720713492198955963)
          ·
            refine ⟨2765195581070238298433945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843463720713492198955963 2765195581070238298433945)
            ·
              refine ⟨2073896685802678723825459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765195581070238298433945 2073896685802678723825459)
              ·
                refine ⟨3110845028704018085738189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2073896685802678723825459 3110845028704018085738189)
                ·
                  refine ⟨1166566885764006782151821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3110845028704018085738189 1166566885764006782151821)
                  ·
                    refine ⟨437462582161502543306933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1166566885764006782151821 437462582161502543306933)
                    ·
                      rfl

theorem cell22_1277933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_1277933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277933 prefixEnd_1277933 := by exact prefixLift 1277933
  have htrace : WordTrace (prefixWord ++ tailWord_1277933) baseStart_1277933 baseEnd_1277933 := by
    simpa [prefixWord, tailWord_1277933, baseEnd_1277933] using wordTrace_append hprefix tailTrace_1277933
  have hstable : (prefixWord ++ tailWord_1277933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277933).length < 2 ^ (prefixWord ++ tailWord_1277933).sum := by decide
  have hdescent : baseEnd_1277933 < baseStart_1277933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277957 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 6]
def baseStart_1277957 : Nat := 118140960795 + 1277957 * 2 ^ 59
def prefixEnd_1277957 : Nat := 4983230072969 + 3 ^ 40 * 1277957 * 2
def baseEnd_1277957 : Nat := 145823599283991493568953

theorem tailTrace_1277957 : CollatzResearch.WordTrace tailWord_1277957 prefixEnd_1277957 145823599283991493568953 := by
  unfold tailWord_1277957
  simp only [CollatzResearch.WordTrace]
  refine ⟨46610921031187521524328125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31073947354125014349552083 46610921031187521524328125)
  ·
    refine ⟨17479095386695320571623047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46610921031187521524328125 17479095386695320571623047)
    ·
      refine ⟨26218643080042980857434571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17479095386695320571623047 26218643080042980857434571)
      ·
        refine ⟨39327964620064471286151857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26218643080042980857434571 39327964620064471286151857)
        ·
          refine ⟨29495973465048353464613893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39327964620064471286151857 29495973465048353464613893)
          ·
            refine ⟨5530495024696566274615105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29495973465048353464613893 5530495024696566274615105)
            ·
              refine ⟨4147871268522424705961329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5530495024696566274615105 4147871268522424705961329)
              ·
                refine ⟨3110903451391818529470997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4147871268522424705961329 3110903451391818529470997)
                ·
                  refine ⟨145823599283991493568953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3110903451391818529470997 145823599283991493568953)
                  ·
                    rfl

theorem cell22_1277957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_1277957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277957 prefixEnd_1277957 := by exact prefixLift 1277957
  have htrace : WordTrace (prefixWord ++ tailWord_1277957) baseStart_1277957 baseEnd_1277957 := by
    simpa [prefixWord, tailWord_1277957, baseEnd_1277957] using wordTrace_append hprefix tailTrace_1277957
  have hstable : (prefixWord ++ tailWord_1277957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277957).length < 2 ^ (prefixWord ++ tailWord_1277957).sum := by decide
  have hdescent : baseEnd_1277957 < baseStart_1277957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277959 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1277959 : Nat := 118140960795 + 1277959 * 2 ^ 59
def prefixEnd_1277959 : Nat := 4983230072969 + 3 ^ 40 * 1277959 * 2
def baseEnd_1277959 : Nat := 437471482492847142156853

theorem tailTrace_1277959 : CollatzResearch.WordTrace tailWord_1277959 prefixEnd_1277959 437471482492847142156853 := by
  unfold tailWord_1277959
  simp only [CollatzResearch.WordTrace]
  refine ⟨46610993977180275865900931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31073995984786850577267287 46610993977180275865900931)
  ·
    refine ⟨69916490965770413798851397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46610993977180275865900931 69916490965770413798851397)
    ·
      refine ⟨13109342056081952587284637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69916490965770413798851397 13109342056081952587284637)
      ·
        refine ⟨4916003271030732220231739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13109342056081952587284637 4916003271030732220231739)
        ·
          refine ⟨7374004906546098330347609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4916003271030732220231739 7374004906546098330347609)
          ·
            refine ⟨5530503679909573747760707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7374004906546098330347609 5530503679909573747760707)
            ·
              refine ⟨8295755519864360621641061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5530503679909573747760707 8295755519864360621641061)
              ·
                refine ⟨1555454159974567616557699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8295755519864360621641061 1555454159974567616557699)
                ·
                  refine ⟨2333181239961851424836549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555454159974567616557699 2333181239961851424836549)
                  ·
                    refine ⟨437471482492847142156853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2333181239961851424836549 437471482492847142156853)
                    ·
                      rfl

theorem cell22_1277959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1277959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277959 prefixEnd_1277959 := by exact prefixLift 1277959
  have htrace : WordTrace (prefixWord ++ tailWord_1277959) baseStart_1277959 baseEnd_1277959 := by
    simpa [prefixWord, tailWord_1277959, baseEnd_1277959] using wordTrace_append hprefix tailTrace_1277959
  have hstable : (prefixWord ++ tailWord_1277959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277959).length < 2 ^ (prefixWord ++ tailWord_1277959).sum := by decide
  have hdescent : baseEnd_1277959 < baseStart_1277959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1277989 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_1277989 : Nat := 118140960795 + 1277989 * 2 ^ 59
def prefixEnd_1277989 : Nat := 4983230072969 + 3 ^ 40 * 1277989 * 2
def baseEnd_1277989 : Nat := 437481752105937063906761

theorem tailTrace_1277989 : CollatzResearch.WordTrace tailWord_1277989 prefixEnd_1277989 437481752105937063906761 := by
  unfold tailWord_1277989
  simp only [CollatzResearch.WordTrace]
  refine ⟨46612088167071590989493021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31074725444714393992995347 46612088167071590989493021)
  ·
    refine ⟨17479533062651846621059883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46612088167071590989493021 17479533062651846621059883)
    ·
      refine ⟨26219299593977769931589825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17479533062651846621059883 26219299593977769931589825)
      ·
        refine ⟨19664474695483327448692369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26219299593977769931589825 19664474695483327448692369)
        ·
          refine ⟨14748356021612495586519277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19664474695483327448692369 14748356021612495586519277)
          ·
            refine ⟨5530633508104685844944729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14748356021612495586519277 5530633508104685844944729)
            ·
              refine ⟨4147975131078514383708547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5530633508104685844944729 4147975131078514383708547)
              ·
                refine ⟨6221962696617771575562821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4147975131078514383708547 6221962696617771575562821)
                ·
                  refine ⟨1166618005615832170418029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6221962696617771575562821 1166618005615832170418029)
                  ·
                    refine ⟨437481752105937063906761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1166618005615832170418029 437481752105937063906761)
                    ·
                      rfl

theorem cell22_1277989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_1277989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1277989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1277989 prefixEnd_1277989 := by exact prefixLift 1277989
  have htrace : WordTrace (prefixWord ++ tailWord_1277989) baseStart_1277989 baseEnd_1277989 := by
    simpa [prefixWord, tailWord_1277989, baseEnd_1277989] using wordTrace_append hprefix tailTrace_1277989
  have hstable : (prefixWord ++ tailWord_1277989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1277989).length < 2 ^ (prefixWord ++ tailWord_1277989).sum := by decide
  have hdescent : baseEnd_1277989 < baseStart_1277989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1277989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278002 : List Nat := [3, 2, 1, 1, 2, 3, 1, 9]
def baseStart_1278002 : Nat := 118140960795 + 1278002 * 2 ^ 59
def prefixEnd_1278002 : Nat := 4983230072969 + 3 ^ 40 * 1278002 * 2
def baseEnd_1278002 : Nat := 48609578030178818147969

theorem tailTrace_1278002 : CollatzResearch.WordTrace tailWord_1278002 prefixEnd_1278002 48609578030178818147969 := by
  unfold tailWord_1278002
  simp only [CollatzResearch.WordTrace]
  refine ⟨11653140579006123552429065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31075041544016329473144173 11653140579006123552429065)
  ·
    refine ⟨8739855434254592664321799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11653140579006123552429065 8739855434254592664321799)
    ·
      refine ⟨13109783151381888996482699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8739855434254592664321799 13109783151381888996482699)
      ·
        refine ⟨19664674727072833494724049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13109783151381888996482699 19664674727072833494724049)
        ·
          refine ⟨14748506045304625121043037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19664674727072833494724049 14748506045304625121043037)
          ·
            refine ⟨5530689766989234420391139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14748506045304625121043037 5530689766989234420391139)
            ·
              refine ⟨8296034650483851630586709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5530689766989234420391139 8296034650483851630586709)
              ·
                refine ⟨48609578030178818147969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8296034650483851630586709 48609578030178818147969)
                ·
                  rfl

theorem cell22_1278002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_1278002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278002 prefixEnd_1278002 := by exact prefixLift 1278002
  have htrace : WordTrace (prefixWord ++ tailWord_1278002) baseStart_1278002 baseEnd_1278002 := by
    simpa [prefixWord, tailWord_1278002, baseEnd_1278002] using wordTrace_append hprefix tailTrace_1278002
  have hstable : (prefixWord ++ tailWord_1278002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278002).length < 2 ^ (prefixWord ++ tailWord_1278002).sum := by decide
  have hdescent : baseEnd_1278002 < baseStart_1278002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278038 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1278038 : Nat := 118140960795 + 1278038 * 2 ^ 59
def prefixEnd_1278038 : Nat := 4983230072969 + 3 ^ 40 * 1278038 * 2
def baseEnd_1278038 : Nat := 437498525807317269431611

theorem tailTrace_1278038 : CollatzResearch.WordTrace tailWord_1278038 prefixEnd_1278038 437498525807317269431611 := by
  unfold tailWord_1278038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2913367208993379522376673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31075916895929381572017845 2913367208993379522376673)
  ·
    refine ⟨2185025406745034641782505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2913367208993379522376673 2185025406745034641782505)
    ·
      refine ⟨1638769055058775981336879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2185025406745034641782505 1638769055058775981336879)
      ·
        refine ⟨2458153582588163972005319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638769055058775981336879 2458153582588163972005319)
        ·
          refine ⟨3687230373882245958007979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458153582588163972005319 3687230373882245958007979)
          ·
            refine ⟨5530845560823368937011969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687230373882245958007979 5530845560823368937011969)
            ·
              refine ⟨4148134170617526702758977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5530845560823368937011969 4148134170617526702758977)
              ·
                refine ⟨3111100627963145027069233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4148134170617526702758977 3111100627963145027069233)
                ·
                  refine ⟨2333325470972358770301925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3111100627963145027069233 2333325470972358770301925)
                  ·
                    refine ⟨437498525807317269431611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2333325470972358770301925 437498525807317269431611)
                    ·
                      rfl

theorem cell22_1278038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1278038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278038 prefixEnd_1278038 := by exact prefixLift 1278038
  have htrace : WordTrace (prefixWord ++ tailWord_1278038) baseStart_1278038 baseEnd_1278038 := by
    simpa [prefixWord, tailWord_1278038, baseEnd_1278038] using wordTrace_append hprefix tailTrace_1278038
  have hstable : (prefixWord ++ tailWord_1278038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278038).length < 2 ^ (prefixWord ++ tailWord_1278038).sum := by decide
  have hdescent : baseEnd_1278038 < baseStart_1278038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278064 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 5]
def baseStart_1278064 : Nat := 118140960795 + 1278064 * 2 ^ 59
def prefixEnd_1278064 : Nat := 4983230072969 + 3 ^ 40 * 1278064 * 2
def baseEnd_1278064 : Nat := 145835808712887289427177

theorem tailTrace_1278064 : CollatzResearch.WordTrace tailWord_1278064 prefixEnd_1278064 145835808712887289427177 := by
  unfold tailWord_1278064
  simp only [CollatzResearch.WordTrace]
  refine ⟨23307411820899939399236623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31076549094533252532315497 23307411820899939399236623)
  ·
    refine ⟨34961117731349909098854935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23307411820899939399236623 34961117731349909098854935)
    ·
      refine ⟨52441676597024863648282403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34961117731349909098854935 52441676597024863648282403)
      ·
        refine ⟨78662514895537295472423605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52441676597024863648282403 78662514895537295472423605)
        ·
          refine ⟨7374610771456621450539713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78662514895537295472423605 7374610771456621450539713)
          ·
            refine ⟨5530958078592466087904785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7374610771456621450539713 5530958078592466087904785)
            ·
              refine ⟨4148218558944349565928589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5530958078592466087904785 4148218558944349565928589)
              ·
                refine ⟨1555581959604131087223221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4148218558944349565928589 1555581959604131087223221)
                ·
                  refine ⟨145835808712887289427177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1555581959604131087223221 145835808712887289427177)
                  ·
                    rfl

theorem cell22_1278064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_1278064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278064 prefixEnd_1278064 := by exact prefixLift 1278064
  have htrace : WordTrace (prefixWord ++ tailWord_1278064) baseStart_1278064 baseEnd_1278064 := by
    simpa [prefixWord, tailWord_1278064, baseEnd_1278064] using wordTrace_append hprefix tailTrace_1278064
  have hstable : (prefixWord ++ tailWord_1278064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278064).length < 2 ^ (prefixWord ++ tailWord_1278064).sum := by decide
  have hdescent : baseEnd_1278064 < baseStart_1278064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278109 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 6]
def baseStart_1278109 : Nat := 118140960795 + 1278109 * 2 ^ 59
def prefixEnd_1278109 : Nat := 4983230072969 + 3 ^ 40 * 1278109 * 2
def baseEnd_1278109 : Nat := 145840943519432250302131

theorem tailTrace_1278109 : CollatzResearch.WordTrace tailWord_1278109 prefixEnd_1278109 145840943519432250302131 := by
  unfold tailWord_1278109
  simp only [CollatzResearch.WordTrace]
  refine ⟨46616464926636851483861381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31077643284424567655907587 46616464926636851483861381)
  ·
    refine ⟨8740587173744409653224009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46616464926636851483861381 8740587173744409653224009)
    ·
      refine ⟨6555440380308307239918007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8740587173744409653224009 6555440380308307239918007)
      ·
        refine ⟨9833160570462460859877011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6555440380308307239918007 9833160570462460859877011)
        ·
          refine ⟨14749740855693691289815517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9833160570462460859877011 14749740855693691289815517)
          ·
            refine ⟨5531152820885134233680819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14749740855693691289815517 5531152820885134233680819)
            ·
              refine ⟨8296729231327701350521229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531152820885134233680819 8296729231327701350521229)
              ·
                refine ⟨3111273461747888006445461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8296729231327701350521229 3111273461747888006445461)
                ·
                  refine ⟨145840943519432250302131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3111273461747888006445461 145840943519432250302131)
                  ·
                    rfl

theorem cell22_1278109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_1278109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278109 prefixEnd_1278109 := by exact prefixLift 1278109
  have htrace : WordTrace (prefixWord ++ tailWord_1278109) baseStart_1278109 baseEnd_1278109 := by
    simpa [prefixWord, tailWord_1278109, baseEnd_1278109] using wordTrace_append hprefix tailTrace_1278109
  have hstable : (prefixWord ++ tailWord_1278109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278109).length < 2 ^ (prefixWord ++ tailWord_1278109).sum := by decide
  have hdescent : baseEnd_1278109 < baseStart_1278109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278139 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 2, 4]
def baseStart_1278139 : Nat := 118140960795 + 1278139 * 2 ^ 59
def prefixEnd_1278139 : Nat := 4983230072969 + 3 ^ 40 * 1278139 * 2
def baseEnd_1278139 : Nat := 437533100171386672656301

theorem tailTrace_1278139 : CollatzResearch.WordTrace tailWord_1278139 prefixEnd_1278139 437533100171386672656301 := by
  unfold tailWord_1278139
  simp only [CollatzResearch.WordTrace]
  refine ⟨46617559116528166607453471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31078372744352111071635647 46617559116528166607453471)
  ·
    refine ⟨69926338674792249911180207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46617559116528166607453471 69926338674792249911180207)
    ·
      refine ⟨104889508012188374866770311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69926338674792249911180207 104889508012188374866770311)
      ·
        refine ⟨157334262018282562300155467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104889508012188374866770311 157334262018282562300155467)
        ·
          refine ⟨236001393027423843450233201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157334262018282562300155467 236001393027423843450233201)
          ·
            refine ⟨177001044770567882587674901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236001393027423843450233201 177001044770567882587674901)
            ·
              refine ⟨8296923973620369496297261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177001044770567882587674901 8296923973620369496297261)
              ·
                refine ⟨3111346490107638561111473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8296923973620369496297261 3111346490107638561111473)
                ·
                  refine ⟨2333509867580728920833605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3111346490107638561111473 2333509867580728920833605)
                  ·
                    refine ⟨437533100171386672656301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2333509867580728920833605 437533100171386672656301)
                    ·
                      rfl

theorem cell22_1278139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 4].length) (baseStart_1278139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278139 prefixEnd_1278139 := by exact prefixLift 1278139
  have htrace : WordTrace (prefixWord ++ tailWord_1278139) baseStart_1278139 baseEnd_1278139 := by
    simpa [prefixWord, tailWord_1278139, baseEnd_1278139] using wordTrace_append hprefix tailTrace_1278139
  have hstable : (prefixWord ++ tailWord_1278139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278139).length < 2 ^ (prefixWord ++ tailWord_1278139).sum := by decide
  have hdescent : baseEnd_1278139 < baseStart_1278139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278186 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_1278186 : Nat := 118140960795 + 1278186 * 2 ^ 59
def prefixEnd_1278186 : Nat := 4983230072969 + 3 ^ 40 * 1278186 * 2
def baseEnd_1278186 : Nat := 437549189231894216731157

theorem tailTrace_1278186 : CollatzResearch.WordTrace tailWord_1278186 prefixEnd_1278186 437549189231894216731157 := by
  unfold tailWord_1278186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11654818336839473408603603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31079515564905262422942941 11654818336839473408603603)
  ·
    refine ⟨17482227505259210112905405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11654818336839473408603603 17482227505259210112905405)
    ·
      refine ⟨6555835314472203792339527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17482227505259210112905405 6555835314472203792339527)
      ·
        refine ⟨9833752971708305688509291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6555835314472203792339527 9833752971708305688509291)
        ·
          refine ⟨14750629457562458532763937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9833752971708305688509291 14750629457562458532763937)
          ·
            refine ⟨11062972093171843899572953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14750629457562458532763937 11062972093171843899572953)
            ·
              refine ⟨8297229069878882924679715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11062972093171843899572953 8297229069878882924679715)
              ·
                refine ⟨12445843604818324387019573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8297229069878882924679715 12445843604818324387019573)
                ·
                  refine ⟨1166797837951717911283085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12445843604818324387019573 1166797837951717911283085)
                  ·
                    refine ⟨437549189231894216731157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1166797837951717911283085 437549189231894216731157)
                    ·
                      rfl

theorem cell22_1278186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_1278186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278186 prefixEnd_1278186 := by exact prefixLift 1278186
  have htrace : WordTrace (prefixWord ++ tailWord_1278186) baseStart_1278186 baseEnd_1278186 := by
    simpa [prefixWord, tailWord_1278186, baseEnd_1278186] using wordTrace_append hprefix tailTrace_1278186
  have hstable : (prefixWord ++ tailWord_1278186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278186).length < 2 ^ (prefixWord ++ tailWord_1278186).sum := by decide
  have hdescent : baseEnd_1278186 < baseStart_1278186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278216 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 5]
def baseStart_1278216 : Nat := 118140960795 + 1278216 * 2 ^ 59
def prefixEnd_1278216 : Nat := 4983230072969 + 3 ^ 40 * 1278216 * 2
def baseEnd_1278216 : Nat := 145853152948328046160355

theorem tailTrace_1278216 : CollatzResearch.WordTrace tailWord_1278216 prefixEnd_1278216 145853152948328046160355 := by
  unfold tailWord_1278216
  simp only [CollatzResearch.WordTrace]
  refine ⟨23310183768624604379003251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31080245024832805838671001 23310183768624604379003251)
  ·
    refine ⟨34965275652936906568504877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23310183768624604379003251 34965275652936906568504877)
    ·
      refine ⟨13111978369851339963189329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34965275652936906568504877 13111978369851339963189329)
      ·
        refine ⟨9833983777388504972391997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13111978369851339963189329 9833983777388504972391997)
        ·
          refine ⟨3687743916520689364646999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9833983777388504972391997 3687743916520689364646999)
          ·
            refine ⟨5531615874781034046970499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687743916520689364646999 5531615874781034046970499)
            ·
              refine ⟨8297423812171551070455749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5531615874781034046970499 8297423812171551070455749)
              ·
                refine ⟨1555766964782165825710453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8297423812171551070455749 1555766964782165825710453)
                ·
                  refine ⟨145853152948328046160355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1555766964782165825710453 145853152948328046160355)
                  ·
                    rfl

theorem cell22_1278216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_1278216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278216 prefixEnd_1278216 := by exact prefixLift 1278216
  have htrace : WordTrace (prefixWord ++ tailWord_1278216) baseStart_1278216 baseEnd_1278216 := by
    simpa [prefixWord, tailWord_1278216, baseEnd_1278216] using wordTrace_append hprefix tailTrace_1278216
  have hstable : (prefixWord ++ tailWord_1278216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278216).length < 2 ^ (prefixWord ++ tailWord_1278216).sum := by decide
  have hdescent : baseEnd_1278216 < baseStart_1278216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278231 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 2, 5]
def baseStart_1278231 : Nat := 118140960795 + 1278231 * 2 ^ 59
def prefixEnd_1278231 : Nat := 4983230072969 + 3 ^ 40 * 1278231 * 2
def baseEnd_1278231 : Nat := 437564593651529099356019

theorem tailTrace_1278231 : CollatzResearch.WordTrace tailWord_1278231 prefixEnd_1278231 437564593651529099356019 := by
  unfold tailWord_1278231
  simp only [CollatzResearch.WordTrace]
  refine ⟨46620914632194866319802547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31080609754796577546535031 46620914632194866319802547)
  ·
    refine ⟨69931371948292299479703821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46620914632194866319802547 69931371948292299479703821)
    ·
      refine ⟨26224264480609612304888933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69931371948292299479703821 26224264480609612304888933)
      ·
        refine ⟨4917049590114302307166675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26224264480609612304888933 4917049590114302307166675)
        ·
          refine ⟨7375574385171453460750013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4917049590114302307166675 7375574385171453460750013)
          ·
            refine ⟨2765840394439295047781255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7375574385171453460750013 2765840394439295047781255)
            ·
              refine ⟨4148760591658942571671883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2765840394439295047781255 4148760591658942571671883)
              ·
                refine ⟨6223140887488413857507825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148760591658942571671883 6223140887488413857507825)
                ·
                  refine ⟨4667355665616310393130869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6223140887488413857507825 4667355665616310393130869)
                  ·
                    refine ⟨437564593651529099356019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4667355665616310393130869 437564593651529099356019)
                    ·
                      rfl

theorem cell22_1278231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_1278231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278231 prefixEnd_1278231 := by exact prefixLift 1278231
  have htrace : WordTrace (prefixWord ++ tailWord_1278231) baseStart_1278231 baseEnd_1278231 := by
    simpa [prefixWord, tailWord_1278231, baseEnd_1278231] using wordTrace_append hprefix tailTrace_1278231
  have hstable : (prefixWord ++ tailWord_1278231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278231).length < 2 ^ (prefixWord ++ tailWord_1278231).sum := by decide
  have hdescent : baseEnd_1278231 < baseStart_1278231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278254 : List Nat := [4, 1, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1278254 : Nat := 118140960795 + 1278254 * 2 ^ 59
def prefixEnd_1278254 : Nat := 4983230072969 + 3 ^ 40 * 1278254 * 2
def baseEnd_1278254 : Nat := 437572467021564706030949

theorem tailTrace_1278254 : CollatzResearch.WordTrace tailWord_1278254 prefixEnd_1278254 437572467021564706030949 := by
  unfold tailWord_1278254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5827719188888942655986227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31081169007407694165259877 5827719188888942655986227)
  ·
    refine ⟨8741578783333413983979341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5827719188888942655986227 8741578783333413983979341)
    ·
      refine ⟨3278092043750030243992253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8741578783333413983979341 3278092043750030243992253)
      ·
        refine ⟨1229284516406261341497095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3278092043750030243992253 1229284516406261341497095)
        ·
          refine ⟨1843926774609392012245643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229284516406261341497095 1843926774609392012245643)
          ·
            refine ⟨2765890161914088018368465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843926774609392012245643 2765890161914088018368465)
            ·
              refine ⟨2074417621435566013776349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2765890161914088018368465 2074417621435566013776349)
              ·
                refine ⟨777906608038337255166131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2074417621435566013776349 777906608038337255166131)
                ·
                  refine ⟨1166859912057505882749197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777906608038337255166131 1166859912057505882749197)
                  ·
                    refine ⟨437572467021564706030949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1166859912057505882749197 437572467021564706030949)
                    ·
                      rfl

theorem cell22_1278254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1278254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278254 prefixEnd_1278254 := by exact prefixLift 1278254
  have htrace : WordTrace (prefixWord ++ tailWord_1278254) baseStart_1278254 baseEnd_1278254 := by
    simpa [prefixWord, tailWord_1278254, baseEnd_1278254] using wordTrace_append hprefix tailTrace_1278254
  have hstable : (prefixWord ++ tailWord_1278254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278254).length < 2 ^ (prefixWord ++ tailWord_1278254).sum := by decide
  have hdescent : baseEnd_1278254 < baseStart_1278254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278398 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1278398 : Nat := 118140960795 + 1278398 * 2 ^ 59
def prefixEnd_1278398 : Nat := 4983230072969 + 3 ^ 40 * 1278398 * 2
def baseEnd_1278398 : Nat := 437621761164396330430507

theorem tailTrace_1278398 : CollatzResearch.WordTrace tailWord_1278398 prefixEnd_1278398 437621761164396330430507 := by
  unfold tailWord_1278398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828375702823731730141481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31084670415059902560754565 5828375702823731730141481)
  ·
    refine ⟨4371281777117798797606111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5828375702823731730141481 4371281777117798797606111)
    ·
      refine ⟨6556922665676698196409167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4371281777117798797606111 6556922665676698196409167)
      ·
        refine ⟨9835383998515047294613751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6556922665676698196409167 9835383998515047294613751)
        ·
          refine ⟨14753075997772570941920627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9835383998515047294613751 14753075997772570941920627)
          ·
            refine ⟨22129613996658856412880941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14753075997772570941920627 22129613996658856412880941)
            ·
              refine ⟨8298605248747071154830353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22129613996658856412880941 8298605248747071154830353)
              ·
                refine ⟨6223953936560303366122765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8298605248747071154830353 6223953936560303366122765)
                ·
                  refine ⟨2333982726210113762296037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6223953936560303366122765 2333982726210113762296037)
                  ·
                    refine ⟨437621761164396330430507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2333982726210113762296037 437621761164396330430507)
                    ·
                      rfl

theorem cell22_1278398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1278398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278398 prefixEnd_1278398 := by exact prefixLift 1278398
  have htrace : WordTrace (prefixWord ++ tailWord_1278398) baseStart_1278398 baseEnd_1278398 := by
    simpa [prefixWord, tailWord_1278398, baseEnd_1278398] using wordTrace_append hprefix tailTrace_1278398
  have hstable : (prefixWord ++ tailWord_1278398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278398).length < 2 ^ (prefixWord ++ tailWord_1278398).sum := by decide
  have hdescent : baseEnd_1278398 < baseStart_1278398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278473 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 5, 3]
def baseStart_1278473 : Nat := 118140960795 + 1278473 * 2 ^ 59
def prefixEnd_1278473 : Nat := 4983230072969 + 3 ^ 40 * 1278473 * 2
def baseEnd_1278473 : Nat := 437647435197121134805277

theorem tailTrace_1278473 : CollatzResearch.WordTrace tailWord_1278473 prefixEnd_1278473 437647435197121134805277 := by
  unfold tailWord_1278473
  simp only [CollatzResearch.WordTrace]
  refine ⟨46629741097318141650112073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31086494064878761100074715 46629741097318141650112073)
  ·
    refine ⟨34972305822988606237584055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46629741097318141650112073 34972305822988606237584055)
    ·
      refine ⟨52458458734482909356376083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34972305822988606237584055 52458458734482909356376083)
      ·
        refine ⟨78687688101724364034564125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52458458734482909356376083 78687688101724364034564125)
        ·
          refine ⟨29507883038146636512961547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78687688101724364034564125 29507883038146636512961547)
          ·
            refine ⟨44261824557219954769442321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29507883038146636512961547 44261824557219954769442321)
            ·
              refine ⟨33196368417914966077081741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44261824557219954769442321 33196368417914966077081741)
              ·
                refine ⟨12448638156718112278905653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33196368417914966077081741 12448638156718112278905653)
                ·
                  refine ⟨1167059827192323026147405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12448638156718112278905653 1167059827192323026147405)
                  ·
                    refine ⟨437647435197121134805277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167059827192323026147405 437647435197121134805277)
                    ·
                      rfl

theorem cell22_1278473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_1278473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278473 prefixEnd_1278473 := by exact prefixLift 1278473
  have htrace : WordTrace (prefixWord ++ tailWord_1278473) baseStart_1278473 baseEnd_1278473 := by
    simpa [prefixWord, tailWord_1278473, baseEnd_1278473] using wordTrace_append hprefix tailTrace_1278473
  have hstable : (prefixWord ++ tailWord_1278473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278473).length < 2 ^ (prefixWord ++ tailWord_1278473).sum := by decide
  have hdescent : baseEnd_1278473 < baseStart_1278473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278475 : List Nat := [1, 1, 1, 1, 7, 3, 2, 6]
def baseStart_1278475 : Nat := 118140960795 + 1278475 * 2 ^ 59
def prefixEnd_1278475 : Nat := 4983230072969 + 3 ^ 40 * 1278475 * 2
def baseEnd_1278475 : Nat := 48627568870888199583919

theorem tailTrace_1278475 : CollatzResearch.WordTrace tailWord_1278475 prefixEnd_1278475 48627568870888199583919 := by
  unfold tailWord_1278475
  simp only [CollatzResearch.WordTrace]
  refine ⟨46629814043310895991684879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31086542695540597327789919 46629814043310895991684879)
  ·
    refine ⟨69944721064966343987527319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46629814043310895991684879 69944721064966343987527319)
    ·
      refine ⟨104917081597449515981290979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69944721064966343987527319 104917081597449515981290979)
      ·
        refine ⟨157375622396174273971936469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104917081597449515981290979 157375622396174273971936469)
        ·
          refine ⟨3688491149910334546217261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 157375622396174273971936469 3688491149910334546217261)
          ·
            refine ⟨1383184181216375454831473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3688491149910334546217261 1383184181216375454831473)
            ·
              refine ⟨1037388135912281591123605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383184181216375454831473 1037388135912281591123605)
              ·
                refine ⟨48627568870888199583919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1037388135912281591123605 48627568870888199583919)
                ·
                  rfl

theorem cell22_1278475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 6].length) (baseStart_1278475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278475 prefixEnd_1278475 := by exact prefixLift 1278475
  have htrace : WordTrace (prefixWord ++ tailWord_1278475) baseStart_1278475 baseEnd_1278475 := by
    simpa [prefixWord, tailWord_1278475, baseEnd_1278475] using wordTrace_append hprefix tailTrace_1278475
  have hstable : (prefixWord ++ tailWord_1278475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278475).length < 2 ^ (prefixWord ++ tailWord_1278475).sum := by decide
  have hdescent : baseEnd_1278475 < baseStart_1278475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278477 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1278477 : Nat := 118140960795 + 1278477 * 2 ^ 59
def prefixEnd_1278477 : Nat := 4983230072969 + 3 ^ 40 * 1278477 * 2
def baseEnd_1278477 : Nat := 437648804478866457705265

theorem tailTrace_1278477 : CollatzResearch.WordTrace tailWord_1278477 prefixEnd_1278477 437648804478866457705265 := by
  unfold tailWord_1278477
  simp only [CollatzResearch.WordTrace]
  refine ⟨46629886989303650333257685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31086591326202433555505123 46629886989303650333257685)
  ·
    refine ⟨1092887976311804304685727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 46629886989303650333257685 1092887976311804304685727)
    ·
      refine ⟨1639331964467706457028591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092887976311804304685727 1639331964467706457028591)
      ·
        refine ⟨2458997946701559685542887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639331964467706457028591 2458997946701559685542887)
        ·
          refine ⟨3688496920052339528314331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458997946701559685542887 3688496920052339528314331)
          ·
            refine ⟨5532745380078509292471497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688496920052339528314331 5532745380078509292471497)
            ·
              refine ⟨4149559035058881969353623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5532745380078509292471497 4149559035058881969353623)
              ·
                refine ⟨6224338552588322954030435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149559035058881969353623 6224338552588322954030435)
                ·
                  refine ⟨9336507828882484431045653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224338552588322954030435 9336507828882484431045653)
                  ·
                    refine ⟨437648804478866457705265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9336507828882484431045653 437648804478866457705265)
                    ·
                      rfl

theorem cell22_1278477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1278477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278477 prefixEnd_1278477 := by exact prefixLift 1278477
  have htrace : WordTrace (prefixWord ++ tailWord_1278477) baseStart_1278477 baseEnd_1278477 := by
    simpa [prefixWord, tailWord_1278477, baseEnd_1278477] using wordTrace_append hprefix tailTrace_1278477
  have hstable : (prefixWord ++ tailWord_1278477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278477).length < 2 ^ (prefixWord ++ tailWord_1278477).sum := by decide
  have hdescent : baseEnd_1278477 < baseStart_1278477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278509 : List Nat := [1, 5, 4, 1, 1, 1, 2, 7]
def baseStart_1278509 : Nat := 118140960795 + 1278509 * 2 ^ 59
def prefixEnd_1278509 : Nat := 4983230072969 + 3 ^ 40 * 1278509 * 2
def baseEnd_1278509 : Nat := 48628862081425448989463

theorem tailTrace_1278509 : CollatzResearch.WordTrace tailWord_1278509 prefixEnd_1278509 48628862081425448989463 := by
  unfold tailWord_1278509
  simp only [CollatzResearch.WordTrace]
  refine ⟨46631054125187719798422581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31087369416791813198948387 46631054125187719798422581)
  ·
    refine ⟨4371661324236348731102117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46631054125187719798422581 4371661324236348731102117)
    ·
      refine ⟨819686498294315387081647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4371661324236348731102117 819686498294315387081647)
      ·
        refine ⟨1229529747441473080622471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819686498294315387081647 1229529747441473080622471)
        ·
          refine ⟨1844294621162209620933707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229529747441473080622471 1844294621162209620933707)
          ·
            refine ⟨2766441931743314431400561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844294621162209620933707 2766441931743314431400561)
            ·
              refine ⟨2074831448807485823550421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766441931743314431400561 2074831448807485823550421)
              ·
                refine ⟨48628862081425448989463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2074831448807485823550421 48628862081425448989463)
                ·
                  rfl

theorem cell22_1278509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 7].length) (baseStart_1278509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278509 prefixEnd_1278509 := by exact prefixLift 1278509
  have htrace : WordTrace (prefixWord ++ tailWord_1278509) baseStart_1278509 baseEnd_1278509 := by
    simpa [prefixWord, tailWord_1278509, baseEnd_1278509] using wordTrace_append hprefix tailTrace_1278509
  have hstable : (prefixWord ++ tailWord_1278509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278509).length < 2 ^ (prefixWord ++ tailWord_1278509).sum := by decide
  have hdescent : baseEnd_1278509 < baseStart_1278509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278563 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 3, 5]
def baseStart_1278563 : Nat := 118140960795 + 1278563 * 2 ^ 59
def prefixEnd_1278563 : Nat := 4983230072969 + 3 ^ 40 * 1278563 * 2
def baseEnd_1278563 : Nat := 437678244036390900055001

theorem tailTrace_1278563 : CollatzResearch.WordTrace tailWord_1278563 prefixEnd_1278563 437678244036390900055001 := by
  unfold tailWord_1278563
  simp only [CollatzResearch.WordTrace]
  refine ⟨46633023666992087020888343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31088682444661391347258895 46633023666992087020888343)
  ·
    refine ⟨69949535500488130531332515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46633023666992087020888343 69949535500488130531332515)
    ·
      refine ⟨104924303250732195796998773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69949535500488130531332515 104924303250732195796998773)
      ·
        refine ⟨9836653429756143355968635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104924303250732195796998773 9836653429756143355968635)
        ·
          refine ⟨14754980144634215033952953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9836653429756143355968635 14754980144634215033952953)
          ·
            refine ⟨11066235108475661275464715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14754980144634215033952953 11066235108475661275464715)
            ·
              refine ⟨16599352662713491913197073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11066235108475661275464715 16599352662713491913197073)
              ·
                refine ⟨12449514497035118934897805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16599352662713491913197073 12449514497035118934897805)
                ·
                  refine ⟨4668567936388169600586677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12449514497035118934897805 4668567936388169600586677)
                  ·
                    refine ⟨437678244036390900055001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4668567936388169600586677 437678244036390900055001)
                    ·
                      rfl

theorem cell22_1278563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_1278563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278563 prefixEnd_1278563 := by exact prefixLift 1278563
  have htrace : WordTrace (prefixWord ++ tailWord_1278563) baseStart_1278563 baseEnd_1278563 := by
    simpa [prefixWord, tailWord_1278563, baseEnd_1278563] using wordTrace_append hprefix tailTrace_1278563
  have hstable : (prefixWord ++ tailWord_1278563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278563).length < 2 ^ (prefixWord ++ tailWord_1278563).sum := by decide
  have hdescent : baseEnd_1278563 < baseStart_1278563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278582 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1278582 : Nat := 118140960795 + 1278582 * 2 ^ 59
def prefixEnd_1278582 : Nat := 4983230072969 + 3 ^ 40 * 1278582 * 2
def baseEnd_1278582 : Nat := 145894916041560394609981

theorem tailTrace_1278582 : CollatzResearch.WordTrace tailWord_1278582 prefixEnd_1278582 145894916041560394609981 := by
  unfold tailWord_1278582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914607290870203329114375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31089144435948835510553333 2914607290870203329114375)
  ·
    refine ⟨4371910936305304993671563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2914607290870203329114375 4371910936305304993671563)
    ·
      refine ⟨6557866404457957490507345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4371910936305304993671563 6557866404457957490507345)
      ·
        refine ⟨4918399803343468117880509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6557866404457957490507345 4918399803343468117880509)
        ·
          refine ⟨1844399926253800544205191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4918399803343468117880509 1844399926253800544205191)
          ·
            refine ⟨2766599889380700816307787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844399926253800544205191 2766599889380700816307787)
            ·
              refine ⟨4149899834071051224461681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766599889380700816307787 4149899834071051224461681)
              ·
                refine ⟨3112424875553288418346261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4149899834071051224461681 3112424875553288418346261)
                ·
                  refine ⟨145894916041560394609981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3112424875553288418346261 145894916041560394609981)
                  ·
                    rfl

theorem cell22_1278582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1278582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278582 prefixEnd_1278582 := by exact prefixLift 1278582
  have htrace : WordTrace (prefixWord ++ tailWord_1278582) baseStart_1278582 baseEnd_1278582 := by
    simpa [prefixWord, tailWord_1278582, baseEnd_1278582] using wordTrace_append hprefix tailTrace_1278582
  have hstable : (prefixWord ++ tailWord_1278582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278582).length < 2 ^ (prefixWord ++ tailWord_1278582).sum := by decide
  have hdescent : baseEnd_1278582 < baseStart_1278582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278595 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 2, 4]
def baseStart_1278595 : Nat := 118140960795 + 1278595 * 2 ^ 59
def prefixEnd_1278595 : Nat := 4983230072969 + 3 ^ 40 * 1278595 * 2
def baseEnd_1278595 : Nat := 437689198290353483254903

theorem tailTrace_1278595 : CollatzResearch.WordTrace tailWord_1278595 prefixEnd_1278595 437689198290353483254903 := by
  unfold tailWord_1278595
  simp only [CollatzResearch.WordTrace]
  refine ⟨46634190802876156486053239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31089460535250770990702159 46634190802876156486053239)
  ·
    refine ⟨69951286204314234729079859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46634190802876156486053239 69951286204314234729079859)
    ·
      refine ⟨104926929306471352093619789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69951286204314234729079859 104926929306471352093619789)
      ·
        refine ⟨39347598489926757035107421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104926929306471352093619789 39347598489926757035107421)
        ·
          refine ⟨14755349433722533888165283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39347598489926757035107421 14755349433722533888165283)
          ·
            refine ⟨22133024150583800832247925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14755349433722533888165283 22133024150583800832247925)
            ·
              refine ⟨2074971014117231328023243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22133024150583800832247925 2074971014117231328023243)
              ·
                refine ⟨3112456521175846992034865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2074971014117231328023243 3112456521175846992034865)
                ·
                  refine ⟨2334342390881885244026149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112456521175846992034865 2334342390881885244026149)
                  ·
                    refine ⟨437689198290353483254903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2334342390881885244026149 437689198290353483254903)
                    ·
                      rfl

theorem cell22_1278595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 4].length) (baseStart_1278595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278595 prefixEnd_1278595 := by exact prefixLift 1278595
  have htrace : WordTrace (prefixWord ++ tailWord_1278595) baseStart_1278595 baseEnd_1278595 := by
    simpa [prefixWord, tailWord_1278595, baseEnd_1278595] using wordTrace_append hprefix tailTrace_1278595
  have hstable : (prefixWord ++ tailWord_1278595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278595).length < 2 ^ (prefixWord ++ tailWord_1278595).sum := by decide
  have hdescent : baseEnd_1278595 < baseStart_1278595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278610 : List Nat := [3, 2, 3, 1, 2, 2, 9]
def baseStart_1278610 : Nat := 118140960795 + 1278610 * 2 ^ 59
def prefixEnd_1278610 : Nat := 4983230072969 + 3 ^ 40 * 1278610 * 2
def baseEnd_1278610 : Nat := 16210901225811053486291

theorem tailTrace_1278610 : CollatzResearch.WordTrace tailWord_1278610 prefixEnd_1278610 16210901225811053486291 := by
  unfold tailWord_1278610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11658684474455453511962321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31089825265214542698566189 11658684474455453511962321)
  ·
    refine ⟨8744013355841590133971741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11658684474455453511962321 8744013355841590133971741)
    ·
      refine ⟨3279005008440596300239403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8744013355841590133971741 3279005008440596300239403)
      ·
        refine ⟨4918507512660894450359105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3279005008440596300239403 4918507512660894450359105)
        ·
          refine ⟨3688880634495670837769329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4918507512660894450359105 3688880634495670837769329)
          ·
            refine ⟨2766660475871753128326997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3688880634495670837769329 2766660475871753128326997)
            ·
              refine ⟨16210901225811053486291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2766660475871753128326997 16210901225811053486291)
              ·
                rfl

theorem cell22_1278610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 9].length) (baseStart_1278610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278610 prefixEnd_1278610 := by exact prefixLift 1278610
  have htrace : WordTrace (prefixWord ++ tailWord_1278610) baseStart_1278610 baseEnd_1278610 := by
    simpa [prefixWord, tailWord_1278610, baseEnd_1278610] using wordTrace_append hprefix tailTrace_1278610
  have hstable : (prefixWord ++ tailWord_1278610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278610).length < 2 ^ (prefixWord ++ tailWord_1278610).sum := by decide
  have hdescent : baseEnd_1278610 < baseStart_1278610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278631 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1278631 : Nat := 118140960795 + 1278631 * 2 ^ 59
def prefixEnd_1278631 : Nat := 4983230072969 + 3 ^ 40 * 1278631 * 2
def baseEnd_1278631 : Nat := 437701521826061389354793

theorem tailTrace_1278631 : CollatzResearch.WordTrace tailWord_1278631 prefixEnd_1278631 437701521826061389354793 := by
  unfold tailWord_1278631
  simp only [CollatzResearch.WordTrace]
  refine ⟨46635503830745734634363747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31090335887163823089575831 46635503830745734634363747)
  ·
    refine ⟨69953255746118601951545621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46635503830745734634363747 69953255746118601951545621)
    ·
      refine ⟨3279058863099309466478701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69953255746118601951545621 3279058863099309466478701)
      ·
        refine ⟨1229647073662241049929513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3279058863099309466478701 1229647073662241049929513)
        ·
          refine ⟨922235305246680787447135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229647073662241049929513 922235305246680787447135)
          ·
            refine ⟨1383352957870021181170703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922235305246680787447135 1383352957870021181170703)
            ·
              refine ⟨2075029436805031771756055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383352957870021181170703 2075029436805031771756055)
              ·
                refine ⟨3112544155207547657634083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075029436805031771756055 3112544155207547657634083)
                ·
                  refine ⟨4668816232811321486451125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112544155207547657634083 4668816232811321486451125)
                  ·
                    refine ⟨437701521826061389354793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4668816232811321486451125 437701521826061389354793)
                    ·
                      rfl

theorem cell22_1278631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1278631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278631 prefixEnd_1278631 := by exact prefixLift 1278631
  have htrace : WordTrace (prefixWord ++ tailWord_1278631) baseStart_1278631 baseEnd_1278631 := by
    simpa [prefixWord, tailWord_1278631, baseEnd_1278631] using wordTrace_append hprefix tailTrace_1278631
  have hstable : (prefixWord ++ tailWord_1278631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278631).length < 2 ^ (prefixWord ++ tailWord_1278631).sum := by decide
  have hdescent : baseEnd_1278631 < baseStart_1278631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278676 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1278676 : Nat := 118140960795 + 1278676 * 2 ^ 59
def prefixEnd_1278676 : Nat := 4983230072969 + 3 ^ 40 * 1278676 * 2
def baseEnd_1278676 : Nat := 437716926245696271979655

theorem tailTrace_1278676 : CollatzResearch.WordTrace tailWord_1278676 prefixEnd_1278676 437716926245696271979655 := by
  unfold tailWord_1278676
  simp only [CollatzResearch.WordTrace]
  refine ⟨23318572557791353659875941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31091430077055138213167921 23318572557791353659875941)
  ·
    refine ⟨4372232354585878811226739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23318572557791353659875941 4372232354585878811226739)
    ·
      refine ⟨6558348531878818216840109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4372232354585878811226739 6558348531878818216840109)
      ·
        refine ⟨2459380699454556831315041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6558348531878818216840109 2459380699454556831315041)
        ·
          refine ⟨1844535524590917623486281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2459380699454556831315041 1844535524590917623486281)
          ·
            refine ⟨1383401643443188217614711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844535524590917623486281 1383401643443188217614711)
            ·
              refine ⟨2075102465164782326422067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383401643443188217614711 2075102465164782326422067)
              ·
                refine ⟨3112653697747173489633101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075102465164782326422067 3112653697747173489633101)
                ·
                  refine ⟨1167245136655190058612413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3112653697747173489633101 1167245136655190058612413)
                  ·
                    refine ⟨437716926245696271979655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167245136655190058612413 437716926245696271979655)
                    ·
                      rfl

theorem cell22_1278676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1278676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278676 prefixEnd_1278676 := by exact prefixLift 1278676
  have htrace : WordTrace (prefixWord ++ tailWord_1278676) baseStart_1278676 baseEnd_1278676 := by
    simpa [prefixWord, tailWord_1278676, baseEnd_1278676] using wordTrace_append hprefix tailTrace_1278676
  have hstable : (prefixWord ++ tailWord_1278676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278676).length < 2 ^ (prefixWord ++ tailWord_1278676).sum := by decide
  have hdescent : baseEnd_1278676 < baseStart_1278676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278683 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 12]
def baseStart_1278683 : Nat := 118140960795 + 1278683 * 2 ^ 59
def prefixEnd_1278683 : Nat := 4983230072969 + 3 ^ 40 * 1278683 * 2
def baseEnd_1278683 : Nat := 145906440829583529018211

theorem tailTrace_1278683 : CollatzResearch.WordTrace tailWord_1278683 prefixEnd_1278683 145906440829583529018211 := by
  unfold tailWord_1278683
  simp only [CollatzResearch.WordTrace]
  refine ⟨46637400426557347515256703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31091600284371565010171135 46637400426557347515256703)
  ·
    refine ⟨69956100639836021272885055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46637400426557347515256703 69956100639836021272885055)
    ·
      refine ⟨104934150959754031909327583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69956100639836021272885055 104934150959754031909327583)
      ·
        refine ⟨157401226439631047863991375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104934150959754031909327583 157401226439631047863991375)
        ·
          refine ⟨236101839659446571795987063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157401226439631047863991375 236101839659446571795987063)
          ·
            refine ⟨354152759489169857693980595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236101839659446571795987063 354152759489169857693980595)
            ·
              refine ⟨531229139233754786540970893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354152759489169857693980595 531229139233754786540970893)
              ·
                refine ⟨199210927212658044952864085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531229139233754786540970893 199210927212658044952864085)
                ·
                  refine ⟨145906440829583529018211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 199210927212658044952864085 145906440829583529018211)
                  ·
                    rfl

theorem cell22_1278683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 12].length) (baseStart_1278683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278683 prefixEnd_1278683 := by exact prefixLift 1278683
  have htrace : WordTrace (prefixWord ++ tailWord_1278683) baseStart_1278683 baseEnd_1278683 := by
    simpa [prefixWord, tailWord_1278683, baseEnd_1278683] using wordTrace_append hprefix tailTrace_1278683
  have hstable : (prefixWord ++ tailWord_1278683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278683).length < 2 ^ (prefixWord ++ tailWord_1278683).sum := by decide
  have hdescent : baseEnd_1278683 < baseStart_1278683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278689 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 5]
def baseStart_1278689 : Nat := 118140960795 + 1278689 * 2 ^ 59
def prefixEnd_1278689 : Nat := 4983230072969 + 3 ^ 40 * 1278689 * 2
def baseEnd_1278689 : Nat := 145907125470456190468205

theorem tailTrace_1278689 : CollatzResearch.WordTrace tailWord_1278689 prefixEnd_1278689 145907125470456190468205 := by
  unfold tailWord_1278689
  simp only [CollatzResearch.WordTrace]
  refine ⟨46637619264535610539975121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31091746176357073693316747 46637619264535610539975121)
  ·
    refine ⟨34978214448401707904981341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46637619264535610539975121 34978214448401707904981341)
    ·
      refine ⟨13116830418150640464368003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34978214448401707904981341 13116830418150640464368003)
      ·
        refine ⟨19675245627225960696552005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13116830418150640464368003 19675245627225960696552005)
        ·
          refine ⟨3689108555104867630603501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19675245627225960696552005 3689108555104867630603501)
          ·
            refine ⟨1383415708164325361476313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3689108555104867630603501 1383415708164325361476313)
            ·
              refine ⟨1037561781123244021107235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383415708164325361476313 1037561781123244021107235)
              ·
                refine ⟨1556342671684866031660853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037561781123244021107235 1556342671684866031660853)
                ·
                  refine ⟨145907125470456190468205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1556342671684866031660853 145907125470456190468205)
                  ·
                    rfl

theorem cell22_1278689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_1278689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278689 prefixEnd_1278689 := by exact prefixLift 1278689
  have htrace : WordTrace (prefixWord ++ tailWord_1278689) baseStart_1278689 baseEnd_1278689 := by
    simpa [prefixWord, tailWord_1278689, baseEnd_1278689] using wordTrace_append hprefix tailTrace_1278689
  have hstable : (prefixWord ++ tailWord_1278689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278689).length < 2 ^ (prefixWord ++ tailWord_1278689).sum := by decide
  have hdescent : baseEnd_1278689 < baseStart_1278689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278702 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1278702 : Nat := 118140960795 + 1278702 * 2 ^ 59
def prefixEnd_1278702 : Nat := 4983230072969 + 3 ^ 40 * 1278702 * 2
def baseEnd_1278702 : Nat := 437725826577040870829575

theorem tailTrace_1278702 : CollatzResearch.WordTrace tailWord_1278702 prefixEnd_1278702 437725826577040870829575 := by
  unfold tailWord_1278702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5829761676686064220024795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31092062275659009173465573 5829761676686064220024795)
  ·
    refine ⟨8744642515029096330037193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5829761676686064220024795 8744642515029096330037193)
    ·
      refine ⟨6558481886271822247527895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8744642515029096330037193 6558481886271822247527895)
      ·
        refine ⟨9837722829407733371291843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6558481886271822247527895 9837722829407733371291843)
        ·
          refine ⟨14756584244111600056937765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9837722829407733371291843 14756584244111600056937765)
          ·
            refine ⟨2766859545770925010675831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14756584244111600056937765 2766859545770925010675831)
            ·
              refine ⟨4150289318656387516013747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2766859545770925010675831 4150289318656387516013747)
              ·
                refine ⟨6225433977984581274020621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150289318656387516013747 6225433977984581274020621)
                ·
                  refine ⟨2334537741744217977757733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6225433977984581274020621 2334537741744217977757733)
                  ·
                    refine ⟨437725826577040870829575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2334537741744217977757733 437725826577040870829575)
                    ·
                      rfl

theorem cell22_1278702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1278702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278702 prefixEnd_1278702 := by exact prefixLift 1278702
  have htrace : WordTrace (prefixWord ++ tailWord_1278702) baseStart_1278702 baseEnd_1278702 := by
    simpa [prefixWord, tailWord_1278702, baseEnd_1278702] using wordTrace_append hprefix tailTrace_1278702
  have hstable : (prefixWord ++ tailWord_1278702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278702).length < 2 ^ (prefixWord ++ tailWord_1278702).sum := by decide
  have hdescent : baseEnd_1278702 < baseStart_1278702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278717 : List Nat := [1, 4, 1, 1, 1, 1, 4, 5, 4]
def baseStart_1278717 : Nat := 118140960795 + 1278717 * 2 ^ 59
def prefixEnd_1278717 : Nat := 4983230072969 + 3 ^ 40 * 1278717 * 2
def baseEnd_1278717 : Nat := 145910320461195277234843

theorem tailTrace_1278717 : CollatzResearch.WordTrace tailWord_1278717 prefixEnd_1278717 145910320461195277234843 := by
  unfold tailWord_1278717
  simp only [CollatzResearch.WordTrace]
  refine ⟨46638640508434171321994405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31092427005622780881329603 46638640508434171321994405)
  ·
    refine ⟨8744745095331407122873951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46638640508434171321994405 8744745095331407122873951)
    ·
      refine ⟨13117117642997110684310927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8744745095331407122873951 13117117642997110684310927)
      ·
        refine ⟨19675676464495666026466391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13117117642997110684310927 19675676464495666026466391)
        ·
          refine ⟨29513514696743499039699587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19675676464495666026466391 29513514696743499039699587)
          ·
            refine ⟨44270272045115248559549381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29513514696743499039699587 44270272045115248559549381)
            ·
              refine ⟨8300676008459109104915509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44270272045115248559549381 8300676008459109104915509)
              ·
                refine ⟨778188375793041478585829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8300676008459109104915509 778188375793041478585829)
                ·
                  refine ⟨145910320461195277234843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 778188375793041478585829 145910320461195277234843)
                  ·
                    rfl

theorem cell22_1278717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_1278717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278717 prefixEnd_1278717 := by exact prefixLift 1278717
  have htrace : WordTrace (prefixWord ++ tailWord_1278717) baseStart_1278717 baseEnd_1278717 := by
    simpa [prefixWord, tailWord_1278717, baseEnd_1278717] using wordTrace_append hprefix tailTrace_1278717
  have hstable : (prefixWord ++ tailWord_1278717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278717).length < 2 ^ (prefixWord ++ tailWord_1278717).sum := by decide
  have hdescent : baseEnd_1278717 < baseStart_1278717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278835 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 8]
def baseStart_1278835 : Nat := 118140960795 + 1278835 * 2 ^ 59
def prefixEnd_1278835 : Nat := 4983230072969 + 3 ^ 40 * 1278835 * 2
def baseEnd_1278835 : Nat := 145923785065024285751389

theorem tailTrace_1278835 : CollatzResearch.WordTrace tailWord_1278835 prefixEnd_1278835 145923785065024285751389 := by
  unfold tailWord_1278835
  simp only [CollatzResearch.WordTrace]
  refine ⟨46642944322006677474789959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31095296214671118316526639 46642944322006677474789959)
  ·
    refine ⟨69964416483010016212184939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46642944322006677474789959 69964416483010016212184939)
    ·
      refine ⟨104946624724515024318277409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69964416483010016212184939 104946624724515024318277409)
      ·
        refine ⟨78709968543386268238708057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104946624724515024318277409 78709968543386268238708057)
        ·
          refine ⟨59032476407539701179031043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78709968543386268238708057 59032476407539701179031043)
          ·
            refine ⟨88548714611309551768546565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59032476407539701179031043 88548714611309551768546565)
            ·
              refine ⟨16602883989620540956602481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88548714611309551768546565 16602883989620540956602481)
              ·
                refine ⟨12452162992215405717451861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16602883989620540956602481 12452162992215405717451861)
                ·
                  refine ⟨145923785065024285751389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12452162992215405717451861 145923785065024285751389)
                  ·
                    rfl

theorem cell22_1278835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 8].length) (baseStart_1278835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278835 prefixEnd_1278835 := by exact prefixLift 1278835
  have htrace : WordTrace (prefixWord ++ tailWord_1278835) baseStart_1278835 baseEnd_1278835 := by
    simpa [prefixWord, tailWord_1278835, baseEnd_1278835] using wordTrace_append hprefix tailTrace_1278835
  have hstable : (prefixWord ++ tailWord_1278835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278835).length < 2 ^ (prefixWord ++ tailWord_1278835).sum := by decide
  have hdescent : baseEnd_1278835 < baseStart_1278835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278867 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 6, 3]
def baseStart_1278867 : Nat := 118140960795 + 1278867 * 2 ^ 59
def prefixEnd_1278867 : Nat := 4983230072969 + 3 ^ 40 * 1278867 * 2
def baseEnd_1278867 : Nat := 437782309449035440454069

theorem tailTrace_1278867 : CollatzResearch.WordTrace tailWord_1278867 prefixEnd_1278867 437782309449035440454069 := by
  unfold tailWord_1278867
  simp only [CollatzResearch.WordTrace]
  refine ⟨46644111457890746939954855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31096074305260497959969903 46644111457890746939954855)
  ·
    refine ⟨69966167186836120409932283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46644111457890746939954855 69966167186836120409932283)
    ·
      refine ⟨104949250780254180614898425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69966167186836120409932283 104949250780254180614898425)
      ·
        refine ⟨78711938085190635461173819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104949250780254180614898425 78711938085190635461173819)
        ·
          refine ⟨118067907127785953191760729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78711938085190635461173819 118067907127785953191760729)
          ·
            refine ⟨88550930345839464893820547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118067907127785953191760729 88550930345839464893820547)
            ·
              refine ⟨132826395518759197340730821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88550930345839464893820547 132826395518759197340730821)
              ·
                refine ⟨24904949159767349501387029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132826395518759197340730821 24904949159767349501387029)
                ·
                  refine ⟨1167419491864094507877517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24904949159767349501387029 1167419491864094507877517)
                  ·
                    refine ⟨437782309449035440454069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167419491864094507877517 437782309449035440454069)
                    ·
                      rfl

theorem cell22_1278867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 3].length) (baseStart_1278867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278867 prefixEnd_1278867 := by exact prefixLift 1278867
  have htrace : WordTrace (prefixWord ++ tailWord_1278867) baseStart_1278867 baseEnd_1278867 := by
    simpa [prefixWord, tailWord_1278867, baseEnd_1278867] using wordTrace_append hprefix tailTrace_1278867
  have hstable : (prefixWord ++ tailWord_1278867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278867).length < 2 ^ (prefixWord ++ tailWord_1278867).sum := by decide
  have hdescent : baseEnd_1278867 < baseStart_1278867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278897 : List Nat := [1, 2, 2, 4, 3, 10]
def baseStart_1278897 : Nat := 118140960795 + 1278897 * 2 ^ 59
def prefixEnd_1278897 : Nat := 4983230072969 + 3 ^ 40 * 1278897 * 2
def baseEnd_1278897 : Nat := 5404846655087967434617

theorem tailTrace_1278897 : CollatzResearch.WordTrace tailWord_1278897 prefixEnd_1278897 5404846655087967434617 := by
  unfold tailWord_1278897
  simp only [CollatzResearch.WordTrace]
  refine ⟨46645205647782062063546945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31096803765188041375697963 46645205647782062063546945)
  ·
    refine ⟨34983904235836546547660209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46645205647782062063546945 34983904235836546547660209)
    ·
      refine ⟨26237928176877409910745157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34983904235836546547660209 26237928176877409910745157)
      ·
        refine ⟨4919611533164514358264717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26237928176877409910745157 4919611533164514358264717)
        ·
          refine ⟨1844854324936692884349269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4919611533164514358264717 1844854324936692884349269)
          ·
            refine ⟨5404846655087967434617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1844854324936692884349269 5404846655087967434617)
            ·
              rfl

theorem cell22_1278897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 10].length) (baseStart_1278897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278897 prefixEnd_1278897 := by exact prefixLift 1278897
  have htrace : WordTrace (prefixWord ++ tailWord_1278897) baseStart_1278897 baseEnd_1278897 := by
    simpa [prefixWord, tailWord_1278897, baseEnd_1278897] using wordTrace_append hprefix tailTrace_1278897
  have hstable : (prefixWord ++ tailWord_1278897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278897).length < 2 ^ (prefixWord ++ tailWord_1278897).sum := by decide
  have hdescent : baseEnd_1278897 < baseStart_1278897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278901 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1278901 : Nat := 118140960795 + 1278901 * 2 ^ 59
def prefixEnd_1278901 : Nat := 4983230072969 + 3 ^ 40 * 1278901 * 2
def baseEnd_1278901 : Nat := 437793948343870685103965

theorem tailTrace_1278901 : CollatzResearch.WordTrace tailWord_1278901 prefixEnd_1278901 437793948343870685103965 := by
  unfold tailWord_1278901
  simp only [CollatzResearch.WordTrace]
  refine ⟨46645351539767570746692557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31096901026511713831128371 46645351539767570746692557)
  ·
    refine ⟨17492006827412839030009709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46645351539767570746692557 17492006827412839030009709)
    ·
      refine ⟨6559502560279814636253641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17492006827412839030009709 6559502560279814636253641)
      ·
        refine ⟨4919626920209860977190231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6559502560279814636253641 4919626920209860977190231)
        ·
          refine ⟨7379440380314791465785347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4919626920209860977190231 7379440380314791465785347)
          ·
            refine ⟨11069160570472187198678021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379440380314791465785347 11069160570472187198678021)
            ·
              refine ⟨2075467606963535099752129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11069160570472187198678021 2075467606963535099752129)
              ·
                refine ⟨1556600705222651324814097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075467606963535099752129 1556600705222651324814097)
                ·
                  refine ⟨1167450528916988493610573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1556600705222651324814097 1167450528916988493610573)
                  ·
                    refine ⟨437793948343870685103965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167450528916988493610573 437793948343870685103965)
                    ·
                      rfl

theorem cell22_1278901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1278901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278901 prefixEnd_1278901 := by exact prefixLift 1278901
  have htrace : WordTrace (prefixWord ++ tailWord_1278901) baseStart_1278901 baseEnd_1278901 := by
    simpa [prefixWord, tailWord_1278901, baseEnd_1278901] using wordTrace_append hprefix tailTrace_1278901
  have hstable : (prefixWord ++ tailWord_1278901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278901).length < 2 ^ (prefixWord ++ tailWord_1278901).sum := by decide
  have hdescent : baseEnd_1278901 < baseStart_1278901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278929 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 3, 3]
def baseStart_1278929 : Nat := 118140960795 + 1278929 * 2 ^ 59
def prefixEnd_1278929 : Nat := 4983230072969 + 3 ^ 40 * 1278929 * 2
def baseEnd_1278929 : Nat := 437803533316087945403879

theorem tailTrace_1278929 : CollatzResearch.WordTrace tailWord_1278929 prefixEnd_1278929 437803533316087945403879 := by
  unfold tailWord_1278929
  simp only [CollatzResearch.WordTrace]
  refine ⟨46646372783666131528711841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31097581855777421019141227 46646372783666131528711841)
  ·
    refine ⟨34984779587749598646533881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46646372783666131528711841 34984779587749598646533881)
    ·
      refine ⟨26238584690812198984900411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34984779587749598646533881 26238584690812198984900411)
      ·
        refine ⟨39357877036218298477350617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26238584690812198984900411 39357877036218298477350617)
        ·
          refine ⟨29518407777163723858012963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39357877036218298477350617 29518407777163723858012963)
          ·
            refine ⟨44277611665745585787019445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29518407777163723858012963 44277611665745585787019445)
            ·
              refine ⟨4151026093663648667533073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44277611665745585787019445 4151026093663648667533073)
              ·
                refine ⟨3113269570247736500649805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4151026093663648667533073 3113269570247736500649805)
                ·
                  refine ⟨1167476088842901187743677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3113269570247736500649805 1167476088842901187743677)
                  ·
                    refine ⟨437803533316087945403879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167476088842901187743677 437803533316087945403879)
                    ·
                      rfl

theorem cell22_1278929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_1278929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278929 prefixEnd_1278929 := by exact prefixLift 1278929
  have htrace : WordTrace (prefixWord ++ tailWord_1278929) baseStart_1278929 baseEnd_1278929 := by
    simpa [prefixWord, tailWord_1278929, baseEnd_1278929] using wordTrace_append hprefix tailTrace_1278929
  have hstable : (prefixWord ++ tailWord_1278929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278929).length < 2 ^ (prefixWord ++ tailWord_1278929).sum := by decide
  have hdescent : baseEnd_1278929 < baseStart_1278929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278933 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 2, 4]
def baseStart_1278933 : Nat := 118140960795 + 1278933 * 2 ^ 59
def prefixEnd_1278933 : Nat := 4983230072969 + 3 ^ 40 * 1278933 * 2
def baseEnd_1278933 : Nat := 437804902597833268303867

theorem tailTrace_1278933 : CollatzResearch.WordTrace tailWord_1278933 prefixEnd_1278933 437804902597833268303867 := by
  unfold tailWord_1278933
  simp only [CollatzResearch.WordTrace]
  refine ⟨46646518675651640211857453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31097679117101093474571635 46646518675651640211857453)
  ·
    refine ⟨17492444503369365079446545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46646518675651640211857453 17492444503369365079446545)
    ·
      refine ⟨13119333377527023809584909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17492444503369365079446545 13119333377527023809584909)
      ·
        refine ⟨4919750016572633928594341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13119333377527023809584909 4919750016572633928594341)
        ·
          refine ⟨922453128107368861611439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4919750016572633928594341 922453128107368861611439)
          ·
            refine ⟨1383679692161053292417159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922453128107368861611439 1383679692161053292417159)
            ·
              refine ⟨2075519538241579938625739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383679692161053292417159 2075519538241579938625739)
              ·
                refine ⟨3113279307362369907938609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075519538241579938625739 3113279307362369907938609)
                ·
                  refine ⟨2334959480521777430953957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3113279307362369907938609 2334959480521777430953957)
                  ·
                    refine ⟨437804902597833268303867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2334959480521777430953957 437804902597833268303867)
                    ·
                      rfl

theorem cell22_1278933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_1278933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278933 prefixEnd_1278933 := by exact prefixLift 1278933
  have htrace : WordTrace (prefixWord ++ tailWord_1278933) baseStart_1278933 baseEnd_1278933 := by
    simpa [prefixWord, tailWord_1278933, baseEnd_1278933] using wordTrace_append hprefix tailTrace_1278933
  have hstable : (prefixWord ++ tailWord_1278933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278933).length < 2 ^ (prefixWord ++ tailWord_1278933).sum := by decide
  have hdescent : baseEnd_1278933 < baseStart_1278933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1278959 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 5]
def baseStart_1278959 : Nat := 118140960795 + 1278959 * 2 ^ 59
def prefixEnd_1278959 : Nat := 4983230072969 + 3 ^ 40 * 1278959 * 2
def baseEnd_1278959 : Nat := 145937934309725955717929

theorem tailTrace_1278959 : CollatzResearch.WordTrace tailWord_1278959 prefixEnd_1278959 145937934309725955717929 := by
  unfold tailWord_1278959
  simp only [CollatzResearch.WordTrace]
  refine ⟨46647466973557446652303931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31098311315704964434869287 46647466973557446652303931)
  ·
    refine ⟨69971200460336169978455897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46647466973557446652303931 69971200460336169978455897)
    ·
      refine ⟨52478400345252127483841923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69971200460336169978455897 52478400345252127483841923)
      ·
        refine ⟨78717600517878191225762885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52478400345252127483841923 78717600517878191225762885)
        ·
          refine ⟨14759550097102160854830541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78717600517878191225762885 14759550097102160854830541)
          ·
            refine ⟨5534831286413310320561453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14759550097102160854830541 5534831286413310320561453)
            ·
              refine ⟨2075561732404991370210545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5534831286413310320561453 2075561732404991370210545)
              ·
                refine ⟨1556671299303743527657909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075561732404991370210545 1556671299303743527657909)
                ·
                  refine ⟨145937934309725955717929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1556671299303743527657909 145937934309725955717929)
                  ·
                    rfl

theorem cell22_1278959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 5].length) (baseStart_1278959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1278959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1278959 prefixEnd_1278959 := by exact prefixLift 1278959
  have htrace : WordTrace (prefixWord ++ tailWord_1278959) baseStart_1278959 baseEnd_1278959 := by
    simpa [prefixWord, tailWord_1278959, baseEnd_1278959] using wordTrace_append hprefix tailTrace_1278959
  have hstable : (prefixWord ++ tailWord_1278959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1278959).length < 2 ^ (prefixWord ++ tailWord_1278959).sum := by decide
  have hdescent : baseEnd_1278959 < baseStart_1278959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1278959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279019 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 4, 3]
def baseStart_1279019 : Nat := 118140960795 + 1279019 * 2 ^ 59
def prefixEnd_1279019 : Nat := 4983230072969 + 3 ^ 40 * 1279019 * 2
def baseEnd_1279019 : Nat := 437834342155357710653603

theorem tailTrace_1279019 : CollatzResearch.WordTrace tailWord_1279019 prefixEnd_1279019 437834342155357710653603 := by
  unfold tailWord_1279019
  simp only [CollatzResearch.WordTrace]
  refine ⟨46649655353340076899488111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31099770235560051266325407 46649655353340076899488111)
  ·
    refine ⟨69974483030010115349232167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46649655353340076899488111 69974483030010115349232167)
    ·
      refine ⟨104961724545015173023848251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69974483030010115349232167 104961724545015173023848251)
      ·
        refine ⟨157442586817522759535772377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104961724545015173023848251 157442586817522759535772377)
        ·
          refine ⟨118081940113142069651829283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157442586817522759535772377 118081940113142069651829283)
          ·
            refine ⟨177122910169713104477743925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118081940113142069651829283 177122910169713104477743925)
            ·
              refine ⟨16605272828410603544788493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177122910169713104477743925 16605272828410603544788493)
              ·
                refine ⟨6226977310653976329295685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16605272828410603544788493 6226977310653976329295685)
                ·
                  refine ⟨1167558245747620561742941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6226977310653976329295685 1167558245747620561742941)
                  ·
                    refine ⟨437834342155357710653603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167558245747620561742941 437834342155357710653603)
                    ·
                      rfl

theorem cell22_1279019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 3].length) (baseStart_1279019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279019 prefixEnd_1279019 := by exact prefixLift 1279019
  have htrace : WordTrace (prefixWord ++ tailWord_1279019) baseStart_1279019 baseEnd_1279019 := by
    simpa [prefixWord, tailWord_1279019, baseEnd_1279019] using wordTrace_append hprefix tailTrace_1279019
  have hstable : (prefixWord ++ tailWord_1279019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279019).length < 2 ^ (prefixWord ++ tailWord_1279019).sum := by decide
  have hdescent : baseEnd_1279019 < baseStart_1279019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279079 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1279079 : Nat := 118140960795 + 1279079 * 2 ^ 59
def prefixEnd_1279079 : Nat := 4983230072969 + 3 ^ 40 * 1279079 * 2
def baseEnd_1279079 : Nat := 437854881381537554153419

theorem tailTrace_1279079 : CollatzResearch.WordTrace tailWord_1279079 prefixEnd_1279079 437854881381537554153419 := by
  unfold tailWord_1279079
  simp only [CollatzResearch.WordTrace]
  refine ⟨46651843733122707146672291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31101229155415138097781527 46651843733122707146672291)
  ·
    refine ⟨69977765599684060720008437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46651843733122707146672291 69977765599684060720008437)
    ·
      refine ⟨6560415524970380692500791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69977765599684060720008437 6560415524970380692500791)
      ·
        refine ⟨9840623287455571038751187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6560415524970380692500791 9840623287455571038751187)
        ·
          refine ⟨14760934931183356558126781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9840623287455571038751187 14760934931183356558126781)
          ·
            refine ⟨5535350599193758709297543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14760934931183356558126781 5535350599193758709297543)
            ·
              refine ⟨8303025898790638063946315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5535350599193758709297543 8303025898790638063946315)
              ·
                refine ⟨12454538848185957095919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8303025898790638063946315 12454538848185957095919473)
                ·
                  refine ⟨9340904136139467821939605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12454538848185957095919473 9340904136139467821939605)
                  ·
                    refine ⟨437854881381537554153419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9340904136139467821939605 437854881381537554153419)
                    ·
                      rfl

theorem cell22_1279079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1279079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279079 prefixEnd_1279079 := by exact prefixLift 1279079
  have htrace : WordTrace (prefixWord ++ tailWord_1279079) baseStart_1279079 baseEnd_1279079 := by
    simpa [prefixWord, tailWord_1279079, baseEnd_1279079] using wordTrace_append hprefix tailTrace_1279079
  have hstable : (prefixWord ++ tailWord_1279079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279079).length < 2 ^ (prefixWord ++ tailWord_1279079).sum := by decide
  have hdescent : baseEnd_1279079 < baseStart_1279079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279128 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 5]
def baseStart_1279128 : Nat := 118140960795 + 1279128 * 2 ^ 59
def prefixEnd_1279128 : Nat := 4983230072969 + 3 ^ 40 * 1279128 * 2
def baseEnd_1279128 : Nat := 145957218360972586559423

theorem tailTrace_1279128 : CollatzResearch.WordTrace tailWord_1279128 prefixEnd_1279128 145957218360972586559423 := by
  unfold tailWord_1279128
  simp only [CollatzResearch.WordTrace]
  refine ⟨23326815454972594257603019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31102420606630125676804025 23326815454972594257603019)
  ·
    refine ⟨34990223182458891386404529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23326815454972594257603019 34990223182458891386404529)
    ·
      refine ⟨26242667386844168539803397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34990223182458891386404529 26242667386844168539803397)
      ·
        refine ⟨4920500135033281601213137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26242667386844168539803397 4920500135033281601213137)
        ·
          refine ⟨3690375101274961200909853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4920500135033281601213137 3690375101274961200909853)
          ·
            refine ⟨1383890662978110450341195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3690375101274961200909853 1383890662978110450341195)
            ·
              refine ⟨2075835994467165675511793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383890662978110450341195 2075835994467165675511793)
              ·
                refine ⟨1556876995850374256633845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075835994467165675511793 1556876995850374256633845)
                ·
                  refine ⟨145957218360972586559423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1556876995850374256633845 145957218360972586559423)
                  ·
                    rfl

theorem cell22_1279128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_1279128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279128 prefixEnd_1279128 := by exact prefixLift 1279128
  have htrace : WordTrace (prefixWord ++ tailWord_1279128) baseStart_1279128 baseEnd_1279128 := by
    simpa [prefixWord, tailWord_1279128, baseEnd_1279128] using wordTrace_append hprefix tailTrace_1279128
  have hstable : (prefixWord ++ tailWord_1279128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279128).length < 2 ^ (prefixWord ++ tailWord_1279128).sum := by decide
  have hdescent : baseEnd_1279128 < baseStart_1279128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279201 : List Nat := [1, 2, 3, 1, 3, 3, 2, 7]
def baseStart_1279201 : Nat := 118140960795 + 1279201 * 2 ^ 59
def prefixEnd_1279201 : Nat := 4983230072969 + 3 ^ 40 * 1279201 * 2
def baseEnd_1279201 : Nat := 48655182719418878067005

theorem tailTrace_1279201 : CollatzResearch.WordTrace tailWord_1279201 prefixEnd_1279201 48655182719418878067005 := by
  unfold tailWord_1279201
  simp only [CollatzResearch.WordTrace]
  refine ⟨46656293438680721982613457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31104195625787147988408971 46656293438680721982613457)
  ·
    refine ⟨34992220079010541486960093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46656293438680721982613457 34992220079010541486960093)
    ·
      refine ⟨13122082529628953057610035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34992220079010541486960093 13122082529628953057610035)
      ·
        refine ⟨19683123794443429586415053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13122082529628953057610035 19683123794443429586415053)
        ·
          refine ⟨7381171422916286094905645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19683123794443429586415053 7381171422916286094905645)
          ·
            refine ⟨2767939283593607285589617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7381171422916286094905645 2767939283593607285589617)
            ·
              refine ⟨2075954462695205464192213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2767939283593607285589617 2075954462695205464192213)
              ·
                refine ⟨48655182719418878067005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2075954462695205464192213 48655182719418878067005)
                ·
                  rfl

theorem cell22_1279201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 7].length) (baseStart_1279201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279201 prefixEnd_1279201 := by exact prefixLift 1279201
  have htrace : WordTrace (prefixWord ++ tailWord_1279201) baseStart_1279201 baseEnd_1279201 := by
    simpa [prefixWord, tailWord_1279201, baseEnd_1279201] using wordTrace_append hprefix tailTrace_1279201
  have hstable : (prefixWord ++ tailWord_1279201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279201).length < 2 ^ (prefixWord ++ tailWord_1279201).sum := by decide
  have hdescent : baseEnd_1279201 < baseStart_1279201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1279205 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_1279205 : Nat := 118140960795 + 1279205 * 2 ^ 59
def prefixEnd_1279205 : Nat := 4983230072969 + 3 ^ 40 * 1279205 * 2
def baseEnd_1279205 : Nat := 437898013756515225503033

theorem tailTrace_1279205 : CollatzResearch.WordTrace tailWord_1279205 prefixEnd_1279205 437898013756515225503033 := by
  unfold tailWord_1279205
  simp only [CollatzResearch.WordTrace]
  refine ⟨46656439330666230665759069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31104292887110820443839379 46656439330666230665759069)
  ·
    refine ⟨17496164748999836499659651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46656439330666230665759069 17496164748999836499659651)
    ·
      refine ⟨26244247123499754749489477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17496164748999836499659651 26244247123499754749489477)
      ·
        refine ⟨4920796335656204015529277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26244247123499754749489477 4920796335656204015529277)
        ·
          refine ⟨1845298625871076505823479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4920796335656204015529277 1845298625871076505823479)
          ·
            refine ⟨2767947938806614758735219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845298625871076505823479 2767947938806614758735219)
            ·
              refine ⟨4151921908209922138102829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2767947938806614758735219 4151921908209922138102829)
              ·
                refine ⟨1556970715578720801788561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4151921908209922138102829 1556970715578720801788561)
                ·
                  refine ⟨1167728036684040601341421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1556970715578720801788561 1167728036684040601341421)
                  ·
                    refine ⟨437898013756515225503033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167728036684040601341421 437898013756515225503033)
                    ·
                      rfl

theorem cell22_1279205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_1279205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1279205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1279205 prefixEnd_1279205 := by exact prefixLift 1279205
  have htrace : WordTrace (prefixWord ++ tailWord_1279205) baseStart_1279205 baseEnd_1279205 := by
    simpa [prefixWord, tailWord_1279205, baseEnd_1279205] using wordTrace_append hprefix tailTrace_1279205
  have hstable : (prefixWord ++ tailWord_1279205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1279205).length < 2 ^ (prefixWord ++ tailWord_1279205).sum := by decide
  have hdescent : baseEnd_1279205 < baseStart_1279205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1279205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
