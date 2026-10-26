import V185TrunkScan20Chunk117

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_718178 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_718178 : Nat := 118140960795 + 718178 * 2 ^ 59
def prefixEnd_718178 : Nat := 4983230072969 + 3 ^ 40 * 718178 * 2
def baseEnd_718178 : Nat := 327796008430930096864147

theorem tailTrace_718178 : CollatzResearch.WordTrace tailWord_718178 prefixEnd_718178 327796008430930096864147 := by
  unfold tailWord_718178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6548525898042808970610797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17462735728114157254962125 6548525898042808970610797)
  ·
    refine ⟨2455697211766053363979049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6548525898042808970610797 2455697211766053363979049)
    ·
      refine ⟨1841772908824540022984287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2455697211766053363979049 1841772908824540022984287)
      ·
        refine ⟨2762659363236810034476431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841772908824540022984287 2762659363236810034476431)
        ·
          refine ⟨4143989044855215051714647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762659363236810034476431 4143989044855215051714647)
          ·
            refine ⟨6215983567282822577571971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143989044855215051714647 6215983567282822577571971)
            ·
              refine ⟨9323975350924233866357957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6215983567282822577571971 9323975350924233866357957)
              ·
                refine ⟨1748245378298293849942117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9323975350924233866357957 1748245378298293849942117)
                ·
                  refine ⟨327796008430930096864147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748245378298293849942117 327796008430930096864147)
                  ·
                    rfl

theorem cell20_718178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_718178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718178 prefixEnd_718178 := by exact prefixLift 718178
  have htrace : WordTrace (prefixWord ++ tailWord_718178) baseStart_718178 baseEnd_718178 := by
    simpa [prefixWord, tailWord_718178, baseEnd_718178] using wordTrace_append hprefix tailTrace_718178
  have hstable : (prefixWord ++ tailWord_718178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718178).length < 2 ^ (prefixWord ++ tailWord_718178).sum := by decide
  have hdescent : baseEnd_718178 < baseStart_718178 := by decide
  rcases family_descends (prefixWord ++ tailWord_718178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718212 : List Nat := [2, 3, 2, 1, 1, 4, 3, 2, 2]
def baseStart_718212 : Nat := 118140960795 + 718212 * 2 ^ 59
def prefixEnd_718212 : Nat := 4983230072969 + 3 ^ 40 * 718212 * 2
def baseEnd_718212 : Nat := 327811526957377089730675

theorem tailTrace_718212 : CollatzResearch.WordTrace tailWord_718212 prefixEnd_718212 327811526957377089730675 := by
  unfold tailWord_718212
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097671837024029844590445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17463562449365373126120593 13097671837024029844590445)
  ·
    refine ⟨4911626938884011191721417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13097671837024029844590445 4911626938884011191721417)
    ·
      refine ⟨3683720204163008393791063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4911626938884011191721417 3683720204163008393791063)
      ·
        refine ⟨5525580306244512590686595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3683720204163008393791063 5525580306244512590686595)
        ·
          refine ⟨8288370459366768886029893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525580306244512590686595 8288370459366768886029893)
          ·
            refine ⟨1554069461131269166130605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8288370459366768886029893 1554069461131269166130605)
            ·
              refine ⟨582776047924225937298977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1554069461131269166130605 582776047924225937298977)
              ·
                refine ⟨437082035943169452974233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582776047924225937298977 437082035943169452974233)
                ·
                  refine ⟨327811526957377089730675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437082035943169452974233 327811526957377089730675)
                  ·
                    rfl

theorem cell20_718212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_718212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718212 prefixEnd_718212 := by exact prefixLift 718212
  have htrace : WordTrace (prefixWord ++ tailWord_718212) baseStart_718212 baseEnd_718212 := by
    simpa [prefixWord, tailWord_718212, baseEnd_718212] using wordTrace_append hprefix tailTrace_718212
  have hstable : (prefixWord ++ tailWord_718212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718212).length < 2 ^ (prefixWord ++ tailWord_718212).sum := by decide
  have hdescent : baseEnd_718212 < baseStart_718212 := by decide
  rcases family_descends (prefixWord ++ tailWord_718212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718216 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_718216 : Nat := 118140960795 + 718216 * 2 ^ 59
def prefixEnd_718216 : Nat := 4983230072969 + 3 ^ 40 * 718216 * 2
def baseEnd_718216 : Nat := 327813352666370853597325

theorem tailTrace_718216 : CollatzResearch.WordTrace tailWord_718216 prefixEnd_718216 327813352666370853597325 := by
  unfold tailWord_718216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13097744783016784186163251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17463659710689045581551001 13097744783016784186163251)
  ·
    refine ⟨19646617174525176279244877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13097744783016784186163251 19646617174525176279244877)
    ·
      refine ⟨7367481440446941104716829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19646617174525176279244877 7367481440446941104716829)
      ·
        refine ⟨2762805540167602914268811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7367481440446941104716829 2762805540167602914268811)
        ·
          refine ⟨4144208310251404371403217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2762805540167602914268811 4144208310251404371403217)
          ·
            refine ⟨3108156232688553278552413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4144208310251404371403217 3108156232688553278552413)
            ·
              refine ⟨1165558587258207479457155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3108156232688553278552413 1165558587258207479457155)
              ·
                refine ⟨1748337880887311219185733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165558587258207479457155 1748337880887311219185733)
                ·
                  refine ⟨327813352666370853597325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748337880887311219185733 327813352666370853597325)
                  ·
                    rfl

theorem cell20_718216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_718216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718216 prefixEnd_718216 := by exact prefixLift 718216
  have htrace : WordTrace (prefixWord ++ tailWord_718216) baseStart_718216 baseEnd_718216 := by
    simpa [prefixWord, tailWord_718216, baseEnd_718216] using wordTrace_append hprefix tailTrace_718216
  have hstable : (prefixWord ++ tailWord_718216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718216).length < 2 ^ (prefixWord ++ tailWord_718216).sum := by decide
  have hdescent : baseEnd_718216 < baseStart_718216 := by decide
  rcases family_descends (prefixWord ++ tailWord_718216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718222 : List Nat := [4, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_718222 : Nat := 118140960795 + 718222 * 2 ^ 59
def prefixEnd_718222 : Nat := 4983230072969 + 3 ^ 40 * 718222 * 2
def baseEnd_718222 : Nat := 327816091229861499397301

theorem tailTrace_718222 : CollatzResearch.WordTrace tailWord_718222 prefixEnd_718222 327816091229861499397301 := by
  unfold tailWord_718222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3274463550501478924630615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17463805602674554264696613 3274463550501478924630615)
  ·
    refine ⟨4911695325752218386945923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3274463550501478924630615 4911695325752218386945923)
    ·
      refine ⟨7367542988628327580418885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4911695325752218386945923 7367542988628327580418885)
      ·
        refine ⟨1381414310367811421328541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7367542988628327580418885 1381414310367811421328541)
        ·
          refine ⟨518030366387929282998203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1381414310367811421328541 518030366387929282998203)
          ·
            refine ⟨777045549581893924497305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518030366387929282998203 777045549581893924497305)
            ·
              refine ⟨582784162186420443372979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777045549581893924497305 582784162186420443372979)
              ·
                refine ⟨874176243279630665059469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582784162186420443372979 874176243279630665059469)
                ·
                  refine ⟨327816091229861499397301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874176243279630665059469 327816091229861499397301)
                  ·
                    rfl

theorem cell20_718222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_718222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718222 prefixEnd_718222 := by exact prefixLift 718222
  have htrace : WordTrace (prefixWord ++ tailWord_718222) baseStart_718222 baseEnd_718222 := by
    simpa [prefixWord, tailWord_718222, baseEnd_718222] using wordTrace_append hprefix tailTrace_718222
  have hstable : (prefixWord ++ tailWord_718222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718222).length < 2 ^ (prefixWord ++ tailWord_718222).sum := by decide
  have hdescent : baseEnd_718222 < baseStart_718222 := by decide
  rcases family_descends (prefixWord ++ tailWord_718222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718289 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_718289 : Nat := 118140960795 + 718289 * 2 ^ 59
def prefixEnd_718289 : Nat := 4983230072969 + 3 ^ 40 * 718289 * 2
def baseEnd_718289 : Nat := 327846671855507044163693

theorem tailTrace_718289 : CollatzResearch.WordTrace tailWord_718289 prefixEnd_718289 327846671855507044163693 := by
  unfold tailWord_718289
  simp only [CollatzResearch.WordTrace]
  refine ⟨26198152094769101839733921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17465434729846067893155947 26198152094769101839733921)
  ·
    refine ⟨19648614071076826379800441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26198152094769101839733921 19648614071076826379800441)
    ·
      refine ⟨14736460553307619784850331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19648614071076826379800441 14736460553307619784850331)
      ·
        refine ⟨22104690829961429677275497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14736460553307619784850331 22104690829961429677275497)
        ·
          refine ⟨16578518122471072257956623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22104690829961429677275497 16578518122471072257956623)
          ·
            refine ⟨24867777183706608386934935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16578518122471072257956623 24867777183706608386934935)
            ·
              refine ⟨37301665775559912580402403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24867777183706608386934935 37301665775559912580402403)
              ·
                refine ⟨55952498663339868870603605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37301665775559912580402403 55952498663339868870603605)
                ·
                  refine ⟨327846671855507044163693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55952498663339868870603605 327846671855507044163693)
                  ·
                    rfl

theorem cell20_718289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_718289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718289 prefixEnd_718289 := by exact prefixLift 718289
  have htrace : WordTrace (prefixWord ++ tailWord_718289) baseStart_718289 baseEnd_718289 := by
    simpa [prefixWord, tailWord_718289, baseEnd_718289] using wordTrace_append hprefix tailTrace_718289
  have hstable : (prefixWord ++ tailWord_718289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718289).length < 2 ^ (prefixWord ++ tailWord_718289).sum := by decide
  have hdescent : baseEnd_718289 < baseStart_718289 := by decide
  rcases family_descends (prefixWord ++ tailWord_718289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718309 : List Nat := [1, 3, 1, 5, 1, 1, 1, 5, 2]
def baseStart_718309 : Nat := 118140960795 + 718309 * 2 ^ 59
def prefixEnd_718309 : Nat := 4983230072969 + 3 ^ 40 * 718309 * 2
def baseEnd_718309 : Nat := 327855800400475863496945

theorem tailTrace_718309 : CollatzResearch.WordTrace tailWord_718309 prefixEnd_718309 327855800400475863496945 := by
  unfold tailWord_718309
  simp only [CollatzResearch.WordTrace]
  refine ⟨26198881554696645255461981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17465921036464430170307987 26198881554696645255461981)
  ·
    refine ⟨9824580583011241970798243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26198881554696645255461981 9824580583011241970798243)
    ·
      refine ⟨14736870874516862956197365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9824580583011241970798243 14736870874516862956197365)
      ·
        refine ⟨1381581644485955902143503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14736870874516862956197365 1381581644485955902143503)
        ·
          refine ⟨2072372466728933853215255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381581644485955902143503 2072372466728933853215255)
          ·
            refine ⟨3108558700093400779822883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072372466728933853215255 3108558700093400779822883)
            ·
              refine ⟨4662838050140101169734325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3108558700093400779822883 4662838050140101169734325)
              ·
                refine ⟨437141067200634484662593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4662838050140101169734325 437141067200634484662593)
                ·
                  refine ⟨327855800400475863496945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437141067200634484662593 327855800400475863496945)
                  ·
                    rfl

theorem cell20_718309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_718309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718309 prefixEnd_718309 := by exact prefixLift 718309
  have htrace : WordTrace (prefixWord ++ tailWord_718309) baseStart_718309 baseEnd_718309 := by
    simpa [prefixWord, tailWord_718309, baseEnd_718309] using wordTrace_append hprefix tailTrace_718309
  have hstable : (prefixWord ++ tailWord_718309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718309).length < 2 ^ (prefixWord ++ tailWord_718309).sum := by decide
  have hdescent : baseEnd_718309 < baseStart_718309 := by decide
  rcases family_descends (prefixWord ++ tailWord_718309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718320 : List Nat := [2, 1, 1, 1, 3, 5, 7]
def baseStart_718320 : Nat := 118140960795 + 718320 * 2 ^ 59
def prefixEnd_718320 : Nat := 4983230072969 + 3 ^ 40 * 718320 * 2
def baseEnd_718320 : Nat := 36428980122245412681137

theorem tailTrace_718320 : CollatzResearch.WordTrace tailWord_718320 prefixEnd_718320 36428980122245412681137 := by
  unfold tailWord_718320
  simp only [CollatzResearch.WordTrace]
  refine ⟨13099641378828397067056207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17466188505104529422741609 13099641378828397067056207)
  ·
    refine ⟨19649462068242595600584311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13099641378828397067056207 19649462068242595600584311)
    ·
      refine ⟨29474193102363893400876467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19649462068242595600584311 29474193102363893400876467)
      ·
        refine ⟨44211289653545840101314701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29474193102363893400876467 44211289653545840101314701)
        ·
          refine ⟨16579233620079690037993013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44211289653545840101314701 16579233620079690037993013)
          ·
            refine ⟨1554303151882470941061845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16579233620079690037993013 1554303151882470941061845)
            ·
              refine ⟨36428980122245412681137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1554303151882470941061845 36428980122245412681137)
              ·
                rfl

theorem cell20_718320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 7].length) (baseStart_718320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718320 prefixEnd_718320 := by exact prefixLift 718320
  have htrace : WordTrace (prefixWord ++ tailWord_718320) baseStart_718320 baseEnd_718320 := by
    simpa [prefixWord, tailWord_718320, baseEnd_718320] using wordTrace_append hprefix tailTrace_718320
  have hstable : (prefixWord ++ tailWord_718320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718320).length < 2 ^ (prefixWord ++ tailWord_718320).sum := by decide
  have hdescent : baseEnd_718320 < baseStart_718320 := by decide
  rcases family_descends (prefixWord ++ tailWord_718320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718330 : List Nat := [3, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_718330 : Nat := 118140960795 + 718330 * 2 ^ 59
def prefixEnd_718330 : Nat := 4983230072969 + 3 ^ 40 * 718330 * 2
def baseEnd_718330 : Nat := 327865385372693123796859

theorem tailTrace_718330 : CollatzResearch.WordTrace tailWord_718330 prefixEnd_718330 327865385372693123796859 := by
  unfold tailWord_718330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6549911871905141460494111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17466431658413710561317629 6549911871905141460494111)
  ·
    refine ⟨9824867807857712190741167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6549911871905141460494111 9824867807857712190741167)
    ·
      refine ⟨14737301711786568286111751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9824867807857712190741167 14737301711786568286111751)
      ·
        refine ⟨22105952567679852429167627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14737301711786568286111751 22105952567679852429167627)
        ·
          refine ⟨33158928851519778643751441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22105952567679852429167627 33158928851519778643751441)
          ·
            refine ⟨24869196638639833982813581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33158928851519778643751441 24869196638639833982813581)
            ·
              refine ⟨9325948739489937743555093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24869196638639833982813581 9325948739489937743555093)
              ·
                refine ⟨437153847163590831729145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9325948739489937743555093 437153847163590831729145)
                ·
                  refine ⟨327865385372693123796859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437153847163590831729145 327865385372693123796859)
                  ·
                    rfl

theorem cell20_718330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_718330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718330 prefixEnd_718330 := by exact prefixLift 718330
  have htrace : WordTrace (prefixWord ++ tailWord_718330) baseStart_718330 baseEnd_718330 := by
    simpa [prefixWord, tailWord_718330, baseEnd_718330] using wordTrace_append hprefix tailTrace_718330
  have hstable : (prefixWord ++ tailWord_718330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718330).length < 2 ^ (prefixWord ++ tailWord_718330).sum := by decide
  have hdescent : baseEnd_718330 < baseStart_718330 := by decide
  rcases family_descends (prefixWord ++ tailWord_718330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718344 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_718344 : Nat := 118140960795 + 718344 * 2 ^ 59
def prefixEnd_718344 : Nat := 4983230072969 + 3 ^ 40 * 718344 * 2
def baseEnd_718344 : Nat := 327871775354171297330135

theorem tailTrace_718344 : CollatzResearch.WordTrace tailWord_718344 prefixEnd_718344 327871775354171297330135 := by
  unfold tailWord_718344
  simp only [CollatzResearch.WordTrace]
  refine ⟨13100079054784923116493043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17466772073046564155324057 13100079054784923116493043)
  ·
    refine ⟨19650118582177384674739565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13100079054784923116493043 19650118582177384674739565)
    ·
      refine ⟨7368794468316519253027337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19650118582177384674739565 7368794468316519253027337)
      ·
        refine ⟨5526595851237389439770503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7368794468316519253027337 5526595851237389439770503)
        ·
          refine ⟨8289893776856084159655755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526595851237389439770503 8289893776856084159655755)
          ·
            refine ⟨12434840665284126239483633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289893776856084159655755 12434840665284126239483633)
            ·
              refine ⟨9326130498963094679612725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12434840665284126239483633 9326130498963094679612725)
              ·
                refine ⟨874324734277790126213693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9326130498963094679612725 874324734277790126213693)
                ·
                  refine ⟨327871775354171297330135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874324734277790126213693 327871775354171297330135)
                  ·
                    rfl

theorem cell20_718344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_718344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718344 prefixEnd_718344 := by exact prefixLift 718344
  have htrace : WordTrace (prefixWord ++ tailWord_718344) baseStart_718344 baseEnd_718344 := by
    simpa [prefixWord, tailWord_718344, baseEnd_718344] using wordTrace_append hprefix tailTrace_718344
  have hstable : (prefixWord ++ tailWord_718344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718344).length < 2 ^ (prefixWord ++ tailWord_718344).sum := by decide
  have hdescent : baseEnd_718344 < baseStart_718344 := by decide
  rcases family_descends (prefixWord ++ tailWord_718344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718399 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 3]
def baseStart_718399 : Nat := 118140960795 + 718399 * 2 ^ 59
def prefixEnd_718399 : Nat := 4983230072969 + 3 ^ 40 * 718399 * 2
def baseEnd_718399 : Nat := 327896878852835550496577

theorem tailTrace_718399 : CollatzResearch.WordTrace tailWord_718399 prefixEnd_718399 327896878852835550496577 := by
  unfold tailWord_718399
  simp only [CollatzResearch.WordTrace]
  refine ⟨26202164124370590626238251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17468109416247060417492167 26202164124370590626238251)
  ·
    refine ⟨39303246186555885939357377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26202164124370590626238251 39303246186555885939357377)
    ·
      refine ⟨29477434639916914454518033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39303246186555885939357377 29477434639916914454518033)
      ·
        refine ⟨22108075979937685840888525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29477434639916914454518033 22108075979937685840888525)
        ·
          refine ⟨8290528492476632190333197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22108075979937685840888525 8290528492476632190333197)
          ·
            refine ⟨3108948184678737071374949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8290528492476632190333197 3108948184678737071374949)
            ·
              refine ⟨582927784627263200882803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3108948184678737071374949 582927784627263200882803)
              ·
                refine ⟨874391676940894801324205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582927784627263200882803 874391676940894801324205)
                ·
                  refine ⟨327896878852835550496577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874391676940894801324205 327896878852835550496577)
                  ·
                    rfl

theorem cell20_718399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 3].length) (baseStart_718399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718399 prefixEnd_718399 := by exact prefixLift 718399
  have htrace : WordTrace (prefixWord ++ tailWord_718399) baseStart_718399 baseEnd_718399 := by
    simpa [prefixWord, tailWord_718399, baseEnd_718399] using wordTrace_append hprefix tailTrace_718399
  have hstable : (prefixWord ++ tailWord_718399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718399).length < 2 ^ (prefixWord ++ tailWord_718399).sum := by decide
  have hdescent : baseEnd_718399 < baseStart_718399 := by decide
  rcases family_descends (prefixWord ++ tailWord_718399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718434 : List Nat := [3, 3, 2, 12]
def baseStart_718434 : Nat := 118140960795 + 718434 * 2 ^ 59
def prefixEnd_718434 : Nat := 4983230072969 + 3 ^ 40 * 718434 * 2
def baseEnd_718434 : Nat := 1349435612372555491069

theorem tailTrace_718434 : CollatzResearch.WordTrace tailWord_718434 prefixEnd_718434 1349435612372555491069 := by
  unfold tailWord_718434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550860169810947900940589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17468960452829194402508237 6550860169810947900940589)
  ·
    refine ⟨2456572563679105462852721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6550860169810947900940589 2456572563679105462852721)
    ·
      refine ⟨1842429422759329097139541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2456572563679105462852721 1842429422759329097139541)
      ·
        refine ⟨1349435612372555491069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1842429422759329097139541 1349435612372555491069)
        ·
          rfl

theorem cell20_718434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 12].length) (baseStart_718434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718434 prefixEnd_718434 := by exact prefixLift 718434
  have htrace : WordTrace (prefixWord ++ tailWord_718434) baseStart_718434 baseEnd_718434 := by
    simpa [prefixWord, tailWord_718434, baseEnd_718434] using wordTrace_append hprefix tailTrace_718434
  have hstable : (prefixWord ++ tailWord_718434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718434).length < 2 ^ (prefixWord ++ tailWord_718434).sum := by decide
  have hdescent : baseEnd_718434 < baseStart_718434 := by decide
  rcases family_descends (prefixWord ++ tailWord_718434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718437 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 3]
def baseStart_718437 : Nat := 118140960795 + 718437 * 2 ^ 59
def prefixEnd_718437 : Nat := 4983230072969 + 3 ^ 40 * 718437 * 2
def baseEnd_718437 : Nat := 327914223088276307229755

theorem tailTrace_718437 : CollatzResearch.WordTrace tailWord_718437 prefixEnd_718437 327914223088276307229755 := by
  unfold tailWord_718437
  simp only [CollatzResearch.WordTrace]
  refine ⟨26203550098232923116121565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17469033398821948744081043 26203550098232923116121565)
  ·
    refine ⟨9826331286837346168545587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26203550098232923116121565 9826331286837346168545587)
    ·
      refine ⟨14739496930256019252818381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826331286837346168545587 14739496930256019252818381)
      ·
        refine ⟨5527311348846007219806893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14739496930256019252818381 5527311348846007219806893)
        ·
          refine ⟨2072741755817252707427585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5527311348846007219806893 2072741755817252707427585)
          ·
            refine ⟨1554556316862939530570689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2072741755817252707427585 1554556316862939530570689)
            ·
              refine ⟨1165917237647204647928017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1554556316862939530570689 1165917237647204647928017)
              ·
                refine ⟨874437928235403485946013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165917237647204647928017 874437928235403485946013)
                ·
                  refine ⟨327914223088276307229755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874437928235403485946013 327914223088276307229755)
                  ·
                    rfl

theorem cell20_718437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_718437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718437 prefixEnd_718437 := by exact prefixLift 718437
  have htrace : WordTrace (prefixWord ++ tailWord_718437) baseStart_718437 baseEnd_718437 := by
    simpa [prefixWord, tailWord_718437, baseEnd_718437] using wordTrace_append hprefix tailTrace_718437
  have hstable : (prefixWord ++ tailWord_718437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718437).length < 2 ^ (prefixWord ++ tailWord_718437).sum := by decide
  have hdescent : baseEnd_718437 < baseStart_718437 := by decide
  rcases family_descends (prefixWord ++ tailWord_718437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718440 : List Nat := [2, 1, 4, 3, 1, 1, 4, 2, 2]
def baseStart_718440 : Nat := 118140960795 + 718440 * 2 ^ 59
def prefixEnd_718440 : Nat := 4983230072969 + 3 ^ 40 * 718440 * 2
def baseEnd_718440 : Nat := 327915592370021630129743

theorem tailTrace_718440 : CollatzResearch.WordTrace tailWord_718440 prefixEnd_718440 327915592370021630129743 := by
  unfold tailWord_718440
  simp only [CollatzResearch.WordTrace]
  refine ⟨13101829758611027314240387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17469106344814703085653849 13101829758611027314240387)
  ·
    refine ⟨19652744637916540971360581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13101829758611027314240387 19652744637916540971360581)
    ·
      refine ⟨3684889619609351432130109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19652744637916540971360581 3684889619609351432130109)
      ·
        refine ⟨1381833607353506787048791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3684889619609351432130109 1381833607353506787048791)
        ·
          refine ⟨2072750411030260180573187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381833607353506787048791 2072750411030260180573187)
          ·
            refine ⟨3109125616545390270859781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072750411030260180573187 3109125616545390270859781)
            ·
              refine ⟨582961053102260675786209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3109125616545390270859781 582961053102260675786209)
              ·
                refine ⟨437220789826695506839657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582961053102260675786209 437220789826695506839657)
                ·
                  refine ⟨327915592370021630129743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437220789826695506839657 327915592370021630129743)
                  ·
                    rfl

theorem cell20_718440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 2].length) (baseStart_718440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718440 prefixEnd_718440 := by exact prefixLift 718440
  have htrace : WordTrace (prefixWord ++ tailWord_718440) baseStart_718440 baseEnd_718440 := by
    simpa [prefixWord, tailWord_718440, baseEnd_718440] using wordTrace_append hprefix tailTrace_718440
  have hstable : (prefixWord ++ tailWord_718440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718440).length < 2 ^ (prefixWord ++ tailWord_718440).sum := by decide
  have hdescent : baseEnd_718440 < baseStart_718440 := by decide
  rcases family_descends (prefixWord ++ tailWord_718440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718441 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_718441 : Nat := 118140960795 + 718441 * 2 ^ 59
def prefixEnd_718441 : Nat := 4983230072969 + 3 ^ 40 * 718441 * 2
def baseEnd_718441 : Nat := 327916048797270071096405

theorem tailTrace_718441 : CollatzResearch.WordTrace tailWord_718441 prefixEnd_718441 327916048797270071096405 := by
  unfold tailWord_718441
  simp only [CollatzResearch.WordTrace]
  refine ⟨26203695990218431799267177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17469130660145621199511451 26203695990218431799267177)
  ·
    refine ⟨19652771992663823849450383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26203695990218431799267177 19652771992663823849450383)
    ·
      refine ⟨29479157988995735774175575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19652771992663823849450383 29479157988995735774175575)
      ·
        refine ⟨44218736983493603661263363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29479157988995735774175575 44218736983493603661263363)
        ·
          refine ⟨66328105475240405491895045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44218736983493603661263363 66328105475240405491895045)
          ·
            refine ⟨12436519776607576029730321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66328105475240405491895045 12436519776607576029730321)
            ·
              refine ⟨9327389832455682022297741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12436519776607576029730321 9327389832455682022297741)
              ·
                refine ⟨3497771187170880758361653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9327389832455682022297741 3497771187170880758361653)
                ·
                  refine ⟨327916048797270071096405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3497771187170880758361653 327916048797270071096405)
                  ·
                    rfl

theorem cell20_718441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_718441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718441 prefixEnd_718441 := by exact prefixLift 718441
  have htrace : WordTrace (prefixWord ++ tailWord_718441) baseStart_718441 baseEnd_718441 := by
    simpa [prefixWord, tailWord_718441, baseEnd_718441] using wordTrace_append hprefix tailTrace_718441
  have hstable : (prefixWord ++ tailWord_718441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718441).length < 2 ^ (prefixWord ++ tailWord_718441).sum := by decide
  have hdescent : baseEnd_718441 < baseStart_718441 := by decide
  rcases family_descends (prefixWord ++ tailWord_718441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718465 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_718465 : Nat := 118140960795 + 718465 * 2 ^ 59
def prefixEnd_718465 : Nat := 4983230072969 + 3 ^ 40 * 718465 * 2
def baseEnd_718465 : Nat := 327927003051232654296307

theorem tailTrace_718465 : CollatzResearch.WordTrace tailWord_718465 prefixEnd_718465 327927003051232654296307 := by
  unfold tailWord_718465
  simp only [CollatzResearch.WordTrace]
  refine ⟨26204571342131483898140849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17469714228087655932093899 26204571342131483898140849)
  ·
    refine ⟨19653428506598612923605637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26204571342131483898140849 19653428506598612923605637)
    ·
      refine ⟨3685017844987239923176057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19653428506598612923605637 3685017844987239923176057)
      ·
        refine ⟨2763763383740429942382043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3685017844987239923176057 2763763383740429942382043)
        ·
          refine ⟨4145645075610644913573065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763763383740429942382043 4145645075610644913573065)
          ·
            refine ⟨3109233806707983685179799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4145645075610644913573065 3109233806707983685179799)
            ·
              refine ⟨4663850710061975527769699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3109233806707983685179799 4663850710061975527769699)
              ·
                refine ⟨6995776065092963291654549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663850710061975527769699 6995776065092963291654549)
                ·
                  refine ⟨327927003051232654296307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6995776065092963291654549 327927003051232654296307)
                  ·
                    rfl

theorem cell20_718465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_718465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718465 prefixEnd_718465 := by exact prefixLift 718465
  have htrace : WordTrace (prefixWord ++ tailWord_718465) baseStart_718465 baseEnd_718465 := by
    simpa [prefixWord, tailWord_718465, baseEnd_718465] using wordTrace_append hprefix tailTrace_718465
  have hstable : (prefixWord ++ tailWord_718465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718465).length < 2 ^ (prefixWord ++ tailWord_718465).sum := by decide
  have hdescent : baseEnd_718465 < baseStart_718465 := by decide
  rcases family_descends (prefixWord ++ tailWord_718465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718468 : List Nat := [2, 3, 2, 1, 4, 1, 3, 4]
def baseStart_718468 : Nat := 118140960795 + 718468 * 2 ^ 59
def prefixEnd_718468 : Nat := 4983230072969 + 3 ^ 40 * 718468 * 2
def baseEnd_718468 : Nat := 109309457444325992398765

theorem tailTrace_718468 : CollatzResearch.WordTrace tailWord_718468 prefixEnd_718468 109309457444325992398765 := by
  unfold tailWord_718468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102340380560307705250029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17469787174080410273666705 13102340380560307705250029)
  ·
    refine ⟨4913377642710115389468761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13102340380560307705250029 4913377642710115389468761)
    ·
      refine ⟨3685033232032586542101571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4913377642710115389468761 3685033232032586542101571)
      ·
        refine ⟨5527549848048879813152357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685033232032586542101571 5527549848048879813152357)
        ·
          refine ⟨1036415596509164964966067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5527549848048879813152357 1036415596509164964966067)
          ·
            refine ⟨1554623394763747447449101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036415596509164964966067 1554623394763747447449101)
            ·
              refine ⟨582983773036405292793413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1554623394763747447449101 582983773036405292793413)
              ·
                refine ⟨109309457444325992398765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582983773036405292793413 109309457444325992398765)
                ·
                  rfl

theorem cell20_718468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_718468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718468 prefixEnd_718468 := by exact prefixLift 718468
  have htrace : WordTrace (prefixWord ++ tailWord_718468) baseStart_718468 baseEnd_718468 := by
    simpa [prefixWord, tailWord_718468, baseEnd_718468] using wordTrace_append hprefix tailTrace_718468
  have hstable : (prefixWord ++ tailWord_718468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718468).length < 2 ^ (prefixWord ++ tailWord_718468).sum := by decide
  have hdescent : baseEnd_718468 < baseStart_718468 := by decide
  rcases family_descends (prefixWord ++ tailWord_718468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718492 : List Nat := [2, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_718492 : Nat := 118140960795 + 718492 * 2 ^ 59
def prefixEnd_718492 : Nat := 4983230072969 + 3 ^ 40 * 718492 * 2
def baseEnd_718492 : Nat := 327939326586940560396197

theorem tailTrace_718492 : CollatzResearch.WordTrace tailWord_718492 prefixEnd_718492 327939326586940560396197 := by
  unfold tailWord_718492
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102778056516833754686865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17470370742022445006249153 13102778056516833754686865)
  ·
    refine ⟨9827083542387625316015149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13102778056516833754686865 9827083542387625316015149)
    ·
      refine ⟨3685156328395359493505681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9827083542387625316015149 3685156328395359493505681)
      ·
        refine ⟨2763867246296519620129261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3685156328395359493505681 2763867246296519620129261)
        ·
          refine ⟨1036450217361194857548473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2763867246296519620129261 1036450217361194857548473)
          ·
            refine ⟨777337663020896143161355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036450217361194857548473 777337663020896143161355)
            ·
              refine ⟨1166006494531344214742033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777337663020896143161355 1166006494531344214742033)
              ·
                refine ⟨874504870898508161056525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166006494531344214742033 874504870898508161056525)
                ·
                  refine ⟨327939326586940560396197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874504870898508161056525 327939326586940560396197)
                  ·
                    rfl

theorem cell20_718492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_718492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718492 prefixEnd_718492 := by exact prefixLift 718492
  have htrace : WordTrace (prefixWord ++ tailWord_718492) baseStart_718492 baseEnd_718492 := by
    simpa [prefixWord, tailWord_718492, baseEnd_718492] using wordTrace_append hprefix tailTrace_718492
  have hstable : (prefixWord ++ tailWord_718492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718492).length < 2 ^ (prefixWord ++ tailWord_718492).sum := by decide
  have hdescent : baseEnd_718492 < baseStart_718492 := by decide
  rcases family_descends (prefixWord ++ tailWord_718492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718496 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_718496 : Nat := 118140960795 + 718496 * 2 ^ 59
def prefixEnd_718496 : Nat := 4983230072969 + 3 ^ 40 * 718496 * 2
def baseEnd_718496 : Nat := 327941152295934324262847

theorem tailTrace_718496 : CollatzResearch.WordTrace tailWord_718496 prefixEnd_718496 327941152295934324262847 := by
  unfold tailWord_718496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102851002509588096259671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17470468003346117461679561 13102851002509588096259671)
  ·
    refine ⟨19654276503764382144389507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13102851002509588096259671 19654276503764382144389507)
    ·
      refine ⟨29481414755646573216584261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19654276503764382144389507 29481414755646573216584261)
      ·
        refine ⟨5527765266683732478109549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29481414755646573216584261 5527765266683732478109549)
        ·
          refine ⟨2072911975006399679291081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5527765266683732478109549 2072911975006399679291081)
          ·
            refine ⟨1554683981254799759468311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2072911975006399679291081 1554683981254799759468311)
            ·
              refine ⟨2332025971882199639202467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554683981254799759468311 2332025971882199639202467)
              ·
                refine ⟨3498038957823299458803701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332025971882199639202467 3498038957823299458803701)
                ·
                  refine ⟨327941152295934324262847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3498038957823299458803701 327941152295934324262847)
                  ·
                    rfl

theorem cell20_718496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_718496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718496 prefixEnd_718496 := by exact prefixLift 718496
  have htrace : WordTrace (prefixWord ++ tailWord_718496) baseStart_718496 baseEnd_718496 := by
    simpa [prefixWord, tailWord_718496, baseEnd_718496] using wordTrace_append hprefix tailTrace_718496
  have hstable : (prefixWord ++ tailWord_718496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718496).length < 2 ^ (prefixWord ++ tailWord_718496).sum := by decide
  have hdescent : baseEnd_718496 < baseStart_718496 := by decide
  rcases family_descends (prefixWord ++ tailWord_718496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718550 : List Nat := [5, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_718550 : Nat := 118140960795 + 718550 * 2 ^ 59
def prefixEnd_718550 : Nat := 4983230072969 + 3 ^ 40 * 718550 * 2
def baseEnd_718550 : Nat := 327965799367350136462627

theorem tailTrace_718550 : CollatzResearch.WordTrace tailWord_718550 prefixEnd_718550 327965799367350136462627 := by
  unfold tailWord_718550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1637979471676471463436569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17471781031215695609990069 1637979471676471463436569)
  ·
    refine ⟨1228484603757353597577427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1637979471676471463436569 1228484603757353597577427)
    ·
      refine ⟨1842726905636030396366141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228484603757353597577427 1842726905636030396366141)
      ·
        refine ⟨691022589613511398637303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1842726905636030396366141 691022589613511398637303)
        ·
          refine ⟨1036533884420267097955955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691022589613511398637303 1036533884420267097955955)
          ·
            refine ⟨1554800826630400646933933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036533884420267097955955 1554800826630400646933933)
            ·
              refine ⟨583050309986400242600225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1554800826630400646933933 583050309986400242600225)
              ·
                refine ⟨437287732489800181950169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583050309986400242600225 437287732489800181950169)
                ·
                  refine ⟨327965799367350136462627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437287732489800181950169 327965799367350136462627)
                  ·
                    rfl

theorem cell20_718550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_718550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718550 prefixEnd_718550 := by exact prefixLift 718550
  have htrace : WordTrace (prefixWord ++ tailWord_718550) baseStart_718550 baseEnd_718550 := by
    simpa [prefixWord, tailWord_718550, baseEnd_718550] using wordTrace_append hprefix tailTrace_718550
  have hstable : (prefixWord ++ tailWord_718550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718550).length < 2 ^ (prefixWord ++ tailWord_718550).sum := by decide
  have hdescent : baseEnd_718550 < baseStart_718550 := by decide
  rcases family_descends (prefixWord ++ tailWord_718550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718568 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_718568 : Nat := 118140960795 + 718568 * 2 ^ 59
def prefixEnd_718568 : Nat := 4983230072969 + 3 ^ 40 * 718568 * 2
def baseEnd_718568 : Nat := 327974015057822073862553

theorem tailTrace_718568 : CollatzResearch.WordTrace tailWord_718568 prefixEnd_718568 327974015057822073862553 := by
  unfold tailWord_718568
  simp only [CollatzResearch.WordTrace]
  refine ⟨13104164030379166244570179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17472218707172221659426905 13104164030379166244570179)
  ·
    refine ⟨19656246045568749366855269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13104164030379166244570179 19656246045568749366855269)
    ·
      refine ⟨3685546133544140506285363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19656246045568749366855269 3685546133544140506285363)
      ·
        refine ⟨5528319200316210759428045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685546133544140506285363 5528319200316210759428045)
        ·
          refine ⟨2073119700118579034785517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5528319200316210759428045 2073119700118579034785517)
          ·
            refine ⟨777419887544467138044569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2073119700118579034785517 777419887544467138044569)
            ·
              refine ⟨583064915658350353533427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777419887544467138044569 583064915658350353533427)
              ·
                refine ⟨874597373487525530300141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583064915658350353533427 874597373487525530300141)
                ·
                  refine ⟨327974015057822073862553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874597373487525530300141 327974015057822073862553)
                  ·
                    rfl

theorem cell20_718568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_718568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718568 prefixEnd_718568 := by exact prefixLift 718568
  have htrace : WordTrace (prefixWord ++ tailWord_718568) baseStart_718568 baseEnd_718568 := by
    simpa [prefixWord, tailWord_718568, baseEnd_718568] using wordTrace_append hprefix tailTrace_718568
  have hstable : (prefixWord ++ tailWord_718568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718568).length < 2 ^ (prefixWord ++ tailWord_718568).sum := by decide
  have hdescent : baseEnd_718568 < baseStart_718568 := by decide
  rcases family_descends (prefixWord ++ tailWord_718568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718593 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_718593 : Nat := 118140960795 + 718593 * 2 ^ 59
def prefixEnd_718593 : Nat := 4983230072969 + 3 ^ 40 * 718593 * 2
def baseEnd_718593 : Nat := 327985425739033098029117

theorem tailTrace_718593 : CollatzResearch.WordTrace tailWord_718593 prefixEnd_718593 327985425739033098029117 := by
  unfold tailWord_718593
  simp only [CollatzResearch.WordTrace]
  refine ⟨26209239885667761758800433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17472826590445174505866955 26209239885667761758800433)
  ·
    refine ⟨19656929914250821319100325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26209239885667761758800433 19656929914250821319100325)
    ·
      refine ⟨3685674358922028997331311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19656929914250821319100325 3685674358922028997331311)
      ·
        refine ⟨5528511538383043495996967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685674358922028997331311 5528511538383043495996967)
        ·
          refine ⟨8292767307574565243995451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5528511538383043495996967 8292767307574565243995451)
          ·
            refine ⟨12439150961361847865993177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8292767307574565243995451 12439150961361847865993177)
            ·
              refine ⟨9329363221021385899494883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12439150961361847865993177 9329363221021385899494883)
              ·
                refine ⟨13994044831532078849242325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9329363221021385899494883 13994044831532078849242325)
                ·
                  refine ⟨327985425739033098029117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13994044831532078849242325 327985425739033098029117)
                  ·
                    rfl

theorem cell20_718593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_718593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718593 prefixEnd_718593 := by exact prefixLift 718593
  have htrace : WordTrace (prefixWord ++ tailWord_718593) baseStart_718593 baseEnd_718593 := by
    simpa [prefixWord, tailWord_718593, baseEnd_718593] using wordTrace_append hprefix tailTrace_718593
  have hstable : (prefixWord ++ tailWord_718593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718593).length < 2 ^ (prefixWord ++ tailWord_718593).sum := by decide
  have hdescent : baseEnd_718593 < baseStart_718593 := by decide
  rcases family_descends (prefixWord ++ tailWord_718593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718613 : List Nat := [1, 3, 2, 1, 2, 3, 4, 2, 2]
def baseStart_718613 : Nat := 118140960795 + 718613 * 2 ^ 59
def prefixEnd_718613 : Nat := 4983230072969 + 3 ^ 40 * 718613 * 2
def baseEnd_718613 : Nat := 327994554284001917362369

theorem tailTrace_718613 : CollatzResearch.WordTrace tailWord_718613 prefixEnd_718613 327994554284001917362369 := by
  unfold tailWord_718613
  simp only [CollatzResearch.WordTrace]
  refine ⟨26209969345595305174528493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17473312897063536783018995 26209969345595305174528493)
  ·
    refine ⟨9828738504598239440448185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26209969345595305174528493 9828738504598239440448185)
    ·
      refine ⟨7371553878448679580336139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9828738504598239440448185 7371553878448679580336139)
      ·
        refine ⟨11057330817673019370504209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7371553878448679580336139 11057330817673019370504209)
        ·
          refine ⟨8292998113254764527878157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11057330817673019370504209 8292998113254764527878157)
          ·
            refine ⟨3109874292470536697954309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8292998113254764527878157 3109874292470536697954309)
            ·
              refine ⟨583101429838225630866433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3109874292470536697954309 583101429838225630866433)
              ·
                refine ⟨437326072378669223149825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583101429838225630866433 437326072378669223149825)
                ·
                  refine ⟨327994554284001917362369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437326072378669223149825 327994554284001917362369)
                  ·
                    rfl

theorem cell20_718613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_718613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718613 prefixEnd_718613 := by exact prefixLift 718613
  have htrace : WordTrace (prefixWord ++ tailWord_718613) baseStart_718613 baseEnd_718613 := by
    simpa [prefixWord, tailWord_718613, baseEnd_718613] using wordTrace_append hprefix tailTrace_718613
  have hstable : (prefixWord ++ tailWord_718613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718613).length < 2 ^ (prefixWord ++ tailWord_718613).sum := by decide
  have hdescent : baseEnd_718613 < baseStart_718613 := by decide
  rcases family_descends (prefixWord ++ tailWord_718613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718641 : List Nat := [1, 2, 2, 3, 2, 3, 3, 4]
def baseStart_718641 : Nat := 118140960795 + 718641 * 2 ^ 59
def prefixEnd_718641 : Nat := 4983230072969 + 3 ^ 40 * 718641 * 2
def baseEnd_718641 : Nat := 109335778082319421476307

theorem tailTrace_718641 : CollatzResearch.WordTrace tailWord_718641 prefixEnd_718641 109335778082319421476307 := by
  unfold tailWord_718641
  simp only [CollatzResearch.WordTrace]
  refine ⟨26210990589493865956547777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17473993726329243971031851 26210990589493865956547777)
  ·
    refine ⟨19658242942120399467410833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26210990589493865956547777 19658242942120399467410833)
    ·
      refine ⟨14743682206590299600558125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19658242942120399467410833 14743682206590299600558125)
      ·
        refine ⟨5528880827471362350209297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14743682206590299600558125 5528880827471362350209297)
        ·
          refine ⟨4146660620603521762656973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5528880827471362350209297 4146660620603521762656973)
          ·
            refine ⟨1554997732726320660996365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4146660620603521762656973 1554997732726320660996365)
            ·
              refine ⟨583124149772370247873637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1554997732726320660996365 583124149772370247873637)
              ·
                refine ⟨109335778082319421476307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583124149772370247873637 109335778082319421476307)
                ·
                  rfl

theorem cell20_718641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 4].length) (baseStart_718641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718641 prefixEnd_718641 := by exact prefixLift 718641
  have htrace : WordTrace (prefixWord ++ tailWord_718641) baseStart_718641 baseEnd_718641 := by
    simpa [prefixWord, tailWord_718641, baseEnd_718641] using wordTrace_append hprefix tailTrace_718641
  have hstable : (prefixWord ++ tailWord_718641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718641).length < 2 ^ (prefixWord ++ tailWord_718641).sum := by decide
  have hdescent : baseEnd_718641 < baseStart_718641 := by decide
  rcases family_descends (prefixWord ++ tailWord_718641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718700 : List Nat := [2, 2, 1, 1, 4, 3, 1, 6]
def baseStart_718700 : Nat := 118140960795 + 718700 * 2 ^ 59
def prefixEnd_718700 : Nat := 4983230072969 + 3 ^ 40 * 718700 * 2
def baseEnd_718700 : Nat := 109344754484872093820671

theorem tailTrace_718700 : CollatzResearch.WordTrace tailWord_718700 prefixEnd_718700 109344754484872093820671 := by
  unfold tailWord_718700
  simp only [CollatzResearch.WordTrace]
  refine ⟨13106571248140059516472777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17475428330853412688630369 13106571248140059516472777)
  ·
    refine ⟨9829928436105044637354583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13106571248140059516472777 9829928436105044637354583)
    ·
      refine ⟨14744892654157566956031875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9829928436105044637354583 14744892654157566956031875)
      ·
        refine ⟨22117338981236350434047813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14744892654157566956031875 22117338981236350434047813)
        ·
          refine ⟨4147001058981815706383965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22117338981236350434047813 4147001058981815706383965)
          ·
            refine ⟨1555125397118180889893987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4147001058981815706383965 1555125397118180889893987)
            ·
              refine ⟨2332688095677271334840981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555125397118180889893987 2332688095677271334840981)
              ·
                refine ⟨109344754484872093820671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2332688095677271334840981 109344754484872093820671)
                ·
                  rfl

theorem cell20_718700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_718700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718700 prefixEnd_718700 := by exact prefixLift 718700
  have htrace : WordTrace (prefixWord ++ tailWord_718700) baseStart_718700 baseEnd_718700 := by
    simpa [prefixWord, tailWord_718700, baseEnd_718700] using wordTrace_append hprefix tailTrace_718700
  have hstable : (prefixWord ++ tailWord_718700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718700).length < 2 ^ (prefixWord ++ tailWord_718700).sum := by decide
  have hdescent : baseEnd_718700 < baseStart_718700 := by decide
  rcases family_descends (prefixWord ++ tailWord_718700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718714 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_718714 : Nat := 118140960795 + 718714 * 2 ^ 59
def prefixEnd_718714 : Nat := 4983230072969 + 3 ^ 40 * 718714 * 2
def baseEnd_718714 : Nat := 328040653436094454995289

theorem tailTrace_718714 : CollatzResearch.WordTrace tailWord_718714 prefixEnd_718714 328040653436094454995289 := by
  unfold tailWord_718714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553413279557349855988799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17475768745486266282636797 6553413279557349855988799)
  ·
    refine ⟨9830119919336024783983199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6553413279557349855988799 9830119919336024783983199)
    ·
      refine ⟨14745179879004037175974799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9830119919336024783983199 14745179879004037175974799)
      ·
        refine ⟨22117769818506055763962199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14745179879004037175974799 22117769818506055763962199)
        ·
          refine ⟨33176654727759083645943299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22117769818506055763962199 33176654727759083645943299)
          ·
            refine ⟨49764982091638625468914949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33176654727759083645943299 49764982091638625468914949)
            ·
              refine ⟨9330934142182242275421553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49764982091638625468914949 9330934142182242275421553)
              ·
                refine ⟨6998200606636681706566165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9330934142182242275421553 6998200606636681706566165)
                ·
                  refine ⟨328040653436094454995289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6998200606636681706566165 328040653436094454995289)
                  ·
                    rfl

theorem cell20_718714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_718714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718714 prefixEnd_718714 := by exact prefixLift 718714
  have htrace : WordTrace (prefixWord ++ tailWord_718714) baseStart_718714 baseEnd_718714 := by
    simpa [prefixWord, tailWord_718714, baseEnd_718714] using wordTrace_append hprefix tailTrace_718714
  have hstable : (prefixWord ++ tailWord_718714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718714).length < 2 ^ (prefixWord ++ tailWord_718714).sum := by decide
  have hdescent : baseEnd_718714 < baseStart_718714 := by decide
  rcases family_descends (prefixWord ++ tailWord_718714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718727 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 4]
def baseStart_718727 : Nat := 118140960795 + 718727 * 2 ^ 59
def prefixEnd_718727 : Nat := 4983230072969 + 3 ^ 40 * 718727 * 2
def baseEnd_718727 : Nat := 328046586990324187561903

theorem tailTrace_718727 : CollatzResearch.WordTrace tailWord_718727 prefixEnd_718727 328046586990324187561903 := by
  unfold tailWord_718727
  simp only [CollatzResearch.WordTrace]
  refine ⟨26214127267182302644178435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17476084844788201762785623 26214127267182302644178435)
  ·
    refine ⟨39321190900773453966267653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26214127267182302644178435 39321190900773453966267653)
    ·
      refine ⟨7372723293895022618675185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39321190900773453966267653 7372723293895022618675185)
      ·
        refine ⟨5529542470421266964006389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7372723293895022618675185 5529542470421266964006389)
        ·
          refine ⟨518394606601993777875599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5529542470421266964006389 518394606601993777875599)
          ·
            refine ⟨777591909902990666813399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518394606601993777875599 777591909902990666813399)
            ·
              refine ⟨1166387864854486000220099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777591909902990666813399 1166387864854486000220099)
              ·
                refine ⟨1749581797281729000330149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166387864854486000220099 1749581797281729000330149)
                ·
                  refine ⟨328046586990324187561903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749581797281729000330149 328046586990324187561903)
                  ·
                    rfl

theorem cell20_718727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 4].length) (baseStart_718727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718727 prefixEnd_718727 := by exact prefixLift 718727
  have htrace : WordTrace (prefixWord ++ tailWord_718727) baseStart_718727 baseEnd_718727 := by
    simpa [prefixWord, tailWord_718727, baseEnd_718727] using wordTrace_append hprefix tailTrace_718727
  have hstable : (prefixWord ++ tailWord_718727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718727).length < 2 ^ (prefixWord ++ tailWord_718727).sum := by decide
  have hdescent : baseEnd_718727 < baseStart_718727 := by decide
  rcases family_descends (prefixWord ++ tailWord_718727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718734 : List Nat := [4, 1, 1, 5, 1, 1, 2, 5]
def baseStart_718734 : Nat := 118140960795 + 718734 * 2 ^ 59
def prefixEnd_718734 : Nat := 4983230072969 + 3 ^ 40 * 718734 * 2
def baseEnd_718734 : Nat := 109349927327021091442847

theorem tailTrace_718734 : CollatzResearch.WordTrace tailWord_718734 prefixEnd_718734 109349927327021091442847 := by
  unfold tailWord_718734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276797822269617854960407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17476255052104628559788837 3276797822269617854960407)
  ·
    refine ⟨4915196733404426782440611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3276797822269617854960407 4915196733404426782440611)
    ·
      refine ⟨7372795100106640173660917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4915196733404426782440611 7372795100106640173660917)
      ·
        refine ⟨691199540634997516280711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7372795100106640173660917 691199540634997516280711)
        ·
          refine ⟨1036799310952496274421067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691199540634997516280711 1036799310952496274421067)
          ·
            refine ⟨1555198966428744411631601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036799310952496274421067 1555198966428744411631601)
            ·
              refine ⟨1166399224821558308723701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555198966428744411631601 1166399224821558308723701)
              ·
                refine ⟨109349927327021091442847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1166399224821558308723701 109349927327021091442847)
                ·
                  rfl

theorem cell20_718734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_718734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718734 prefixEnd_718734 := by exact prefixLift 718734
  have htrace : WordTrace (prefixWord ++ tailWord_718734) baseStart_718734 baseEnd_718734 := by
    simpa [prefixWord, tailWord_718734, baseEnd_718734] using wordTrace_append hprefix tailTrace_718734
  have hstable : (prefixWord ++ tailWord_718734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718734).length < 2 ^ (prefixWord ++ tailWord_718734).sum := by decide
  have hdescent : baseEnd_718734 < baseStart_718734 := by decide
  rcases family_descends (prefixWord ++ tailWord_718734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718752 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_718752 : Nat := 118140960795 + 718752 * 2 ^ 59
def prefixEnd_718752 : Nat := 4983230072969 + 3 ^ 40 * 718752 * 2
def baseEnd_718752 : Nat := 328057997671535211728467

theorem tailTrace_718752 : CollatzResearch.WordTrace tailWord_718752 prefixEnd_718752 328057997671535211728467 := by
  unfold tailWord_718752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107519546045865956919255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17476692728061154609225673 13107519546045865956919255)
  ·
    refine ⟨19661279319068798935378883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13107519546045865956919255 19661279319068798935378883)
    ·
      refine ⟨29491918978603198403068325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19661279319068798935378883 29491918978603198403068325)
      ·
        refine ⟨5529734808488099700575311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29491918978603198403068325 5529734808488099700575311)
        ·
          refine ⟨8294602212732149550862967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529734808488099700575311 8294602212732149550862967)
          ·
            refine ⟨12441903319098224326294451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294602212732149550862967 12441903319098224326294451)
            ·
              refine ⟨18662854978647336489441677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12441903319098224326294451 18662854978647336489441677)
              ·
                refine ⟨6998570616992751183540629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18662854978647336489441677 6998570616992751183540629)
                ·
                  refine ⟨328057997671535211728467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6998570616992751183540629 328057997671535211728467)
                  ·
                    rfl

theorem cell20_718752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_718752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718752 prefixEnd_718752 := by exact prefixLift 718752
  have htrace : WordTrace (prefixWord ++ tailWord_718752) baseStart_718752 baseEnd_718752 := by
    simpa [prefixWord, tailWord_718752, baseEnd_718752] using wordTrace_append hprefix tailTrace_718752
  have hstable : (prefixWord ++ tailWord_718752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718752).length < 2 ^ (prefixWord ++ tailWord_718752).sum := by decide
  have hdescent : baseEnd_718752 < baseStart_718752 := by decide
  rcases family_descends (prefixWord ++ tailWord_718752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718772 : List Nat := [2, 5, 2, 1, 3, 7]
def baseStart_718772 : Nat := 118140960795 + 718772 * 2 ^ 59
def prefixEnd_718772 : Nat := 4983230072969 + 3 ^ 40 * 718772 * 2
def baseEnd_718772 : Nat := 12150634304314964113397

theorem tailTrace_718772 : CollatzResearch.WordTrace tailWord_718772 prefixEnd_718772 12150634304314964113397 := by
  unfold tailWord_718772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107884276009637664783285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17477179034679516886377713 13107884276009637664783285)
  ·
    refine ⟨1228864150875903531073433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13107884276009637664783285 1228864150875903531073433)
    ·
      refine ⟨921648113156927648305075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1228864150875903531073433 921648113156927648305075)
      ·
        refine ⟨1382472169735391472457613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921648113156927648305075 1382472169735391472457613)
        ·
          refine ⟨518427063650771802171605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1382472169735391472457613 518427063650771802171605)
          ·
            refine ⟨12150634304314964113397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 518427063650771802171605 12150634304314964113397)
            ·
              rfl

theorem cell20_718772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 7].length) (baseStart_718772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718772 prefixEnd_718772 := by exact prefixLift 718772
  have htrace : WordTrace (prefixWord ++ tailWord_718772) baseStart_718772 baseEnd_718772 := by
    simpa [prefixWord, tailWord_718772, baseEnd_718772] using wordTrace_append hprefix tailTrace_718772
  have hstable : (prefixWord ++ tailWord_718772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718772).length < 2 ^ (prefixWord ++ tailWord_718772).sum := by decide
  have hdescent : baseEnd_718772 < baseStart_718772 := by decide
  rcases family_descends (prefixWord ++ tailWord_718772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718782 : List Nat := [4, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_718782 : Nat := 118140960795 + 718782 * 2 ^ 59
def prefixEnd_718782 : Nat := 4983230072969 + 3 ^ 40 * 718782 * 2
def baseEnd_718782 : Nat := 328071690488988440728345

theorem tailTrace_718782 : CollatzResearch.WordTrace tailWord_718782 prefixEnd_718782 328071690488988440728345 := by
  unfold tailWord_718782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277016660247880879678825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17477422187988698024953733 3277016660247880879678825)
  ·
    refine ⟨2457762495185910659759119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3277016660247880879678825 2457762495185910659759119)
    ·
      refine ⟨3686643742778865989638679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2457762495185910659759119 3686643742778865989638679)
      ·
        refine ⟨5529965614168298984458019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686643742778865989638679 5529965614168298984458019)
        ·
          refine ⟨8294948421252448476687029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529965614168298984458019 8294948421252448476687029)
          ·
            refine ⟨777651414492417044689409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8294948421252448476687029 777651414492417044689409)
            ·
              refine ⟨583238560869312783517057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777651414492417044689409 583238560869312783517057)
              ·
                refine ⟨437428920651984587637793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583238560869312783517057 437428920651984587637793)
                ·
                  refine ⟨328071690488988440728345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437428920651984587637793 328071690488988440728345)
                  ·
                    rfl

theorem cell20_718782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_718782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718782 prefixEnd_718782 := by exact prefixLift 718782
  have htrace : WordTrace (prefixWord ++ tailWord_718782) baseStart_718782 baseEnd_718782 := by
    simpa [prefixWord, tailWord_718782, baseEnd_718782] using wordTrace_append hprefix tailTrace_718782
  have hstable : (prefixWord ++ tailWord_718782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718782).length < 2 ^ (prefixWord ++ tailWord_718782).sum := by decide
  have hdescent : baseEnd_718782 < baseStart_718782 := by decide
  rcases family_descends (prefixWord ++ tailWord_718782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718855 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 3]
def baseStart_718855 : Nat := 118140960795 + 718855 * 2 ^ 59
def prefixEnd_718855 : Nat := 4983230072969 + 3 ^ 40 * 718855 * 2
def baseEnd_718855 : Nat := 328105009678124631294713

theorem tailTrace_718855 : CollatzResearch.WordTrace tailWord_718855 prefixEnd_718855 328105009678124631294713 := by
  unfold tailWord_718855
  simp only [CollatzResearch.WordTrace]
  refine ⟨26218795810718580504838019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17479197207145720336558679 26218795810718580504838019)
  ·
    refine ⟨39328193716077870757257029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26218795810718580504838019 39328193716077870757257029)
    ·
      refine ⟨7374036321764600766985693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39328193716077870757257029 7374036321764600766985693)
      ·
        refine ⟨2765263620661725287619635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7374036321764600766985693 2765263620661725287619635)
        ·
          refine ⟨4147895430992587931429453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2765263620661725287619635 4147895430992587931429453)
          ·
            refine ⟨1555460786622220474286045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4147895430992587931429453 1555460786622220474286045)
            ·
              refine ⟨583297794983332677857267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1555460786622220474286045 583297794983332677857267)
              ·
                refine ⟨874946692474999016785901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583297794983332677857267 874946692474999016785901)
                ·
                  refine ⟨328105009678124631294713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874946692474999016785901 328105009678124631294713)
                  ·
                    rfl

theorem cell20_718855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 3].length) (baseStart_718855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718855 prefixEnd_718855 := by exact prefixLift 718855
  have htrace : WordTrace (prefixWord ++ tailWord_718855) baseStart_718855 baseEnd_718855 := by
    simpa [prefixWord, tailWord_718855, baseEnd_718855] using wordTrace_append hprefix tailTrace_718855
  have hstable : (prefixWord ++ tailWord_718855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718855).length < 2 ^ (prefixWord ++ tailWord_718855).sum := by decide
  have hdescent : baseEnd_718855 < baseStart_718855 := by decide
  rcases family_descends (prefixWord ++ tailWord_718855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718861 : List Nat := [1, 7, 1, 2, 2, 1, 2, 4]
def baseStart_718861 : Nat := 118140960795 + 718861 * 2 ^ 59
def prefixEnd_718861 : Nat := 4983230072969 + 3 ^ 40 * 718861 * 2
def baseEnd_718861 : Nat := 109369249413871759031563

theorem tailTrace_718861 : CollatzResearch.WordTrace tailWord_718861 prefixEnd_718861 109369249413871759031563 := by
  unfold tailWord_718861
  simp only [CollatzResearch.WordTrace]
  refine ⟨26219014648696843529556437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17479343099131229019704291 26219014648696843529556437)
  ·
    refine ⟨614508155828832270223979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 26219014648696843529556437 614508155828832270223979)
    ·
      refine ⟨921762233743248405335969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614508155828832270223979 921762233743248405335969)
      ·
        refine ⟨691321675307436304001977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 921762233743248405335969 691321675307436304001977)
        ·
          refine ⟨518491256480577228001483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691321675307436304001977 518491256480577228001483)
          ·
            refine ⟨777736884720865842002225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518491256480577228001483 777736884720865842002225)
            ·
              refine ⟨583302663540649381501669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777736884720865842002225 583302663540649381501669)
              ·
                refine ⟨109369249413871759031563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583302663540649381501669 109369249413871759031563)
                ·
                  rfl

theorem cell20_718861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 4].length) (baseStart_718861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718861 prefixEnd_718861 := by exact prefixLift 718861
  have htrace : WordTrace (prefixWord ++ tailWord_718861) baseStart_718861 baseEnd_718861 := by
    simpa [prefixWord, tailWord_718861, baseEnd_718861] using wordTrace_append hprefix tailTrace_718861
  have hstable : (prefixWord ++ tailWord_718861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718861).length < 2 ^ (prefixWord ++ tailWord_718861).sum := by decide
  have hdescent : baseEnd_718861 < baseStart_718861 := by decide
  rcases family_descends (prefixWord ++ tailWord_718861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718890 : List Nat := [3, 1, 4, 1, 2, 1, 8]
def baseStart_718890 : Nat := 118140960795 + 718890 * 2 ^ 59
def prefixEnd_718890 : Nat := 4983230072969 + 3 ^ 40 * 718890 * 2
def baseEnd_718890 : Nat := 36457887181313340569767

theorem tailTrace_718890 : CollatzResearch.WordTrace tailWord_718890 prefixEnd_718890 36457887181313340569767 := by
  unfold tailWord_718890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555018091397945370590531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17480048243727854321574749 6555018091397945370590531)
  ·
    refine ⟨9832527137096918055885797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6555018091397945370590531 9832527137096918055885797)
    ·
      refine ⟨1843598838205672135478587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9832527137096918055885797 1843598838205672135478587)
      ·
        refine ⟨2765398257308508203217881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843598838205672135478587 2765398257308508203217881)
        ·
          refine ⟨2074048692981381152413411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765398257308508203217881 2074048692981381152413411)
          ·
            refine ⟨3111073039472071728620117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074048692981381152413411 3111073039472071728620117)
            ·
              refine ⟨36457887181313340569767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3111073039472071728620117 36457887181313340569767)
              ·
                rfl

theorem cell20_718890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 8].length) (baseStart_718890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718890 prefixEnd_718890 := by exact prefixLift 718890
  have htrace : WordTrace (prefixWord ++ tailWord_718890) baseStart_718890 baseEnd_718890 := by
    simpa [prefixWord, tailWord_718890, baseEnd_718890] using wordTrace_append hprefix tailTrace_718890
  have hstable : (prefixWord ++ tailWord_718890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718890).length < 2 ^ (prefixWord ++ tailWord_718890).sum := by decide
  have hdescent : baseEnd_718890 < baseStart_718890 := by decide
  rcases family_descends (prefixWord ++ tailWord_718890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718897 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_718897 : Nat := 118140960795 + 718897 * 2 ^ 59
def prefixEnd_718897 : Nat := 4983230072969 + 3 ^ 40 * 718897 * 2
def baseEnd_718897 : Nat := 328124179622559151894541

theorem tailTrace_718897 : CollatzResearch.WordTrace tailWord_718897 prefixEnd_718897 328124179622559151894541 := by
  unfold tailWord_718897
  simp only [CollatzResearch.WordTrace]
  refine ⟨26220327676566421677866945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17480218451044281118577963 26220327676566421677866945)
  ·
    refine ⟨19665245757424816258400209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26220327676566421677866945 19665245757424816258400209)
    ·
      refine ⟨14748934318068612193800157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19665245757424816258400209 14748934318068612193800157)
      ·
        refine ⟨5530850369275729572675059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14748934318068612193800157 5530850369275729572675059)
        ·
          refine ⟨8296275553913594359012589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5530850369275729572675059 8296275553913594359012589)
          ·
            refine ⟨3111103332717597884629721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8296275553913594359012589 3111103332717597884629721)
            ·
              refine ⟨2333327499538198413472291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3111103332717597884629721 2333327499538198413472291)
              ·
                refine ⟨3499991249307297620208437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2333327499538198413472291 3499991249307297620208437)
                ·
                  refine ⟨328124179622559151894541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3499991249307297620208437 328124179622559151894541)
                  ·
                    rfl

theorem cell20_718897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_718897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718897 prefixEnd_718897 := by exact prefixLift 718897
  have htrace : WordTrace (prefixWord ++ tailWord_718897) baseStart_718897 baseEnd_718897 := by
    simpa [prefixWord, tailWord_718897, baseEnd_718897] using wordTrace_append hprefix tailTrace_718897
  have hstable : (prefixWord ++ tailWord_718897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718897).length < 2 ^ (prefixWord ++ tailWord_718897).sum := by decide
  have hdescent : baseEnd_718897 < baseStart_718897 := by decide
  rcases family_descends (prefixWord ++ tailWord_718897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718911 : List Nat := [1, 1, 2, 2, 3, 1, 3, 7]
def baseStart_718911 : Nat := 118140960795 + 718911 * 2 ^ 59
def prefixEnd_718911 : Nat := 4983230072969 + 3 ^ 40 * 718911 * 2
def baseEnd_718911 : Nat := 109376856534679108475939

theorem tailTrace_718911 : CollatzResearch.WordTrace tailWord_718911 prefixEnd_718911 109376856534679108475939 := by
  unfold tailWord_718911
  simp only [CollatzResearch.WordTrace]
  refine ⟨26220838298515702068876587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17480558865677134712584391 26220838298515702068876587)
  ·
    refine ⟨39331257447773553103314881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26220838298515702068876587 39331257447773553103314881)
    ·
      refine ⟨29498443085830164827486161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39331257447773553103314881 29498443085830164827486161)
      ·
        refine ⟨22123832314372623620614621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29498443085830164827486161 22123832314372623620614621)
        ·
          refine ⟨8296437117889733857730483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22123832314372623620614621 8296437117889733857730483)
          ·
            refine ⟨12444655676834600786595725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8296437117889733857730483 12444655676834600786595725)
            ·
              refine ⟨4666745878812975294973397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12444655676834600786595725 4666745878812975294973397)
              ·
                refine ⟨109376856534679108475939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4666745878812975294973397 109376856534679108475939)
                ·
                  rfl

theorem cell20_718911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_718911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718911 prefixEnd_718911 := by exact prefixLift 718911
  have htrace : WordTrace (prefixWord ++ tailWord_718911) baseStart_718911 baseEnd_718911 := by
    simpa [prefixWord, tailWord_718911, baseEnd_718911] using wordTrace_append hprefix tailTrace_718911
  have hstable : (prefixWord ++ tailWord_718911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718911).length < 2 ^ (prefixWord ++ tailWord_718911).sum := by decide
  have hdescent : baseEnd_718911 < baseStart_718911 := by decide
  rcases family_descends (prefixWord ++ tailWord_718911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718949 : List Nat := [1, 3, 1, 3, 2, 10]
def baseStart_718949 : Nat := 118140960795 + 718949 * 2 ^ 59
def prefixEnd_718949 : Nat := 4983230072969 + 3 ^ 40 * 718949 * 2
def baseEnd_718949 : Nat := 12153626438499188228185

theorem tailTrace_718949 : CollatzResearch.WordTrace tailWord_718949 prefixEnd_718949 12153626438499188228185 := by
  unfold tailWord_718949
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222224272378034558759901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17481482848252023039173267 26222224272378034558759901)
  ·
    refine ⟨9833334102141762959534963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26222224272378034558759901 9833334102141762959534963)
    ·
      refine ⟨14750001153212644439302445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9833334102141762959534963 14750001153212644439302445)
      ·
        refine ⟨5531250432454741664738417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14750001153212644439302445 5531250432454741664738417)
        ·
          refine ⟨4148437824341056248553813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5531250432454741664738417 4148437824341056248553813)
          ·
            refine ⟨12153626438499188228185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4148437824341056248553813 12153626438499188228185)
            ·
              rfl

theorem cell20_718949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 10].length) (baseStart_718949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_718949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_718949 prefixEnd_718949 := by exact prefixLift 718949
  have htrace : WordTrace (prefixWord ++ tailWord_718949) baseStart_718949 baseEnd_718949 := by
    simpa [prefixWord, tailWord_718949, baseEnd_718949] using wordTrace_append hprefix tailTrace_718949
  have hstable : (prefixWord ++ tailWord_718949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718949).length < 2 ^ (prefixWord ++ tailWord_718949).sum := by decide
  have hdescent : baseEnd_718949 < baseStart_718949 := by decide
  rcases family_descends (prefixWord ++ tailWord_718949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719007 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 3]
def baseStart_719007 : Nat := 118140960795 + 719007 * 2 ^ 59
def prefixEnd_719007 : Nat := 4983230072969 + 3 ^ 40 * 719007 * 2
def baseEnd_719007 : Nat := 328174386619887658227425

theorem tailTrace_719007 : CollatzResearch.WordTrace tailWord_719007 prefixEnd_719007 328174386619887658227425 := by
  unfold tailWord_719007
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224339706167910464371275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17482893137445273642914183 26224339706167910464371275)
  ·
    refine ⟨39336509559251865696556913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26224339706167910464371275 39336509559251865696556913)
    ·
      refine ⟨29502382169438899272417685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39336509559251865696556913 29502382169438899272417685)
      ·
        refine ⟨1382924164192448403394579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29502382169438899272417685 1382924164192448403394579)
        ·
          refine ⟨2074386246288672605091869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382924164192448403394579 2074386246288672605091869)
          ·
            refine ⟨777894842358252226909451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2074386246288672605091869 777894842358252226909451)
            ·
              refine ⟨1166842263537378340364177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777894842358252226909451 1166842263537378340364177)
              ·
                refine ⟨875131697653033755273133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166842263537378340364177 875131697653033755273133)
                ·
                  refine ⟨328174386619887658227425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875131697653033755273133 328174386619887658227425)
                  ·
                    rfl

theorem cell20_719007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 3].length) (baseStart_719007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719007 prefixEnd_719007 := by exact prefixLift 719007
  have htrace : WordTrace (prefixWord ++ tailWord_719007) baseStart_719007 baseEnd_719007 := by
    simpa [prefixWord, tailWord_719007, baseEnd_719007] using wordTrace_append hprefix tailTrace_719007
  have hstable : (prefixWord ++ tailWord_719007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719007).length < 2 ^ (prefixWord ++ tailWord_719007).sum := by decide
  have hdescent : baseEnd_719007 < baseStart_719007 := by decide
  rcases family_descends (prefixWord ++ tailWord_719007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719038 : List Nat := [4, 2, 1, 1, 4, 2, 2, 4]
def baseStart_719038 : Nat := 118140960795 + 719038 * 2 ^ 59
def prefixEnd_719038 : Nat := 4983230072969 + 3 ^ 40 * 719038 * 2
def baseEnd_719038 : Nat := 109396178621529776064655

theorem tailTrace_719038 : CollatzResearch.WordTrace tailWord_719038 prefixEnd_719038 109396178621529776064655 := by
  unfold tailWord_719038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278183796131950344843721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17483646912703735172499845 3278183796131950344843721)
  ·
    refine ⟨2458637847098962758632791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3278183796131950344843721 2458637847098962758632791)
    ·
      refine ⟨3687956770648444137949187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2458637847098962758632791 3687956770648444137949187)
      ·
        refine ⟨5531935155972666206923781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3687956770648444137949187 5531935155972666206923781)
        ·
          refine ⟨1037237841744874913798209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5531935155972666206923781 1037237841744874913798209)
          ·
            refine ⟨777928381308656185348657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037237841744874913798209 777928381308656185348657)
            ·
              refine ⟨583446285981492139011493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777928381308656185348657 583446285981492139011493)
              ·
                refine ⟨109396178621529776064655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583446285981492139011493 109396178621529776064655)
                ·
                  rfl

theorem cell20_719038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_719038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719038 prefixEnd_719038 := by exact prefixLift 719038
  have htrace : WordTrace (prefixWord ++ tailWord_719038) baseStart_719038 baseEnd_719038 := by
    simpa [prefixWord, tailWord_719038, baseEnd_719038] using wordTrace_append hprefix tailTrace_719038
  have hstable : (prefixWord ++ tailWord_719038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719038).length < 2 ^ (prefixWord ++ tailWord_719038).sum := by decide
  have hdescent : baseEnd_719038 < baseStart_719038 := by decide
  rcases family_descends (prefixWord ++ tailWord_719038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719080 : List Nat := [2, 1, 4, 1, 2, 3, 2, 5]
def baseStart_719080 : Nat := 118140960795 + 719080 * 2 ^ 59
def prefixEnd_719080 : Nat := 4983230072969 + 3 ^ 40 * 719080 * 2
def baseEnd_719080 : Nat := 109402568603007949597931

theorem tailTrace_719080 : CollatzResearch.WordTrace tailWord_719080 prefixEnd_719080 109402568603007949597931 := by
  unfold tailWord_719080
  simp only [CollatzResearch.WordTrace]
  refine ⟨13113501117451721965889347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17484668156602295954519129 13113501117451721965889347)
  ·
    refine ⟨19670251676177582948834021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13113501117451721965889347 19670251676177582948834021)
    ·
      refine ⟨3688172189283296802906379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19670251676177582948834021 3688172189283296802906379)
      ·
        refine ⟨5532258283924945204359569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688172189283296802906379 5532258283924945204359569)
        ·
          refine ⟨4149193712943708903269677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5532258283924945204359569 4149193712943708903269677)
          ·
            refine ⟨1555947642353890838726129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4149193712943708903269677 1555947642353890838726129)
            ·
              refine ⟨1166960731765418129044597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555947642353890838726129 1166960731765418129044597)
              ·
                refine ⟨109402568603007949597931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1166960731765418129044597 109402568603007949597931)
                ·
                  rfl

theorem cell20_719080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_719080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719080 prefixEnd_719080 := by exact prefixLift 719080
  have htrace : WordTrace (prefixWord ++ tailWord_719080) baseStart_719080 baseEnd_719080 := by
    simpa [prefixWord, tailWord_719080, baseEnd_719080] using wordTrace_append hprefix tailTrace_719080
  have hstable : (prefixWord ++ tailWord_719080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719080).length < 2 ^ (prefixWord ++ tailWord_719080).sum := by decide
  have hdescent : baseEnd_719080 < baseStart_719080 := by decide
  rcases family_descends (prefixWord ++ tailWord_719080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719125 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 3]
def baseStart_719125 : Nat := 118140960795 + 719125 * 2 ^ 59
def prefixEnd_719125 : Nat := 4983230072969 + 3 ^ 40 * 719125 * 2
def baseEnd_719125 : Nat := 328228245035203692293609

theorem tailTrace_719125 : CollatzResearch.WordTrace tailWord_719125 prefixEnd_719125 328228245035203692293609 := by
  unfold tailWord_719125
  simp only [CollatzResearch.WordTrace]
  refine ⟨26228643519740416617166829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17485762346493611078111219 26228643519740416617166829)
  ·
    refine ⟨9835741319902656231437561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26228643519740416617166829 9835741319902656231437561)
    ·
      refine ⟨7376805989926992173578171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9835741319902656231437561 7376805989926992173578171)
      ·
        refine ⟨11065208984890488260367257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7376805989926992173578171 11065208984890488260367257)
        ·
          refine ⟨8298906738667866195275443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11065208984890488260367257 8298906738667866195275443)
          ·
            refine ⟨12448360108001799292913165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8298906738667866195275443 12448360108001799292913165)
            ·
              refine ⟨4668135040500674734842437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12448360108001799292913165 4668135040500674734842437)
              ·
                refine ⟨875275320093876512782957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4668135040500674734842437 875275320093876512782957)
                ·
                  refine ⟨328228245035203692293609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875275320093876512782957 328228245035203692293609)
                  ·
                    rfl

theorem cell20_719125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_719125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719125 prefixEnd_719125 := by exact prefixLift 719125
  have htrace : WordTrace (prefixWord ++ tailWord_719125) baseStart_719125 baseEnd_719125 := by
    simpa [prefixWord, tailWord_719125, baseEnd_719125] using wordTrace_append hprefix tailTrace_719125
  have hstable : (prefixWord ++ tailWord_719125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719125).length < 2 ^ (prefixWord ++ tailWord_719125).sum := by decide
  have hdescent : baseEnd_719125 < baseStart_719125 := by decide
  rcases family_descends (prefixWord ++ tailWord_719125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719132 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_719132 : Nat := 118140960795 + 719132 * 2 ^ 59
def prefixEnd_719132 : Nat := 4983230072969 + 3 ^ 40 * 719132 * 2
def baseEnd_719132 : Nat := 328231440025942779060247

theorem tailTrace_719132 : CollatzResearch.WordTrace tailWord_719132 prefixEnd_719132 328231440025942779060247 := by
  unfold tailWord_719132
  simp only [CollatzResearch.WordTrace]
  refine ⟨13114449415357528406335825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17485932553810037875114433 13114449415357528406335825)
  ·
    refine ⟨9835837061518146304751869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13114449415357528406335825 9835837061518146304751869)
    ·
      refine ⟨3688438898069304864281951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9835837061518146304751869 3688438898069304864281951)
      ·
        refine ⟨5532658347103957296422927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688438898069304864281951 5532658347103957296422927)
        ·
          refine ⟨8298987520655935944634391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532658347103957296422927 8298987520655935944634391)
          ·
            refine ⟨12448481280983903916951587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8298987520655935944634391 12448481280983903916951587)
            ·
              refine ⟨18672721921475855875427381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12448481280983903916951587 18672721921475855875427381)
              ·
                refine ⟨1750567680138361488321317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18672721921475855875427381 1750567680138361488321317)
                ·
                  refine ⟨328231440025942779060247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1750567680138361488321317 328231440025942779060247)
                  ·
                    rfl

theorem cell20_719132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_719132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719132 prefixEnd_719132 := by exact prefixLift 719132
  have htrace : WordTrace (prefixWord ++ tailWord_719132) baseStart_719132 baseEnd_719132 := by
    simpa [prefixWord, tailWord_719132, baseEnd_719132] using wordTrace_append hprefix tailTrace_719132
  have hstable : (prefixWord ++ tailWord_719132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719132).length < 2 ^ (prefixWord ++ tailWord_719132).sum := by decide
  have hdescent : baseEnd_719132 < baseStart_719132 := by decide
  rcases family_descends (prefixWord ++ tailWord_719132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719166 : List Nat := [4, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_719166 : Nat := 118140960795 + 719166 * 2 ^ 59
def prefixEnd_719166 : Nat := 4983230072969 + 3 ^ 40 * 719166 * 2
def baseEnd_719166 : Nat := 328246958552389771926775

theorem tailTrace_719166 : CollatzResearch.WordTrace tailWord_719166 prefixEnd_719166 328246958552389771926775 := by
  unfold tailWord_719166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278767364073985077426169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17486759275061253746272901 3278767364073985077426169)
  ·
    refine ⟨2459075523055488808069627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3278767364073985077426169 2459075523055488808069627)
    ·
      refine ⟨3688613284583233212104441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2459075523055488808069627 3688613284583233212104441)
      ·
        refine ⟨2766459963437424909078331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3688613284583233212104441 2766459963437424909078331)
        ·
          refine ⟨4149689945156137363617497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766459963437424909078331 4149689945156137363617497)
          ·
            refine ⟨3112267458867103022713123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4149689945156137363617497 3112267458867103022713123)
            ·
              refine ⟨4668401188300654534069685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112267458867103022713123 4668401188300654534069685)
              ·
                refine ⟨437662611403186362569033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4668401188300654534069685 437662611403186362569033)
                ·
                  refine ⟨328246958552389771926775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437662611403186362569033 328246958552389771926775)
                  ·
                    rfl

theorem cell20_719166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_719166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719166 prefixEnd_719166 := by exact prefixLift 719166
  have htrace : WordTrace (prefixWord ++ tailWord_719166) baseStart_719166 baseEnd_719166 := by
    simpa [prefixWord, tailWord_719166, baseEnd_719166] using wordTrace_append hprefix tailTrace_719166
  have hstable : (prefixWord ++ tailWord_719166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719166).length < 2 ^ (prefixWord ++ tailWord_719166).sum := by decide
  have hdescent : baseEnd_719166 < baseStart_719166 := by decide
  rcases family_descends (prefixWord ++ tailWord_719166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719221 : List Nat := [1, 3, 4, 1, 2, 3, 1, 3, 2]
def baseStart_719221 : Nat := 118140960795 + 719221 * 2 ^ 59
def prefixEnd_719221 : Nat := 4983230072969 + 3 ^ 40 * 719221 * 2
def baseEnd_719221 : Nat := 328272062051054025093217

theorem tailTrace_719221 : CollatzResearch.WordTrace tailWord_719221 prefixEnd_719221 328272062051054025093217 := by
  unfold tailWord_719221
  simp only [CollatzResearch.WordTrace]
  refine ⟨26232144927392625012661517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17488096618261750008441011 26232144927392625012661517)
  ·
    refine ⟨9837054347772234379748069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26232144927392625012661517 9837054347772234379748069)
    ·
      refine ⟨1844447690207293946202763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9837054347772234379748069 1844447690207293946202763)
      ·
        refine ⟨2766671535310940919304145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844447690207293946202763 2766671535310940919304145)
        ·
          refine ⟨2075003651483205689478109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2766671535310940919304145 2075003651483205689478109)
          ·
            refine ⟨778126369306202133554291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2075003651483205689478109 778126369306202133554291)
            ·
              refine ⟨1167189553959303200331437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778126369306202133554291 1167189553959303200331437)
              ·
                refine ⟨437696082734738700124289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167189553959303200331437 437696082734738700124289)
                ·
                  refine ⟨328272062051054025093217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437696082734738700124289 328272062051054025093217)
                  ·
                    rfl

theorem cell20_719221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_719221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719221 prefixEnd_719221 := by exact prefixLift 719221
  have htrace : WordTrace (prefixWord ++ tailWord_719221) baseStart_719221 baseEnd_719221 := by
    simpa [prefixWord, tailWord_719221, baseEnd_719221] using wordTrace_append hprefix tailTrace_719221
  have hstable : (prefixWord ++ tailWord_719221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719221).length < 2 ^ (prefixWord ++ tailWord_719221).sum := by decide
  have hdescent : baseEnd_719221 < baseStart_719221 := by decide
  rcases family_descends (prefixWord ++ tailWord_719221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719239 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 3]
def baseStart_719239 : Nat := 118140960795 + 719239 * 2 ^ 59
def prefixEnd_719239 : Nat := 4983230072969 + 3 ^ 40 * 719239 * 2
def baseEnd_719239 : Nat := 328280277741525962493143

theorem tailTrace_719239 : CollatzResearch.WordTrace tailWord_719239 prefixEnd_719239 328280277741525962493143 := by
  unfold tailWord_719239
  simp only [CollatzResearch.WordTrace]
  refine ⟨26232801441327414086816771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17488534294218276057877847 26232801441327414086816771)
  ·
    refine ⟨39349202161991121130225157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26232801441327414086816771 39349202161991121130225157)
    ·
      refine ⟨7377975405373335211917217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39349202161991121130225157 7377975405373335211917217)
      ·
        refine ⟨5533481554030001408937913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7377975405373335211917217 5533481554030001408937913)
        ·
          refine ⟨4150111165522501056703435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5533481554030001408937913 4150111165522501056703435)
          ·
            refine ⟨6225166748283751585055153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150111165522501056703435 6225166748283751585055153)
            ·
              refine ⟨4668875061212813688791365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6225166748283751585055153 4668875061212813688791365)
              ·
                refine ⟨875414073977402566648381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4668875061212813688791365 875414073977402566648381)
                ·
                  refine ⟨328280277741525962493143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875414073977402566648381 328280277741525962493143)
                  ·
                    rfl

theorem cell20_719239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_719239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719239 prefixEnd_719239 := by exact prefixLift 719239
  have htrace : WordTrace (prefixWord ++ tailWord_719239) baseStart_719239 baseEnd_719239 := by
    simpa [prefixWord, tailWord_719239, baseEnd_719239] using wordTrace_append hprefix tailTrace_719239
  have hstable : (prefixWord ++ tailWord_719239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719239).length < 2 ^ (prefixWord ++ tailWord_719239).sum := by decide
  have hdescent : baseEnd_719239 < baseStart_719239 := by decide
  rcases family_descends (prefixWord ++ tailWord_719239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719252 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_719252 : Nat := 118140960795 + 719252 * 2 ^ 59
def prefixEnd_719252 : Nat := 4983230072969 + 3 ^ 40 * 719252 * 2
def baseEnd_719252 : Nat := 328286211295755695059757

theorem tailTrace_719252 : CollatzResearch.WordTrace tailWord_719252 prefixEnd_719252 328286211295755695059757 := by
  unfold tailWord_719252
  simp only [CollatzResearch.WordTrace]
  refine ⟨13116637795140158653520005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17488850393520211538026673 13116637795140158653520005)
  ·
    refine ⟨2459369586588779747535001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13116637795140158653520005 2459369586588779747535001)
    ·
      refine ⟨1844527189941584810651251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2459369586588779747535001 1844527189941584810651251)
      ·
        refine ⟨2766790784912377215976877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844527189941584810651251 2766790784912377215976877)
        ·
          refine ⟨1037546544342141455991329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2766790784912377215976877 1037546544342141455991329)
          ·
            refine ⟨778159908256606091993497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037546544342141455991329 778159908256606091993497)
            ·
              refine ⟨583619931192454568995123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778159908256606091993497 583619931192454568995123)
              ·
                refine ⟨875429896788681853492685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583619931192454568995123 875429896788681853492685)
                ·
                  refine ⟨328286211295755695059757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875429896788681853492685 328286211295755695059757)
                  ·
                    rfl

theorem cell20_719252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_719252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719252 prefixEnd_719252 := by exact prefixLift 719252
  have htrace : WordTrace (prefixWord ++ tailWord_719252) baseStart_719252 baseEnd_719252 := by
    simpa [prefixWord, tailWord_719252, baseEnd_719252] using wordTrace_append hprefix tailTrace_719252
  have hstable : (prefixWord ++ tailWord_719252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719252).length < 2 ^ (prefixWord ++ tailWord_719252).sum := by decide
  have hdescent : baseEnd_719252 < baseStart_719252 := by decide
  rcases family_descends (prefixWord ++ tailWord_719252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719256 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_719256 : Nat := 118140960795 + 719256 * 2 ^ 59
def prefixEnd_719256 : Nat := 4983230072969 + 3 ^ 40 * 719256 * 2
def baseEnd_719256 : Nat := 328288037004749458926407

theorem tailTrace_719256 : CollatzResearch.WordTrace tailWord_719256 prefixEnd_719256 328288037004749458926407 := by
  unfold tailWord_719256
  simp only [CollatzResearch.WordTrace]
  refine ⟨13116710741132912995092811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17488947654843883993457081 13116710741132912995092811)
  ·
    refine ⟨19675066111699369492639217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13116710741132912995092811 19675066111699369492639217)
    ·
      refine ⟨14756299583774527119479413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19675066111699369492639217 14756299583774527119479413)
      ·
        refine ⟨1383403085978861917451195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14756299583774527119479413 1383403085978861917451195)
        ·
          refine ⟨2075104628968292876176793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383403085978861917451195 2075104628968292876176793)
          ·
            refine ⟨1556328471726219657132595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2075104628968292876176793 1556328471726219657132595)
            ·
              refine ⟨2334492707589329485698893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556328471726219657132595 2334492707589329485698893)
              ·
                refine ⟨875434765345998557137085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2334492707589329485698893 875434765345998557137085)
                ·
                  refine ⟨328288037004749458926407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875434765345998557137085 328288037004749458926407)
                  ·
                    rfl

theorem cell20_719256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_719256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719256 prefixEnd_719256 := by exact prefixLift 719256
  have htrace : WordTrace (prefixWord ++ tailWord_719256) baseStart_719256 baseEnd_719256 := by
    simpa [prefixWord, tailWord_719256, baseEnd_719256] using wordTrace_append hprefix tailTrace_719256
  have hstable : (prefixWord ++ tailWord_719256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719256).length < 2 ^ (prefixWord ++ tailWord_719256).sum := by decide
  have hdescent : baseEnd_719256 < baseStart_719256 := by decide
  rcases family_descends (prefixWord ++ tailWord_719256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719322 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_719322 : Nat := 118140960795 + 719322 * 2 ^ 59
def prefixEnd_719322 : Nat := 4983230072969 + 3 ^ 40 * 719322 * 2
def baseEnd_719322 : Nat := 328318161203146562726137

theorem tailTrace_719322 : CollatzResearch.WordTrace tailWord_719322 prefixEnd_719322 328318161203146562726137 := by
  unfold tailWord_719322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558957175006679815522055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17490552466684479508058813 6558957175006679815522055)
  ·
    refine ⟨9838435762510019723283083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6558957175006679815522055 9838435762510019723283083)
    ·
      refine ⟨14757653643765029584924625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9838435762510019723283083 14757653643765029584924625)
      ·
        refine ⟨11068240232823772188693469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14757653643765029584924625 11068240232823772188693469)
        ·
          refine ⟨4150590087308914570760051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11068240232823772188693469 4150590087308914570760051)
          ·
            refine ⟨6225885130963371856140077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150590087308914570760051 6225885130963371856140077)
            ·
              refine ⟨2334706924111264446052529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6225885130963371856140077 2334706924111264446052529)
              ·
                refine ⟨1751030193083448334539397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2334706924111264446052529 1751030193083448334539397)
                ·
                  refine ⟨328318161203146562726137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1751030193083448334539397 328318161203146562726137)
                  ·
                    rfl

theorem cell20_719322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_719322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719322 prefixEnd_719322 := by exact prefixLift 719322
  have htrace : WordTrace (prefixWord ++ tailWord_719322) baseStart_719322 baseEnd_719322 := by
    simpa [prefixWord, tailWord_719322, baseEnd_719322] using wordTrace_append hprefix tailTrace_719322
  have hstable : (prefixWord ++ tailWord_719322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719322).length < 2 ^ (prefixWord ++ tailWord_719322).sum := by decide
  have hdescent : baseEnd_719322 < baseStart_719322 := by decide
  rcases family_descends (prefixWord ++ tailWord_719322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719339 : List Nat := [1, 1, 1, 1, 2, 3, 6, 3, 2]
def baseStart_719339 : Nat := 118140960795 + 719339 * 2 ^ 59
def prefixEnd_719339 : Nat := 4983230072969 + 3 ^ 40 * 719339 * 2
def baseEnd_719339 : Nat := 328325920466370059159401

theorem tailTrace_719339 : CollatzResearch.WordTrace tailWord_719339 prefixEnd_719339 328325920466370059159401 := by
  unfold tailWord_719339
  simp only [CollatzResearch.WordTrace]
  refine ⟨26236448740965131165457071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17490965827310087443638047 26236448740965131165457071)
  ·
    refine ⟨39354673111447696748185607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26236448740965131165457071 39354673111447696748185607)
    ·
      refine ⟨59032009667171545122278411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39354673111447696748185607 59032009667171545122278411)
      ·
        refine ⟨88548014500757317683417617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59032009667171545122278411 88548014500757317683417617)
        ·
          refine ⟨66411010875567988262563213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88548014500757317683417617 66411010875567988262563213)
          ·
            refine ⟨24904129078337995598461205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66411010875567988262563213 24904129078337995598461205)
            ·
              refine ⟨1167381050547093543677869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24904129078337995598461205 1167381050547093543677869)
              ·
                refine ⟨437767893955160078879201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167381050547093543677869 437767893955160078879201)
                ·
                  refine ⟨328325920466370059159401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437767893955160078879201 328325920466370059159401)
                  ·
                    rfl

theorem cell20_719339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 2].length) (baseStart_719339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719339 prefixEnd_719339 := by exact prefixLift 719339
  have htrace : WordTrace (prefixWord ++ tailWord_719339) baseStart_719339 baseEnd_719339 := by
    simpa [prefixWord, tailWord_719339, baseEnd_719339] using wordTrace_append hprefix tailTrace_719339
  have hstable : (prefixWord ++ tailWord_719339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719339).length < 2 ^ (prefixWord ++ tailWord_719339).sum := by decide
  have hdescent : baseEnd_719339 < baseStart_719339 := by decide
  rcases family_descends (prefixWord ++ tailWord_719339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719343 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_719343 : Nat := 118140960795 + 719343 * 2 ^ 59
def prefixEnd_719343 : Nat := 4983230072969 + 3 ^ 40 * 719343 * 2
def baseEnd_719343 : Nat := 328327746175363823026051

theorem tailTrace_719343 : CollatzResearch.WordTrace tailWord_719343 prefixEnd_719343 328327746175363823026051 := by
  unfold tailWord_719343
  simp only [CollatzResearch.WordTrace]
  refine ⟨26236594632950639848602683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17491063088633759899068455 26236594632950639848602683)
  ·
    refine ⟨39354891949425959772904025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26236594632950639848602683 39354891949425959772904025)
    ·
      refine ⟨29516168962069469829678019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39354891949425959772904025 29516168962069469829678019)
      ·
        refine ⟨44274253443104204744517029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29516168962069469829678019 44274253443104204744517029)
        ·
          refine ⟨8301422520582038389596943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44274253443104204744517029 8301422520582038389596943)
          ·
            refine ⟨12452133780873057584395415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8301422520582038389596943 12452133780873057584395415)
            ·
              refine ⟨18678200671309586376593123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12452133780873057584395415 18678200671309586376593123)
              ·
                refine ⟨28017301006964379564889685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18678200671309586376593123 28017301006964379564889685)
                ·
                  refine ⟨328327746175363823026051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28017301006964379564889685 328327746175363823026051)
                  ·
                    rfl

theorem cell20_719343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_719343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719343 prefixEnd_719343 := by exact prefixLift 719343
  have htrace : WordTrace (prefixWord ++ tailWord_719343) baseStart_719343 baseEnd_719343 := by
    simpa [prefixWord, tailWord_719343, baseEnd_719343] using wordTrace_append hprefix tailTrace_719343
  have hstable : (prefixWord ++ tailWord_719343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719343).length < 2 ^ (prefixWord ++ tailWord_719343).sum := by decide
  have hdescent : baseEnd_719343 < baseStart_719343 := by decide
  rcases family_descends (prefixWord ++ tailWord_719343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719346 : List Nat := [3, 2, 1, 4, 2, 1, 7]
def baseStart_719346 : Nat := 118140960795 + 719346 * 2 ^ 59
def prefixEnd_719346 : Nat := 4983230072969 + 3 ^ 40 * 719346 * 2
def baseEnd_719346 : Nat := 36481012828567682880671

theorem tailTrace_719346 : CollatzResearch.WordTrace tailWord_719346 prefixEnd_719346 36481012828567682880671 := by
  unfold tailWord_719346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559176012984942840240473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17491136034626514240641261 6559176012984942840240473)
  ·
    refine ⟨4919382009738707130180355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6559176012984942840240473 4919382009738707130180355)
    ·
      refine ⟨7379073014608060695270533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919382009738707130180355 7379073014608060695270533)
      ·
        refine ⟨1383576190239011380363225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7379073014608060695270533 1383576190239011380363225)
        ·
          refine ⟨1037682142679258535272419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383576190239011380363225 1037682142679258535272419)
          ·
            refine ⟨1556523214018887802908629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037682142679258535272419 1556523214018887802908629)
            ·
              refine ⟨36481012828567682880671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1556523214018887802908629 36481012828567682880671)
              ·
                rfl

theorem cell20_719346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 7].length) (baseStart_719346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719346 prefixEnd_719346 := by exact prefixLift 719346
  have htrace : WordTrace (prefixWord ++ tailWord_719346) baseStart_719346 baseEnd_719346 := by
    simpa [prefixWord, tailWord_719346, baseEnd_719346] using wordTrace_append hprefix tailTrace_719346
  have hstable : (prefixWord ++ tailWord_719346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719346).length < 2 ^ (prefixWord ++ tailWord_719346).sum := by decide
  have hdescent : baseEnd_719346 < baseStart_719346 := by decide
  rcases family_descends (prefixWord ++ tailWord_719346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719353 : List Nat := [1, 2, 1, 3, 1, 2, 5, 2, 3]
def baseStart_719353 : Nat := 118140960795 + 719353 * 2 ^ 59
def prefixEnd_719353 : Nat := 4983230072969 + 3 ^ 40 * 719353 * 2
def baseEnd_719353 : Nat := 328332310447848232692677

theorem tailTrace_719353 : CollatzResearch.WordTrace tailWord_719353 prefixEnd_719353 328332310447848232692677 := by
  unfold tailWord_719353
  simp only [CollatzResearch.WordTrace]
  refine ⟨26236959362914411556466713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17491306241942941037644475 26236959362914411556466713)
  ·
    refine ⟨19677719522185808667350035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26236959362914411556466713 19677719522185808667350035)
    ·
      refine ⟨29516579283278713001025053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19677719522185808667350035 29516579283278713001025053)
      ·
        refine ⟨11068717231229517375384395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29516579283278713001025053 11068717231229517375384395)
        ·
          refine ⟨16603075846844276063076593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11068717231229517375384395 16603075846844276063076593)
          ·
            refine ⟨12452306885133207047307445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16603075846844276063076593 12452306885133207047307445)
            ·
              refine ⟨1167403770481238160685073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12452306885133207047307445 1167403770481238160685073)
              ·
                refine ⟨875552827860928620513805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167403770481238160685073 875552827860928620513805)
                ·
                  refine ⟨328332310447848232692677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875552827860928620513805 328332310447848232692677)
                  ·
                    rfl

theorem cell20_719353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_719353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719353 prefixEnd_719353 := by exact prefixLift 719353
  have htrace : WordTrace (prefixWord ++ tailWord_719353) baseStart_719353 baseEnd_719353 := by
    simpa [prefixWord, tailWord_719353, baseEnd_719353] using wordTrace_append hprefix tailTrace_719353
  have hstable : (prefixWord ++ tailWord_719353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719353).length < 2 ^ (prefixWord ++ tailWord_719353).sum := by decide
  have hdescent : baseEnd_719353 < baseStart_719353 := by decide
  rcases family_descends (prefixWord ++ tailWord_719353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719370 : List Nat := [3, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_719370 : Nat := 118140960795 + 719370 * 2 ^ 59
def prefixEnd_719370 : Nat := 4983230072969 + 3 ^ 40 * 719370 * 2
def baseEnd_719370 : Nat := 328340069711071729125941

theorem tailTrace_719370 : CollatzResearch.WordTrace tailWord_719370 prefixEnd_719370 328340069711071729125941 := by
  unfold tailWord_719370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559394850963205864958891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17491719602568548973223709 6559394850963205864958891)
  ·
    refine ⟨9839092276444808797438337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6559394850963205864958891 9839092276444808797438337)
    ·
      refine ⟨7379319207333606598078753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9839092276444808797438337 7379319207333606598078753)
      ·
        refine ⟨5534489405500204948559065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7379319207333606598078753 5534489405500204948559065)
        ·
          refine ⟨4150867054125153711419299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5534489405500204948559065 4150867054125153711419299)
          ·
            refine ⟨6226300581187730567128949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150867054125153711419299 6226300581187730567128949)
            ·
              refine ⟨583715679486349740668339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6226300581187730567128949 583715679486349740668339)
              ·
                refine ⟨875573519229524611002509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583715679486349740668339 875573519229524611002509)
                ·
                  refine ⟨328340069711071729125941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875573519229524611002509 328340069711071729125941)
                  ·
                    rfl

theorem cell20_719370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_719370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719370 prefixEnd_719370 := by exact prefixLift 719370
  have htrace : WordTrace (prefixWord ++ tailWord_719370) baseStart_719370 baseEnd_719370 := by
    simpa [prefixWord, tailWord_719370, baseEnd_719370] using wordTrace_append hprefix tailTrace_719370
  have hstable : (prefixWord ++ tailWord_719370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719370).length < 2 ^ (prefixWord ++ tailWord_719370).sum := by decide
  have hdescent : baseEnd_719370 < baseStart_719370 := by decide
  rcases family_descends (prefixWord ++ tailWord_719370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719380 : List Nat := [2, 4, 3, 1, 1, 3, 2, 4]
def baseStart_719380 : Nat := 118140960795 + 719380 * 2 ^ 59
def prefixEnd_719380 : Nat := 4983230072969 + 3 ^ 40 * 719380 * 2
def baseEnd_719380 : Nat := 109448211327852046264189

theorem tailTrace_719380 : CollatzResearch.WordTrace tailWord_719380 prefixEnd_719380 109448211327852046264189 := by
  unfold tailWord_719380
  simp only [CollatzResearch.WordTrace]
  refine ⟨13118972066908297583849797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17491962755877730111799729 13118972066908297583849797)
  ·
    refine ⟨2459807262545305796971837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13118972066908297583849797 2459807262545305796971837)
    ·
      refine ⟨922427723454489673864439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2459807262545305796971837 922427723454489673864439)
      ·
        refine ⟨1383641585181734510796659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922427723454489673864439 1383641585181734510796659)
        ·
          refine ⟨2075462377772601766194989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383641585181734510796659 2075462377772601766194989)
          ·
            refine ⟨778298391664725662323121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2075462377772601766194989 778298391664725662323121)
            ·
              refine ⟨583723793748544246742341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778298391664725662323121 583723793748544246742341)
              ·
                refine ⟨109448211327852046264189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583723793748544246742341 109448211327852046264189)
                ·
                  rfl

theorem cell20_719380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_719380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719380 prefixEnd_719380 := by exact prefixLift 719380
  have htrace : WordTrace (prefixWord ++ tailWord_719380) baseStart_719380 baseEnd_719380 := by
    simpa [prefixWord, tailWord_719380, baseEnd_719380] using wordTrace_append hprefix tailTrace_719380
  have hstable : (prefixWord ++ tailWord_719380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719380).length < 2 ^ (prefixWord ++ tailWord_719380).sum := by decide
  have hdescent : baseEnd_719380 < baseStart_719380 := by decide
  rcases family_descends (prefixWord ++ tailWord_719380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719384 : List Nat := [2, 1, 2, 3, 3, 1, 4, 4]
def baseStart_719384 : Nat := 118140960795 + 719384 * 2 ^ 59
def prefixEnd_719384 : Nat := 4983230072969 + 3 ^ 40 * 719384 * 2
def baseEnd_719384 : Nat := 109448819897516634219739

theorem tailTrace_719384 : CollatzResearch.WordTrace tailWord_719384 prefixEnd_719384 109448819897516634219739 := by
  unfold tailWord_719384
  simp only [CollatzResearch.WordTrace]
  refine ⟨13119045012901051925422603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17492060017201402567230137 13119045012901051925422603)
  ·
    refine ⟨19678567519351577888133905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13119045012901051925422603 19678567519351577888133905)
    ·
      refine ⟨14758925639513683416100429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19678567519351577888133905 14758925639513683416100429)
      ·
        refine ⟨5534597114817631281037661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14758925639513683416100429 5534597114817631281037661)
        ·
          refine ⟨2075473918056611730389123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5534597114817631281037661 2075473918056611730389123)
          ·
            refine ⟨3113210877084917595583685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075473918056611730389123 3113210877084917595583685)
            ·
              refine ⟨583727039453422049171941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3113210877084917595583685 583727039453422049171941)
              ·
                refine ⟨109448819897516634219739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583727039453422049171941 109448819897516634219739)
                ·
                  rfl

theorem cell20_719384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_719384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719384 prefixEnd_719384 := by exact prefixLift 719384
  have htrace : WordTrace (prefixWord ++ tailWord_719384) baseStart_719384 baseEnd_719384 := by
    simpa [prefixWord, tailWord_719384, baseEnd_719384] using wordTrace_append hprefix tailTrace_719384
  have hstable : (prefixWord ++ tailWord_719384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719384).length < 2 ^ (prefixWord ++ tailWord_719384).sum := by decide
  have hdescent : baseEnd_719384 < baseStart_719384 := by decide
  rcases family_descends (prefixWord ++ tailWord_719384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719425 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 3]
def baseStart_719425 : Nat := 118140960795 + 719425 * 2 ^ 59
def prefixEnd_719425 : Nat := 4983230072969 + 3 ^ 40 * 719425 * 2
def baseEnd_719425 : Nat := 328365173209735982292383

theorem tailTrace_719425 : CollatzResearch.WordTrace tailWord_719425 prefixEnd_719425 328365173209735982292383 := by
  unfold tailWord_719425
  simp only [CollatzResearch.WordTrace]
  refine ⟨26239585418653567853087729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17493056945769045235391819 26239585418653567853087729)
  ·
    refine ⟨19679689063990175889815797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26239585418653567853087729 19679689063990175889815797)
    ·
      refine ⟨1844970849749078989670231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19679689063990175889815797 1844970849749078989670231)
      ·
        refine ⟨2767456274623618484505347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844970849749078989670231 2767456274623618484505347)
        ·
          refine ⟨4151184411935427726758021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767456274623618484505347 4151184411935427726758021)
          ·
            refine ⟨778347077237892698767129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4151184411935427726758021 778347077237892698767129)
            ·
              refine ⟨583760307928419524075347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778347077237892698767129 583760307928419524075347)
              ·
                refine ⟨875640461892629286113021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583760307928419524075347 875640461892629286113021)
                ·
                  refine ⟨328365173209735982292383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875640461892629286113021 328365173209735982292383)
                  ·
                    rfl

theorem cell20_719425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_719425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719425 prefixEnd_719425 := by exact prefixLift 719425
  have htrace : WordTrace (prefixWord ++ tailWord_719425) baseStart_719425 baseEnd_719425 := by
    simpa [prefixWord, tailWord_719425, baseEnd_719425] using wordTrace_append hprefix tailTrace_719425
  have hstable : (prefixWord ++ tailWord_719425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719425).length < 2 ^ (prefixWord ++ tailWord_719425).sum := by decide
  have hdescent : baseEnd_719425 < baseStart_719425 := by decide
  rcases family_descends (prefixWord ++ tailWord_719425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719429 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 3]
def baseStart_719429 : Nat := 118140960795 + 719429 * 2 ^ 59
def prefixEnd_719429 : Nat := 4983230072969 + 3 ^ 40 * 719429 * 2
def baseEnd_719429 : Nat := 328366998918729746159033

theorem tailTrace_719429 : CollatzResearch.WordTrace tailWord_719429 prefixEnd_719429 328366998918729746159033 := by
  unfold tailWord_719429
  simp only [CollatzResearch.WordTrace]
  refine ⟨26239731310639076536233341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17493154207092717690822227 26239731310639076536233341)
  ·
    refine ⟨9839899241489653701087503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26239731310639076536233341 9839899241489653701087503)
    ·
      refine ⟨14759848862234480551631255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9839899241489653701087503 14759848862234480551631255)
      ·
        refine ⟨22139773293351720827446883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14759848862234480551631255 22139773293351720827446883)
        ·
          refine ⟨33209659940027581241170325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22139773293351720827446883 33209659940027581241170325)
          ·
            refine ⟨1556702809688792870679859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33209659940027581241170325 1556702809688792870679859)
            ·
              refine ⟨2335054214533189306019789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556702809688792870679859 2335054214533189306019789)
              ·
                refine ⟨875645330449945989757421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2335054214533189306019789 875645330449945989757421)
                ·
                  refine ⟨328366998918729746159033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875645330449945989757421 328366998918729746159033)
                  ·
                    rfl

theorem cell20_719429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_719429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719429 prefixEnd_719429 := by exact prefixLift 719429
  have htrace : WordTrace (prefixWord ++ tailWord_719429) baseStart_719429 baseEnd_719429 := by
    simpa [prefixWord, tailWord_719429, baseEnd_719429] using wordTrace_append hprefix tailTrace_719429
  have hstable : (prefixWord ++ tailWord_719429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719429).length < 2 ^ (prefixWord ++ tailWord_719429).sum := by decide
  have hdescent : baseEnd_719429 < baseStart_719429 := by decide
  rcases family_descends (prefixWord ++ tailWord_719429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719470 : List Nat := [4, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_719470 : Nat := 118140960795 + 719470 * 2 ^ 59
def prefixEnd_719470 : Nat := 4983230072969 + 3 ^ 40 * 719470 * 2
def baseEnd_719470 : Nat := 328385712435915825792199

theorem tailTrace_719470 : CollatzResearch.WordTrace tailWord_719470 prefixEnd_719470 328385712435915825792199 := by
  unfold tailWord_719470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280153337936317567309483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17494151135660360358983909 3280153337936317567309483)
  ·
    refine ⟨4920230006904476350964225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3280153337936317567309483 4920230006904476350964225)
    ·
      refine ⟨3690172505178357263223169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4920230006904476350964225 3690172505178357263223169)
      ·
        refine ⟨2767629378883767947417377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3690172505178357263223169 2767629378883767947417377)
        ·
          refine ⟨2075722034162825960563033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2767629378883767947417377 2075722034162825960563033)
          ·
            refine ⟨1556791525622119470422275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2075722034162825960563033 1556791525622119470422275)
            ·
              refine ⟨2335187288433179205633413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556791525622119470422275 2335187288433179205633413)
              ·
                refine ⟨437847616581221101056265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2335187288433179205633413 437847616581221101056265)
                ·
                  refine ⟨328385712435915825792199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437847616581221101056265 328385712435915825792199)
                  ·
                    rfl

theorem cell20_719470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_719470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719470 prefixEnd_719470 := by exact prefixLift 719470
  have htrace : WordTrace (prefixWord ++ tailWord_719470) baseStart_719470 baseEnd_719470 := by
    simpa [prefixWord, tailWord_719470, baseEnd_719470] using wordTrace_append hprefix tailTrace_719470
  have hstable : (prefixWord ++ tailWord_719470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719470).length < 2 ^ (prefixWord ++ tailWord_719470).sum := by decide
  have hdescent : baseEnd_719470 < baseStart_719470 := by decide
  rcases family_descends (prefixWord ++ tailWord_719470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719477 : List Nat := [1, 3, 4, 2, 2, 2, 1, 5]
def baseStart_719477 : Nat := 118140960795 + 719477 * 2 ^ 59
def prefixEnd_719477 : Nat := 4983230072969 + 3 ^ 40 * 719477 * 2
def baseEnd_719477 : Nat := 109462969142218304186279

theorem tailTrace_719477 : CollatzResearch.WordTrace tailWord_719477 prefixEnd_719477 109462969142218304186279 := by
  unfold tailWord_719477
  simp only [CollatzResearch.WordTrace]
  refine ⟨26241482014465180733980685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17494321342976787155987123 26241482014465180733980685)
  ·
    refine ⟨9840555755424442775242757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26241482014465180733980685 9840555755424442775242757)
    ·
      refine ⟨1845104204142083020358017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9840555755424442775242757 1845104204142083020358017)
      ·
        refine ⟨1383828153106562265268513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1845104204142083020358017 1383828153106562265268513)
        ·
          refine ⟨1037871114829921698951385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383828153106562265268513 1037871114829921698951385)
          ·
            refine ⟨778403336122441274213539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037871114829921698951385 778403336122441274213539)
            ·
              refine ⟨1167605004183661911320309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778403336122441274213539 1167605004183661911320309)
              ·
                refine ⟨109462969142218304186279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1167605004183661911320309 109462969142218304186279)
                ·
                  rfl

theorem cell20_719477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_719477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719477 prefixEnd_719477 := by exact prefixLift 719477
  have htrace : WordTrace (prefixWord ++ tailWord_719477) baseStart_719477 baseEnd_719477 := by
    simpa [prefixWord, tailWord_719477, baseEnd_719477] using wordTrace_append hprefix tailTrace_719477
  have hstable : (prefixWord ++ tailWord_719477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719477).length < 2 ^ (prefixWord ++ tailWord_719477).sum := by decide
  have hdescent : baseEnd_719477 < baseStart_719477 := by decide
  rcases family_descends (prefixWord ++ tailWord_719477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719481 : List Nat := [1, 2, 1, 3, 3, 2, 3, 5]
def baseStart_719481 : Nat := 118140960795 + 719481 * 2 ^ 59
def prefixEnd_719481 : Nat := 4983230072969 + 3 ^ 40 * 719481 * 2
def baseEnd_719481 : Nat := 109463577711882892141829

theorem tailTrace_719481 : CollatzResearch.WordTrace tailWord_719481 prefixEnd_719481 109463577711882892141829 := by
  unfold tailWord_719481
  simp only [CollatzResearch.WordTrace]
  refine ⟨26241627906450689417126297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17494418604300459611417531 26241627906450689417126297)
  ·
    refine ⟨19681220929838017062844723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26241627906450689417126297 19681220929838017062844723)
    ·
      refine ⟨29521831394757025594267085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19681220929838017062844723 29521831394757025594267085)
      ·
        refine ⟨11070686773033884597850157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29521831394757025594267085 11070686773033884597850157)
        ·
          refine ⟨4151507539887706724193809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11070686773033884597850157 4151507539887706724193809)
          ·
            refine ⟨3113630654915780043145357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4151507539887706724193809 3113630654915780043145357)
            ·
              refine ⟨1167611495593417516179509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3113630654915780043145357 1167611495593417516179509)
              ·
                refine ⟨109463577711882892141829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1167611495593417516179509 109463577711882892141829)
                ·
                  rfl

theorem cell20_719481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 5].length) (baseStart_719481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719481 prefixEnd_719481 := by exact prefixLift 719481
  have htrace : WordTrace (prefixWord ++ tailWord_719481) baseStart_719481 baseEnd_719481 := by
    simpa [prefixWord, tailWord_719481, baseEnd_719481] using wordTrace_append hprefix tailTrace_719481
  have hstable : (prefixWord ++ tailWord_719481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719481).length < 2 ^ (prefixWord ++ tailWord_719481).sum := by decide
  have hdescent : baseEnd_719481 < baseStart_719481 := by decide
  rcases family_descends (prefixWord ++ tailWord_719481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719508 : List Nat := [2, 4, 2, 2, 1, 1, 1, 5, 2]
def baseStart_719508 : Nat := 118140960795 + 719508 * 2 ^ 59
def prefixEnd_719508 : Nat := 4983230072969 + 3 ^ 40 * 719508 * 2
def baseEnd_719508 : Nat := 328403056671356582525377

theorem tailTrace_719508 : CollatzResearch.WordTrace tailWord_719508 prefixEnd_719508 328403056671356582525377 := by
  unfold tailWord_719508
  simp only [CollatzResearch.WordTrace]
  refine ⟨13121306338676436514179589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17495075118235248685572785 13121306338676436514179589)
  ·
    refine ⟨2460244938501831846408673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13121306338676436514179589 2460244938501831846408673)
    ·
      refine ⟨1845183703876373884806505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2460244938501831846408673 1845183703876373884806505)
      ·
        refine ⟨1383887777907280413604879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1845183703876373884806505 1383887777907280413604879)
        ·
          refine ⟨2075831666860920620407319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383887777907280413604879 2075831666860920620407319)
          ·
            refine ⟨3113747500291380930610979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075831666860920620407319 3113747500291380930610979)
            ·
              refine ⟨4670621250437071395916469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113747500291380930610979 4670621250437071395916469)
              ·
                refine ⟨437870742228475443367169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4670621250437071395916469 437870742228475443367169)
                ·
                  refine ⟨328403056671356582525377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437870742228475443367169 328403056671356582525377)
                  ·
                    rfl

theorem cell20_719508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_719508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719508 prefixEnd_719508 := by exact prefixLift 719508
  have htrace : WordTrace (prefixWord ++ tailWord_719508) baseStart_719508 baseEnd_719508 := by
    simpa [prefixWord, tailWord_719508, baseEnd_719508] using wordTrace_append hprefix tailTrace_719508
  have hstable : (prefixWord ++ tailWord_719508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719508).length < 2 ^ (prefixWord ++ tailWord_719508).sum := by decide
  have hdescent : baseEnd_719508 < baseStart_719508 := by decide
  rcases family_descends (prefixWord ++ tailWord_719508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719550 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_719550 : Nat := 118140960795 + 719550 * 2 ^ 59
def prefixEnd_719550 : Nat := 4983230072969 + 3 ^ 40 * 719550 * 2
def baseEnd_719550 : Nat := 328422226615791103125205

theorem tailTrace_719550 : CollatzResearch.WordTrace tailWord_719550 prefixEnd_719550 328422226615791103125205 := by
  unfold tailWord_719550
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280518067900089275173513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17496096362133809467592069 3280518067900089275173513)
  ·
    refine ⟨2460388550925066956380135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3280518067900089275173513 2460388550925066956380135)
    ·
      refine ⟨3690582826387600434570203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460388550925066956380135 3690582826387600434570203)
      ·
        refine ⟨5535874239581400651855305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3690582826387600434570203 5535874239581400651855305)
        ·
          refine ⟨4151905679686050488891479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5535874239581400651855305 4151905679686050488891479)
          ·
            refine ⟨6227858519529075733337219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151905679686050488891479 6227858519529075733337219)
            ·
              refine ⟨9341787779293613600005829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6227858519529075733337219 9341787779293613600005829)
              ·
                refine ⟨1751585208617552550001093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9341787779293613600005829 1751585208617552550001093)
                ·
                  refine ⟨328422226615791103125205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1751585208617552550001093 328422226615791103125205)
                  ·
                    rfl

theorem cell20_719550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_719550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719550 prefixEnd_719550 := by exact prefixLift 719550
  have htrace : WordTrace (prefixWord ++ tailWord_719550) baseStart_719550 baseEnd_719550 := by
    simpa [prefixWord, tailWord_719550, baseEnd_719550] using wordTrace_append hprefix tailTrace_719550
  have hstable : (prefixWord ++ tailWord_719550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719550).length < 2 ^ (prefixWord ++ tailWord_719550).sum := by decide
  have hdescent : baseEnd_719550 < baseStart_719550 := by decide
  rcases family_descends (prefixWord ++ tailWord_719550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719553 : List Nat := [1, 2, 6, 2, 1, 1, 1, 6]
def baseStart_719553 : Nat := 118140960795 + 719553 * 2 ^ 59
def prefixEnd_719553 : Nat := 4983230072969 + 3 ^ 40 * 719553 * 2
def baseEnd_719553 : Nat := 109474531965845475341731

theorem tailTrace_719553 : CollatzResearch.WordTrace tailWord_719553 prefixEnd_719553 109474531965845475341731 := by
  unfold tailWord_719553
  simp only [CollatzResearch.WordTrace]
  refine ⟨26244253962189845713747313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17496169308126563809164875 26244253962189845713747313)
  ·
    refine ⟨19683190471642384285310485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26244253962189845713747313 19683190471642384285310485)
    ·
      refine ⟨922649553358236763373929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19683190471642384285310485 922649553358236763373929)
      ·
        refine ⟨691987165018677572530447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 922649553358236763373929 691987165018677572530447)
        ·
          refine ⟨1037980747528016358795671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691987165018677572530447 1037980747528016358795671)
          ·
            refine ⟨1556971121292024538193507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037980747528016358795671 1556971121292024538193507)
            ·
              refine ⟨2335456681938036807290261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556971121292024538193507 2335456681938036807290261)
              ·
                refine ⟨109474531965845475341731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2335456681938036807290261 109474531965845475341731)
                ·
                  rfl

theorem cell20_719553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 6].length) (baseStart_719553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719553 prefixEnd_719553 := by exact prefixLift 719553
  have htrace : WordTrace (prefixWord ++ tailWord_719553) baseStart_719553 baseEnd_719553 := by
    simpa [prefixWord, tailWord_719553, baseEnd_719553] using wordTrace_append hprefix tailTrace_719553
  have hstable : (prefixWord ++ tailWord_719553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719553).length < 2 ^ (prefixWord ++ tailWord_719553).sum := by decide
  have hdescent : baseEnd_719553 < baseStart_719553 := by decide
  rcases family_descends (prefixWord ++ tailWord_719553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719588 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_719588 : Nat := 118140960795 + 719588 * 2 ^ 59
def prefixEnd_719588 : Nat := 4983230072969 + 3 ^ 40 * 719588 * 2
def baseEnd_719588 : Nat := 328439570851231859858383

theorem tailTrace_719588 : CollatzResearch.WordTrace tailWord_719588 prefixEnd_719588 328439570851231859858383 := by
  unfold tailWord_719588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122765258531523345635709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17497020344708697794180945 13122765258531523345635709)
  ·
    refine ⟨4921036971949321254613391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13122765258531523345635709 4921036971949321254613391)
    ·
      refine ⟨7381555457923981881920087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4921036971949321254613391 7381555457923981881920087)
      ·
        refine ⟨11072333186885972822880131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7381555457923981881920087 11072333186885972822880131)
        ·
          refine ⟨16608499780328959234320197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11072333186885972822880131 16608499780328959234320197)
          ·
            refine ⟨3114093708811679856435037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16608499780328959234320197 3114093708811679856435037)
            ·
              refine ⟨1167785140804379946163139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3114093708811679856435037 1167785140804379946163139)
              ·
                refine ⟨1751677711206569919244709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167785140804379946163139 1751677711206569919244709)
                ·
                  refine ⟨328439570851231859858383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1751677711206569919244709 328439570851231859858383)
                  ·
                    rfl

theorem cell20_719588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_719588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719588 prefixEnd_719588 := by exact prefixLift 719588
  have htrace : WordTrace (prefixWord ++ tailWord_719588) baseStart_719588 baseEnd_719588 := by
    simpa [prefixWord, tailWord_719588, baseEnd_719588] using wordTrace_append hprefix tailTrace_719588
  have hstable : (prefixWord ++ tailWord_719588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719588).length < 2 ^ (prefixWord ++ tailWord_719588).sum := by decide
  have hdescent : baseEnd_719588 < baseStart_719588 := by decide
  rcases family_descends (prefixWord ++ tailWord_719588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719598 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_719598 : Nat := 118140960795 + 719598 * 2 ^ 59
def prefixEnd_719598 : Nat := 4983230072969 + 3 ^ 40 * 719598 * 2
def baseEnd_719598 : Nat := 328444135123716269525009

theorem tailTrace_719598 : CollatzResearch.WordTrace tailWord_719598 prefixEnd_719598 328444135123716269525009 := by
  unfold tailWord_719598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280736905878352299891931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17497263498017878932756965 3280736905878352299891931)
  ·
    refine ⟨4921105358817528449837897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3280736905878352299891931 4921105358817528449837897)
    ·
      refine ⟨3690829019113146337378423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4921105358817528449837897 3690829019113146337378423)
      ·
        refine ⟨5536243528669719506067635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3690829019113146337378423 5536243528669719506067635)
        ·
          refine ⟨8304365293004579259101453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5536243528669719506067635 8304365293004579259101453)
          ·
            refine ⟨3114136984876717222163045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8304365293004579259101453 3114136984876717222163045)
            ·
              refine ⟨583900684664384479155571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3114136984876717222163045 583900684664384479155571)
              ·
                refine ⟨875851026996576718733357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583900684664384479155571 875851026996576718733357)
                ·
                  refine ⟨328444135123716269525009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 875851026996576718733357 328444135123716269525009)
                  ·
                    rfl

theorem cell20_719598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_719598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719598 prefixEnd_719598 := by exact prefixLift 719598
  have htrace : WordTrace (prefixWord ++ tailWord_719598) baseStart_719598 baseEnd_719598 := by
    simpa [prefixWord, tailWord_719598, baseEnd_719598] using wordTrace_append hprefix tailTrace_719598
  have hstable : (prefixWord ++ tailWord_719598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719598).length < 2 ^ (prefixWord ++ tailWord_719598).sum := by decide
  have hdescent : baseEnd_719598 < baseStart_719598 := by decide
  rcases family_descends (prefixWord ++ tailWord_719598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719609 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 4]
def baseStart_719609 : Nat := 118140960795 + 719609 * 2 ^ 59
def prefixEnd_719609 : Nat := 4983230072969 + 3 ^ 40 * 719609 * 2
def baseEnd_719609 : Nat := 328449155823449120158297

theorem tailTrace_719609 : CollatzResearch.WordTrace tailWord_719609 prefixEnd_719609 328449155823449120158297 := by
  unfold tailWord_719609
  simp only [CollatzResearch.WordTrace]
  refine ⟨26246296449986967277785881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17497530966657978185190587 26246296449986967277785881)
  ·
    refine ⟨19684722337490225458339411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26246296449986967277785881 19684722337490225458339411)
    ·
      refine ⟨29527083506235338187509117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19684722337490225458339411 29527083506235338187509117)
      ·
        refine ⟨11072656314838251820315919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29527083506235338187509117 11072656314838251820315919)
        ·
          refine ⟨16608984472257377730473879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11072656314838251820315919 16608984472257377730473879)
          ·
            refine ⟨24913476708386066595710819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16608984472257377730473879 24913476708386066595710819)
            ·
              refine ⟨37370215062579099893566229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24913476708386066595710819 37370215062579099893566229)
              ·
                refine ⟨1751728831058395307510917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37370215062579099893566229 1751728831058395307510917)
                ·
                  refine ⟨328449155823449120158297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1751728831058395307510917 328449155823449120158297)
                  ·
                    rfl

theorem cell20_719609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_719609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719609 prefixEnd_719609 := by exact prefixLift 719609
  have htrace : WordTrace (prefixWord ++ tailWord_719609) baseStart_719609 baseEnd_719609 := by
    simpa [prefixWord, tailWord_719609, baseEnd_719609] using wordTrace_append hprefix tailTrace_719609
  have hstable : (prefixWord ++ tailWord_719609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719609).length < 2 ^ (prefixWord ++ tailWord_719609).sum := by decide
  have hdescent : baseEnd_719609 < baseStart_719609 := by decide
  rcases family_descends (prefixWord ++ tailWord_719609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719639 : List Nat := [1, 1, 3, 4, 3, 2, 2, 2, 2]
def baseStart_719639 : Nat := 118140960795 + 719639 * 2 ^ 59
def prefixEnd_719639 : Nat := 4983230072969 + 3 ^ 40 * 719639 * 2
def baseEnd_719639 : Nat := 328462848640902349158175

theorem tailTrace_719639 : CollatzResearch.WordTrace tailWord_719639 prefixEnd_719639 328462848640902349158175 := by
  unfold tailWord_719639
  simp only [CollatzResearch.WordTrace]
  refine ⟨26247390639878282401377971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17498260426585521600918647 26247390639878282401377971)
  ·
    refine ⟨39371085959817423602066957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26247390639878282401377971 39371085959817423602066957)
    ·
      refine ⟨14764157234931533850775109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39371085959817423602066957 14764157234931533850775109)
      ·
        refine ⟨2768279481549662597020333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14764157234931533850775109 2768279481549662597020333)
        ·
          refine ⟨1038104805581123473882625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2768279481549662597020333 1038104805581123473882625)
          ·
            refine ⟨778578604185842605411969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1038104805581123473882625 778578604185842605411969)
            ·
              refine ⟨583933953139381954058977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778578604185842605411969 583933953139381954058977)
              ·
                refine ⟨437950464854536465544233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583933953139381954058977 437950464854536465544233)
                ·
                  refine ⟨328462848640902349158175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437950464854536465544233 328462848640902349158175)
                  ·
                    rfl

theorem cell20_719639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 2].length) (baseStart_719639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719639 prefixEnd_719639 := by exact prefixLift 719639
  have htrace : WordTrace (prefixWord ++ tailWord_719639) baseStart_719639 baseEnd_719639 := by
    simpa [prefixWord, tailWord_719639, baseEnd_719639] using wordTrace_append hprefix tailTrace_719639
  have hstable : (prefixWord ++ tailWord_719639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719639).length < 2 ^ (prefixWord ++ tailWord_719639).sum := by decide
  have hdescent : baseEnd_719639 < baseStart_719639 := by decide
  rcases family_descends (prefixWord ++ tailWord_719639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719650 : List Nat := [3, 3, 1, 1, 2, 4, 1, 5]
def baseStart_719650 : Nat := 118140960795 + 719650 * 2 ^ 59
def prefixEnd_719650 : Nat := 4983230072969 + 3 ^ 40 * 719650 * 2
def baseEnd_719650 : Nat := 109489289780211733263821

theorem tailTrace_719650 : CollatzResearch.WordTrace tailWord_719650 prefixEnd_719650 109489289780211733263821 := by
  unfold tailWord_719650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6561947960709607820007101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17498527895225620853352269 6561947960709607820007101)
  ·
    refine ⟨2460730485266102932502663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6561947960709607820007101 2460730485266102932502663)
    ·
      refine ⟨3691095727899154398753995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2460730485266102932502663 3691095727899154398753995)
      ·
        refine ⟨5536643591848731598130993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3691095727899154398753995 5536643591848731598130993)
        ·
          refine ⟨4152482693886548698598245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5536643591848731598130993 4152482693886548698598245)
          ·
            refine ⟨778590505103727880987171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4152482693886548698598245 778590505103727880987171)
            ·
              refine ⟨1167885757655591821480757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778590505103727880987171 1167885757655591821480757)
              ·
                refine ⟨109489289780211733263821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1167885757655591821480757 109489289780211733263821)
                ·
                  rfl

theorem cell20_719650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_719650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719650 prefixEnd_719650 := by exact prefixLift 719650
  have htrace : WordTrace (prefixWord ++ tailWord_719650) baseStart_719650 baseEnd_719650 := by
    simpa [prefixWord, tailWord_719650, baseEnd_719650] using wordTrace_append hprefix tailTrace_719650
  have hstable : (prefixWord ++ tailWord_719650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719650).length < 2 ^ (prefixWord ++ tailWord_719650).sum := by decide
  have hdescent : baseEnd_719650 < baseStart_719650 := by decide
  rcases family_descends (prefixWord ++ tailWord_719650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719671 : List Nat := [1, 1, 3, 1, 2, 1, 7, 4]
def baseStart_719671 : Nat := 118140960795 + 719671 * 2 ^ 59
def prefixEnd_719671 : Nat := 4983230072969 + 3 ^ 40 * 719671 * 2
def baseEnd_719671 : Nat := 109492484770950820030459

theorem tailTrace_719671 : CollatzResearch.WordTrace tailWord_719671 prefixEnd_719671 109492484770950820030459 := by
  unfold tailWord_719671
  simp only [CollatzResearch.WordTrace]
  refine ⟨26248557775762351866542867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17499038517174901244361911 26248557775762351866542867)
  ·
    refine ⟨39372836663643527799814301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26248557775762351866542867 39372836663643527799814301)
    ·
      refine ⟨14764813748866322924930363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39372836663643527799814301 14764813748866322924930363)
      ·
        refine ⟨22147220623299484387395545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14764813748866322924930363 22147220623299484387395545)
        ·
          refine ⟨16610415467474613290546659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22147220623299484387395545 16610415467474613290546659)
          ·
            refine ⟨24915623201211919935819989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16610415467474613290546659 24915623201211919935819989)
            ·
              refine ⟨583959918778404373495781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24915623201211919935819989 583959918778404373495781)
              ·
                refine ⟨109492484770950820030459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583959918778404373495781 109492484770950820030459)
                ·
                  rfl

theorem cell20_719671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 4].length) (baseStart_719671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719671 prefixEnd_719671 := by exact prefixLift 719671
  have htrace : WordTrace (prefixWord ++ tailWord_719671) baseStart_719671 baseEnd_719671 := by
    simpa [prefixWord, tailWord_719671, baseEnd_719671] using wordTrace_append hprefix tailTrace_719671
  have hstable : (prefixWord ++ tailWord_719671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719671).length < 2 ^ (prefixWord ++ tailWord_719671).sum := by decide
  have hdescent : baseEnd_719671 < baseStart_719671 := by decide
  rcases family_descends (prefixWord ++ tailWord_719671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719723 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_719723 : Nat := 118140960795 + 719723 * 2 ^ 59
def prefixEnd_719723 : Nat := 4983230072969 + 3 ^ 40 * 719723 * 2
def baseEnd_719723 : Nat := 328501188529771390357831

theorem tailTrace_719723 : CollatzResearch.WordTrace tailWord_719723 prefixEnd_719723 328501188529771390357831 := by
  unfold tailWord_719723
  simp only [CollatzResearch.WordTrace]
  refine ⟨26250454371573964747435823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17500302914382643164957215 26250454371573964747435823)
  ·
    refine ⟨39375681557360947121153735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26250454371573964747435823 39375681557360947121153735)
    ·
      refine ⟨59063522336041420681730603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39375681557360947121153735 59063522336041420681730603)
      ·
        refine ⟨88595283504062131022595905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59063522336041420681730603 88595283504062131022595905)
        ·
          refine ⟨66446462628046598266946929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88595283504062131022595905 66446462628046598266946929)
          ·
            refine ⟨49834846971034948700210197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66446462628046598266946929 49834846971034948700210197)
            ·
              refine ⟨2336008451767263220322353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49834846971034948700210197 2336008451767263220322353)
              ·
                refine ⟨1752006338825447415241765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336008451767263220322353 1752006338825447415241765)
                ·
                  refine ⟨328501188529771390357831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1752006338825447415241765 328501188529771390357831)
                  ·
                    rfl

theorem cell20_719723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_719723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719723 prefixEnd_719723 := by exact prefixLift 719723
  have htrace : WordTrace (prefixWord ++ tailWord_719723) baseStart_719723 baseEnd_719723 := by
    simpa [prefixWord, tailWord_719723, baseEnd_719723] using wordTrace_append hprefix tailTrace_719723
  have hstable : (prefixWord ++ tailWord_719723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719723).length < 2 ^ (prefixWord ++ tailWord_719723).sum := by decide
  have hdescent : baseEnd_719723 < baseStart_719723 := by decide
  rcases family_descends (prefixWord ++ tailWord_719723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719726 : List Nat := [4, 1, 2, 3, 2, 1, 1, 6]
def baseStart_719726 : Nat := 118140960795 + 719726 * 2 ^ 59
def prefixEnd_719726 : Nat := 4983230072969 + 3 ^ 40 * 719726 * 2
def baseEnd_719726 : Nat := 109500852603838904419273

theorem tailTrace_719726 : CollatzResearch.WordTrace tailWord_719726 prefixEnd_719726 109500852603838904419273 := by
  unfold tailWord_719726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281320473820387032474379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17500375860375397506530021 3281320473820387032474379)
  ·
    refine ⟨4921980710730580548711569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3281320473820387032474379 4921980710730580548711569)
    ·
      refine ⟨3691485533047935411533677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4921980710730580548711569 3691485533047935411533677)
      ·
        refine ⟨1384307074892975779325129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3691485533047935411533677 1384307074892975779325129)
        ·
          refine ⟨1038230306169731834493847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384307074892975779325129 1038230306169731834493847)
          ·
            refine ⟨1557345459254597751740771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038230306169731834493847 1557345459254597751740771)
            ·
              refine ⟨2336018188881896627611157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557345459254597751740771 2336018188881896627611157)
              ·
                refine ⟨109500852603838904419273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2336018188881896627611157 109500852603838904419273)
                ·
                  rfl

theorem cell20_719726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_719726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719726 prefixEnd_719726 := by exact prefixLift 719726
  have htrace : WordTrace (prefixWord ++ tailWord_719726) baseStart_719726 baseEnd_719726 := by
    simpa [prefixWord, tailWord_719726, baseEnd_719726] using wordTrace_append hprefix tailTrace_719726
  have hstable : (prefixWord ++ tailWord_719726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719726).length < 2 ^ (prefixWord ++ tailWord_719726).sum := by decide
  have hdescent : baseEnd_719726 < baseStart_719726 := by decide
  rcases family_descends (prefixWord ++ tailWord_719726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719798 : List Nat := [5, 1, 4, 1, 2, 7]
def baseStart_719798 : Nat := 118140960795 + 719798 * 2 ^ 59
def prefixEnd_719798 : Nat := 4983230072969 + 3 ^ 40 * 719798 * 2
def baseEnd_719798 : Nat := 12167978539755720846575

theorem tailTrace_719798 : CollatzResearch.WordTrace tailWord_719798 prefixEnd_719798 12167978539755720846575 := by
  unfold tailWord_719798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640824365393890784776003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17502126564201501704277365 1640824365393890784776003)
  ·
    refine ⟨2461236548090836177164005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1640824365393890784776003 2461236548090836177164005)
    ·
      refine ⟨461481852767031783218251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2461236548090836177164005 461481852767031783218251)
      ·
        refine ⟨692222779150547674827377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461481852767031783218251 692222779150547674827377)
        ·
          refine ⟨519167084362910756120533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692222779150547674827377 519167084362910756120533)
          ·
            refine ⟨12167978539755720846575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 519167084362910756120533 12167978539755720846575)
            ·
              rfl

theorem cell20_719798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 7].length) (baseStart_719798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719798 prefixEnd_719798 := by exact prefixLift 719798
  have htrace : WordTrace (prefixWord ++ tailWord_719798) baseStart_719798 baseEnd_719798 := by
    simpa [prefixWord, tailWord_719798, baseEnd_719798] using wordTrace_append hprefix tailTrace_719798
  have hstable : (prefixWord ++ tailWord_719798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719798).length < 2 ^ (prefixWord ++ tailWord_719798).sum := by decide
  have hdescent : baseEnd_719798 < baseStart_719798 := by decide
  rcases family_descends (prefixWord ++ tailWord_719798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719813 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_719813 : Nat := 118140960795 + 719813 * 2 ^ 59
def prefixEnd_719813 : Nat := 4983230072969 + 3 ^ 40 * 719813 * 2
def baseEnd_719813 : Nat := 328542266982131077357463

theorem tailTrace_719813 : CollatzResearch.WordTrace tailWord_719813 prefixEnd_719813 328542266982131077357463 := by
  unfold tailWord_719813
  simp only [CollatzResearch.WordTrace]
  refine ⟨26253736941247910118212093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17502491294165273412141395 26253736941247910118212093)
  ·
    refine ⟨9845151352967966294329535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26253736941247910118212093 9845151352967966294329535)
    ·
      refine ⟨14767727029451949441494303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845151352967966294329535 14767727029451949441494303)
      ·
        refine ⟨22151590544177924162241455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14767727029451949441494303 22151590544177924162241455)
        ·
          refine ⟨33227385816266886243362183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22151590544177924162241455 33227385816266886243362183)
          ·
            refine ⟨49841078724400329365043275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33227385816266886243362183 49841078724400329365043275)
            ·
              refine ⟨74761618086600494047564913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49841078724400329365043275 74761618086600494047564913)
              ·
                refine ⟨56071213564950370535673685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74761618086600494047564913 56071213564950370535673685)
                ·
                  refine ⟨328542266982131077357463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56071213564950370535673685 328542266982131077357463)
                  ·
                    rfl

theorem cell20_719813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_719813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719813 prefixEnd_719813 := by exact prefixLift 719813
  have htrace : WordTrace (prefixWord ++ tailWord_719813) baseStart_719813 baseEnd_719813 := by
    simpa [prefixWord, tailWord_719813, baseEnd_719813] using wordTrace_append hprefix tailTrace_719813
  have hstable : (prefixWord ++ tailWord_719813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719813).length < 2 ^ (prefixWord ++ tailWord_719813).sum := by decide
  have hdescent : baseEnd_719813 < baseStart_719813 := by decide
  rcases family_descends (prefixWord ++ tailWord_719813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719823 : List Nat := [1, 1, 2, 1, 1, 8, 1, 5]
def baseStart_719823 : Nat := 118140960795 + 719823 * 2 ^ 59
def prefixEnd_719823 : Nat := 4983230072969 + 3 ^ 40 * 719823 * 2
def baseEnd_719823 : Nat := 109515610418205162341363

theorem tailTrace_719823 : CollatzResearch.WordTrace tailWord_719823 prefixEnd_719823 109515610418205162341363 := by
  unfold tailWord_719823
  simp only [CollatzResearch.WordTrace]
  refine ⟨26254101671211681826076123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17502734447474454550717415 26254101671211681826076123)
  ·
    refine ⟨39381152506817522739114185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26254101671211681826076123 39381152506817522739114185)
    ·
      refine ⟨29535864380113142054335639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39381152506817522739114185 29535864380113142054335639)
      ·
        refine ⟨44303796570169713081503459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29535864380113142054335639 44303796570169713081503459)
        ·
          refine ⟨66455694855254569622255189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44303796570169713081503459 66455694855254569622255189)
          ·
            refine ⟨778777674085014487760803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 66455694855254569622255189 778777674085014487760803)
            ·
              refine ⟨1168166511127521731641205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778777674085014487760803 1168166511127521731641205)
              ·
                refine ⟨109515610418205162341363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1168166511127521731641205 109515610418205162341363)
                ·
                  rfl

theorem cell20_719823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 5].length) (baseStart_719823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719823 prefixEnd_719823 := by exact prefixLift 719823
  have htrace : WordTrace (prefixWord ++ tailWord_719823) baseStart_719823 baseEnd_719823 := by
    simpa [prefixWord, tailWord_719823, baseEnd_719823] using wordTrace_append hprefix tailTrace_719823
  have hstable : (prefixWord ++ tailWord_719823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719823).length < 2 ^ (prefixWord ++ tailWord_719823).sum := by decide
  have hdescent : baseEnd_719823 < baseStart_719823 := by decide
  rcases family_descends (prefixWord ++ tailWord_719823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719860 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 5]
def baseStart_719860 : Nat := 118140960795 + 719860 * 2 ^ 59
def prefixEnd_719860 : Nat := 4983230072969 + 3 ^ 40 * 719860 * 2
def baseEnd_719860 : Nat := 328563719062807802790605

theorem tailTrace_719860 : CollatzResearch.WordTrace tailWord_719860 prefixEnd_719860 328563719062807802790605 := by
  unfold tailWord_719860
  simp only [CollatzResearch.WordTrace]
  refine ⟨13127725586038818572586517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17503634114718424763448689 13127725586038818572586517)
  ·
    refine ⟨615362136845569620589993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13127725586038818572586517 615362136845569620589993)
    ·
      refine ⟨461521602634177215442495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 615362136845569620589993 461521602634177215442495)
      ·
        refine ⟨692282403951265823163743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461521602634177215442495 692282403951265823163743)
        ·
          refine ⟨1038423605926898734745615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692282403951265823163743 1038423605926898734745615)
          ·
            refine ⟨1557635408890348102118423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038423605926898734745615 1557635408890348102118423)
            ·
              refine ⟨2336453113335522153177635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557635408890348102118423 2336453113335522153177635)
              ·
                refine ⟨3504679670003283229766453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336453113335522153177635 3504679670003283229766453)
                ·
                  refine ⟨328563719062807802790605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3504679670003283229766453 328563719062807802790605)
                  ·
                    rfl

theorem cell20_719860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_719860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719860 prefixEnd_719860 := by exact prefixLift 719860
  have htrace : WordTrace (prefixWord ++ tailWord_719860) baseStart_719860 baseEnd_719860 := by
    simpa [prefixWord, tailWord_719860, baseEnd_719860] using wordTrace_append hprefix tailTrace_719860
  have hstable : (prefixWord ++ tailWord_719860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719860).length < 2 ^ (prefixWord ++ tailWord_719860).sum := by decide
  have hdescent : baseEnd_719860 < baseStart_719860 := by decide
  rcases family_descends (prefixWord ++ tailWord_719860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719868 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_719868 : Nat := 118140960795 + 719868 * 2 ^ 59
def prefixEnd_719868 : Nat := 4983230072969 + 3 ^ 40 * 719868 * 2
def baseEnd_719868 : Nat := 328567370480795330523905

theorem tailTrace_719868 : CollatzResearch.WordTrace tailWord_719868 prefixEnd_719868 328567370480795330523905 := by
  unfold tailWord_719868
  simp only [CollatzResearch.WordTrace]
  refine ⟨13127871478024327255732129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17503828637365769674309505 13127871478024327255732129)
  ·
    refine ⟨9845903608518245441799097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13127871478024327255732129 9845903608518245441799097)
    ·
      refine ⟨7384427706388684081349323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9845903608518245441799097 7384427706388684081349323)
      ·
        refine ⟨11076641559583026122023985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7384427706388684081349323 11076641559583026122023985)
        ·
          refine ⟨8307481169687269591517989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11076641559583026122023985 8307481169687269591517989)
          ·
            refine ⟨1557652719316363048409623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8307481169687269591517989 1557652719316363048409623)
            ·
              refine ⟨2336479078974544572614435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557652719316363048409623 2336479078974544572614435)
              ·
                refine ⟨3504718618461816858921653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336479078974544572614435 3504718618461816858921653)
                ·
                  refine ⟨328567370480795330523905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3504718618461816858921653 328567370480795330523905)
                  ·
                    rfl

theorem cell20_719868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_719868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719868 prefixEnd_719868 := by exact prefixLift 719868
  have htrace : WordTrace (prefixWord ++ tailWord_719868) baseStart_719868 baseEnd_719868 := by
    simpa [prefixWord, tailWord_719868, baseEnd_719868] using wordTrace_append hprefix tailTrace_719868
  have hstable : (prefixWord ++ tailWord_719868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719868).length < 2 ^ (prefixWord ++ tailWord_719868).sum := by decide
  have hdescent : baseEnd_719868 < baseStart_719868 := by decide
  rcases family_descends (prefixWord ++ tailWord_719868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719906 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_719906 : Nat := 118140960795 + 719906 * 2 ^ 59
def prefixEnd_719906 : Nat := 4983230072969 + 3 ^ 40 * 719906 * 2
def baseEnd_719906 : Nat := 328584714716236087257083

theorem tailTrace_719906 : CollatzResearch.WordTrace tailWord_719906 prefixEnd_719906 328584714716236087257083 := by
  unfold tailWord_719906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6564282232477746750336893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17504752619940658000898381 6564282232477746750336893)
  ·
    refine ⟨2461605837179155031376335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6564282232477746750336893 2461605837179155031376335)
    ·
      refine ⟨3692408755768732547064503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461605837179155031376335 3692408755768732547064503)
      ·
        refine ⟨5538613133653098820596755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3692408755768732547064503 5538613133653098820596755)
        ·
          refine ⟨8307919700479648230895133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5538613133653098820596755 8307919700479648230895133)
          ·
            refine ⟨3115469887679868086585675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8307919700479648230895133 3115469887679868086585675)
            ·
              refine ⟨4673204831519802129878513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115469887679868086585675 4673204831519802129878513)
              ·
                refine ⟨3504903623639851597408885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4673204831519802129878513 3504903623639851597408885)
                ·
                  refine ⟨328584714716236087257083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3504903623639851597408885 328584714716236087257083)
                  ·
                    rfl

theorem cell20_719906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_719906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719906 prefixEnd_719906 := by exact prefixLift 719906
  have htrace : WordTrace (prefixWord ++ tailWord_719906) baseStart_719906 baseEnd_719906 := by
    simpa [prefixWord, tailWord_719906, baseEnd_719906] using wordTrace_append hprefix tailTrace_719906
  have hstable : (prefixWord ++ tailWord_719906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719906).length < 2 ^ (prefixWord ++ tailWord_719906).sum := by decide
  have hdescent : baseEnd_719906 < baseStart_719906 := by decide
  rcases family_descends (prefixWord ++ tailWord_719906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719930 : List Nat := [3, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_719930 : Nat := 118140960795 + 719930 * 2 ^ 59
def prefixEnd_719930 : Nat := 4983230072969 + 3 ^ 40 * 719930 * 2
def baseEnd_719930 : Nat := 328595668970198670456985

theorem tailTrace_719930 : CollatzResearch.WordTrace tailWord_719930 prefixEnd_719930 328595668970198670456985 := by
  unfold tailWord_719930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6564501070456009775055311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17505336187882692733480829 6564501070456009775055311)
  ·
    refine ⟨9846751605684014662582967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6564501070456009775055311 9846751605684014662582967)
    ·
      refine ⟨14770127408526021993874451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9846751605684014662582967 14770127408526021993874451)
      ·
        refine ⟨22155191112789032990811677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14770127408526021993874451 22155191112789032990811677)
        ·
          refine ⟨8308196667295887371554379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22155191112789032990811677 8308196667295887371554379)
          ·
            refine ⟨12462295000943831057331569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8308196667295887371554379 12462295000943831057331569)
            ·
              refine ⟨9346721250707873292998677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12462295000943831057331569 9346721250707873292998677)
              ·
                refine ⟨438127558626931560609313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9346721250707873292998677 438127558626931560609313)
                ·
                  refine ⟨328595668970198670456985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438127558626931560609313 328595668970198670456985)
                  ·
                    rfl

theorem cell20_719930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_719930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719930 prefixEnd_719930 := by exact prefixLift 719930
  have htrace : WordTrace (prefixWord ++ tailWord_719930) baseStart_719930 baseEnd_719930 := by
    simpa [prefixWord, tailWord_719930, baseEnd_719930] using wordTrace_append hprefix tailTrace_719930
  have hstable : (prefixWord ++ tailWord_719930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719930).length < 2 ^ (prefixWord ++ tailWord_719930).sum := by decide
  have hdescent : baseEnd_719930 < baseStart_719930 := by decide
  rcases family_descends (prefixWord ++ tailWord_719930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719944 : List Nat := [2, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_719944 : Nat := 118140960795 + 719944 * 2 ^ 59
def prefixEnd_719944 : Nat := 4983230072969 + 3 ^ 40 * 719944 * 2
def baseEnd_719944 : Nat := 328602058951676843990261

theorem tailTrace_719944 : CollatzResearch.WordTrace tailWord_719944 prefixEnd_719944 328602058951676843990261 := by
  unfold tailWord_719944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13129257451886659745615443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17505676602515546327487257 13129257451886659745615443)
  ·
    refine ⟨19693886177829989618423165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13129257451886659745615443 19693886177829989618423165)
    ·
      refine ⟨7385207316686246106908687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19693886177829989618423165 7385207316686246106908687)
      ·
        refine ⟨11077810975029369160363031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385207316686246106908687 11077810975029369160363031)
        ·
          refine ⟨16616716462544053740544547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11077810975029369160363031 16616716462544053740544547)
          ·
            refine ⟨24925074693816080610816821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16616716462544053740544547 24925074693816080610816821)
            ·
              refine ⟨2336725752545257557264077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24925074693816080610816821 2336725752545257557264077)
              ·
                refine ⟨876272157204471583974029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2336725752545257557264077 876272157204471583974029)
                ·
                  refine ⟨328602058951676843990261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876272157204471583974029 328602058951676843990261)
                  ·
                    rfl

theorem cell20_719944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_719944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719944 prefixEnd_719944 := by exact prefixLift 719944
  have htrace : WordTrace (prefixWord ++ tailWord_719944) baseStart_719944 baseEnd_719944 := by
    simpa [prefixWord, tailWord_719944, baseEnd_719944] using wordTrace_append hprefix tailTrace_719944
  have hstable : (prefixWord ++ tailWord_719944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719944).length < 2 ^ (prefixWord ++ tailWord_719944).sum := by decide
  have hdescent : baseEnd_719944 < baseStart_719944 := by decide
  rcases family_descends (prefixWord ++ tailWord_719944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719968 : List Nat := [2, 1, 1, 3, 2, 2, 2, 5, 2]
def baseStart_719968 : Nat := 118140960795 + 719968 * 2 ^ 59
def prefixEnd_719968 : Nat := 4983230072969 + 3 ^ 40 * 719968 * 2
def baseEnd_719968 : Nat := 328613013205639427190163

theorem tailTrace_719968 : CollatzResearch.WordTrace tailWord_719968 prefixEnd_719968 328613013205639427190163 := by
  unfold tailWord_719968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13129695127843185795052279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17506260170457581060069705 13129695127843185795052279)
  ·
    refine ⟨19694542691764778692578419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13129695127843185795052279 19694542691764778692578419)
    ·
      refine ⟨29541814037647168038867629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19694542691764778692578419 29541814037647168038867629)
      ·
        refine ⟨11078180264117688014575361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29541814037647168038867629 11078180264117688014575361)
        ·
          refine ⟨8308635198088266010931521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11078180264117688014575361 8308635198088266010931521)
          ·
            refine ⟨6231476398566199508198641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8308635198088266010931521 6231476398566199508198641)
            ·
              refine ⟨4673607298924649631148981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6231476398566199508198641 4673607298924649631148981)
              ·
                refine ⟨438150684274185902920217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4673607298924649631148981 438150684274185902920217)
                ·
                  refine ⟨328613013205639427190163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438150684274185902920217 328613013205639427190163)
                  ·
                    rfl

theorem cell20_719968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_719968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_719968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_719968 prefixEnd_719968 := by exact prefixLift 719968
  have htrace : WordTrace (prefixWord ++ tailWord_719968) baseStart_719968 baseEnd_719968 := by
    simpa [prefixWord, tailWord_719968, baseEnd_719968] using wordTrace_append hprefix tailTrace_719968
  have hstable : (prefixWord ++ tailWord_719968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719968).length < 2 ^ (prefixWord ++ tailWord_719968).sum := by decide
  have hdescent : baseEnd_719968 < baseStart_719968 := by decide
  rcases family_descends (prefixWord ++ tailWord_719968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720023 : List Nat := [1, 1, 3, 3, 3, 2, 2, 3, 2]
def baseStart_720023 : Nat := 118140960795 + 720023 * 2 ^ 59
def prefixEnd_720023 : Nat := 4983230072969 + 3 ^ 40 * 720023 * 2
def baseEnd_720023 : Nat := 328638116704303680356605

theorem tailTrace_720023 : CollatzResearch.WordTrace tailWord_720023 prefixEnd_720023 328638116704303680356605 := by
  unfold tailWord_720023
  simp only [CollatzResearch.WordTrace]
  refine ⟨26261396270487115983356723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17507597513658077322237815 26261396270487115983356723)
  ·
    refine ⟨39392094405730673975035085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26261396270487115983356723 39392094405730673975035085)
    ·
      refine ⟨14772035402149002740638157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39392094405730673975035085 14772035402149002740638157)
      ·
        refine ⟨5539513275805876027739309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14772035402149002740638157 5539513275805876027739309)
        ·
          refine ⟨2077317478427203510402241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5539513275805876027739309 2077317478427203510402241)
          ·
            refine ⟨1557988108820402632801681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2077317478427203510402241 1557988108820402632801681)
            ·
              refine ⟨1168491081615301974601261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557988108820402632801681 1168491081615301974601261)
              ·
                refine ⟨438184155605738240475473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1168491081615301974601261 438184155605738240475473)
                ·
                  refine ⟨328638116704303680356605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438184155605738240475473 328638116704303680356605)
                  ·
                    rfl

theorem cell20_720023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 3, 2].length) (baseStart_720023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720023 prefixEnd_720023 := by exact prefixLift 720023
  have htrace : WordTrace (prefixWord ++ tailWord_720023) baseStart_720023 baseEnd_720023 := by
    simpa [prefixWord, tailWord_720023, baseEnd_720023] using wordTrace_append hprefix tailTrace_720023
  have hstable : (prefixWord ++ tailWord_720023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720023).length < 2 ^ (prefixWord ++ tailWord_720023).sum := by decide
  have hdescent : baseEnd_720023 < baseStart_720023 := by decide
  rcases family_descends (prefixWord ++ tailWord_720023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720037 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 3]
def baseStart_720037 : Nat := 118140960795 + 720037 * 2 ^ 59
def prefixEnd_720037 : Nat := 4983230072969 + 3 ^ 40 * 720037 * 2
def baseEnd_720037 : Nat := 328644506685781853889881

theorem tailTrace_720037 : CollatzResearch.WordTrace tailWord_720037 prefixEnd_720037 328644506685781853889881 := by
  unfold tailWord_720037
  simp only [CollatzResearch.WordTrace]
  refine ⟨26261906892436396374366365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17507937928290930916244243 26261906892436396374366365)
  ·
    refine ⟨9848215084663648640387387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26261906892436396374366365 9848215084663648640387387)
    ·
      refine ⟨14772322626995472960581081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9848215084663648640387387 14772322626995472960581081)
      ·
        refine ⟨11079241970246604720435811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14772322626995472960581081 11079241970246604720435811)
        ·
          refine ⟨16618862955369907080653717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11079241970246604720435811 16618862955369907080653717)
          ·
            refine ⟨779009201032964394405643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16618862955369907080653717 779009201032964394405643)
            ·
              refine ⟨1168513801549446591608465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779009201032964394405643 1168513801549446591608465)
              ·
                refine ⟨876385351162084943706349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168513801549446591608465 876385351162084943706349)
                ·
                  refine ⟨328644506685781853889881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876385351162084943706349 328644506685781853889881)
                  ·
                    rfl

theorem cell20_720037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_720037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720037 prefixEnd_720037 := by exact prefixLift 720037
  have htrace : WordTrace (prefixWord ++ tailWord_720037) baseStart_720037 baseEnd_720037 := by
    simpa [prefixWord, tailWord_720037, baseEnd_720037] using wordTrace_append hprefix tailTrace_720037
  have hstable : (prefixWord ++ tailWord_720037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720037).length < 2 ^ (prefixWord ++ tailWord_720037).sum := by decide
  have hdescent : baseEnd_720037 < baseStart_720037 := by decide
  rcases family_descends (prefixWord ++ tailWord_720037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720048 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_720048 : Nat := 118140960795 + 720048 * 2 ^ 59
def prefixEnd_720048 : Nat := 4983230072969 + 3 ^ 40 * 720048 * 2
def baseEnd_720048 : Nat := 328649527385514704523169

theorem tailTrace_720048 : CollatzResearch.WordTrace tailWord_720048 prefixEnd_720048 328649527385514704523169 := by
  unfold tailWord_720048
  simp only [CollatzResearch.WordTrace]
  refine ⟨13131154047698272626508399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17508205396931030168677865 13131154047698272626508399)
  ·
    refine ⟨19696731071547408939762599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13131154047698272626508399 19696731071547408939762599)
    ·
      refine ⟨29545096607321113409643899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19696731071547408939762599 29545096607321113409643899)
      ·
        refine ⟨44317644910981670114465849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29545096607321113409643899 44317644910981670114465849)
        ·
          refine ⟨33238233683236252585849387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44317644910981670114465849 33238233683236252585849387)
          ·
            refine ⟨49857350524854378878774081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33238233683236252585849387 49857350524854378878774081)
            ·
              refine ⟨37393012893640784159080561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49857350524854378878774081 37393012893640784159080561)
              ·
                refine ⟨28044759670230588119310421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37393012893640784159080561 28044759670230588119310421)
                ·
                  refine ⟨328649527385514704523169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28044759670230588119310421 328649527385514704523169)
                  ·
                    rfl

theorem cell20_720048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_720048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720048 prefixEnd_720048 := by exact prefixLift 720048
  have htrace : WordTrace (prefixWord ++ tailWord_720048) baseStart_720048 baseEnd_720048 := by
    simpa [prefixWord, tailWord_720048, baseEnd_720048] using wordTrace_append hprefix tailTrace_720048
  have hstable : (prefixWord ++ tailWord_720048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720048).length < 2 ^ (prefixWord ++ tailWord_720048).sum := by decide
  have hdescent : baseEnd_720048 < baseStart_720048 := by decide
  rcases family_descends (prefixWord ++ tailWord_720048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720078 : List Nat := [4, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_720078 : Nat := 118140960795 + 720078 * 2 ^ 59
def prefixEnd_720078 : Nat := 4983230072969 + 3 ^ 40 * 720078 * 2
def baseEnd_720078 : Nat := 328663220202967933523047

theorem tailTrace_720078 : CollatzResearch.WordTrace tailWord_720078 prefixEnd_720078 328663220202967933523047 := by
  unfold tailWord_720078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3282925285660982547076111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17508934856858573584405925 3282925285660982547076111)
  ·
    refine ⟨4924387928491473820614167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3282925285660982547076111 4924387928491473820614167)
    ·
      refine ⟨7386581892737210730921251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4924387928491473820614167 7386581892737210730921251)
      ·
        refine ⟨11079872839105816096381877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386581892737210730921251 11079872839105816096381877)
        ·
          refine ⟨1038738078666170259035801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11079872839105816096381877 1038738078666170259035801)
          ·
            refine ⟨779053558999627694276851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1038738078666170259035801 779053558999627694276851)
            ·
              refine ⟨1168580338499441541415277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779053558999627694276851 1168580338499441541415277)
              ·
                refine ⟨438217626937290578030729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1168580338499441541415277 438217626937290578030729)
                ·
                  refine ⟨328663220202967933523047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438217626937290578030729 328663220202967933523047)
                  ·
                    rfl

theorem cell20_720078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_720078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720078 prefixEnd_720078 := by exact prefixLift 720078
  have htrace : WordTrace (prefixWord ++ tailWord_720078) baseStart_720078 baseEnd_720078 := by
    simpa [prefixWord, tailWord_720078, baseEnd_720078] using wordTrace_append hprefix tailTrace_720078
  have hstable : (prefixWord ++ tailWord_720078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720078).length < 2 ^ (prefixWord ++ tailWord_720078).sum := by decide
  have hdescent : baseEnd_720078 < baseStart_720078 := by decide
  rcases family_descends (prefixWord ++ tailWord_720078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720110 : List Nat := [4, 1, 2, 1, 1, 1, 3, 7]
def baseStart_720110 : Nat := 118140960795 + 720110 * 2 ^ 59
def prefixEnd_720110 : Nat := 4983230072969 + 3 ^ 40 * 720110 * 2
def baseEnd_720110 : Nat := 109559275291639348152083

theorem tailTrace_720110 : CollatzResearch.WordTrace tailWord_720110 prefixEnd_720110 109559275291639348152083 := by
  unfold tailWord_720110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3283071177646491230221723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17509712947447953227849189 3283071177646491230221723)
  ·
    refine ⟨4924606766469736845332585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3283071177646491230221723 4924606766469736845332585)
    ·
      refine ⟨3693455074852302633999439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4924606766469736845332585 3693455074852302633999439)
      ·
        refine ⟨5540182612278453950999159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693455074852302633999439 5540182612278453950999159)
        ·
          refine ⟨8310273918417680926498739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540182612278453950999159 8310273918417680926498739)
          ·
            refine ⟨12465410877626521389748109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8310273918417680926498739 12465410877626521389748109)
            ·
              refine ⟨4674529079109945521155541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12465410877626521389748109 4674529079109945521155541)
              ·
                refine ⟨109559275291639348152083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4674529079109945521155541 109559275291639348152083)
                ·
                  rfl

theorem cell20_720110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_720110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720110 prefixEnd_720110 := by exact prefixLift 720110
  have htrace : WordTrace (prefixWord ++ tailWord_720110) baseStart_720110 baseEnd_720110 := by
    simpa [prefixWord, tailWord_720110, baseEnd_720110] using wordTrace_append hprefix tailTrace_720110
  have hstable : (prefixWord ++ tailWord_720110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720110).length < 2 ^ (prefixWord ++ tailWord_720110).sum := by decide
  have hdescent : baseEnd_720110 < baseStart_720110 := by decide
  rcases family_descends (prefixWord ++ tailWord_720110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720154 : List Nat := [3, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_720154 : Nat := 118140960795 + 720154 * 2 ^ 59
def prefixEnd_720154 : Nat := 4983230072969 + 3 ^ 40 * 720154 * 2
def baseEnd_720154 : Nat := 328697908673849446989403

theorem tailTrace_720154 : CollatzResearch.WordTrace tailWord_720154 prefixEnd_720154 328697908673849446989403 := by
  unfold tailWord_720154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566543558253131339093879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17510782822008350237583677 6566543558253131339093879)
  ·
    refine ⟨9849815337379697008640819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6566543558253131339093879 9849815337379697008640819)
    ·
      refine ⟨14774723006069545512961229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9849815337379697008640819 14774723006069545512961229)
      ·
        refine ⟨5540521127276079567360461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14774723006069545512961229 5540521127276079567360461)
        ·
          refine ⟨2077695422728529837760173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5540521127276079567360461 2077695422728529837760173)
          ·
            refine ⟨779135783523198689160065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2077695422728529837760173 779135783523198689160065)
            ·
              refine ⟨584351837642399016870049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779135783523198689160065 584351837642399016870049)
              ·
                refine ⟨438263878231799262652537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584351837642399016870049 438263878231799262652537)
                ·
                  refine ⟨328697908673849446989403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438263878231799262652537 328697908673849446989403)
                  ·
                    rfl

theorem cell20_720154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_720154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720154 prefixEnd_720154 := by exact prefixLift 720154
  have htrace : WordTrace (prefixWord ++ tailWord_720154) baseStart_720154 baseEnd_720154 := by
    simpa [prefixWord, tailWord_720154, baseEnd_720154] using wordTrace_append hprefix tailTrace_720154
  have hstable : (prefixWord ++ tailWord_720154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720154).length < 2 ^ (prefixWord ++ tailWord_720154).sum := by decide
  have hdescent : baseEnd_720154 < baseStart_720154 := by decide
  rcases family_descends (prefixWord ++ tailWord_720154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720165 : List Nat := [1, 3, 1, 2, 4, 3, 1, 5]
def baseStart_720165 : Nat := 118140960795 + 720165 * 2 ^ 59
def prefixEnd_720165 : Nat := 4983230072969 + 3 ^ 40 * 720165 * 2
def baseEnd_720165 : Nat := 109567643124527432540897

theorem tailTrace_720165 : CollatzResearch.WordTrace tailWord_720165 prefixEnd_720165 109567643124527432540897 := by
  unfold tailWord_720165
  simp only [CollatzResearch.WordTrace]
  refine ⟨26266575435972674235025949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17511050290648449490017299 26266575435972674235025949)
  ·
    refine ⟨9849965788489752838134731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26266575435972674235025949 9849965788489752838134731)
    ·
      refine ⟨14774948682734629257202097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9849965788489752838134731 14774948682734629257202097)
      ·
        refine ⟨11081211512050971942901573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14774948682734629257202097 11081211512050971942901573)
        ·
          refine ⟨2077727158509557239294045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11081211512050971942901573 2077727158509557239294045)
          ·
            refine ⟨779147684441083964735267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2077727158509557239294045 779147684441083964735267)
            ·
              refine ⟨1168721526661625947102901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779147684441083964735267 1168721526661625947102901)
              ·
                refine ⟨109567643124527432540897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1168721526661625947102901 109567643124527432540897)
                ·
                  rfl

theorem cell20_720165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 5].length) (baseStart_720165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720165 prefixEnd_720165 := by exact prefixLift 720165
  have htrace : WordTrace (prefixWord ++ tailWord_720165) baseStart_720165 baseEnd_720165 := by
    simpa [prefixWord, tailWord_720165, baseEnd_720165] using wordTrace_append hprefix tailTrace_720165
  have hstable : (prefixWord ++ tailWord_720165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720165).length < 2 ^ (prefixWord ++ tailWord_720165).sum := by decide
  have hdescent : baseEnd_720165 < baseStart_720165 := by decide
  rcases family_descends (prefixWord ++ tailWord_720165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720179 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_720179 : Nat := 118140960795 + 720179 * 2 ^ 59
def prefixEnd_720179 : Nat := 4983230072969 + 3 ^ 40 * 720179 * 2
def baseEnd_720179 : Nat := 328709319355060471155967

theorem tailTrace_720179 : CollatzResearch.WordTrace tailWord_720179 prefixEnd_720179 328709319355060471155967 := by
  unfold tailWord_720179
  simp only [CollatzResearch.WordTrace]
  refine ⟨26267086057921954626035591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17511390705281303084023727 26267086057921954626035591)
  ·
    refine ⟨39400629086882931939053387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26267086057921954626035591 39400629086882931939053387)
    ·
      refine ⟨59100943630324397908580081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39400629086882931939053387 59100943630324397908580081)
      ·
        refine ⟨44325707722743298431435061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59100943630324397908580081 44325707722743298431435061)
        ·
          refine ⟨4155535099007184227947037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44325707722743298431435061 4155535099007184227947037)
          ·
            refine ⟨1558325662127694085480139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4155535099007184227947037 1558325662127694085480139)
            ·
              refine ⟨2337488493191541128220209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558325662127694085480139 2337488493191541128220209)
              ·
                refine ⟨1753116369893655846165157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337488493191541128220209 1753116369893655846165157)
                ·
                  refine ⟨328709319355060471155967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753116369893655846165157 328709319355060471155967)
                  ·
                    rfl

theorem cell20_720179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_720179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720179 prefixEnd_720179 := by exact prefixLift 720179
  have htrace : WordTrace (prefixWord ++ tailWord_720179) baseStart_720179 baseEnd_720179 := by
    simpa [prefixWord, tailWord_720179, baseEnd_720179] using wordTrace_append hprefix tailTrace_720179
  have hstable : (prefixWord ++ tailWord_720179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720179).length < 2 ^ (prefixWord ++ tailWord_720179).sum := by decide
  have hdescent : baseEnd_720179 < baseStart_720179 := by decide
  rcases family_descends (prefixWord ++ tailWord_720179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720200 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_720200 : Nat := 118140960795 + 720200 * 2 ^ 59
def prefixEnd_720200 : Nat := 4983230072969 + 3 ^ 40 * 720200 * 2
def baseEnd_720200 : Nat := 328718904327277731455881

theorem tailTrace_720200 : CollatzResearch.WordTrace tailWord_720200 prefixEnd_720200 328718904327277731455881 := by
  unfold tailWord_720200
  simp only [CollatzResearch.WordTrace]
  refine ⟨13133925995422937606275027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17511901327230583475033369 13133925995422937606275027)
  ·
    refine ⟨19700888993134406409412541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13133925995422937606275027 19700888993134406409412541)
    ·
      refine ⟨7387833372425402403529703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19700888993134406409412541 7387833372425402403529703)
      ·
        refine ⟨11081750058638103605294555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7387833372425402403529703 11081750058638103605294555)
        ·
          refine ⟨16622625087957155407941833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11081750058638103605294555 16622625087957155407941833)
          ·
            refine ⟨12466968815967866555956375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16622625087957155407941833 12466968815967866555956375)
            ·
              refine ⟨18700453223951799833934563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12466968815967866555956375 18700453223951799833934563)
              ·
                refine ⟨28050679835927699750901845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18700453223951799833934563 28050679835927699750901845)
                ·
                  refine ⟨328718904327277731455881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28050679835927699750901845 328718904327277731455881)
                  ·
                    rfl

theorem cell20_720200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_720200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720200 prefixEnd_720200 := by exact prefixLift 720200
  have htrace : WordTrace (prefixWord ++ tailWord_720200) baseStart_720200 baseEnd_720200 := by
    simpa [prefixWord, tailWord_720200, baseEnd_720200] using wordTrace_append hprefix tailTrace_720200
  have hstable : (prefixWord ++ tailWord_720200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720200).length < 2 ^ (prefixWord ++ tailWord_720200).sum := by decide
  have hdescent : baseEnd_720200 < baseStart_720200 := by decide
  rcases family_descends (prefixWord ++ tailWord_720200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720227 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 3]
def baseStart_720227 : Nat := 118140960795 + 720227 * 2 ^ 59
def prefixEnd_720227 : Nat := 4983230072969 + 3 ^ 40 * 720227 * 2
def baseEnd_720227 : Nat := 328731227862985637555771

theorem tailTrace_720227 : CollatzResearch.WordTrace tailWord_720227 prefixEnd_720227 328731227862985637555771 := by
  unfold tailWord_720227
  simp only [CollatzResearch.WordTrace]
  refine ⟨26268836761748058823782935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17512557841165372549188623 26268836761748058823782935)
  ·
    refine ⟨39403255142622088235674403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26268836761748058823782935 39403255142622088235674403)
    ·
      refine ⟨59104882713933132353511605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39403255142622088235674403 59104882713933132353511605)
      ·
        refine ⟨5541082754431231158141713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59104882713933132353511605 5541082754431231158141713)
        ·
          refine ⟨4155812065823423368606285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5541082754431231158141713 4155812065823423368606285)
          ·
            refine ⟨1558429524683783763227357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4155812065823423368606285 1558429524683783763227357)
            ·
              refine ⟨584411071756418911210259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1558429524683783763227357 584411071756418911210259)
              ·
                refine ⟨876616607634628366815389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584411071756418911210259 876616607634628366815389)
                ·
                  refine ⟨328731227862985637555771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876616607634628366815389 328731227862985637555771)
                  ·
                    rfl

theorem cell20_720227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 3].length) (baseStart_720227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720227 prefixEnd_720227 := by exact prefixLift 720227
  have htrace : WordTrace (prefixWord ++ tailWord_720227) baseStart_720227 baseEnd_720227 := by
    simpa [prefixWord, tailWord_720227, baseEnd_720227] using wordTrace_append hprefix tailTrace_720227
  have hstable : (prefixWord ++ tailWord_720227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720227).length < 2 ^ (prefixWord ++ tailWord_720227).sum := by decide
  have hdescent : baseEnd_720227 < baseStart_720227 := by decide
  rcases family_descends (prefixWord ++ tailWord_720227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720258 : List Nat := [3, 4, 2, 1, 1, 3, 6]
def baseStart_720258 : Nat := 118140960795 + 720258 * 2 ^ 59
def prefixEnd_720258 : Nat := 4983230072969 + 3 ^ 40 * 720258 * 2
def baseEnd_720258 : Nat := 36527264123076367502479

theorem tailTrace_720258 : CollatzResearch.WordTrace tailWord_720258 prefixEnd_720258 36527264123076367502479 := by
  unfold tailWord_720258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567491856158937779540357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17513311616423834078774285 6567491856158937779540357)
  ·
    refine ⟨1231404723029800833663817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6567491856158937779540357 1231404723029800833663817)
    ·
      refine ⟨923553542272350625247863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1231404723029800833663817 923553542272350625247863)
      ·
        refine ⟨1385330313408525937871795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923553542272350625247863 1385330313408525937871795)
        ·
          refine ⟨2077995470112788906807693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385330313408525937871795 2077995470112788906807693)
          ·
            refine ⟨779248301292295840052885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2077995470112788906807693 779248301292295840052885)
            ·
              refine ⟨36527264123076367502479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 779248301292295840052885 36527264123076367502479)
              ·
                rfl

theorem cell20_720258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 6].length) (baseStart_720258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720258 prefixEnd_720258 := by exact prefixLift 720258
  have htrace : WordTrace (prefixWord ++ tailWord_720258) baseStart_720258 baseEnd_720258 := by
    simpa [prefixWord, tailWord_720258, baseEnd_720258] using wordTrace_append hprefix tailTrace_720258
  have hstable : (prefixWord ++ tailWord_720258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720258).length < 2 ^ (prefixWord ++ tailWord_720258).sum := by decide
  have hdescent : baseEnd_720258 < baseStart_720258 := by decide
  rcases family_descends (prefixWord ++ tailWord_720258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720355 : List Nat := [1, 1, 1, 6, 2, 2, 3, 4]
def baseStart_720355 : Nat := 118140960795 + 720355 * 2 ^ 59
def prefixEnd_720355 : Nat := 4983230072969 + 3 ^ 40 * 720355 * 2
def baseEnd_720355 : Nat := 109596550183595360429527

theorem tailTrace_720355 : CollatzResearch.WordTrace tailWord_720355 prefixEnd_720355 109596550183595360429527 := by
  unfold tailWord_720355
  simp only [CollatzResearch.WordTrace]
  refine ⟨26273505305284336684442519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17515670203522891122961679 26273505305284336684442519)
  ·
    refine ⟨39410257957926505026663779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26273505305284336684442519 39410257957926505026663779)
    ·
      refine ⟨59115386936889757539995669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39410257957926505026663779 59115386936889757539995669)
      ·
        refine ⟨2771033762666707384687297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59115386936889757539995669 2771033762666707384687297)
        ·
          refine ⟨2078275322000030538515473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2771033762666707384687297 2078275322000030538515473)
          ·
            refine ⟨1558706491500022903886605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2078275322000030538515473 1558706491500022903886605)
            ·
              refine ⟨584514934312508588957477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1558706491500022903886605 584514934312508588957477)
              ·
                refine ⟨109596550183595360429527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 584514934312508588957477 109596550183595360429527)
                ·
                  rfl

theorem cell20_720355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 4].length) (baseStart_720355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720355 prefixEnd_720355 := by exact prefixLift 720355
  have htrace : WordTrace (prefixWord ++ tailWord_720355) baseStart_720355 baseEnd_720355 := by
    simpa [prefixWord, tailWord_720355, baseEnd_720355] using wordTrace_append hprefix tailTrace_720355
  have hstable : (prefixWord ++ tailWord_720355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720355).length < 2 ^ (prefixWord ++ tailWord_720355).sum := by decide
  have hdescent : baseEnd_720355 < baseStart_720355 := by decide
  rcases family_descends (prefixWord ++ tailWord_720355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720383 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 3]
def baseStart_720383 : Nat := 118140960795 + 720383 * 2 ^ 59
def prefixEnd_720383 : Nat := 4983230072969 + 3 ^ 40 * 720383 * 2
def baseEnd_720383 : Nat := 328802430513742428355133

theorem tailTrace_720383 : CollatzResearch.WordTrace tailWord_720383 prefixEnd_720383 328802430513742428355133 := by
  unfold tailWord_720383
  simp only [CollatzResearch.WordTrace]
  refine ⟨26274526549182897466461803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17516351032788598310974535 26274526549182897466461803)
  ·
    refine ⟨39411789823774346199692705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26274526549182897466461803 39411789823774346199692705)
    ·
      refine ⟨29558842367830759649769529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39411789823774346199692705 29558842367830759649769529)
      ·
        refine ⟨22169131775873069737327147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29558842367830759649769529 22169131775873069737327147)
        ·
          refine ⟨33253697663809604605990721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22169131775873069737327147 33253697663809604605990721)
          ·
            refine ⟨24940273247857203454493041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33253697663809604605990721 24940273247857203454493041)
            ·
              refine ⟨18705204935892902590869781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24940273247857203454493041 18705204935892902590869781)
              ·
                refine ⟨876806481369979808947021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18705204935892902590869781 876806481369979808947021)
                ·
                  refine ⟨328802430513742428355133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876806481369979808947021 328802430513742428355133)
                  ·
                    rfl

theorem cell20_720383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_720383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720383 prefixEnd_720383 := by exact prefixLift 720383
  have htrace : WordTrace (prefixWord ++ tailWord_720383) baseStart_720383 baseEnd_720383 := by
    simpa [prefixWord, tailWord_720383, baseEnd_720383] using wordTrace_append hprefix tailTrace_720383
  have hstable : (prefixWord ++ tailWord_720383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720383).length < 2 ^ (prefixWord ++ tailWord_720383).sum := by decide
  have hdescent : baseEnd_720383 < baseStart_720383 := by decide
  rcases family_descends (prefixWord ++ tailWord_720383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720386 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_720386 : Nat := 118140960795 + 720386 * 2 ^ 59
def prefixEnd_720386 : Nat := 4983230072969 + 3 ^ 40 * 720386 * 2
def baseEnd_720386 : Nat := 328803799795487751255121

theorem tailTrace_720386 : CollatzResearch.WordTrace tailWord_720386 prefixEnd_720386 328803799795487751255121 := by
  unfold tailWord_720386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6568658992043007244705253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17516423978781352652547341 6568658992043007244705253)
  ·
    refine ⟨1231623561008063858382235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6568658992043007244705253 1231623561008063858382235)
    ·
      refine ⟨1847435341512095787573353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231623561008063858382235 1847435341512095787573353)
      ·
        refine ⟨1385576506134071840680015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1847435341512095787573353 1385576506134071840680015)
        ·
          refine ⟨2078364759201107761020023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385576506134071840680015 2078364759201107761020023)
          ·
            refine ⟨3117547138801661641530035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078364759201107761020023 3117547138801661641530035)
            ·
              refine ⟨4676320708202492462295053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117547138801661641530035 4676320708202492462295053)
              ·
                refine ⟨1753620265575934673360645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4676320708202492462295053 1753620265575934673360645)
                ·
                  refine ⟨328803799795487751255121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753620265575934673360645 328803799795487751255121)
                  ·
                    rfl

theorem cell20_720386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_720386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720386 prefixEnd_720386 := by exact prefixLift 720386
  have htrace : WordTrace (prefixWord ++ tailWord_720386) baseStart_720386 baseEnd_720386 := by
    simpa [prefixWord, tailWord_720386, baseEnd_720386] using wordTrace_append hprefix tailTrace_720386
  have hstable : (prefixWord ++ tailWord_720386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720386).length < 2 ^ (prefixWord ++ tailWord_720386).sum := by decide
  have hdescent : baseEnd_720386 < baseStart_720386 := by decide
  rcases family_descends (prefixWord ++ tailWord_720386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720435 : List Nat := [1, 1, 1, 2, 4, 3, 8]
def baseStart_720435 : Nat := 118140960795 + 720435 * 2 ^ 59
def prefixEnd_720435 : Nat := 4983230072969 + 3 ^ 40 * 720435 * 2
def baseEnd_720435 : Nat := 36536240525629039846843

theorem tailTrace_720435 : CollatzResearch.WordTrace tailWord_720435 prefixEnd_720435 36536240525629039846843 := by
  unfold tailWord_720435
  simp only [CollatzResearch.WordTrace]
  refine ⟨26276423144994510347354759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17517615429996340231569839 26276423144994510347354759)
  ·
    refine ⟨39414634717491765521032139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26276423144994510347354759 39414634717491765521032139)
    ·
      refine ⟨59121952076237648281548209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39414634717491765521032139 59121952076237648281548209)
      ·
        refine ⟨44341464057178236211161157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59121952076237648281548209 44341464057178236211161157)
        ·
          refine ⟨8314024510720919289592717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44341464057178236211161157 8314024510720919289592717)
          ·
            refine ⟨3117759191520344733597269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8314024510720919289592717 3117759191520344733597269)
            ·
              refine ⟨36536240525629039846843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3117759191520344733597269 36536240525629039846843)
              ·
                rfl

theorem cell20_720435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 8].length) (baseStart_720435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720435 prefixEnd_720435 := by exact prefixLift 720435
  have htrace : WordTrace (prefixWord ++ tailWord_720435) baseStart_720435 baseEnd_720435 := by
    simpa [prefixWord, tailWord_720435, baseEnd_720435] using wordTrace_append hprefix tailTrace_720435
  have hstable : (prefixWord ++ tailWord_720435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720435).length < 2 ^ (prefixWord ++ tailWord_720435).sum := by decide
  have hdescent : baseEnd_720435 < baseStart_720435 := by decide
  rcases family_descends (prefixWord ++ tailWord_720435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720441 : List Nat := [1, 2, 1, 5, 1, 3, 3, 2, 2]
def baseStart_720441 : Nat := 118140960795 + 720441 * 2 ^ 59
def prefixEnd_720441 : Nat := 4983230072969 + 3 ^ 40 * 720441 * 2
def baseEnd_720441 : Nat := 328828903294152004421563

theorem tailTrace_720441 : CollatzResearch.WordTrace tailWord_720441 prefixEnd_720441 328828903294152004421563 := by
  unfold tailWord_720441
  simp only [CollatzResearch.WordTrace]
  refine ⟨26276641982972773372073177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17517761321981848914715451 26276641982972773372073177)
  ·
    refine ⟨19707481487229580029054883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26276641982972773372073177 19707481487229580029054883)
    ·
      refine ⟨29561222230844370043582325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19707481487229580029054883 29561222230844370043582325)
      ·
        refine ⟨2771364584141659691585843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29561222230844370043582325 2771364584141659691585843)
        ·
          refine ⟨4157046876212489537378765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771364584141659691585843 4157046876212489537378765)
          ·
            refine ⟨1558892578579683576517037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4157046876212489537378765 1558892578579683576517037)
            ·
              refine ⟨584584716967381341193889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1558892578579683576517037 584584716967381341193889)
              ·
                refine ⟨438438537725536005895417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584584716967381341193889 438438537725536005895417)
                ·
                  refine ⟨328828903294152004421563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438438537725536005895417 328828903294152004421563)
                  ·
                    rfl

theorem cell20_720441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_720441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720441 prefixEnd_720441 := by exact prefixLift 720441
  have htrace : WordTrace (prefixWord ++ tailWord_720441) baseStart_720441 baseEnd_720441 := by
    simpa [prefixWord, tailWord_720441, baseEnd_720441] using wordTrace_append hprefix tailTrace_720441
  have hstable : (prefixWord ++ tailWord_720441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720441).length < 2 ^ (prefixWord ++ tailWord_720441).sum := by decide
  have hdescent : baseEnd_720441 < baseStart_720441 := by decide
  rcases family_descends (prefixWord ++ tailWord_720441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720493 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 3]
def baseStart_720493 : Nat := 118140960795 + 720493 * 2 ^ 59
def prefixEnd_720493 : Nat := 4983230072969 + 3 ^ 40 * 720493 * 2
def baseEnd_720493 : Nat := 328852637511070934688017

theorem tailTrace_720493 : CollatzResearch.WordTrace tailWord_720493 prefixEnd_720493 328852637511070934688017 := by
  unfold tailWord_720493
  simp only [CollatzResearch.WordTrace]
  refine ⟨26278538578784386252966133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17519025719189590835310755 26278538578784386252966133)
  ·
    refine ⟨2463612991761036211215575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26278538578784386252966133 2463612991761036211215575)
    ·
      refine ⟨3695419487641554316823363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463612991761036211215575 3695419487641554316823363)
      ·
        refine ⟨5543129231462331475235045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3695419487641554316823363 5543129231462331475235045)
        ·
          refine ⟨1039336730899187151606571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5543129231462331475235045 1039336730899187151606571)
          ·
            refine ⟨1559005096348780727409857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039336730899187151606571 1559005096348780727409857)
            ·
              refine ⟨1169253822261585545557393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559005096348780727409857 1169253822261585545557393)
              ·
                refine ⟨876940366696189159168045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169253822261585545557393 876940366696189159168045)
                ·
                  refine ⟨328852637511070934688017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876940366696189159168045 328852637511070934688017)
                  ·
                    rfl

theorem cell20_720493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_720493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720493 prefixEnd_720493 := by exact prefixLift 720493
  have htrace : WordTrace (prefixWord ++ tailWord_720493) baseStart_720493 baseEnd_720493 := by
    simpa [prefixWord, tailWord_720493, baseEnd_720493] using wordTrace_append hprefix tailTrace_720493
  have hstable : (prefixWord ++ tailWord_720493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720493).length < 2 ^ (prefixWord ++ tailWord_720493).sum := by decide
  have hdescent : baseEnd_720493 < baseStart_720493 := by decide
  rcases family_descends (prefixWord ++ tailWord_720493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720559 : List Nat := [1, 1, 2, 1, 2, 4, 1, 6, 2]
def baseStart_720559 : Nat := 118140960795 + 720559 * 2 ^ 59
def prefixEnd_720559 : Nat := 4983230072969 + 3 ^ 40 * 720559 * 2
def baseEnd_720559 : Nat := 328882761709468038487747

theorem tailTrace_720559 : CollatzResearch.WordTrace tailWord_720559 prefixEnd_720559 328882761709468038487747 := by
  unfold tailWord_720559
  simp only [CollatzResearch.WordTrace]
  refine ⟨26280945796545279524868731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17520630531030186349912487 26280945796545279524868731)
  ·
    refine ⟨39421418694817919287303097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26280945796545279524868731 39421418694817919287303097)
    ·
      refine ⟨29566064021113439465477323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39421418694817919287303097 29566064021113439465477323)
      ·
        refine ⟨44349096031670159198215985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29566064021113439465477323 44349096031670159198215985)
        ·
          refine ⟨33261822023752619398661989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44349096031670159198215985 33261822023752619398661989)
          ·
            refine ⟨6236591629453616137249123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33261822023752619398661989 6236591629453616137249123)
            ·
              refine ⟨9354887444180424205873685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6236591629453616137249123 9354887444180424205873685)
              ·
                refine ⟨438510348945957384650329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9354887444180424205873685 438510348945957384650329)
                ·
                  refine ⟨328882761709468038487747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438510348945957384650329 328882761709468038487747)
                  ·
                    rfl

theorem cell20_720559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 2].length) (baseStart_720559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720559 prefixEnd_720559 := by exact prefixLift 720559
  have htrace : WordTrace (prefixWord ++ tailWord_720559) baseStart_720559 baseEnd_720559 := by
    simpa [prefixWord, tailWord_720559, baseEnd_720559] using wordTrace_append hprefix tailTrace_720559
  have hstable : (prefixWord ++ tailWord_720559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720559).length < 2 ^ (prefixWord ++ tailWord_720559).sum := by decide
  have hdescent : baseEnd_720559 < baseStart_720559 := by decide
  rcases family_descends (prefixWord ++ tailWord_720559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720625 : List Nat := [1, 2, 2, 2, 2, 3, 1, 7]
def baseStart_720625 : Nat := 118140960795 + 720625 * 2 ^ 59
def prefixEnd_720625 : Nat := 4983230072969 + 3 ^ 40 * 720625 * 2
def baseEnd_720625 : Nat := 109637628635955047429159

theorem tailTrace_720625 : CollatzResearch.WordTrace tailWord_720625 prefixEnd_720625 109637628635955047429159 := by
  unfold tailWord_720625
  simp only [CollatzResearch.WordTrace]
  refine ⟨26283353014306172796771329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17522235342870781864514219 26283353014306172796771329)
  ·
    refine ⟨19712514760729629597578497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26283353014306172796771329 19712514760729629597578497)
    ·
      refine ⟨14784386070547222198183873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19712514760729629597578497 14784386070547222198183873)
      ·
        refine ⟨11088289552910416648637905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14784386070547222198183873 11088289552910416648637905)
        ·
          refine ⟨8316217164682812486478429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11088289552910416648637905 8316217164682812486478429)
          ·
            refine ⟨3118581436756054682429411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8316217164682812486478429 3118581436756054682429411)
            ·
              refine ⟨4677872155134082023644117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118581436756054682429411 4677872155134082023644117)
              ·
                refine ⟨109637628635955047429159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4677872155134082023644117 109637628635955047429159)
                ·
                  rfl

theorem cell20_720625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_720625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720625 prefixEnd_720625 := by exact prefixLift 720625
  have htrace : WordTrace (prefixWord ++ tailWord_720625) baseStart_720625 baseEnd_720625 := by
    simpa [prefixWord, tailWord_720625, baseEnd_720625] using wordTrace_append hprefix tailTrace_720625
  have hstable : (prefixWord ++ tailWord_720625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720625).length < 2 ^ (prefixWord ++ tailWord_720625).sum := by decide
  have hdescent : baseEnd_720625 < baseStart_720625 := by decide
  rcases family_descends (prefixWord ++ tailWord_720625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720632 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_720632 : Nat := 118140960795 + 720632 * 2 ^ 59
def prefixEnd_720632 : Nat := 4983230072969 + 3 ^ 40 * 720632 * 2
def baseEnd_720632 : Nat := 328916080898604229054115

theorem tailTrace_720632 : CollatzResearch.WordTrace tailWord_720632 prefixEnd_720632 328916080898604229054115 := by
  unfold tailWord_720632
  simp only [CollatzResearch.WordTrace]
  refine ⟨13141804162640406496138075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17522405550187208661517433 13141804162640406496138075)
  ·
    refine ⟨19712706243960609744207113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13141804162640406496138075 19712706243960609744207113)
    ·
      refine ⟨14784529682970457308155335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19712706243960609744207113 14784529682970457308155335)
      ·
        refine ⟨22176794524455685962233003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14784529682970457308155335 22176794524455685962233003)
        ·
          refine ⟨33265191786683528943349505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22176794524455685962233003 33265191786683528943349505)
          ·
            refine ⟨24948893840012646707512129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33265191786683528943349505 24948893840012646707512129)
            ·
              refine ⟨18711670380009485030634097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24948893840012646707512129 18711670380009485030634097)
              ·
                refine ⟨14033752785007113772975573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18711670380009485030634097 14033752785007113772975573)
                ·
                  refine ⟨328916080898604229054115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14033752785007113772975573 328916080898604229054115)
                  ·
                    rfl

theorem cell20_720632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_720632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720632 prefixEnd_720632 := by exact prefixLift 720632
  have htrace : WordTrace (prefixWord ++ tailWord_720632) baseStart_720632 baseEnd_720632 := by
    simpa [prefixWord, tailWord_720632, baseEnd_720632] using wordTrace_append hprefix tailTrace_720632
  have hstable : (prefixWord ++ tailWord_720632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720632).length < 2 ^ (prefixWord ++ tailWord_720632).sum := by decide
  have hdescent : baseEnd_720632 < baseStart_720632 := by decide
  rcases family_descends (prefixWord ++ tailWord_720632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720642 : List Nat := [3, 4, 1, 1, 1, 1, 1, 8]
def baseStart_720642 : Nat := 118140960795 + 720642 * 2 ^ 59
def prefixEnd_720642 : Nat := 4983230072969 + 3 ^ 40 * 720642 * 2
def baseEnd_720642 : Nat := 109640215057029546240247

theorem tailTrace_720642 : CollatzResearch.WordTrace tailWord_720642 prefixEnd_720642 109640215057029546240247 := by
  unfold tailWord_720642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6570993263811146175035045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17522648703496389800093453 6570993263811146175035045)
  ·
    refine ⟨1232061236964589907819071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6570993263811146175035045 1232061236964589907819071)
    ·
      refine ⟨1848091855446884861728607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232061236964589907819071 1848091855446884861728607)
      ·
        refine ⟨2772137783170327292592911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848091855446884861728607 2772137783170327292592911)
        ·
          refine ⟨4158206674755490938889367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772137783170327292592911 4158206674755490938889367)
          ·
            refine ⟨6237310012133236408334051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158206674755490938889367 6237310012133236408334051)
            ·
              refine ⟨9355965018199854612501077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6237310012133236408334051 9355965018199854612501077)
              ·
                refine ⟨109640215057029546240247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9355965018199854612501077 109640215057029546240247)
                ·
                  rfl

theorem cell20_720642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_720642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720642 prefixEnd_720642 := by exact prefixLift 720642
  have htrace : WordTrace (prefixWord ++ tailWord_720642) baseStart_720642 baseEnd_720642 := by
    simpa [prefixWord, tailWord_720642, baseEnd_720642] using wordTrace_append hprefix tailTrace_720642
  have hstable : (prefixWord ++ tailWord_720642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720642).length < 2 ^ (prefixWord ++ tailWord_720642).sum := by decide
  have hdescent : baseEnd_720642 < baseStart_720642 := by decide
  rcases family_descends (prefixWord ++ tailWord_720642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720663 : List Nat := [1, 1, 3, 4, 2, 9]
def baseStart_720663 : Nat := 118140960795 + 720663 * 2 ^ 59
def prefixEnd_720663 : Nat := 4983230072969 + 3 ^ 40 * 720663 * 2
def baseEnd_720663 : Nat := 12182601116418737000765

theorem tailTrace_720663 : CollatzResearch.WordTrace tailWord_720663 prefixEnd_720663 12182601116418737000765 := by
  unfold tailWord_720663
  simp only [CollatzResearch.WordTrace]
  refine ⟨26284738988168505286654643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17523159325445670191103095 26284738988168505286654643)
  ·
    refine ⟨39427108482252757929981965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26284738988168505286654643 39427108482252757929981965)
    ·
      refine ⟨14785165680844784223743237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39427108482252757929981965 14785165680844784223743237)
      ·
        refine ⟨2772218565158397041951857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14785165680844784223743237 2772218565158397041951857)
        ·
          refine ⟨2079163923868797781463893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2772218565158397041951857 2079163923868797781463893)
          ·
            refine ⟨12182601116418737000765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2079163923868797781463893 12182601116418737000765)
            ·
              rfl

theorem cell20_720663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 9].length) (baseStart_720663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720663 prefixEnd_720663 := by exact prefixLift 720663
  have htrace : WordTrace (prefixWord ++ tailWord_720663) baseStart_720663 baseEnd_720663 := by
    simpa [prefixWord, tailWord_720663, baseEnd_720663] using wordTrace_append hprefix tailTrace_720663
  have hstable : (prefixWord ++ tailWord_720663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720663).length < 2 ^ (prefixWord ++ tailWord_720663).sum := by decide
  have hdescent : baseEnd_720663 < baseStart_720663 := by decide
  rcases family_descends (prefixWord ++ tailWord_720663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720666 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_720666 : Nat := 118140960795 + 720666 * 2 ^ 59
def prefixEnd_720666 : Nat := 4983230072969 + 3 ^ 40 * 720666 * 2
def baseEnd_720666 : Nat := 328931599425051221920643

theorem tailTrace_720666 : CollatzResearch.WordTrace tailWord_720666 prefixEnd_720666 328931599425051221920643 := by
  unfold tailWord_720666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571212101789409199753463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17523232271438424532675901 6571212101789409199753463)
  ·
    refine ⟨9856818152684113799630195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571212101789409199753463 9856818152684113799630195)
    ·
      refine ⟨14785227229026170699445293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9856818152684113799630195 14785227229026170699445293)
      ·
        refine ⟨5544460210884814012291985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14785227229026170699445293 5544460210884814012291985)
        ·
          refine ⟨4158345158163610509218989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5544460210884814012291985 4158345158163610509218989)
          ·
            refine ⟨1559379434311353940957121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4158345158163610509218989 1559379434311353940957121)
            ·
              refine ⟨1169534575733515455717841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559379434311353940957121 1169534575733515455717841)
              ·
                refine ⟨877150931800136591788381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169534575733515455717841 877150931800136591788381)
                ·
                  refine ⟨328931599425051221920643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877150931800136591788381 328931599425051221920643)
                  ·
                    rfl

theorem cell20_720666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_720666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720666 prefixEnd_720666 := by exact prefixLift 720666
  have htrace : WordTrace (prefixWord ++ tailWord_720666) baseStart_720666 baseEnd_720666 := by
    simpa [prefixWord, tailWord_720666, baseEnd_720666] using wordTrace_append hprefix tailTrace_720666
  have hstable : (prefixWord ++ tailWord_720666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720666).length < 2 ^ (prefixWord ++ tailWord_720666).sum := by decide
  have hdescent : baseEnd_720666 < baseStart_720666 := by decide
  rcases family_descends (prefixWord ++ tailWord_720666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720680 : List Nat := [2, 1, 5, 1, 1, 2, 3, 5]
def baseStart_720680 : Nat := 118140960795 + 720680 * 2 ^ 59
def prefixEnd_720680 : Nat := 4983230072969 + 3 ^ 40 * 720680 * 2
def baseEnd_720680 : Nat := 109645996468843131817973

theorem tailTrace_720680 : CollatzResearch.WordTrace tailWord_720680 prefixEnd_720680 109645996468843131817973 := by
  unfold tailWord_720680
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142679514553458595011747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17523572686071278126682329 13142679514553458595011747)
  ·
    refine ⟨19714019271830187892517621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13142679514553458595011747 19714019271830187892517621)
    ·
      refine ⟨1848189306734080114923527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19714019271830187892517621 1848189306734080114923527)
      ·
        refine ⟨2772283960101120172385291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848189306734080114923527 2772283960101120172385291)
        ·
          refine ⟨4158425940151680258577937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772283960101120172385291 4158425940151680258577937)
          ·
            refine ⟨3118819455113760193933453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4158425940151680258577937 3118819455113760193933453)
            ·
              refine ⟨1169557295667660072725045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3118819455113760193933453 1169557295667660072725045)
              ·
                refine ⟨109645996468843131817973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1169557295667660072725045 109645996468843131817973)
                ·
                  rfl

theorem cell20_720680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_720680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720680 prefixEnd_720680 := by exact prefixLift 720680
  have htrace : WordTrace (prefixWord ++ tailWord_720680) baseStart_720680 baseEnd_720680 := by
    simpa [prefixWord, tailWord_720680, baseEnd_720680] using wordTrace_append hprefix tailTrace_720680
  have hstable : (prefixWord ++ tailWord_720680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720680).length < 2 ^ (prefixWord ++ tailWord_720680).sum := by decide
  have hdescent : baseEnd_720680 < baseStart_720680 := by decide
  rcases family_descends (prefixWord ++ tailWord_720680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720711 : List Nat := [1, 1, 4, 1, 2, 1, 3, 5, 2]
def baseStart_720711 : Nat := 118140960795 + 720711 * 2 ^ 59
def prefixEnd_720711 : Nat := 4983230072969 + 3 ^ 40 * 720711 * 2
def baseEnd_720711 : Nat := 328952138651231065420459

theorem tailTrace_720711 : CollatzResearch.WordTrace tailWord_720711 prefixEnd_720711 328952138651231065420459 := by
  unfold tailWord_720711
  simp only [CollatzResearch.WordTrace]
  refine ⟨26286489691994609484401987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17524326461329739656267991 26286489691994609484401987)
  ·
    refine ⟨39429734537991914226602981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26286489691994609484401987 39429734537991914226602981)
    ·
      refine ⟨7393075225873483917488059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39429734537991914226602981 7393075225873483917488059)
      ·
        refine ⟨11089612838810225876232089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7393075225873483917488059 11089612838810225876232089)
        ·
          refine ⟨8317209629107669407174067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11089612838810225876232089 8317209629107669407174067)
          ·
            refine ⟨12475814443661504110761101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8317209629107669407174067 12475814443661504110761101)
            ·
              refine ⟨4678430416373064041535413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12475814443661504110761101 4678430416373064041535413)
              ·
                refine ⟨438602851534974753893945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4678430416373064041535413 438602851534974753893945)
                ·
                  refine ⟨328952138651231065420459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438602851534974753893945 328952138651231065420459)
                  ·
                    rfl

theorem cell20_720711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 2].length) (baseStart_720711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720711 prefixEnd_720711 := by exact prefixLift 720711
  have htrace : WordTrace (prefixWord ++ tailWord_720711) baseStart_720711 baseEnd_720711 := by
    simpa [prefixWord, tailWord_720711, baseEnd_720711] using wordTrace_append hprefix tailTrace_720711
  have hstable : (prefixWord ++ tailWord_720711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720711).length < 2 ^ (prefixWord ++ tailWord_720711).sum := by decide
  have hdescent : baseEnd_720711 < baseStart_720711 := by decide
  rcases family_descends (prefixWord ++ tailWord_720711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720725 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 5]
def baseStart_720725 : Nat := 118140960795 + 720725 * 2 ^ 59
def prefixEnd_720725 : Nat := 4983230072969 + 3 ^ 40 * 720725 * 2
def baseEnd_720725 : Nat := 328958528632709238953735

theorem tailTrace_720725 : CollatzResearch.WordTrace tailWord_720725 prefixEnd_720725 328958528632709238953735 := by
  unfold tailWord_720725
  simp only [CollatzResearch.WordTrace]
  refine ⟨26287000313943889875411629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17524666875962593250274419 26287000313943889875411629)
  ·
    refine ⟨9857625117728958703279361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26287000313943889875411629 9857625117728958703279361)
    ·
      refine ⟨7393218838296719027459521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9857625117728958703279361 7393218838296719027459521)
      ·
        refine ⟨5544914128722539270594641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7393218838296719027459521 5544914128722539270594641)
        ·
          refine ⟨4158685596541904452945981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5544914128722539270594641 4158685596541904452945981)
          ·
            refine ⟨1559507098703214169854743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4158685596541904452945981 1559507098703214169854743)
            ·
              refine ⟨2339260648054821254782115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559507098703214169854743 2339260648054821254782115)
              ·
                refine ⟨3508890972082231882173173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339260648054821254782115 3508890972082231882173173)
                ·
                  refine ⟨328958528632709238953735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3508890972082231882173173 328958528632709238953735)
                  ·
                    rfl

theorem cell20_720725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_720725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720725 prefixEnd_720725 := by exact prefixLift 720725
  have htrace : WordTrace (prefixWord ++ tailWord_720725) baseStart_720725 baseEnd_720725 := by
    simpa [prefixWord, tailWord_720725, baseEnd_720725] using wordTrace_append hprefix tailTrace_720725
  have hstable : (prefixWord ++ tailWord_720725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720725).length < 2 ^ (prefixWord ++ tailWord_720725).sum := by decide
  have hdescent : baseEnd_720725 < baseStart_720725 := by decide
  rcases family_descends (prefixWord ++ tailWord_720725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720794 : List Nat := [3, 1, 1, 4, 2, 2, 2, 5]
def baseStart_720794 : Nat := 118140960795 + 720794 * 2 ^ 59
def prefixEnd_720794 : Nat := 4983230072969 + 3 ^ 40 * 720794 * 2
def baseEnd_720794 : Nat := 109663340704283888551151

theorem tailTrace_720794 : CollatzResearch.WordTrace tailWord_720794 prefixEnd_720794 109663340704283888551151 := by
  unfold tailWord_720794
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572379237673478664918359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17526344633795943106448957 6572379237673478664918359)
  ·
    refine ⟨9858568856510217997377539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6572379237673478664918359 9858568856510217997377539)
    ·
      refine ⟨14787853284765326996066309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9858568856510217997377539 14787853284765326996066309)
      ·
        refine ⟨2772722490893498811762433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14787853284765326996066309 2772722490893498811762433)
        ·
          refine ⟨2079541868170124108821825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2772722490893498811762433 2079541868170124108821825)
          ·
            refine ⟨1559656401127593081616369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2079541868170124108821825 1559656401127593081616369)
            ·
              refine ⟨1169742300845694811212277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559656401127593081616369 1169742300845694811212277)
              ·
                refine ⟨109663340704283888551151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1169742300845694811212277 109663340704283888551151)
                ·
                  rfl

theorem cell20_720794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_720794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720794 prefixEnd_720794 := by exact prefixLift 720794
  have htrace : WordTrace (prefixWord ++ tailWord_720794) baseStart_720794 baseEnd_720794 := by
    simpa [prefixWord, tailWord_720794, baseEnd_720794] using wordTrace_append hprefix tailTrace_720794
  have hstable : (prefixWord ++ tailWord_720794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720794).length < 2 ^ (prefixWord ++ tailWord_720794).sum := by decide
  have hdescent : baseEnd_720794 < baseStart_720794 := by decide
  rcases family_descends (prefixWord ++ tailWord_720794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720797 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 3]
def baseStart_720797 : Nat := 118140960795 + 720797 * 2 ^ 59
def prefixEnd_720797 : Nat := 4983230072969 + 3 ^ 40 * 720797 * 2
def baseEnd_720797 : Nat := 328991391394596988553441

theorem tailTrace_720797 : CollatzResearch.WordTrace tailWord_720797 prefixEnd_720797 328991391394596988553441 := by
  unfold tailWord_720797
  simp only [CollatzResearch.WordTrace]
  refine ⟨26289626369683046172032645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17526417579788697448021763 26289626369683046172032645)
  ·
    refine ⟨4929304944315571157256121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26289626369683046172032645 4929304944315571157256121)
    ·
      refine ⟨3696978708236678367942091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4929304944315571157256121 3696978708236678367942091)
      ·
        refine ⟨5545468062355017551913137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696978708236678367942091 5545468062355017551913137)
        ·
          refine ⟨4159101046766263163934853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5545468062355017551913137 4159101046766263163934853)
          ·
            refine ⟨779831446268674343237785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4159101046766263163934853 779831446268674343237785)
            ·
              refine ⟨584873584701505757428339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779831446268674343237785 584873584701505757428339)
              ·
                refine ⟨877310377052258636142509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584873584701505757428339 877310377052258636142509)
                ·
                  refine ⟨328991391394596988553441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877310377052258636142509 328991391394596988553441)
                  ·
                    rfl

theorem cell20_720797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_720797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720797 prefixEnd_720797 := by exact prefixLift 720797
  have htrace : WordTrace (prefixWord ++ tailWord_720797) baseStart_720797 baseEnd_720797 := by
    simpa [prefixWord, tailWord_720797, baseEnd_720797] using wordTrace_append hprefix tailTrace_720797
  have hstable : (prefixWord ++ tailWord_720797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720797).length < 2 ^ (prefixWord ++ tailWord_720797).sum := by decide
  have hdescent : baseEnd_720797 < baseStart_720797 := by decide
  rcases family_descends (prefixWord ++ tailWord_720797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720825 : List Nat := [1, 2, 1, 4, 2, 1, 2, 5, 2]
def baseStart_720825 : Nat := 118140960795 + 720825 * 2 ^ 59
def prefixEnd_720825 : Nat := 4983230072969 + 3 ^ 40 * 720825 * 2
def baseEnd_720825 : Nat := 329004171357553335619993

theorem tailTrace_720825 : CollatzResearch.WordTrace tailWord_720825 prefixEnd_720825 329004171357553335619993 := by
  unfold tailWord_720825
  simp only [CollatzResearch.WordTrace]
  refine ⟨26290647613581606954051929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17527098409054404636034619 26290647613581606954051929)
  ·
    refine ⟨19717985710186205215538947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26290647613581606954051929 19717985710186205215538947)
    ·
      refine ⟨29576978565279307823308421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19717985710186205215538947 29576978565279307823308421)
      ·
        refine ⟨5545683480989870216870329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29576978565279307823308421 5545683480989870216870329)
        ·
          refine ⟨4159262610742402662652747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5545683480989870216870329 4159262610742402662652747)
          ·
            refine ⟨6238893916113603993979121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159262610742402662652747 6238893916113603993979121)
            ·
              refine ⟨4679170437085202995484341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6238893916113603993979121 4679170437085202995484341)
              ·
                refine ⟨438672228476737780826657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4679170437085202995484341 438672228476737780826657)
                ·
                  refine ⟨329004171357553335619993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438672228476737780826657 329004171357553335619993)
                  ·
                    rfl

theorem cell20_720825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_720825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720825 prefixEnd_720825 := by exact prefixLift 720825
  have htrace : WordTrace (prefixWord ++ tailWord_720825) baseStart_720825 baseEnd_720825 := by
    simpa [prefixWord, tailWord_720825, baseEnd_720825] using wordTrace_append hprefix tailTrace_720825
  have hstable : (prefixWord ++ tailWord_720825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720825).length < 2 ^ (prefixWord ++ tailWord_720825).sum := by decide
  have hdescent : baseEnd_720825 < baseStart_720825 := by decide
  rcases family_descends (prefixWord ++ tailWord_720825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720842 : List Nat := [3, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_720842 : Nat := 118140960795 + 720842 * 2 ^ 59
def prefixEnd_720842 : Nat := 4983230072969 + 3 ^ 40 * 720842 * 2
def baseEnd_720842 : Nat := 329011930620776832053257

theorem tailTrace_720842 : CollatzResearch.WordTrace tailWord_720842 prefixEnd_720842 329011930620776832053257 := by
  unfold tailWord_720842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572816913630004714355195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17527511769680012571613853 6572816913630004714355195)
  ·
    refine ⟨9859225370445007071532793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6572816913630004714355195 9859225370445007071532793)
    ·
      refine ⟨7394419027833755303649595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9859225370445007071532793 7394419027833755303649595)
      ·
        refine ⟨11091628541750632955474393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7394419027833755303649595 11091628541750632955474393)
        ·
          refine ⟨8318721406312974716605795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11091628541750632955474393 8318721406312974716605795)
          ·
            refine ⟨12478082109469462074908693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8318721406312974716605795 12478082109469462074908693)
            ·
              refine ⟨584910098881381034761345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12478082109469462074908693 584910098881381034761345)
              ·
                refine ⟨438682574161035776071009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584910098881381034761345 438682574161035776071009)
                ·
                  refine ⟨329011930620776832053257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438682574161035776071009 329011930620776832053257)
                  ·
                    rfl

theorem cell20_720842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_720842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720842 prefixEnd_720842 := by exact prefixLift 720842
  have htrace : WordTrace (prefixWord ++ tailWord_720842) baseStart_720842 baseEnd_720842 := by
    simpa [prefixWord, tailWord_720842, baseEnd_720842] using wordTrace_append hprefix tailTrace_720842
  have hstable : (prefixWord ++ tailWord_720842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720842).length < 2 ^ (prefixWord ++ tailWord_720842).sum := by decide
  have hdescent : baseEnd_720842 < baseStart_720842 := by decide
  rcases family_descends (prefixWord ++ tailWord_720842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720846 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_720846 : Nat := 118140960795 + 720846 * 2 ^ 59
def prefixEnd_720846 : Nat := 4983230072969 + 3 ^ 40 * 720846 * 2
def baseEnd_720846 : Nat := 329013756329770595919907

theorem tailTrace_720846 : CollatzResearch.WordTrace tailWord_720846 prefixEnd_720846 329013756329770595919907 := by
  unfold tailWord_720846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286426693313190942570799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17527609031003685027044261 3286426693313190942570799)
  ·
    refine ⟨4929640039969786413856199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3286426693313190942570799 4929640039969786413856199)
    ·
      refine ⟨7394460059954679620784299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4929640039969786413856199 7394460059954679620784299)
      ·
        refine ⟨11091690089932019431176449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7394460059954679620784299 11091690089932019431176449)
        ·
          refine ⟨8318767567449014573382337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11091690089932019431176449 8318767567449014573382337)
          ·
            refine ⟨6239075675586760930036753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8318767567449014573382337 6239075675586760930036753)
            ·
              refine ⟨4679306756690070697527565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6239075675586760930036753 4679306756690070697527565)
              ·
                refine ⟨1754740033758776511572837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4679306756690070697527565 1754740033758776511572837)
                ·
                  refine ⟨329013756329770595919907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1754740033758776511572837 329013756329770595919907)
                  ·
                    rfl

theorem cell20_720846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_720846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720846 prefixEnd_720846 := by exact prefixLift 720846
  have htrace : WordTrace (prefixWord ++ tailWord_720846) baseStart_720846 baseEnd_720846 := by
    simpa [prefixWord, tailWord_720846, baseEnd_720846] using wordTrace_append hprefix tailTrace_720846
  have hstable : (prefixWord ++ tailWord_720846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720846).length < 2 ^ (prefixWord ++ tailWord_720846).sum := by decide
  have hdescent : baseEnd_720846 < baseStart_720846 := by decide
  rcases family_descends (prefixWord ++ tailWord_720846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720866 : List Nat := [3, 3, 3, 1, 2, 1, 3, 4]
def baseStart_720866 : Nat := 118140960795 + 720866 * 2 ^ 59
def prefixEnd_720866 : Nat := 4983230072969 + 3 ^ 40 * 720866 * 2
def baseEnd_720866 : Nat := 109674294958246471751053

theorem tailTrace_720866 : CollatzResearch.WordTrace tailWord_720866 prefixEnd_720866 109674294958246471751053 := by
  unfold tailWord_720866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573035751608267739073613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17528095337622047304196301 6573035751608267739073613)
  ·
    refine ⟨2464888406853100402152605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6573035751608267739073613 2464888406853100402152605)
    ·
      refine ⟨924333152569912650807227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2464888406853100402152605 924333152569912650807227)
      ·
        refine ⟨1386499728854868976210841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924333152569912650807227 1386499728854868976210841)
        ·
          refine ⟨1039874796641151732158131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1386499728854868976210841 1039874796641151732158131)
          ·
            refine ⟨1559812194961727598237197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039874796641151732158131 1559812194961727598237197)
            ·
              refine ⟨584929573110647849338949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1559812194961727598237197 584929573110647849338949)
              ·
                refine ⟨109674294958246471751053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 584929573110647849338949 109674294958246471751053)
                ·
                  rfl

theorem cell20_720866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_720866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720866 prefixEnd_720866 := by exact prefixLift 720866
  have htrace : WordTrace (prefixWord ++ tailWord_720866) baseStart_720866 baseEnd_720866 := by
    simpa [prefixWord, tailWord_720866, baseEnd_720866] using wordTrace_append hprefix tailTrace_720866
  have hstable : (prefixWord ++ tailWord_720866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720866).length < 2 ^ (prefixWord ++ tailWord_720866).sum := by decide
  have hdescent : baseEnd_720866 < baseStart_720866 := by decide
  rcases family_descends (prefixWord ++ tailWord_720866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720894 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_720894 : Nat := 118140960795 + 720894 * 2 ^ 59
def prefixEnd_720894 : Nat := 4983230072969 + 3 ^ 40 * 720894 * 2
def baseEnd_720894 : Nat := 329035664837695762319711

theorem tailTrace_720894 : CollatzResearch.WordTrace tailWord_720894 prefixEnd_720894 329035664837695762319711 := by
  unfold tailWord_720894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286645531291453967289217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17528776166887754492209157 3286645531291453967289217)
  ·
    refine ⟨2464984148468590475466913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3286645531291453967289217 2464984148468590475466913)
    ·
      refine ⟨1848738111351442856600185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2464984148468590475466913 1848738111351442856600185)
      ·
        refine ⟨1386553583513582142450139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1848738111351442856600185 1386553583513582142450139)
        ·
          refine ⟨2079830375270373213675209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386553583513582142450139 2079830375270373213675209)
          ·
            refine ⟨1559872781452779910256407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2079830375270373213675209 1559872781452779910256407)
            ·
              refine ⟨2339809172179169865384611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559872781452779910256407 2339809172179169865384611)
              ·
                refine ⟨3509713758268754798076917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339809172179169865384611 3509713758268754798076917)
                ·
                  refine ⟨329035664837695762319711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3509713758268754798076917 329035664837695762319711)
                  ·
                    rfl

theorem cell20_720894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_720894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720894 prefixEnd_720894 := by exact prefixLift 720894
  have htrace : WordTrace (prefixWord ++ tailWord_720894) baseStart_720894 baseEnd_720894 := by
    simpa [prefixWord, tailWord_720894, baseEnd_720894] using wordTrace_append hprefix tailTrace_720894
  have hstable : (prefixWord ++ tailWord_720894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720894).length < 2 ^ (prefixWord ++ tailWord_720894).sum := by decide
  have hdescent : baseEnd_720894 < baseStart_720894 := by decide
  rcases family_descends (prefixWord ++ tailWord_720894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720901 : List Nat := [1, 3, 1, 1, 2, 4, 2, 4, 2]
def baseStart_720901 : Nat := 118140960795 + 720901 * 2 ^ 59
def prefixEnd_720901 : Nat := 4983230072969 + 3 ^ 40 * 720901 * 2
def baseEnd_720901 : Nat := 329038859828434849086349

theorem tailTrace_720901 : CollatzResearch.WordTrace tailWord_720901 prefixEnd_720901 329038859828434849086349 := by
  unfold tailWord_720901
  simp only [CollatzResearch.WordTrace]
  refine ⟨26293419561306271933818557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17528946374204181289212371 26293419561306271933818557)
  ·
    refine ⟨9860032335489851975181959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26293419561306271933818557 9860032335489851975181959)
    ·
      refine ⟨14790048503234777962772939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9860032335489851975181959 14790048503234777962772939)
      ·
        refine ⟨22185072754852166944159409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14790048503234777962772939 22185072754852166944159409)
        ·
          refine ⟨16638804566139125208119557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22185072754852166944159409 16638804566139125208119557)
          ·
            refine ⟨3119775856151085976522417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16638804566139125208119557 3119775856151085976522417)
            ·
              refine ⟨2339831892113314482391813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119775856151085976522417 2339831892113314482391813)
              ·
                refine ⟨438718479771246465448465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2339831892113314482391813 438718479771246465448465)
                ·
                  refine ⟨329038859828434849086349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438718479771246465448465 329038859828434849086349)
                  ·
                    rfl

theorem cell20_720901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_720901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720901 prefixEnd_720901 := by exact prefixLift 720901
  have htrace : WordTrace (prefixWord ++ tailWord_720901) baseStart_720901 baseEnd_720901 := by
    simpa [prefixWord, tailWord_720901, baseEnd_720901] using wordTrace_append hprefix tailTrace_720901
  have hstable : (prefixWord ++ tailWord_720901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720901).length < 2 ^ (prefixWord ++ tailWord_720901).sum := by decide
  have hdescent : baseEnd_720901 < baseStart_720901 := by decide
  rcases family_descends (prefixWord ++ tailWord_720901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720922 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_720922 : Nat := 118140960795 + 720922 * 2 ^ 59
def prefixEnd_720922 : Nat := 4983230072969 + 3 ^ 40 * 720922 * 2
def baseEnd_720922 : Nat := 329048444800652109386263

theorem tailTrace_720922 : CollatzResearch.WordTrace tailWord_720922 prefixEnd_720922 329048444800652109386263 := by
  unfold tailWord_720922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573546373557548130083255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17529456996153461680222013 6573546373557548130083255)
  ·
    refine ⟨9860319560336322195124883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6573546373557548130083255 9860319560336322195124883)
    ·
      refine ⟨14790479340504483292687325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9860319560336322195124883 14790479340504483292687325)
      ·
        refine ⟨5546429752689181234757747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14790479340504483292687325 5546429752689181234757747)
        ·
          refine ⟨8319644629033771852136621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5546429752689181234757747 8319644629033771852136621)
          ·
            refine ⟨3119866735887664444551233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8319644629033771852136621 3119866735887664444551233)
            ·
              refine ⟨2339900051915748333413425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119866735887664444551233 2339900051915748333413425)
              ·
                refine ⟨1754925038936811250060069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339900051915748333413425 1754925038936811250060069)
                ·
                  refine ⟨329048444800652109386263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1754925038936811250060069 329048444800652109386263)
                  ·
                    rfl

theorem cell20_720922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_720922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720922 prefixEnd_720922 := by exact prefixLift 720922
  have htrace : WordTrace (prefixWord ++ tailWord_720922) baseStart_720922 baseEnd_720922 := by
    simpa [prefixWord, tailWord_720922, baseEnd_720922] using wordTrace_append hprefix tailTrace_720922
  have hstable : (prefixWord ++ tailWord_720922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720922).length < 2 ^ (prefixWord ++ tailWord_720922).sum := by decide
  have hdescent : baseEnd_720922 < baseStart_720922 := by decide
  rcases family_descends (prefixWord ++ tailWord_720922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720925 : List Nat := [1, 4, 2, 2, 2, 3, 2, 4]
def baseStart_720925 : Nat := 118140960795 + 720925 * 2 ^ 59
def prefixEnd_720925 : Nat := 4983230072969 + 3 ^ 40 * 720925 * 2
def baseEnd_720925 : Nat := 109683271360799144095417

theorem tailTrace_720925 : CollatzResearch.WordTrace tailWord_720925 prefixEnd_720925 109683271360799144095417 := by
  unfold tailWord_720925
  simp only [CollatzResearch.WordTrace]
  refine ⟨26294294913219324032692229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17529529942146216021794819 26294294913219324032692229)
  ·
    refine ⟨4930180296228623256129793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26294294913219324032692229 4930180296228623256129793)
    ·
      refine ⟨3697635222171467442097345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4930180296228623256129793 3697635222171467442097345)
      ·
        refine ⟨2773226416628600581573009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3697635222171467442097345 2773226416628600581573009)
        ·
          refine ⟨2079919812471450436179757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2773226416628600581573009 2079919812471450436179757)
          ·
            refine ⟨779969929676793913567409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2079919812471450436179757 779969929676793913567409)
            ·
              refine ⟨584977447257595435175557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779969929676793913567409 584977447257595435175557)
              ·
                refine ⟨109683271360799144095417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 584977447257595435175557 109683271360799144095417)
                ·
                  rfl

theorem cell20_720925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 4].length) (baseStart_720925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720925 prefixEnd_720925 := by exact prefixLift 720925
  have htrace : WordTrace (prefixWord ++ tailWord_720925) baseStart_720925 baseEnd_720925 := by
    simpa [prefixWord, tailWord_720925, baseEnd_720925] using wordTrace_append hprefix tailTrace_720925
  have hstable : (prefixWord ++ tailWord_720925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720925).length < 2 ^ (prefixWord ++ tailWord_720925).sum := by decide
  have hdescent : baseEnd_720925 < baseStart_720925 := by decide
  rcases family_descends (prefixWord ++ tailWord_720925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720956 : List Nat := [2, 2, 2, 2, 2, 1, 5, 2, 2]
def baseStart_720956 : Nat := 118140960795 + 720956 * 2 ^ 59
def prefixEnd_720956 : Nat := 4983230072969 + 3 ^ 40 * 720956 * 2
def baseEnd_720956 : Nat := 329063963327099102252791

theorem tailTrace_720956 : CollatzResearch.WordTrace tailWord_720956 prefixEnd_720956 329063963327099102252791 := by
  unfold tailWord_720956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147712788053508163535361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17530283717404677551380481 13147712788053508163535361)
  ·
    refine ⟨9860784591040131122651521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13147712788053508163535361 9860784591040131122651521)
    ·
      refine ⟨7395588443280098341988641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9860784591040131122651521 7395588443280098341988641)
      ·
        refine ⟨5546691332460073756491481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7395588443280098341988641 5546691332460073756491481)
        ·
          refine ⟨4160018499345055317368611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5546691332460073756491481 4160018499345055317368611)
          ·
            refine ⟨6240027749017582976052917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160018499345055317368611 6240027749017582976052917)
            ·
              refine ⟨585002601470398404004961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6240027749017582976052917 585002601470398404004961)
              ·
                refine ⟨438751951102798803003721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585002601470398404004961 438751951102798803003721)
                ·
                  refine ⟨329063963327099102252791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438751951102798803003721 329063963327099102252791)
                  ·
                    rfl

theorem cell20_720956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_720956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720956 prefixEnd_720956 := by exact prefixLift 720956
  have htrace : WordTrace (prefixWord ++ tailWord_720956) baseStart_720956 baseEnd_720956 := by
    simpa [prefixWord, tailWord_720956, baseEnd_720956] using wordTrace_append hprefix tailTrace_720956
  have hstable : (prefixWord ++ tailWord_720956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720956).length < 2 ^ (prefixWord ++ tailWord_720956).sum := by decide
  have hdescent : baseEnd_720956 < baseStart_720956 := by decide
  rcases family_descends (prefixWord ++ tailWord_720956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720960 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_720960 : Nat := 118140960795 + 720960 * 2 ^ 59
def prefixEnd_720960 : Nat := 4983230072969 + 3 ^ 40 * 720960 * 2
def baseEnd_720960 : Nat := 329065789036092866119441

theorem tailTrace_720960 : CollatzResearch.WordTrace tailWord_720960 prefixEnd_720960 329065789036092866119441 := by
  unfold tailWord_720960
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147785734046262505108167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17530380978728350006810889 13147785734046262505108167)
  ·
    refine ⟨19721678601069393757662251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13147785734046262505108167 19721678601069393757662251)
    ·
      refine ⟨29582517901604090636493377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19721678601069393757662251 29582517901604090636493377)
      ·
        refine ⟨22186888426203067977370033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29582517901604090636493377 22186888426203067977370033)
        ·
          refine ⟨16640166319652300983027525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22186888426203067977370033 16640166319652300983027525)
          ·
            refine ⟨3120031184934806434317661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16640166319652300983027525 3120031184934806434317661)
            ·
              refine ⟨1170011694350552412869123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3120031184934806434317661 1170011694350552412869123)
              ·
                refine ⟨1755017541525828619303685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170011694350552412869123 1755017541525828619303685)
                ·
                  refine ⟨329065789036092866119441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755017541525828619303685 329065789036092866119441)
                  ·
                    rfl

theorem cell20_720960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_720960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720960 prefixEnd_720960 := by exact prefixLift 720960
  have htrace : WordTrace (prefixWord ++ tailWord_720960) baseStart_720960 baseEnd_720960 := by
    simpa [prefixWord, tailWord_720960, baseEnd_720960] using wordTrace_append hprefix tailTrace_720960
  have hstable : (prefixWord ++ tailWord_720960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720960).length < 2 ^ (prefixWord ++ tailWord_720960).sum := by decide
  have hdescent : baseEnd_720960 < baseStart_720960 := by decide
  rcases family_descends (prefixWord ++ tailWord_720960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720967 : List Nat := [1, 1, 4, 1, 3, 1, 4, 5]
def baseStart_720967 : Nat := 118140960795 + 720967 * 2 ^ 59
def prefixEnd_720967 : Nat := 4983230072969 + 3 ^ 40 * 720967 * 2
def baseEnd_720967 : Nat := 109689661342277317628693

theorem tailTrace_720967 : CollatzResearch.WordTrace tailWord_720967 prefixEnd_720967 109689661342277317628693 := by
  unfold tailWord_720967
  simp only [CollatzResearch.WordTrace]
  refine ⟨26295826779067165205721155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17530551186044776803814103 26295826779067165205721155)
  ·
    refine ⟨39443740168600747808581733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26295826779067165205721155 39443740168600747808581733)
    ·
      refine ⟨7395701281612640214109075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39443740168600747808581733 7395701281612640214109075)
      ·
        refine ⟨11093551922418960321163613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395701281612640214109075 11093551922418960321163613)
        ·
          refine ⟨4160081970907110120436355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11093551922418960321163613 4160081970907110120436355)
          ·
            refine ⟨6240122956360665180654533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160081970907110120436355 6240122956360665180654533)
            ·
              refine ⟨1170023054317624721372725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6240122956360665180654533 1170023054317624721372725)
              ·
                refine ⟨109689661342277317628693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1170023054317624721372725 109689661342277317628693)
                ·
                  rfl

theorem cell20_720967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 5].length) (baseStart_720967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_720967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_720967 prefixEnd_720967 := by exact prefixLift 720967
  have htrace : WordTrace (prefixWord ++ tailWord_720967) baseStart_720967 baseEnd_720967 := by
    simpa [prefixWord, tailWord_720967, baseEnd_720967] using wordTrace_append hprefix tailTrace_720967
  have hstable : (prefixWord ++ tailWord_720967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720967).length < 2 ^ (prefixWord ++ tailWord_720967).sum := by decide
  have hdescent : baseEnd_720967 < baseStart_720967 := by decide
  rcases family_descends (prefixWord ++ tailWord_720967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721015 : List Nat := [1, 1, 3, 1, 1, 6, 1, 4, 2]
def baseStart_721015 : Nat := 118140960795 + 721015 * 2 ^ 59
def prefixEnd_721015 : Nat := 4983230072969 + 3 ^ 40 * 721015 * 2
def baseEnd_721015 : Nat := 329090892534757119285883

theorem tailTrace_721015 : CollatzResearch.WordTrace tailWord_721015 prefixEnd_721015 329090892534757119285883 := by
  unfold tailWord_721015
  simp only [CollatzResearch.WordTrace]
  refine ⟨26297577482893269403468499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17531718321928846268978999 26297577482893269403468499)
  ·
    refine ⟨39446366224339904105202749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26297577482893269403468499 39446366224339904105202749)
    ·
      refine ⟨14792387334127464039451031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39446366224339904105202749 14792387334127464039451031)
      ·
        refine ⟨22188581001191196059176547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14792387334127464039451031 22188581001191196059176547)
        ·
          refine ⟨33282871501786794088764821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22188581001191196059176547 33282871501786794088764821)
          ·
            refine ⟨1560134601646255972910851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33282871501786794088764821 1560134601646255972910851)
            ·
              refine ⟨2340201902469383959366277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560134601646255972910851 2340201902469383959366277)
              ·
                refine ⟨438787856713009492381177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2340201902469383959366277 438787856713009492381177)
                ·
                  refine ⟨329090892534757119285883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438787856713009492381177 329090892534757119285883)
                  ·
                    rfl

theorem cell20_721015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 2].length) (baseStart_721015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721015 prefixEnd_721015 := by exact prefixLift 721015
  have htrace : WordTrace (prefixWord ++ tailWord_721015) baseStart_721015 baseEnd_721015 := by
    simpa [prefixWord, tailWord_721015, baseEnd_721015] using wordTrace_append hprefix tailTrace_721015
  have hstable : (prefixWord ++ tailWord_721015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721015).length < 2 ^ (prefixWord ++ tailWord_721015).sum := by decide
  have hdescent : baseEnd_721015 < baseStart_721015 := by decide
  rcases family_descends (prefixWord ++ tailWord_721015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721029 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 3]
def baseStart_721029 : Nat := 118140960795 + 721029 * 2 ^ 59
def prefixEnd_721029 : Nat := 4983230072969 + 3 ^ 40 * 721029 * 2
def baseEnd_721029 : Nat := 329097282516235292819159

theorem tailTrace_721029 : CollatzResearch.WordTrace tailWord_721029 prefixEnd_721029 329097282516235292819159 := by
  unfold tailWord_721029
  simp only [CollatzResearch.WordTrace]
  refine ⟨26298088104842549794478141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17532058736561699862985427 26298088104842549794478141)
  ·
    refine ⟨9861783039315956172929303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26298088104842549794478141 9861783039315956172929303)
    ·
      refine ⟨14792674558973934259393955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9861783039315956172929303 14792674558973934259393955)
      ·
        refine ⟨22189011838460901389090933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14792674558973934259393955 22189011838460901389090933)
        ·
          refine ⟨2080219859855709505227275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22189011838460901389090933 2080219859855709505227275)
          ·
            refine ⟨3120329789783564257840913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080219859855709505227275 3120329789783564257840913)
            ·
              refine ⟨2340247342337673193380685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120329789783564257840913 2340247342337673193380685)
              ·
                refine ⟨877592753376627447517757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2340247342337673193380685 877592753376627447517757)
                ·
                  refine ⟨329097282516235292819159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877592753376627447517757 329097282516235292819159)
                  ·
                    rfl

theorem cell20_721029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_721029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721029 prefixEnd_721029 := by exact prefixLift 721029
  have htrace : WordTrace (prefixWord ++ tailWord_721029) baseStart_721029 baseEnd_721029 := by
    simpa [prefixWord, tailWord_721029, baseEnd_721029] using wordTrace_append hprefix tailTrace_721029
  have hstable : (prefixWord ++ tailWord_721029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721029).length < 2 ^ (prefixWord ++ tailWord_721029).sum := by decide
  have hdescent : baseEnd_721029 < baseStart_721029 := by decide
  rcases family_descends (prefixWord ++ tailWord_721029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721053 : List Nat := [1, 4, 2, 1, 1, 3, 1, 5, 2]
def baseStart_721053 : Nat := 118140960795 + 721053 * 2 ^ 59
def prefixEnd_721053 : Nat := 4983230072969 + 3 ^ 40 * 721053 * 2
def baseEnd_721053 : Nat := 329108236770197876019061

theorem tailTrace_721053 : CollatzResearch.WordTrace tailWord_721053 prefixEnd_721053 329108236770197876019061 := by
  unfold tailWord_721053
  simp only [CollatzResearch.WordTrace]
  refine ⟨26298963456755601893351813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17532642304503734595567875 26298963456755601893351813)
  ·
    refine ⟨4931055648141675355003465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26298963456755601893351813 4931055648141675355003465)
    ·
      refine ⟨3698291736106256516252599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4931055648141675355003465 3698291736106256516252599)
      ·
        refine ⟨5547437604159384774378899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3698291736106256516252599 5547437604159384774378899)
        ·
          refine ⟨8321156406239077161568349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5547437604159384774378899 8321156406239077161568349)
          ·
            refine ⟨3120433652339653935588131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8321156406239077161568349 3120433652339653935588131)
            ·
              refine ⟨4680650478509480903382197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120433652339653935588131 4680650478509480903382197)
              ·
                refine ⟨438810982360263834692081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4680650478509480903382197 438810982360263834692081)
                ·
                  refine ⟨329108236770197876019061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438810982360263834692081 329108236770197876019061)
                  ·
                    rfl

theorem cell20_721053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_721053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721053 prefixEnd_721053 := by exact prefixLift 721053
  have htrace : WordTrace (prefixWord ++ tailWord_721053) baseStart_721053 baseEnd_721053 := by
    simpa [prefixWord, tailWord_721053, baseEnd_721053] using wordTrace_append hprefix tailTrace_721053
  have hstable : (prefixWord ++ tailWord_721053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721053).length < 2 ^ (prefixWord ++ tailWord_721053).sum := by decide
  have hdescent : baseEnd_721053 < baseStart_721053 := by decide
  rcases family_descends (prefixWord ++ tailWord_721053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721063 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 3]
def baseStart_721063 : Nat := 118140960795 + 721063 * 2 ^ 59
def prefixEnd_721063 : Nat := 4983230072969 + 3 ^ 40 * 721063 * 2
def baseEnd_721063 : Nat := 329112801042682285685687

theorem tailTrace_721063 : CollatzResearch.WordTrace tailWord_721063 prefixEnd_721063 329112801042682285685687 := by
  unfold tailWord_721063
  simp only [CollatzResearch.WordTrace]
  refine ⟨26299328186719373601215843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17532885457812915734143895 26299328186719373601215843)
  ·
    refine ⟨39448992280079060401823765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26299328186719373601215843 39448992280079060401823765)
    ·
      refine ⟨1849171513128705956335489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39448992280079060401823765 1849171513128705956335489)
      ·
        refine ⟨1386878634846529467251617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1849171513128705956335489 1386878634846529467251617)
        ·
          refine ⟨1040158976134897100438713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1386878634846529467251617 1040158976134897100438713)
          ·
            refine ⟨780119232101172825329035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1040158976134897100438713 780119232101172825329035)
            ·
              refine ⟨1170178848151759237993553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780119232101172825329035 1170178848151759237993553)
              ·
                refine ⟨877634136113819428495165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170178848151759237993553 877634136113819428495165)
                ·
                  refine ⟨329112801042682285685687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877634136113819428495165 329112801042682285685687)
                  ·
                    rfl

theorem cell20_721063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 3].length) (baseStart_721063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721063 prefixEnd_721063 := by exact prefixLift 721063
  have htrace : WordTrace (prefixWord ++ tailWord_721063) baseStart_721063 baseEnd_721063 := by
    simpa [prefixWord, tailWord_721063, baseEnd_721063] using wordTrace_append hprefix tailTrace_721063
  have hstable : (prefixWord ++ tailWord_721063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721063).length < 2 ^ (prefixWord ++ tailWord_721063).sum := by decide
  have hdescent : baseEnd_721063 < baseStart_721063 := by decide
  rcases family_descends (prefixWord ++ tailWord_721063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721074 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_721074 : Nat := 118140960795 + 721074 * 2 ^ 59
def prefixEnd_721074 : Nat := 4983230072969 + 3 ^ 40 * 721074 * 2
def baseEnd_721074 : Nat := 329117821742415136318975

theorem tailTrace_721074 : CollatzResearch.WordTrace tailWord_721074 prefixEnd_721074 329117821742415136318975 := by
  unfold tailWord_721074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574932347419880619966569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17533152926453014986577517 6574932347419880619966569)
  ·
    refine ⟨4931199260564910464974927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6574932347419880619966569 4931199260564910464974927)
    ·
      refine ⟨7396798890847365697462391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4931199260564910464974927 7396798890847365697462391)
      ·
        refine ⟨11095198336271048546193587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7396798890847365697462391 11095198336271048546193587)
        ·
          refine ⟨16642797504406572819290381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11095198336271048546193587 16642797504406572819290381)
          ·
            refine ⟨6241049064152464807233893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16642797504406572819290381 6241049064152464807233893)
            ·
              refine ⟨1170196699528587151356355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6241049064152464807233893 1170196699528587151356355)
              ·
                refine ⟨1755295049292880727034533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170196699528587151356355 1755295049292880727034533)
                ·
                  refine ⟨329117821742415136318975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755295049292880727034533 329117821742415136318975)
                  ·
                    rfl

theorem cell20_721074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_721074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721074 prefixEnd_721074 := by exact prefixLift 721074
  have htrace : WordTrace (prefixWord ++ tailWord_721074) baseStart_721074 baseEnd_721074 := by
    simpa [prefixWord, tailWord_721074, baseEnd_721074] using wordTrace_append hprefix tailTrace_721074
  have hstable : (prefixWord ++ tailWord_721074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721074).length < 2 ^ (prefixWord ++ tailWord_721074).sum := by decide
  have hdescent : baseEnd_721074 < baseStart_721074 := by decide
  rcases family_descends (prefixWord ++ tailWord_721074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721150 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_721150 : Nat := 118140960795 + 721150 * 2 ^ 59
def prefixEnd_721150 : Nat := 4983230072969 + 3 ^ 40 * 721150 * 2
def baseEnd_721150 : Nat := 329152510213296649785331

theorem tailTrace_721150 : CollatzResearch.WordTrace tailWord_721150 prefixEnd_721150 329152510213296649785331 := by
  unfold tailWord_721150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287812667175523432454113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17535000891602791639755269 3287812667175523432454113)
  ·
    refine ⟨2465859500381642574340585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3287812667175523432454113 2465859500381642574340585)
    ·
      refine ⟨1849394625286231930755439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2465859500381642574340585 1849394625286231930755439)
      ·
        refine ⟨2774091937929347896133159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849394625286231930755439 2774091937929347896133159)
        ·
          refine ⟨4161137906894021844199739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774091937929347896133159 4161137906894021844199739)
          ·
            refine ⟨6241706860341032766299609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161137906894021844199739 6241706860341032766299609)
            ·
              refine ⟨4681280145255774574724707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6241706860341032766299609 4681280145255774574724707)
              ·
                refine ⟨7021920217883661862087061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4681280145255774574724707 7021920217883661862087061)
                ·
                  refine ⟨329152510213296649785331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7021920217883661862087061 329152510213296649785331)
                  ·
                    rfl

theorem cell20_721150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_721150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721150 prefixEnd_721150 := by exact prefixLift 721150
  have htrace : WordTrace (prefixWord ++ tailWord_721150) baseStart_721150 baseEnd_721150 := by
    simpa [prefixWord, tailWord_721150, baseEnd_721150] using wordTrace_append hprefix tailTrace_721150
  have hstable : (prefixWord ++ tailWord_721150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721150).length < 2 ^ (prefixWord ++ tailWord_721150).sum := by decide
  have hdescent : baseEnd_721150 < baseStart_721150 := by decide
  rcases family_descends (prefixWord ++ tailWord_721150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721178 : List Nat := [3, 1, 1, 3, 12]
def baseStart_721178 : Nat := 118140960795 + 721178 * 2 ^ 59
def prefixEnd_721178 : Nat := 4983230072969 + 3 ^ 40 * 721178 * 2
def baseEnd_721178 : Nat := 4063769014521641936443

theorem tailTrace_721178 : CollatzResearch.WordTrace tailWord_721178 prefixEnd_721178 4063769014521641936443 := by
  unfold tailWord_721178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575880645325687060413047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17535681720868498827768125 6575880645325687060413047)
  ·
    refine ⟨9863820967988530590619571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6575880645325687060413047 9863820967988530590619571)
    ·
      refine ⟨14795731451982795885929357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9863820967988530590619571 14795731451982795885929357)
      ·
        refine ⟨5548399294493548457223509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14795731451982795885929357 5548399294493548457223509)
        ·
          refine ⟨4063769014521641936443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5548399294493548457223509 4063769014521641936443)
          ·
            rfl

theorem cell20_721178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 12].length) (baseStart_721178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721178 prefixEnd_721178 := by exact prefixLift 721178
  have htrace : WordTrace (prefixWord ++ tailWord_721178) baseStart_721178 baseEnd_721178 := by
    simpa [prefixWord, tailWord_721178, baseEnd_721178] using wordTrace_append hprefix tailTrace_721178
  have hstable : (prefixWord ++ tailWord_721178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721178).length < 2 ^ (prefixWord ++ tailWord_721178).sum := by decide
  have hdescent : baseEnd_721178 < baseStart_721178 := by decide
  rcases family_descends (prefixWord ++ tailWord_721178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721184 : List Nat := [2, 1, 1, 5, 2, 1, 4, 2, 2]
def baseStart_721184 : Nat := 118140960795 + 721184 * 2 ^ 59
def prefixEnd_721184 : Nat := 4983230072969 + 3 ^ 40 * 721184 * 2
def baseEnd_721184 : Nat := 329168028739743642651859

theorem tailTrace_721184 : CollatzResearch.WordTrace tailWord_721184 prefixEnd_721184 329168028739743642651859 := by
  unfold tailWord_721184
  simp only [CollatzResearch.WordTrace]
  refine ⟨13151870709640505633185303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17535827612854007510913737 13151870709640505633185303)
  ·
    refine ⟨19727806064460758449777955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13151870709640505633185303 19727806064460758449777955)
    ·
      refine ⟨29591709096691137674666933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19727806064460758449777955 29591709096691137674666933)
      ·
        refine ⟨2774222727814794157000025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29591709096691137674666933 2774222727814794157000025)
        ·
          refine ⟨2080667045861095617750019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2774222727814794157000025 2080667045861095617750019)
          ·
            refine ⟨3121000568791643426625029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080667045861095617750019 3121000568791643426625029)
            ·
              refine ⟨585187606648433142492193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3121000568791643426625029 585187606648433142492193)
              ·
                refine ⟨438890704986324856869145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585187606648433142492193 438890704986324856869145)
                ·
                  refine ⟨329168028739743642651859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438890704986324856869145 329168028739743642651859)
                  ·
                    rfl

theorem cell20_721184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_721184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721184 prefixEnd_721184 := by exact prefixLift 721184
  have htrace : WordTrace (prefixWord ++ tailWord_721184) baseStart_721184 baseEnd_721184 := by
    simpa [prefixWord, tailWord_721184, baseEnd_721184] using wordTrace_append hprefix tailTrace_721184
  have hstable : (prefixWord ++ tailWord_721184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721184).length < 2 ^ (prefixWord ++ tailWord_721184).sum := by decide
  have hdescent : baseEnd_721184 < baseStart_721184 := by decide
  rcases family_descends (prefixWord ++ tailWord_721184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721236 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_721236 : Nat := 118140960795 + 721236 * 2 ^ 59
def prefixEnd_721236 : Nat := 4983230072969 + 3 ^ 40 * 721236 * 2
def baseEnd_721236 : Nat := 329191762956662572918313

theorem tailTrace_721236 : CollatzResearch.WordTrace tailWord_721236 prefixEnd_721236 329191762956662572918313 := by
  unfold tailWord_721236
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152819007546312073631781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17537092010061749431509041 13152819007546312073631781)
  ·
    refine ⟨2466153563914933513805959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13152819007546312073631781 2466153563914933513805959)
    ·
      refine ⟨3699230345872400270708939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2466153563914933513805959 3699230345872400270708939)
      ·
        refine ⟨5548845518808600406063409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699230345872400270708939 5548845518808600406063409)
        ·
          refine ⟨4161634139106450304547557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5548845518808600406063409 4161634139106450304547557)
          ·
            refine ⟨780306401082459432102667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4161634139106450304547557 780306401082459432102667)
            ·
              refine ⟨1170459601623689148154001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780306401082459432102667 1170459601623689148154001)
              ·
                refine ⟨877844701217766861115501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170459601623689148154001 877844701217766861115501)
                ·
                  refine ⟨329191762956662572918313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877844701217766861115501 329191762956662572918313)
                  ·
                    rfl

theorem cell20_721236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_721236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721236 prefixEnd_721236 := by exact prefixLift 721236
  have htrace : WordTrace (prefixWord ++ tailWord_721236) baseStart_721236 baseEnd_721236 := by
    simpa [prefixWord, tailWord_721236, baseEnd_721236] using wordTrace_append hprefix tailTrace_721236
  have hstable : (prefixWord ++ tailWord_721236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721236).length < 2 ^ (prefixWord ++ tailWord_721236).sum := by decide
  have hdescent : baseEnd_721236 < baseStart_721236 := by decide
  rcases family_descends (prefixWord ++ tailWord_721236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721240 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_721240 : Nat := 118140960795 + 721240 * 2 ^ 59
def prefixEnd_721240 : Nat := 4983230072969 + 3 ^ 40 * 721240 * 2
def baseEnd_721240 : Nat := 329193588665656336784963

theorem tailTrace_721240 : CollatzResearch.WordTrace tailWord_721240 prefixEnd_721240 329193588665656336784963 := by
  unfold tailWord_721240
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152891953539066415204587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17537189271385421886939449 13152891953539066415204587)
  ·
    refine ⟨19729337930308599622806881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13152891953539066415204587 19729337930308599622806881)
    ·
      refine ⟨14797003447731449717105161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19729337930308599622806881 14797003447731449717105161)
      ·
        refine ⟨11097752585798587287828871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14797003447731449717105161 11097752585798587287828871)
        ·
          refine ⟨16646628878697880931743307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11097752585798587287828871 16646628878697880931743307)
          ·
            refine ⟨24969943318046821397614961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16646628878697880931743307 24969943318046821397614961)
            ·
              refine ⟨18727457488535116048211221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24969943318046821397614961 18727457488535116048211221)
              ·
                refine ⟨877849569775083564759901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18727457488535116048211221 877849569775083564759901)
                ·
                  refine ⟨329193588665656336784963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877849569775083564759901 329193588665656336784963)
                  ·
                    rfl

theorem cell20_721240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_721240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721240 prefixEnd_721240 := by exact prefixLift 721240
  have htrace : WordTrace (prefixWord ++ tailWord_721240) baseStart_721240 baseEnd_721240 := by
    simpa [prefixWord, tailWord_721240, baseEnd_721240] using wordTrace_append hprefix tailTrace_721240
  have hstable : (prefixWord ++ tailWord_721240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721240).length < 2 ^ (prefixWord ++ tailWord_721240).sum := by decide
  have hdescent : baseEnd_721240 < baseStart_721240 := by decide
  rcases family_descends (prefixWord ++ tailWord_721240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721247 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 4]
def baseStart_721247 : Nat := 118140960795 + 721247 * 2 ^ 59
def prefixEnd_721247 : Nat := 4983230072969 + 3 ^ 40 * 721247 * 2
def baseEnd_721247 : Nat := 329196783656395423551601

theorem tailTrace_721247 : CollatzResearch.WordTrace tailWord_721247 prefixEnd_721247 329196783656395423551601 := by
  unfold tailWord_721247
  simp only [CollatzResearch.WordTrace]
  refine ⟨26306039218052773025913995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17537359478701848683942663 26306039218052773025913995)
  ·
    refine ⟨39459058827079159538870993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26306039218052773025913995 39459058827079159538870993)
    ·
      refine ⟨29594294120309369654153245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39459058827079159538870993 29594294120309369654153245)
      ·
        refine ⟨11097860295116013620307467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29594294120309369654153245 11097860295116013620307467)
        ·
          refine ⟨16646790442674020430461201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11097860295116013620307467 16646790442674020430461201)
          ·
            refine ⟨12485092832005515322845901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16646790442674020430461201 12485092832005515322845901)
            ·
              refine ⟨4681909812002068246067213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12485092832005515322845901 4681909812002068246067213)
              ·
                refine ⟨1755716179500775592275205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4681909812002068246067213 1755716179500775592275205)
                ·
                  refine ⟨329196783656395423551601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755716179500775592275205 329196783656395423551601)
                  ·
                    rfl

theorem cell20_721247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_721247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721247 prefixEnd_721247 := by exact prefixLift 721247
  have htrace : WordTrace (prefixWord ++ tailWord_721247) baseStart_721247 baseEnd_721247 := by
    simpa [prefixWord, tailWord_721247, baseEnd_721247] using wordTrace_append hprefix tailTrace_721247
  have hstable : (prefixWord ++ tailWord_721247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721247).length < 2 ^ (prefixWord ++ tailWord_721247).sum := by decide
  have hdescent : baseEnd_721247 < baseStart_721247 := by decide
  rcases family_descends (prefixWord ++ tailWord_721247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721257 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 3]
def baseStart_721257 : Nat := 118140960795 + 721257 * 2 ^ 59
def prefixEnd_721257 : Nat := 4983230072969 + 3 ^ 40 * 721257 * 2
def baseEnd_721257 : Nat := 329201347928879833218227

theorem tailTrace_721257 : CollatzResearch.WordTrace tailWord_721257 prefixEnd_721257 329201347928879833218227 := by
  unfold tailWord_721257
  simp only [CollatzResearch.WordTrace]
  refine ⟨26306403948016544733778025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17537602632011029822518683 26306403948016544733778025)
  ·
    refine ⟨19729802961012408550333519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26306403948016544733778025 19729802961012408550333519)
    ·
      refine ⟨29594704441518612825500279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19729802961012408550333519 29594704441518612825500279)
      ·
        refine ⟨44392056662277919238250419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29594704441518612825500279 44392056662277919238250419)
        ·
          refine ⟨66588084993416878857375629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44392056662277919238250419 66588084993416878857375629)
          ·
            refine ⟨24970531872531329571515861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66588084993416878857375629 24970531872531329571515861)
            ·
              refine ⟨585246840762453036832403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24970531872531329571515861 585246840762453036832403)
              ·
                refine ⟨877870261143679555248605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585246840762453036832403 877870261143679555248605)
                ·
                  refine ⟨329201347928879833218227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877870261143679555248605 329201347928879833218227)
                  ·
                    rfl

theorem cell20_721257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_721257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721257 prefixEnd_721257 := by exact prefixLift 721257
  have htrace : WordTrace (prefixWord ++ tailWord_721257) baseStart_721257 baseEnd_721257 := by
    simpa [prefixWord, tailWord_721257, baseEnd_721257] using wordTrace_append hprefix tailTrace_721257
  have hstable : (prefixWord ++ tailWord_721257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721257).length < 2 ^ (prefixWord ++ tailWord_721257).sum := by decide
  have hdescent : baseEnd_721257 < baseStart_721257 := by decide
  rcases family_descends (prefixWord ++ tailWord_721257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721292 : List Nat := [2, 2, 1, 2, 1, 4, 8]
def baseStart_721292 : Nat := 118140960795 + 721292 * 2 ^ 59
def prefixEnd_721292 : Nat := 4983230072969 + 3 ^ 40 * 721292 * 2
def baseEnd_721292 : Nat := 36579702542508363005713

theorem tailTrace_721292 : CollatzResearch.WordTrace tailWord_721292 prefixEnd_721292 36579702542508363005713 := by
  unfold tailWord_721292
  simp only [CollatzResearch.WordTrace]
  refine ⟨13153840251444872855651065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17538453668593163807534753 13153840251444872855651065)
  ·
    refine ⟨9865380188583654641738299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13153840251444872855651065 9865380188583654641738299)
    ·
      refine ⟨14798070282875481962607449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9865380188583654641738299 14798070282875481962607449)
      ·
        refine ⟨11098552712156611471955587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14798070282875481962607449 11098552712156611471955587)
        ·
          refine ⟨16647829068234917207933381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11098552712156611471955587 16647829068234917207933381)
          ·
            refine ⟨3121467950294046976487509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16647829068234917207933381 3121467950294046976487509)
            ·
              refine ⟨36579702542508363005713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3121467950294046976487509 36579702542508363005713)
              ·
                rfl

theorem cell20_721292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 8].length) (baseStart_721292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721292 prefixEnd_721292 := by exact prefixLift 721292
  have htrace : WordTrace (prefixWord ++ tailWord_721292) baseStart_721292 baseEnd_721292 := by
    simpa [prefixWord, tailWord_721292, baseEnd_721292] using wordTrace_append hprefix tailTrace_721292
  have hstable : (prefixWord ++ tailWord_721292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721292).length < 2 ^ (prefixWord ++ tailWord_721292).sum := by decide
  have hdescent : baseEnd_721292 < baseStart_721292 := by decide
  rcases family_descends (prefixWord ++ tailWord_721292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721312 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_721312 : Nat := 118140960795 + 721312 * 2 ^ 59
def prefixEnd_721312 : Nat := 4983230072969 + 3 ^ 40 * 721312 * 2
def baseEnd_721312 : Nat := 329226451427544086384669

theorem tailTrace_721312 : CollatzResearch.WordTrace tailWord_721312 prefixEnd_721312 329226451427544086384669 := by
  unfold tailWord_721312
  simp only [CollatzResearch.WordTrace]
  refine ⟨13154204981408644563515095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17538939975211526084686793 13154204981408644563515095)
  ·
    refine ⟨19731307472112966845272643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13154204981408644563515095 19731307472112966845272643)
    ·
      refine ⟨29596961208169450267908965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19731307472112966845272643 29596961208169450267908965)
      ·
        refine ⟨5549430226531771925232931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29596961208169450267908965 5549430226531771925232931)
        ·
          refine ⟨8324145339797657887849397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5549430226531771925232931 8324145339797657887849397)
          ·
            refine ⟨780388625606030426985881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8324145339797657887849397 780388625606030426985881)
            ·
              refine ⟨585291469204522820239411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780388625606030426985881 585291469204522820239411)
              ·
                refine ⟨877937203806784230359117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585291469204522820239411 877937203806784230359117)
                ·
                  refine ⟨329226451427544086384669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877937203806784230359117 329226451427544086384669)
                  ·
                    rfl

theorem cell20_721312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_721312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721312 prefixEnd_721312 := by exact prefixLift 721312
  have htrace : WordTrace (prefixWord ++ tailWord_721312) baseStart_721312 baseEnd_721312 := by
    simpa [prefixWord, tailWord_721312, baseEnd_721312] using wordTrace_append hprefix tailTrace_721312
  have hstable : (prefixWord ++ tailWord_721312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721312).length < 2 ^ (prefixWord ++ tailWord_721312).sum := by decide
  have hdescent : baseEnd_721312 < baseStart_721312 := by decide
  rcases family_descends (prefixWord ++ tailWord_721312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721330 : List Nat := [3, 2, 1, 1, 1, 1, 3, 8]
def baseStart_721330 : Nat := 118140960795 + 721330 * 2 ^ 59
def prefixEnd_721330 : Nat := 4983230072969 + 3 ^ 40 * 721330 * 2
def baseEnd_721330 : Nat := 109744889039338674594865

theorem tailTrace_721330 : CollatzResearch.WordTrace tailWord_721330 prefixEnd_721330 109744889039338674594865 := by
  unfold tailWord_721330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577266619188019550296361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17539377651168052134123629 6577266619188019550296361)
  ·
    refine ⟨4932949964391014662722271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6577266619188019550296361 4932949964391014662722271)
    ·
      refine ⟨7399424946586521994083407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4932949964391014662722271 7399424946586521994083407)
      ·
        refine ⟨11099137419879782991125111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7399424946586521994083407 11099137419879782991125111)
        ·
          refine ⟨16648706129819674486687667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11099137419879782991125111 16648706129819674486687667)
          ·
            refine ⟨24973059194729511730031501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16648706129819674486687667 24973059194729511730031501)
            ·
              refine ⟨9364897198023566898761813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24973059194729511730031501 9364897198023566898761813)
              ·
                refine ⟨109744889039338674594865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9364897198023566898761813 109744889039338674594865)
                ·
                  rfl

theorem cell20_721330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_721330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721330 prefixEnd_721330 := by exact prefixLift 721330
  have htrace : WordTrace (prefixWord ++ tailWord_721330) baseStart_721330 baseEnd_721330 := by
    simpa [prefixWord, tailWord_721330, baseEnd_721330] using wordTrace_append hprefix tailTrace_721330
  have hstable : (prefixWord ++ tailWord_721330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721330).length < 2 ^ (prefixWord ++ tailWord_721330).sum := by decide
  have hdescent : baseEnd_721330 < baseStart_721330 := by decide
  rcases family_descends (prefixWord ++ tailWord_721330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721364 : List Nat := [2, 4, 1, 2, 2, 3, 1, 5]
def baseStart_721364 : Nat := 118140960795 + 721364 * 2 ^ 59
def prefixEnd_721364 : Nat := 4983230072969 + 3 ^ 40 * 721364 * 2
def baseEnd_721364 : Nat := 109750061881487672217041

theorem tailTrace_721364 : CollatzResearch.WordTrace tailWord_721364 prefixEnd_721364 109750061881487672217041 := by
  unfold tailWord_721364
  simp only [CollatzResearch.WordTrace]
  refine ⟨13155153279314451003961573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17540204372419268005282097 13155153279314451003961573)
  ·
    refine ⟨2466591239871459563242795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13155153279314451003961573 2466591239871459563242795)
    ·
      refine ⟨3699886859807189344864193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2466591239871459563242795 3699886859807189344864193)
      ·
        refine ⟨2774915144855392008648145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3699886859807189344864193 2774915144855392008648145)
        ·
          refine ⟨2081186358641544006486109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2774915144855392008648145 2081186358641544006486109)
          ·
            refine ⟨780444884490579002432291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2081186358641544006486109 780444884490579002432291)
            ·
              refine ⟨1170667326735868503648437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780444884490579002432291 1170667326735868503648437)
              ·
                refine ⟨109750061881487672217041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1170667326735868503648437 109750061881487672217041)
                ·
                  rfl

theorem cell20_721364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_721364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721364 prefixEnd_721364 := by exact prefixLift 721364
  have htrace : WordTrace (prefixWord ++ tailWord_721364) baseStart_721364 baseEnd_721364 := by
    simpa [prefixWord, tailWord_721364, baseEnd_721364] using wordTrace_append hprefix tailTrace_721364
  have hstable : (prefixWord ++ tailWord_721364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721364).length < 2 ^ (prefixWord ++ tailWord_721364).sum := by decide
  have hdescent : baseEnd_721364 < baseStart_721364 := by decide
  rcases family_descends (prefixWord ++ tailWord_721364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721409 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 3]
def baseStart_721409 : Nat := 118140960795 + 721409 * 2 ^ 59
def prefixEnd_721409 : Nat := 4983230072969 + 3 ^ 40 * 721409 * 2
def baseEnd_721409 : Nat := 329270724870642860150939

theorem tailTrace_721409 : CollatzResearch.WordTrace tailWord_721409 prefixEnd_721409 329270724870642860150939 := by
  unfold tailWord_721409
  simp only [CollatzResearch.WordTrace]
  refine ⟨26311947843465874693311281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17541298562310583128874187 26311947843465874693311281)
  ·
    refine ⟨19733960882599406019983461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26311947843465874693311281 19733960882599406019983461)
    ·
      refine ⟨3700117665487388628746899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19733960882599406019983461 3700117665487388628746899)
      ·
        refine ⟨5550176498231082943120349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3700117665487388628746899 5550176498231082943120349)
        ·
          refine ⟨2081316186836656103670131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5550176498231082943120349 2081316186836656103670131)
          ·
            refine ⟨3121974280254984155505197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081316186836656103670131 3121974280254984155505197)
            ·
              refine ⟨1170740355095619058314449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3121974280254984155505197 1170740355095619058314449)
              ·
                refine ⟨878055266321714293735837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170740355095619058314449 878055266321714293735837)
                ·
                  refine ⟨329270724870642860150939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878055266321714293735837 329270724870642860150939)
                  ·
                    rfl

theorem cell20_721409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_721409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721409 prefixEnd_721409 := by exact prefixLift 721409
  have htrace : WordTrace (prefixWord ++ tailWord_721409) baseStart_721409 baseEnd_721409 := by
    simpa [prefixWord, tailWord_721409, baseEnd_721409] using wordTrace_append hprefix tailTrace_721409
  have hstable : (prefixWord ++ tailWord_721409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721409).length < 2 ^ (prefixWord ++ tailWord_721409).sum := by decide
  have hdescent : baseEnd_721409 < baseStart_721409 := by decide
  rcases family_descends (prefixWord ++ tailWord_721409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721450 : List Nat := [3, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_721450 : Nat := 118140960795 + 721450 * 2 ^ 59
def prefixEnd_721450 : Nat := 4983230072969 + 3 ^ 40 * 721450 * 2
def baseEnd_721450 : Nat := 329289438387828939784105

theorem tailTrace_721450 : CollatzResearch.WordTrace tailWord_721450 prefixEnd_721450 329289438387828939784105 := by
  unfold tailWord_721450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6578360809079334673888451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17542295490878225797035869 6578360809079334673888451)
  ·
    refine ⟨9867541213619002010832677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6578360809079334673888451 9867541213619002010832677)
    ·
      refine ⟨1850163977553562877031127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9867541213619002010832677 1850163977553562877031127)
      ·
        refine ⟨2775245966330344315546691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850163977553562877031127 2775245966330344315546691)
        ·
          refine ⟨4162868949495516473320037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775245966330344315546691 4162868949495516473320037)
          ·
            refine ⟨780537928030409338747507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4162868949495516473320037 780537928030409338747507)
            ·
              refine ⟨1170806892045614008121261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780537928030409338747507 1170806892045614008121261)
              ·
                refine ⟨439052584517105253045473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1170806892045614008121261 439052584517105253045473)
                ·
                  refine ⟨329289438387828939784105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439052584517105253045473 329289438387828939784105)
                  ·
                    rfl

theorem cell20_721450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_721450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721450 prefixEnd_721450 := by exact prefixLift 721450
  have htrace : WordTrace (prefixWord ++ tailWord_721450) baseStart_721450 baseEnd_721450 := by
    simpa [prefixWord, tailWord_721450, baseEnd_721450] using wordTrace_append hprefix tailTrace_721450
  have hstable : (prefixWord ++ tailWord_721450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721450).length < 2 ^ (prefixWord ++ tailWord_721450).sum := by decide
  have hdescent : baseEnd_721450 < baseStart_721450 := by decide
  rcases family_descends (prefixWord ++ tailWord_721450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721468 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_721468 : Nat := 118140960795 + 721468 * 2 ^ 59
def prefixEnd_721468 : Nat := 4983230072969 + 3 ^ 40 * 721468 * 2
def baseEnd_721468 : Nat := 329297654078300877184031

theorem tailTrace_721468 : CollatzResearch.WordTrace tailWord_721468 prefixEnd_721468 329297654078300877184031 := by
  unfold tailWord_721468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157049875126063884854529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17542733166834751846472705 13157049875126063884854529)
  ·
    refine ⟨9867787406344547913640897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13157049875126063884854529 9867787406344547913640897)
    ·
      refine ⟨7400840554758410935230673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9867787406344547913640897 7400840554758410935230673)
      ·
        refine ⟨5550630416068808201423005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7400840554758410935230673 5550630416068808201423005)
        ·
          refine ⟨2081486406025803075533627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5550630416068808201423005 2081486406025803075533627)
          ·
            refine ⟨3122229609038704613300441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081486406025803075533627 3122229609038704613300441)
            ·
              refine ⟨2341672206779028459975331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3122229609038704613300441 2341672206779028459975331)
              ·
                refine ⟨3512508310168542689962997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341672206779028459975331 3512508310168542689962997)
                ·
                  refine ⟨329297654078300877184031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3512508310168542689962997 329297654078300877184031)
                  ·
                    rfl

theorem cell20_721468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_721468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721468 prefixEnd_721468 := by exact prefixLift 721468
  have htrace : WordTrace (prefixWord ++ tailWord_721468) baseStart_721468 baseEnd_721468 := by
    simpa [prefixWord, tailWord_721468, baseEnd_721468] using wordTrace_append hprefix tailTrace_721468
  have hstable : (prefixWord ++ tailWord_721468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721468).length < 2 ^ (prefixWord ++ tailWord_721468).sum := by decide
  have hdescent : baseEnd_721468 < baseStart_721468 := by decide
  rcases family_descends (prefixWord ++ tailWord_721468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721471 : List Nat := [1, 1, 2, 2, 3, 2, 5, 2, 2]
def baseStart_721471 : Nat := 118140960795 + 721471 * 2 ^ 59
def prefixEnd_721471 : Nat := 4983230072969 + 3 ^ 40 * 721471 * 2
def baseEnd_721471 : Nat := 329299023360046200084019

theorem tailTrace_721471 : CollatzResearch.WordTrace tailWord_721471 prefixEnd_721471 329299023360046200084019 := by
  unfold tailWord_721471
  simp only [CollatzResearch.WordTrace]
  refine ⟨26314209169241259282068267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17542806112827506188045511 26314209169241259282068267)
  ·
    refine ⟨39471313753861888923102401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26314209169241259282068267 39471313753861888923102401)
    ·
      refine ⟨29603485315396416692326801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39471313753861888923102401 29603485315396416692326801)
      ·
        refine ⟨22202613986547312519245101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29603485315396416692326801 22202613986547312519245101)
        ·
          refine ⟨8325980244955242194716913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22202613986547312519245101 8325980244955242194716913)
          ·
            refine ⟨6244485183716431646037685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8325980244955242194716913 6244485183716431646037685)
            ·
              refine ⟨585420485973415466816033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6244485183716431646037685 585420485973415466816033)
              ·
                refine ⟨439065364480061600112025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585420485973415466816033 439065364480061600112025)
                ·
                  refine ⟨329299023360046200084019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439065364480061600112025 329299023360046200084019)
                  ·
                    rfl

theorem cell20_721471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 2].length) (baseStart_721471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721471 prefixEnd_721471 := by exact prefixLift 721471
  have htrace : WordTrace (prefixWord ++ tailWord_721471) baseStart_721471 baseEnd_721471 := by
    simpa [prefixWord, tailWord_721471, baseEnd_721471] using wordTrace_append hprefix tailTrace_721471
  have hstable : (prefixWord ++ tailWord_721471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721471).length < 2 ^ (prefixWord ++ tailWord_721471).sum := by decide
  have hdescent : baseEnd_721471 < baseStart_721471 := by decide
  rcases family_descends (prefixWord ++ tailWord_721471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721478 : List Nat := [6, 1, 1, 1, 2, 1, 1, 7]
def baseStart_721478 : Nat := 118140960795 + 721478 * 2 ^ 59
def prefixEnd_721478 : Nat := 4983230072969 + 3 ^ 40 * 721478 * 2
def baseEnd_721478 : Nat := 109767406116928428950219

theorem tailTrace_721478 : CollatzResearch.WordTrace tailWord_721478 prefixEnd_721478 109767406116928428950219 := by
  unfold tailWord_721478
  simp only [CollatzResearch.WordTrace]
  refine ⟨822327015006746858674159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17542976320143932985048725 822327015006746858674159)
  ·
    refine ⟨1233490522510120288011239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 822327015006746858674159 1233490522510120288011239)
    ·
      refine ⟨1850235783765180432016859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1233490522510120288011239 1850235783765180432016859)
      ·
        refine ⟨2775353675647770648025289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850235783765180432016859 2775353675647770648025289)
        ·
          refine ⟨2081515256735827986018967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2775353675647770648025289 2081515256735827986018967)
          ·
            refine ⟨3122272885103741979028451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081515256735827986018967 3122272885103741979028451)
            ·
              refine ⟨4683409327655612968542677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122272885103741979028451 4683409327655612968542677)
              ·
                refine ⟨109767406116928428950219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4683409327655612968542677 109767406116928428950219)
                ·
                  rfl

theorem cell20_721478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_721478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721478 prefixEnd_721478 := by exact prefixLift 721478
  have htrace : WordTrace (prefixWord ++ tailWord_721478) baseStart_721478 baseEnd_721478 := by
    simpa [prefixWord, tailWord_721478, baseEnd_721478] using wordTrace_append hprefix tailTrace_721478
  have hstable : (prefixWord ++ tailWord_721478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721478).length < 2 ^ (prefixWord ++ tailWord_721478).sum := by decide
  have hdescent : baseEnd_721478 < baseStart_721478 := by decide
  rcases family_descends (prefixWord ++ tailWord_721478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721482 : List Nat := [3, 1, 2, 1, 1, 4, 1, 7]
def baseStart_721482 : Nat := 118140960795 + 721482 * 2 ^ 59
def prefixEnd_721482 : Nat := 4983230072969 + 3 ^ 40 * 721482 * 2
def baseEnd_721482 : Nat := 109768014686593016905769

theorem tailTrace_721482 : CollatzResearch.WordTrace tailWord_721482 prefixEnd_721482 109768014686593016905769 := by
  unfold tailWord_721482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6578652593050352040179675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17543073581467605440479133 6578652593050352040179675)
  ·
    refine ⟨9867978889575528060269513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6578652593050352040179675 9867978889575528060269513)
    ·
      refine ⟨7400984167181646045202135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9867978889575528060269513 7400984167181646045202135)
      ·
        refine ⟨11101476250772469067803203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7400984167181646045202135 11101476250772469067803203)
        ·
          refine ⟨16652214376158703601704805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11101476250772469067803203 16652214376158703601704805)
          ·
            refine ⟨3122290195529756925319651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16652214376158703601704805 3122290195529756925319651)
            ·
              refine ⟨4683435293294635387979477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122290195529756925319651 4683435293294635387979477)
              ·
                refine ⟨109768014686593016905769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4683435293294635387979477 109768014686593016905769)
                ·
                  rfl

theorem cell20_721482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_721482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721482 prefixEnd_721482 := by exact prefixLift 721482
  have htrace : WordTrace (prefixWord ++ tailWord_721482) baseStart_721482 baseEnd_721482 := by
    simpa [prefixWord, tailWord_721482, baseEnd_721482] using wordTrace_append hprefix tailTrace_721482
  have hstable : (prefixWord ++ tailWord_721482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721482).length < 2 ^ (prefixWord ++ tailWord_721482).sum := by decide
  have hdescent : baseEnd_721482 < baseStart_721482 := by decide
  rcases family_descends (prefixWord ++ tailWord_721482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721520 : List Nat := [2, 1, 1, 1, 7, 8]
def baseStart_721520 : Nat := 118140960795 + 721520 * 2 ^ 59
def prefixEnd_721520 : Nat := 4983230072969 + 3 ^ 40 * 721520 * 2
def baseEnd_721520 : Nat := 12197088455378511387055

theorem tailTrace_721520 : CollatzResearch.WordTrace tailWord_721520 prefixEnd_721520 12197088455378511387055 := by
  unfold tailWord_721520
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157998173031870325301007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17543997564042493767068009 13157998173031870325301007)
  ·
    refine ⟨19736997259547805487951511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13157998173031870325301007 19736997259547805487951511)
    ·
      refine ⟨29605495889321708231927267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19736997259547805487951511 29605495889321708231927267)
      ·
        refine ⟨44408243833982562347890901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29605495889321708231927267 44408243833982562347890901)
        ·
          refine ⟨1040818214858966305028693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 44408243833982562347890901 1040818214858966305028693)
          ·
            refine ⟨12197088455378511387055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1040818214858966305028693 12197088455378511387055)
            ·
              rfl

theorem cell20_721520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 8].length) (baseStart_721520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721520 prefixEnd_721520 := by exact prefixLift 721520
  have htrace : WordTrace (prefixWord ++ tailWord_721520) baseStart_721520 baseEnd_721520 := by
    simpa [prefixWord, tailWord_721520, baseEnd_721520] using wordTrace_append hprefix tailTrace_721520
  have hstable : (prefixWord ++ tailWord_721520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721520).length < 2 ^ (prefixWord ++ tailWord_721520).sum := by decide
  have hdescent : baseEnd_721520 < baseStart_721520 := by decide
  rcases family_descends (prefixWord ++ tailWord_721520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721526 : List Nat := [5, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_721526 : Nat := 118140960795 + 721526 * 2 ^ 59
def prefixEnd_721526 : Nat := 4983230072969 + 3 ^ 40 * 721526 * 2
def baseEnd_721526 : Nat := 329324126858710453250461

theorem tailTrace_721526 : CollatzResearch.WordTrace tailWord_721526 prefixEnd_721526 329324126858710453250461 := by
  unfold tailWord_721526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644763449002625229707527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17544143456028002450213621 1644763449002625229707527)
  ·
    refine ⟨2467145173503937844561291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1644763449002625229707527 2467145173503937844561291)
    ·
      refine ⟨3700717760255906766841937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467145173503937844561291 3700717760255906766841937)
      ·
        refine ⟨2775538320191930075131453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3700717760255906766841937 2775538320191930075131453)
        ·
          refine ⟨1040826870071973778174295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2775538320191930075131453 1040826870071973778174295)
          ·
            refine ⟨1561240305107960667261443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040826870071973778174295 1561240305107960667261443)
            ·
              refine ⟨2341860457661941000892165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561240305107960667261443 2341860457661941000892165)
              ·
                refine ⟨439098835811613937667281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2341860457661941000892165 439098835811613937667281)
                ·
                  refine ⟨329324126858710453250461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439098835811613937667281 329324126858710453250461)
                  ·
                    rfl

theorem cell20_721526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_721526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721526 prefixEnd_721526 := by exact prefixLift 721526
  have htrace : WordTrace (prefixWord ++ tailWord_721526) baseStart_721526 baseEnd_721526 := by
    simpa [prefixWord, tailWord_721526, baseEnd_721526] using wordTrace_append hprefix tailTrace_721526
  have hstable : (prefixWord ++ tailWord_721526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721526).length < 2 ^ (prefixWord ++ tailWord_721526).sum := by decide
  have hdescent : baseEnd_721526 < baseStart_721526 := by decide
  rcases family_descends (prefixWord ++ tailWord_721526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721527 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_721527 : Nat := 118140960795 + 721527 * 2 ^ 59
def prefixEnd_721527 : Nat := 4983230072969 + 3 ^ 40 * 721527 * 2
def baseEnd_721527 : Nat := 329324583285958894217123

theorem tailTrace_721527 : CollatzResearch.WordTrace tailWord_721527 prefixEnd_721527 329324583285958894217123 := by
  unfold tailWord_721527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26316251657038380846106835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17544167771358920564071223 26316251657038380846106835)
  ·
    refine ⟨39474377485557571269160253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26316251657038380846106835 39474377485557571269160253)
    ·
      refine ⟨14802891557084089225935095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39474377485557571269160253 14802891557084089225935095)
      ·
        refine ⟨22204337335626133838902643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14802891557084089225935095 22204337335626133838902643)
        ·
          refine ⟨33306506003439200758353965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22204337335626133838902643 33306506003439200758353965)
          ·
            refine ⟨12489939751289700284382737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33306506003439200758353965 12489939751289700284382737)
            ·
              refine ⟨9367454813467275213287053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12489939751289700284382737 9367454813467275213287053)
              ·
                refine ⟨3512795555050228204982645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9367454813467275213287053 3512795555050228204982645)
                ·
                  refine ⟨329324583285958894217123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3512795555050228204982645 329324583285958894217123)
                  ·
                    rfl

theorem cell20_721527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_721527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721527 prefixEnd_721527 := by exact prefixLift 721527
  have htrace : WordTrace (prefixWord ++ tailWord_721527) baseStart_721527 baseEnd_721527 := by
    simpa [prefixWord, tailWord_721527, baseEnd_721527] using wordTrace_append hprefix tailTrace_721527
  have hstable : (prefixWord ++ tailWord_721527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721527).length < 2 ^ (prefixWord ++ tailWord_721527).sum := by decide
  have hdescent : baseEnd_721527 < baseStart_721527 := by decide
  rcases family_descends (prefixWord ++ tailWord_721527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721554 : List Nat := [3, 2, 3, 1, 2, 2, 3, 4]
def baseStart_721554 : Nat := 118140960795 + 721554 * 2 ^ 59
def prefixEnd_721554 : Nat := 4983230072969 + 3 ^ 40 * 721554 * 2
def baseEnd_721554 : Nat := 109778968940555600105671

theorem tailTrace_721554 : CollatzResearch.WordTrace tailWord_721554 prefixEnd_721554 109778968940555600105671 := by
  unfold tailWord_721554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6579309106985141114334929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17544824285293709638226477 6579309106985141114334929)
  ·
    refine ⟨4934481830238855835751197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6579309106985141114334929 4934481830238855835751197)
    ·
      refine ⟨1850430686339570938406699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4934481830238855835751197 1850430686339570938406699)
      ·
        refine ⟨2775646029509356407610049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850430686339570938406699 2775646029509356407610049)
        ·
          refine ⟨2081734522132017305707537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2775646029509356407610049 2081734522132017305707537)
          ·
            refine ⟨1561300891599012979280653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2081734522132017305707537 1561300891599012979280653)
            ·
              refine ⟨585487834349629867230245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561300891599012979280653 585487834349629867230245)
              ·
                refine ⟨109778968940555600105671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585487834349629867230245 109778968940555600105671)
                ·
                  rfl

theorem cell20_721554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_721554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721554 prefixEnd_721554 := by exact prefixLift 721554
  have htrace : WordTrace (prefixWord ++ tailWord_721554) baseStart_721554 baseEnd_721554 := by
    simpa [prefixWord, tailWord_721554, baseEnd_721554] using wordTrace_append hprefix tailTrace_721554
  have hstable : (prefixWord ++ tailWord_721554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721554).length < 2 ^ (prefixWord ++ tailWord_721554).sum := by decide
  have hdescent : baseEnd_721554 < baseStart_721554 := by decide
  rcases family_descends (prefixWord ++ tailWord_721554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721578 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_721578 : Nat := 118140960795 + 721578 * 2 ^ 59
def prefixEnd_721578 : Nat := 4983230072969 + 3 ^ 40 * 721578 * 2
def baseEnd_721578 : Nat := 329347861075629383516915

theorem tailTrace_721578 : CollatzResearch.WordTrace tailWord_721578 prefixEnd_721578 329347861075629383516915 := by
  unfold tailWord_721578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6579527944963404139053347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17545407853235744370808925 6579527944963404139053347)
  ·
    refine ⟨9869291917445106208580021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6579527944963404139053347 9869291917445106208580021)
    ·
      refine ⟨925246117260478707054377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9869291917445106208580021 925246117260478707054377)
      ·
        refine ⟨693934587945359030290783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 925246117260478707054377 693934587945359030290783)
        ·
          refine ⟨1040901881918038545436175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693934587945359030290783 1040901881918038545436175)
          ·
            refine ⟨1561352822877057818154263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040901881918038545436175 1561352822877057818154263)
            ·
              refine ⟨2342029234315586727231395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561352822877057818154263 2342029234315586727231395)
              ·
                refine ⟨3513043851473380090847093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342029234315586727231395 3513043851473380090847093)
                ·
                  refine ⟨329347861075629383516915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3513043851473380090847093 329347861075629383516915)
                  ·
                    rfl

theorem cell20_721578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_721578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721578 prefixEnd_721578 := by exact prefixLift 721578
  have htrace : WordTrace (prefixWord ++ tailWord_721578) baseStart_721578 baseEnd_721578 := by
    simpa [prefixWord, tailWord_721578, baseEnd_721578] using wordTrace_append hprefix tailTrace_721578
  have hstable : (prefixWord ++ tailWord_721578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721578).length < 2 ^ (prefixWord ++ tailWord_721578).sum := by decide
  have hdescent : baseEnd_721578 < baseStart_721578 := by decide
  rcases family_descends (prefixWord ++ tailWord_721578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721585 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 4]
def baseStart_721585 : Nat := 118140960795 + 721585 * 2 ^ 59
def prefixEnd_721585 : Nat := 4983230072969 + 3 ^ 40 * 721585 * 2
def baseEnd_721585 : Nat := 329351056066368470283553

theorem tailTrace_721585 : CollatzResearch.WordTrace tailWord_721585 prefixEnd_721585 329351056066368470283553 := by
  unfold tailWord_721585
  simp only [CollatzResearch.WordTrace]
  refine ⟨26318367090828256751718209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17545578060552171167812139 26318367090828256751718209)
  ·
    refine ⟨19738775318121192563788657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26318367090828256751718209 19738775318121192563788657)
    ·
      refine ⟨14804081488590894422841493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19738775318121192563788657 14804081488590894422841493)
      ·
        refine ⟨693941319777698176070695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14804081488590894422841493 693941319777698176070695)
        ·
          refine ⟨1040911979666547264106043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693941319777698176070695 1040911979666547264106043)
          ·
            refine ⟨1561367969499820896159065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040911979666547264106043 1561367969499820896159065)
            ·
              refine ⟨1171025977124865672119299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1561367969499820896159065 1171025977124865672119299)
              ·
                refine ⟨1756538965687298508178949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171025977124865672119299 1756538965687298508178949)
                ·
                  refine ⟨329351056066368470283553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1756538965687298508178949 329351056066368470283553)
                  ·
                    rfl

theorem cell20_721585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_721585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721585 prefixEnd_721585 := by exact prefixLift 721585
  have htrace : WordTrace (prefixWord ++ tailWord_721585) baseStart_721585 baseEnd_721585 := by
    simpa [prefixWord, tailWord_721585, baseEnd_721585] using wordTrace_append hprefix tailTrace_721585
  have hstable : (prefixWord ++ tailWord_721585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721585).length < 2 ^ (prefixWord ++ tailWord_721585).sum := by decide
  have hdescent : baseEnd_721585 < baseStart_721585 := by decide
  rcases family_descends (prefixWord ++ tailWord_721585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721596 : List Nat := [2, 2, 2, 3, 1, 1, 2, 7]
def baseStart_721596 : Nat := 118140960795 + 721596 * 2 ^ 59
def prefixEnd_721596 : Nat := 4983230072969 + 3 ^ 40 * 721596 * 2
def baseEnd_721596 : Nat := 109785358922033773638947

theorem tailTrace_721596 : CollatzResearch.WordTrace tailWord_721596 prefixEnd_721596 109785358922033773638947 := by
  unfold tailWord_721596
  simp only [CollatzResearch.WordTrace]
  refine ⟨13159384146894202815184321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17545845529192270420245761 13159384146894202815184321)
  ·
    refine ⟨9869538110170652111388241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13159384146894202815184321 9869538110170652111388241)
    ·
      refine ⟨7402153582627989083541181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9869538110170652111388241 7402153582627989083541181)
      ·
        refine ⟨2775807593485495906327943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7402153582627989083541181 2775807593485495906327943)
        ·
          refine ⟨4163711390228243859491915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775807593485495906327943 4163711390228243859491915)
          ·
            refine ⟨6245567085342365789237873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163711390228243859491915 6245567085342365789237873)
            ·
              refine ⟨4684175314006774341928405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6245567085342365789237873 4684175314006774341928405)
              ·
                refine ⟨109785358922033773638947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4684175314006774341928405 109785358922033773638947)
                ·
                  rfl

theorem cell20_721596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_721596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721596 prefixEnd_721596 := by exact prefixLift 721596
  have htrace : WordTrace (prefixWord ++ tailWord_721596) baseStart_721596 baseEnd_721596 := by
    simpa [prefixWord, tailWord_721596, baseEnd_721596] using wordTrace_append hprefix tailTrace_721596
  have hstable : (prefixWord ++ tailWord_721596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721596).length < 2 ^ (prefixWord ++ tailWord_721596).sum := by decide
  have hdescent : baseEnd_721596 < baseStart_721596 := by decide
  rcases family_descends (prefixWord ++ tailWord_721596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721599 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 3]
def baseStart_721599 : Nat := 118140960795 + 721599 * 2 ^ 59
def prefixEnd_721599 : Nat := 4983230072969 + 3 ^ 40 * 721599 * 2
def baseEnd_721599 : Nat := 329357446047846643816829

theorem tailTrace_721599 : CollatzResearch.WordTrace tailWord_721599 prefixEnd_721599 329357446047846643816829 := by
  unfold tailWord_721599
  simp only [CollatzResearch.WordTrace]
  refine ⟨26318877712777537142727851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17545918475185024761818567 26318877712777537142727851)
  ·
    refine ⟨39478316569166305714091777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26318877712777537142727851 39478316569166305714091777)
    ·
      refine ⟨29608737426874729285568833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39478316569166305714091777 29608737426874729285568833)
      ·
        refine ⟨22206553070156046964176625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29608737426874729285568833 22206553070156046964176625)
        ·
          refine ⟨16654914802617035223132469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22206553070156046964176625 16654914802617035223132469)
          ·
            refine ⟨1561398262745347052168669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16654914802617035223132469 1561398262745347052168669)
            ·
              refine ⟨585524348529505144563251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561398262745347052168669 585524348529505144563251)
              ·
                refine ⟨878286522794257716844877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585524348529505144563251 878286522794257716844877)
                ·
                  refine ⟨329357446047846643816829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878286522794257716844877 329357446047846643816829)
                  ·
                    rfl

theorem cell20_721599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 3].length) (baseStart_721599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721599 prefixEnd_721599 := by exact prefixLift 721599
  have htrace : WordTrace (prefixWord ++ tailWord_721599) baseStart_721599 baseEnd_721599 := by
    simpa [prefixWord, tailWord_721599, baseEnd_721599] using wordTrace_append hprefix tailTrace_721599
  have hstable : (prefixWord ++ tailWord_721599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721599).length < 2 ^ (prefixWord ++ tailWord_721599).sum := by decide
  have hdescent : baseEnd_721599 < baseStart_721599 := by decide
  rcases family_descends (prefixWord ++ tailWord_721599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721623 : List Nat := [1, 1, 3, 2, 1, 6, 1, 3, 2]
def baseStart_721623 : Nat := 118140960795 + 721623 * 2 ^ 59
def prefixEnd_721623 : Nat := 4983230072969 + 3 ^ 40 * 721623 * 2
def baseEnd_721623 : Nat := 329368400301809227016731

theorem tailTrace_721623 : CollatzResearch.WordTrace tailWord_721623 prefixEnd_721623 329368400301809227016731 := by
  unfold tailWord_721623
  simp only [CollatzResearch.WordTrace]
  refine ⟨26319753064690589241601523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17546502043127059494401015 26319753064690589241601523)
  ·
    refine ⟨39479629597035883862402285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26319753064690589241601523 39479629597035883862402285)
    ·
      refine ⟨14804861098888456448400857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39479629597035883862402285 14804861098888456448400857)
      ·
        refine ⟨11103645824166342336300643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14804861098888456448400857 11103645824166342336300643)
        ·
          refine ⟨16655468736249513504450965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11103645824166342336300643 16655468736249513504450965)
          ·
            refine ⟨780725097011695945521139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16655468736249513504450965 780725097011695945521139)
            ·
              refine ⟨1171087645517543918281709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780725097011695945521139 1171087645517543918281709)
              ·
                refine ⟨439157867069078969355641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1171087645517543918281709 439157867069078969355641)
                ·
                  refine ⟨329368400301809227016731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439157867069078969355641 329368400301809227016731)
                  ·
                    rfl

theorem cell20_721623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 2].length) (baseStart_721623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721623 prefixEnd_721623 := by exact prefixLift 721623
  have htrace : WordTrace (prefixWord ++ tailWord_721623) baseStart_721623 baseEnd_721623 := by
    simpa [prefixWord, tailWord_721623, baseEnd_721623] using wordTrace_append hprefix tailTrace_721623
  have hstable : (prefixWord ++ tailWord_721623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721623).length < 2 ^ (prefixWord ++ tailWord_721623).sum := by decide
  have hdescent : baseEnd_721623 < baseStart_721623 := by decide
  rcases family_descends (prefixWord ++ tailWord_721623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721640 : List Nat := [2, 1, 4, 1, 4, 1, 3, 2, 2]
def baseStart_721640 : Nat := 118140960795 + 721640 * 2 ^ 59
def prefixEnd_721640 : Nat := 4983230072969 + 3 ^ 40 * 721640 * 2
def baseEnd_721640 : Nat := 329376159565032723449995

theorem tailTrace_721640 : CollatzResearch.WordTrace tailWord_721640 prefixEnd_721640 329376159565032723449995 := by
  unfold tailWord_721640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160186552814500572485187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17546915403752667429980249 13160186552814500572485187)
  ·
    refine ⟨19740279829221750858727781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13160186552814500572485187 19740279829221750858727781)
    ·
      refine ⟨3701302467979078286011459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19740279829221750858727781 3701302467979078286011459)
      ·
        refine ⟨5551953701968617429017189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3701302467979078286011459 5551953701968617429017189)
        ·
          refine ⟨1040991319119115767940723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5551953701968617429017189 1040991319119115767940723)
          ·
            refine ⟨1561486978678673651911085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040991319119115767940723 1561486978678673651911085)
            ·
              refine ⟨585557617004502619466657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561486978678673651911085 585557617004502619466657)
              ·
                refine ⟨439168212753376964599993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585557617004502619466657 439168212753376964599993)
                ·
                  refine ⟨329376159565032723449995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439168212753376964599993 329376159565032723449995)
                  ·
                    rfl

theorem cell20_721640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_721640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721640 prefixEnd_721640 := by exact prefixLift 721640
  have htrace : WordTrace (prefixWord ++ tailWord_721640) baseStart_721640 baseEnd_721640 := by
    simpa [prefixWord, tailWord_721640, baseEnd_721640] using wordTrace_append hprefix tailTrace_721640
  have hstable : (prefixWord ++ tailWord_721640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721640).length < 2 ^ (prefixWord ++ tailWord_721640).sum := by decide
  have hdescent : baseEnd_721640 < baseStart_721640 := by decide
  rcases family_descends (prefixWord ++ tailWord_721640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721641 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 5]
def baseStart_721641 : Nat := 118140960795 + 721641 * 2 ^ 59
def prefixEnd_721641 : Nat := 4983230072969 + 3 ^ 40 * 721641 * 2
def baseEnd_721641 : Nat := 329376615992281164416657

theorem tailTrace_721641 : CollatzResearch.WordTrace tailWord_721641 prefixEnd_721641 329376615992281164416657 := by
  unfold tailWord_721641
  simp only [CollatzResearch.WordTrace]
  refine ⟨26320409578625378315756777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17546939719083585543837851 26320409578625378315756777)
  ·
    refine ⟨19740307183969033736817583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26320409578625378315756777 19740307183969033736817583)
    ·
      refine ⟨29610460775953550605226375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19740307183969033736817583 29610460775953550605226375)
      ·
        refine ⟨44415691163930325907839563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29610460775953550605226375 44415691163930325907839563)
        ·
          refine ⟨66623536745895488861759345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44415691163930325907839563 66623536745895488861759345)
          ·
            refine ⟨49967652559421616646319509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66623536745895488861759345 49967652559421616646319509)
            ·
              refine ⟨2342233713722888280296227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49967652559421616646319509 2342233713722888280296227)
              ·
                refine ⟨3513350570584332420444341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342233713722888280296227 3513350570584332420444341)
                ·
                  refine ⟨329376615992281164416657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3513350570584332420444341 329376615992281164416657)
                  ·
                    rfl

theorem cell20_721641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_721641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721641 prefixEnd_721641 := by exact prefixLift 721641
  have htrace : WordTrace (prefixWord ++ tailWord_721641) baseStart_721641 baseEnd_721641 := by
    simpa [prefixWord, tailWord_721641, baseEnd_721641] using wordTrace_append hprefix tailTrace_721641
  have hstable : (prefixWord ++ tailWord_721641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721641).length < 2 ^ (prefixWord ++ tailWord_721641).sum := by decide
  have hdescent : baseEnd_721641 < baseStart_721641 := by decide
  rcases family_descends (prefixWord ++ tailWord_721641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721672 : List Nat := [2, 1, 3, 2, 2, 2, 2, 6]
def baseStart_721672 : Nat := 118140960795 + 721672 * 2 ^ 59
def prefixEnd_721672 : Nat := 4983230072969 + 3 ^ 40 * 721672 * 2
def baseEnd_721672 : Nat := 109796921745660944794399

theorem tailTrace_721672 : CollatzResearch.WordTrace tailWord_721672 prefixEnd_721672 109796921745660944794399 := by
  unfold tailWord_721672
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160770120756535305067635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17547693494342047073423513 13160770120756535305067635)
  ·
    refine ⟨19741155181134802957601453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13160770120756535305067635 19741155181134802957601453)
    ·
      refine ⟨7402933192925551109100545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19741155181134802957601453 7402933192925551109100545)
      ·
        refine ⟨5552199894694163331825409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7402933192925551109100545 5552199894694163331825409)
        ·
          refine ⟨4164149921020622498869057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5552199894694163331825409 4164149921020622498869057)
          ·
            refine ⟨3123112440765466874151793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4164149921020622498869057 3123112440765466874151793)
            ·
              refine ⟨2342334330574100155613845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3123112440765466874151793 2342334330574100155613845)
              ·
                refine ⟨109796921745660944794399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2342334330574100155613845 109796921745660944794399)
                ·
                  rfl

theorem cell20_721672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_721672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721672 prefixEnd_721672 := by exact prefixLift 721672
  have htrace : WordTrace (prefixWord ++ tailWord_721672) baseStart_721672 baseEnd_721672 := by
    simpa [prefixWord, tailWord_721672, baseEnd_721672] using wordTrace_append hprefix tailTrace_721672
  have hstable : (prefixWord ++ tailWord_721672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721672).length < 2 ^ (prefixWord ++ tailWord_721672).sum := by decide
  have hdescent : baseEnd_721672 < baseStart_721672 := by decide
  rcases family_descends (prefixWord ++ tailWord_721672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721696 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_721696 : Nat := 118140960795 + 721696 * 2 ^ 59
def prefixEnd_721696 : Nat := 4983230072969 + 3 ^ 40 * 721696 * 2
def baseEnd_721696 : Nat := 329401719490945417583099

theorem tailTrace_721696 : CollatzResearch.WordTrace tailWord_721696 prefixEnd_721696 329401719490945417583099 := by
  unfold tailWord_721696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13161207796713061354504471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17548277062284081806005961 13161207796713061354504471)
  ·
    refine ⟨19741811695069592031756707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13161207796713061354504471 19741811695069592031756707)
    ·
      refine ⟨29612717542604388047635061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19741811695069592031756707 29612717542604388047635061)
      ·
        refine ⟨2776192269619161379465787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29612717542604388047635061 2776192269619161379465787)
        ·
          refine ⟨4164288404428742069198681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2776192269619161379465787 4164288404428742069198681)
          ·
            refine ⟨3123216303321556551899011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4164288404428742069198681 3123216303321556551899011)
            ·
              refine ⟨4684824454982334827848517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123216303321556551899011 4684824454982334827848517)
              ·
                refine ⟨878404585309187780221597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4684824454982334827848517 878404585309187780221597)
                ·
                  refine ⟨329401719490945417583099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878404585309187780221597 329401719490945417583099)
                  ·
                    rfl

theorem cell20_721696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_721696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721696 prefixEnd_721696 := by exact prefixLift 721696
  have htrace : WordTrace (prefixWord ++ tailWord_721696) baseStart_721696 baseEnd_721696 := by
    simpa [prefixWord, tailWord_721696, baseEnd_721696] using wordTrace_append hprefix tailTrace_721696
  have hstable : (prefixWord ++ tailWord_721696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721696).length < 2 ^ (prefixWord ++ tailWord_721696).sum := by decide
  have hdescent : baseEnd_721696 < baseStart_721696 := by decide
  rcases family_descends (prefixWord ++ tailWord_721696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721727 : List Nat := [1, 1, 2, 2, 5, 2, 3, 4]
def baseStart_721727 : Nat := 118140960795 + 721727 * 2 ^ 59
def prefixEnd_721727 : Nat := 4983230072969 + 3 ^ 40 * 721727 * 2
def baseEnd_721727 : Nat := 109805289578549029183213

theorem tailTrace_721727 : CollatzResearch.WordTrace tailWord_721727 prefixEnd_721727 109805289578549029183213 := by
  unfold tailWord_721727
  simp only [CollatzResearch.WordTrace]
  refine ⟨26323546256313815003387435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17549030837542543335591623 26323546256313815003387435)
  ·
    refine ⟨39485319384470722505081153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26323546256313815003387435 39485319384470722505081153)
    ·
      refine ⟨29613989538353041878810865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39485319384470722505081153 29613989538353041878810865)
      ·
        refine ⟨22210492153764781409108149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29613989538353041878810865 22210492153764781409108149)
        ·
          refine ⟨2082233639415448257103889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22210492153764781409108149 2082233639415448257103889)
          ·
            refine ⟨1561675229561586192827917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082233639415448257103889 1561675229561586192827917)
            ·
              refine ⟨585628211085594822310469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561675229561586192827917 585628211085594822310469)
              ·
                refine ⟨109805289578549029183213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585628211085594822310469 109805289578549029183213)
                ·
                  rfl

theorem cell20_721727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 4].length) (baseStart_721727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721727 prefixEnd_721727 := by exact prefixLift 721727
  have htrace : WordTrace (prefixWord ++ tailWord_721727) baseStart_721727 baseEnd_721727 := by
    simpa [prefixWord, tailWord_721727, baseEnd_721727] using wordTrace_append hprefix tailTrace_721727
  have hstable : (prefixWord ++ tailWord_721727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721727).length < 2 ^ (prefixWord ++ tailWord_721727).sum := by decide
  have hdescent : baseEnd_721727 < baseStart_721727 := by decide
  rcases family_descends (prefixWord ++ tailWord_721727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721751 : List Nat := [1, 1, 3, 2, 4, 3, 1, 2, 3]
def baseStart_721751 : Nat := 118140960795 + 721751 * 2 ^ 59
def prefixEnd_721751 : Nat := 4983230072969 + 3 ^ 40 * 721751 * 2
def baseEnd_721751 : Nat := 329426822989609670749541

theorem tailTrace_721751 : CollatzResearch.WordTrace tailWord_721751 prefixEnd_721751 329426822989609670749541 := by
  unfold tailWord_721751
  simp only [CollatzResearch.WordTrace]
  refine ⟨26324421608226867102261107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17549614405484578068174071 26324421608226867102261107)
  ·
    refine ⟨39486632412340300653391661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26324421608226867102261107 39486632412340300653391661)
    ·
      refine ⟨14807487154627612745021873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39486632412340300653391661 14807487154627612745021873)
      ·
        refine ⟨11105615365970709558766405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14807487154627612745021873 11105615365970709558766405)
        ·
          refine ⟨2082302881119508042268701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11105615365970709558766405 2082302881119508042268701)
          ·
            refine ⟨780863580419815515850763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2082302881119508042268701 780863580419815515850763)
            ·
              refine ⟨1171295370629723273776145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780863580419815515850763 1171295370629723273776145)
              ·
                refine ⟨878471527972292455332109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1171295370629723273776145 878471527972292455332109)
                ·
                  refine ⟨329426822989609670749541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878471527972292455332109 329426822989609670749541)
                  ·
                    rfl

theorem cell20_721751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 3].length) (baseStart_721751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721751 prefixEnd_721751 := by exact prefixLift 721751
  have htrace : WordTrace (prefixWord ++ tailWord_721751) baseStart_721751 baseEnd_721751 := by
    simpa [prefixWord, tailWord_721751, baseEnd_721751] using wordTrace_append hprefix tailTrace_721751
  have hstable : (prefixWord ++ tailWord_721751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721751).length < 2 ^ (prefixWord ++ tailWord_721751).sum := by decide
  have hdescent : baseEnd_721751 < baseStart_721751 := by decide
  rcases family_descends (prefixWord ++ tailWord_721751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721782 : List Nat := [5, 1, 1, 3, 1, 1, 4, 4]
def baseStart_721782 : Nat := 118140960795 + 721782 * 2 ^ 59
def prefixEnd_721782 : Nat := 4983230072969 + 3 ^ 40 * 721782 * 2
def baseEnd_721782 : Nat := 109813657411437113572027

theorem tailTrace_721782 : CollatzResearch.WordTrace tailWord_721782 prefixEnd_721782 109813657411437113572027 := by
  unfold tailWord_721782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1645347016944659962289975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17550368180743039597759733 1645347016944659962289975)
  ·
    refine ⟨2468020525416989943434963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1645347016944659962289975 2468020525416989943434963)
    ·
      refine ⟨3702030788125484915152445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2468020525416989943434963 3702030788125484915152445)
      ·
        refine ⟨1388261545547056843182167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3702030788125484915152445 1388261545547056843182167)
        ·
          refine ⟨2082392318320585264773251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388261545547056843182167 2082392318320585264773251)
          ·
            refine ⟨3123588477480877897159877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082392318320585264773251 3123588477480877897159877)
            ·
              refine ⟨585672839527664605717477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3123588477480877897159877 585672839527664605717477)
              ·
                refine ⟨109813657411437113572027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585672839527664605717477 109813657411437113572027)
                ·
                  rfl

theorem cell20_721782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_721782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721782 prefixEnd_721782 := by exact prefixLift 721782
  have htrace : WordTrace (prefixWord ++ tailWord_721782) baseStart_721782 baseEnd_721782 := by
    simpa [prefixWord, tailWord_721782, baseEnd_721782] using wordTrace_append hprefix tailTrace_721782
  have hstable : (prefixWord ++ tailWord_721782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721782).length < 2 ^ (prefixWord ++ tailWord_721782).sum := by decide
  have hdescent : baseEnd_721782 < baseStart_721782 := by decide
  rcases family_descends (prefixWord ++ tailWord_721782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721813 : List Nat := [1, 3, 2, 1, 1, 5, 3, 2, 2]
def baseStart_721813 : Nat := 118140960795 + 721813 * 2 ^ 59
def prefixEnd_721813 : Nat := 4983230072969 + 3 ^ 40 * 721813 * 2
def baseEnd_721813 : Nat := 329455121479013010682621

theorem tailTrace_721813 : CollatzResearch.WordTrace tailWord_721813 prefixEnd_721813 329455121479013010682621 := by
  unfold tailWord_721813
  simp only [CollatzResearch.WordTrace]
  refine ⟨26326682934002251691018093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17551121956001501127345395 26326682934002251691018093)
  ·
    refine ⟨9872506100250844384131785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26326682934002251691018093 9872506100250844384131785)
    ·
      refine ⟨7404379575188133288098839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9872506100250844384131785 7404379575188133288098839)
      ·
        refine ⟨11106569362782199932148259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7404379575188133288098839 11106569362782199932148259)
        ·
          refine ⟨16659854044173299898222389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11106569362782199932148259 16659854044173299898222389)
          ·
            refine ⟨1561861316641246865458349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16659854044173299898222389 1561861316641246865458349)
            ·
              refine ⟨585697993740467574546881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561861316641246865458349 585697993740467574546881)
              ·
                refine ⟨439273495305350680910161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585697993740467574546881 439273495305350680910161)
                ·
                  refine ⟨329455121479013010682621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439273495305350680910161 329455121479013010682621)
                  ·
                    rfl

theorem cell20_721813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_721813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721813 prefixEnd_721813 := by exact prefixLift 721813
  have htrace : WordTrace (prefixWord ++ tailWord_721813) baseStart_721813 baseEnd_721813 := by
    simpa [prefixWord, tailWord_721813, baseEnd_721813] using wordTrace_append hprefix tailTrace_721813
  have hstable : (prefixWord ++ tailWord_721813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721813).length < 2 ^ (prefixWord ++ tailWord_721813).sum := by decide
  have hdescent : baseEnd_721813 < baseStart_721813 := by decide
  rcases family_descends (prefixWord ++ tailWord_721813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721906 : List Nat := [3, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_721906 : Nat := 118140960795 + 721906 * 2 ^ 59
def prefixEnd_721906 : Nat := 4983230072969 + 3 ^ 40 * 721906 * 2
def baseEnd_721906 : Nat := 329497569213118020582241

theorem tailTrace_721906 : CollatzResearch.WordTrace tailWord_721906 prefixEnd_721906 329497569213118020582241 := by
  unfold tailWord_721906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582518730666332143538393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17553383281776885716102381 6582518730666332143538393)
  ·
    refine ⟨4936889047999749107653795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6582518730666332143538393 4936889047999749107653795)
    ·
      refine ⟨7405333571999623661480693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4936889047999749107653795 7405333571999623661480693)
      ·
        refine ⟨694250022374964718263815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7405333571999623661480693 694250022374964718263815)
        ·
          refine ⟨1041375033562447077395723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694250022374964718263815 1041375033562447077395723)
          ·
            refine ⟨1562062550343670616093585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041375033562447077395723 1562062550343670616093585)
            ·
              refine ⟨1171546912757752962070189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562062550343670616093585 1171546912757752962070189)
              ·
                refine ⟨439330092284157360776321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1171546912757752962070189 439330092284157360776321)
                ·
                  refine ⟨329497569213118020582241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439330092284157360776321 329497569213118020582241)
                  ·
                    rfl

theorem cell20_721906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_721906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721906 prefixEnd_721906 := by exact prefixLift 721906
  have htrace : WordTrace (prefixWord ++ tailWord_721906) baseStart_721906 baseEnd_721906 := by
    simpa [prefixWord, tailWord_721906, baseEnd_721906] using wordTrace_append hprefix tailTrace_721906
  have hstable : (prefixWord ++ tailWord_721906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721906).length < 2 ^ (prefixWord ++ tailWord_721906).sum := by decide
  have hdescent : baseEnd_721906 < baseStart_721906 := by decide
  rcases family_descends (prefixWord ++ tailWord_721906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721931 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 4]
def baseStart_721931 : Nat := 118140960795 + 721931 * 2 ^ 59
def prefixEnd_721931 : Nat := 4983230072969 + 3 ^ 40 * 721931 * 2
def baseEnd_721931 : Nat := 329508979894329044748805

theorem tailTrace_721931 : CollatzResearch.WordTrace tailWord_721931 prefixEnd_721931 329508979894329044748805 := by
  unfold tailWord_721931
  simp only [CollatzResearch.WordTrace]
  refine ⟨26330986747574757843813647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17553991165049838562542431 26330986747574757843813647)
  ·
    refine ⟨39496480121362136765720471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26330986747574757843813647 39496480121362136765720471)
    ·
      refine ⟨59244720182043205148580707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39496480121362136765720471 59244720182043205148580707)
      ·
        refine ⟨88867080273064807722871061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59244720182043205148580707 88867080273064807722871061)
        ·
          refine ⟨4165644387799912862009581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88867080273064807722871061 4165644387799912862009581)
          ·
            refine ⟨1562116645424967323253593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4165644387799912862009581 1562116645424967323253593)
            ·
              refine ⟨1171587484068725492440195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562116645424967323253593 1171587484068725492440195)
              ·
                refine ⟨1757381226103088238660293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171587484068725492440195 1757381226103088238660293)
                ·
                  refine ⟨329508979894329044748805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1757381226103088238660293 329508979894329044748805)
                  ·
                    rfl

theorem cell20_721931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_721931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721931 prefixEnd_721931 := by exact prefixLift 721931
  have htrace : WordTrace (prefixWord ++ tailWord_721931) baseStart_721931 baseEnd_721931 := by
    simpa [prefixWord, tailWord_721931, baseEnd_721931] using wordTrace_append hprefix tailTrace_721931
  have hstable : (prefixWord ++ tailWord_721931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721931).length < 2 ^ (prefixWord ++ tailWord_721931).sum := by decide
  have hdescent : baseEnd_721931 < baseStart_721931 := by decide
  rcases family_descends (prefixWord ++ tailWord_721931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721941 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 3]
def baseStart_721941 : Nat := 118140960795 + 721941 * 2 ^ 59
def prefixEnd_721941 : Nat := 4983230072969 + 3 ^ 40 * 721941 * 2
def baseEnd_721941 : Nat := 329513544166813454415431

theorem tailTrace_721941 : CollatzResearch.WordTrace tailWord_721941 prefixEnd_721941 329513544166813454415431 := by
  unfold tailWord_721941
  simp only [CollatzResearch.WordTrace]
  refine ⟨26331351477538529551677677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17554234318359019701118451 26331351477538529551677677)
  ·
    refine ⟨9874256804076948581879129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26331351477538529551677677 9874256804076948581879129)
    ·
      refine ⟨7405692603057711436409347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9874256804076948581879129 7405692603057711436409347)
      ·
        refine ⟨11108538904586567154614021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7405692603057711436409347 11108538904586567154614021)
        ·
          refine ⟨2082851044609981341490129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11108538904586567154614021 2082851044609981341490129)
          ·
            refine ⟨1562138283457486006117597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082851044609981341490129 1562138283457486006117597)
            ·
              refine ⟨585801856296557252294099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1562138283457486006117597 585801856296557252294099)
              ·
                refine ⟨878702784444835878441149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585801856296557252294099 878702784444835878441149)
                ·
                  refine ⟨329513544166813454415431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878702784444835878441149 329513544166813454415431)
                  ·
                    rfl

theorem cell20_721941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_721941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721941 prefixEnd_721941 := by exact prefixLift 721941
  have htrace : WordTrace (prefixWord ++ tailWord_721941) baseStart_721941 baseEnd_721941 := by
    simpa [prefixWord, tailWord_721941, baseEnd_721941] using wordTrace_append hprefix tailTrace_721941
  have hstable : (prefixWord ++ tailWord_721941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721941).length < 2 ^ (prefixWord ++ tailWord_721941).sum := by decide
  have hdescent : baseEnd_721941 < baseStart_721941 := by decide
  rcases family_descends (prefixWord ++ tailWord_721941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721945 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 3]
def baseStart_721945 : Nat := 118140960795 + 721945 * 2 ^ 59
def prefixEnd_721945 : Nat := 4983230072969 + 3 ^ 40 * 721945 * 2
def baseEnd_721945 : Nat := 329515369875807218282081

theorem tailTrace_721945 : CollatzResearch.WordTrace tailWord_721945 prefixEnd_721945 329515369875807218282081 := by
  unfold tailWord_721945
  simp only [CollatzResearch.WordTrace]
  refine ⟨26331497369524038234823289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17554331579682692156548859 26331497369524038234823289)
  ·
    refine ⟨19748623027143028676117467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26331497369524038234823289 19748623027143028676117467)
    ·
      refine ⟨29622934540714543014176201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19748623027143028676117467 29622934540714543014176201)
      ·
        refine ⟨22217200905535907260632151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29622934540714543014176201 22217200905535907260632151)
        ·
          refine ⟨33325801358303860890948227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22217200905535907260632151 33325801358303860890948227)
          ·
            refine ⟨49988702037455791336422341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33325801358303860890948227 49988702037455791336422341)
            ·
              refine ⟨9372881632022960875579189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49988702037455791336422341 9372881632022960875579189)
              ·
                refine ⟨878707653002152582085549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9372881632022960875579189 878707653002152582085549)
                ·
                  refine ⟨329515369875807218282081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878707653002152582085549 329515369875807218282081)
                  ·
                    rfl

theorem cell20_721945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_721945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721945 prefixEnd_721945 := by exact prefixLift 721945
  have htrace : WordTrace (prefixWord ++ tailWord_721945) baseStart_721945 baseEnd_721945 := by
    simpa [prefixWord, tailWord_721945, baseEnd_721945] using wordTrace_append hprefix tailTrace_721945
  have hstable : (prefixWord ++ tailWord_721945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721945).length < 2 ^ (prefixWord ++ tailWord_721945).sum := by decide
  have hdescent : baseEnd_721945 < baseStart_721945 := by decide
  rcases family_descends (prefixWord ++ tailWord_721945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721955 : List Nat := [1, 1, 1, 4, 3, 4, 2, 4]
def baseStart_721955 : Nat := 118140960795 + 721955 * 2 ^ 59
def prefixEnd_721955 : Nat := 4983230072969 + 3 ^ 40 * 721955 * 2
def baseEnd_721955 : Nat := 109839978049430542649569

theorem tailTrace_721955 : CollatzResearch.WordTrace tailWord_721955 prefixEnd_721955 109839978049430542649569 := by
  unfold tailWord_721955
  simp only [CollatzResearch.WordTrace]
  refine ⟨26331862099487809942687319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17554574732991873295124879 26331862099487809942687319)
  ·
    refine ⟨39497793149231714914030979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26331862099487809942687319 39497793149231714914030979)
    ·
      refine ⟨59246689723847572371046469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39497793149231714914030979 59246689723847572371046469)
      ·
        refine ⟨11108754323221419819571213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59246689723847572371046469 11108754323221419819571213)
        ·
          refine ⟨4165782871208032432339205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11108754323221419819571213 4165782871208032432339205)
          ·
            refine ⟨781084288351506081063601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4165782871208032432339205 781084288351506081063601)
            ·
              refine ⟨585813216263629560797701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781084288351506081063601 585813216263629560797701)
              ·
                refine ⟨109839978049430542649569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585813216263629560797701 109839978049430542649569)
                ·
                  rfl

theorem cell20_721955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 4].length) (baseStart_721955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721955 prefixEnd_721955 := by exact prefixLift 721955
  have htrace : WordTrace (prefixWord ++ tailWord_721955) baseStart_721955 baseEnd_721955 := by
    simpa [prefixWord, tailWord_721955, baseEnd_721955] using wordTrace_append hprefix tailTrace_721955
  have hstable : (prefixWord ++ tailWord_721955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721955).length < 2 ^ (prefixWord ++ tailWord_721955).sum := by decide
  have hdescent : baseEnd_721955 < baseStart_721955 := by decide
  rcases family_descends (prefixWord ++ tailWord_721955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721976 : List Nat := [2, 1, 2, 1, 5, 3, 6]
def baseStart_721976 : Nat := 118140960795 + 721976 * 2 ^ 59
def prefixEnd_721976 : Nat := 4983230072969 + 3 ^ 40 * 721976 * 2
def baseEnd_721976 : Nat := 36614391013389876472069

theorem tailTrace_721976 : CollatzResearch.WordTrace tailWord_721976 prefixEnd_721976 36614391013389876472069 := by
  unfold tailWord_721976
  simp only [CollatzResearch.WordTrace]
  refine ⟨13166314016205865264600891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17555085354941153686134521 13166314016205865264600891)
  ·
    refine ⟨19749471024308797896901337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13166314016205865264600891 19749471024308797896901337)
    ·
      refine ⟨14812103268231598422676003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19749471024308797896901337 14812103268231598422676003)
      ·
        refine ⟨22218154902347397634014005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812103268231598422676003 22218154902347397634014005)
        ·
          refine ⟨2082952022095068528188813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22218154902347397634014005 2082952022095068528188813)
          ·
            refine ⟨781107008285650698070805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2082952022095068528188813 781107008285650698070805)
            ·
              refine ⟨36614391013389876472069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 781107008285650698070805 36614391013389876472069)
              ·
                rfl

theorem cell20_721976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 6].length) (baseStart_721976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721976 prefixEnd_721976 := by exact prefixLift 721976
  have htrace : WordTrace (prefixWord ++ tailWord_721976) baseStart_721976 baseEnd_721976 := by
    simpa [prefixWord, tailWord_721976, baseEnd_721976] using wordTrace_append hprefix tailTrace_721976
  have hstable : (prefixWord ++ tailWord_721976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721976).length < 2 ^ (prefixWord ++ tailWord_721976).sum := by decide
  have hdescent : baseEnd_721976 < baseStart_721976 := by decide
  rcases family_descends (prefixWord ++ tailWord_721976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721982 : List Nat := [4, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_721982 : Nat := 118140960795 + 721982 * 2 ^ 59
def prefixEnd_721982 : Nat := 4983230072969 + 3 ^ 40 * 721982 * 2
def baseEnd_721982 : Nat := 329532257683999534048597

theorem tailTrace_721982 : CollatzResearch.WordTrace tailWord_721982 prefixEnd_721982 329532257683999534048597 := by
  unfold tailWord_721982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3291605858798749194240025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17555231246926662369280133 3291605858798749194240025)
  ·
    refine ⟨2468704394099061895680019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3291605858798749194240025 2468704394099061895680019)
    ·
      refine ⟨3703056591148592843520029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2468704394099061895680019 3703056591148592843520029)
      ·
        refine ⟨1388646221680722316320011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3703056591148592843520029 1388646221680722316320011)
        ·
          refine ⟨2082969332521083474480017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388646221680722316320011 2082969332521083474480017)
          ·
            refine ⟨1562226999390812605860013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082969332521083474480017 1562226999390812605860013)
            ·
              refine ⟨585835124771554727197505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1562226999390812605860013 585835124771554727197505)
              ·
                refine ⟨439376343578666045398129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585835124771554727197505 439376343578666045398129)
                ·
                  refine ⟨329532257683999534048597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439376343578666045398129 329532257683999534048597)
                  ·
                    rfl

theorem cell20_721982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_721982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721982 prefixEnd_721982 := by exact prefixLift 721982
  have htrace : WordTrace (prefixWord ++ tailWord_721982) baseStart_721982 baseEnd_721982 := by
    simpa [prefixWord, tailWord_721982, baseEnd_721982] using wordTrace_append hprefix tailTrace_721982
  have hstable : (prefixWord ++ tailWord_721982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721982).length < 2 ^ (prefixWord ++ tailWord_721982).sum := by decide
  have hdescent : baseEnd_721982 < baseStart_721982 := by decide
  rcases family_descends (prefixWord ++ tailWord_721982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721983 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 3]
def baseStart_721983 : Nat := 118140960795 + 721983 * 2 ^ 59
def prefixEnd_721983 : Nat := 4983230072969 + 3 ^ 40 * 721983 * 2
def baseEnd_721983 : Nat := 329532714111247975015259

theorem tailTrace_721983 : CollatzResearch.WordTrace tailWord_721983 prefixEnd_721983 329532714111247975015259 := by
  unfold tailWord_721983
  simp only [CollatzResearch.WordTrace]
  refine ⟨26332883343386370724706603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17555255562257580483137735 26332883343386370724706603)
  ·
    refine ⟨39499325015079556087059905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26332883343386370724706603 39499325015079556087059905)
    ·
      refine ⟨29624493761309667065294929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39499325015079556087059905 29624493761309667065294929)
      ·
        refine ⟨22218370320982250298971197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29624493761309667065294929 22218370320982250298971197)
        ·
          refine ⟨8331888870368343862114199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22218370320982250298971197 8331888870368343862114199)
          ·
            refine ⟨12497833305552515793171299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331888870368343862114199 12497833305552515793171299)
            ·
              refine ⟨18746749958328773689756949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12497833305552515793171299 18746749958328773689756949)
              ·
                refine ⟨878753904296661266707357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18746749958328773689756949 878753904296661266707357)
                ·
                  refine ⟨329532714111247975015259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878753904296661266707357 329532714111247975015259)
                  ·
                    rfl

theorem cell20_721983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_721983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_721983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_721983 prefixEnd_721983 := by exact prefixLift 721983
  have htrace : WordTrace (prefixWord ++ tailWord_721983) baseStart_721983 baseEnd_721983 := by
    simpa [prefixWord, tailWord_721983, baseEnd_721983] using wordTrace_append hprefix tailTrace_721983
  have hstable : (prefixWord ++ tailWord_721983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721983).length < 2 ^ (prefixWord ++ tailWord_721983).sum := by decide
  have hdescent : baseEnd_721983 < baseStart_721983 := by decide
  rcases family_descends (prefixWord ++ tailWord_721983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722037 : List Nat := [1, 3, 4, 3, 1, 2, 2, 2, 2]
def baseStart_722037 : Nat := 118140960795 + 722037 * 2 ^ 59
def prefixEnd_722037 : Nat := 4983230072969 + 3 ^ 40 * 722037 * 2
def baseEnd_722037 : Nat := 329557361182663787215039

theorem tailTrace_722037 : CollatzResearch.WordTrace tailWord_722037 prefixEnd_722037 329557361182663787215039 := by
  unfold tailWord_722037
  simp only [CollatzResearch.WordTrace]
  refine ⟨26334852885190737947172365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17556568590127158631448243 26334852885190737947172365)
  ·
    refine ⟨9875569831946526730189637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26334852885190737947172365 9875569831946526730189637)
    ·
      refine ⟨1851669343489973761910557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9875569831946526730189637 1851669343489973761910557)
      ·
        refine ⟨694376003808740160716459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1851669343489973761910557 694376003808740160716459)
        ·
          refine ⟨1041564005713110241074689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694376003808740160716459 1041564005713110241074689)
          ·
            refine ⟨781173004284832680806017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1041564005713110241074689 781173004284832680806017)
            ·
              refine ⟨585879753213624510604513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781173004284832680806017 585879753213624510604513)
              ·
                refine ⟨439409814910218382953385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585879753213624510604513 439409814910218382953385)
                ·
                  refine ⟨329557361182663787215039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439409814910218382953385 329557361182663787215039)
                  ·
                    rfl

theorem cell20_722037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_722037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722037 prefixEnd_722037 := by exact prefixLift 722037
  have htrace : WordTrace (prefixWord ++ tailWord_722037) baseStart_722037 baseEnd_722037 := by
    simpa [prefixWord, tailWord_722037, baseEnd_722037] using wordTrace_append hprefix tailTrace_722037
  have hstable : (prefixWord ++ tailWord_722037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722037).length < 2 ^ (prefixWord ++ tailWord_722037).sum := by decide
  have hdescent : baseEnd_722037 < baseStart_722037 := by decide
  rcases family_descends (prefixWord ++ tailWord_722037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722052 : List Nat := [2, 3, 2, 1, 2, 2, 3, 5]
def baseStart_722052 : Nat := 118140960795 + 722052 * 2 ^ 59
def prefixEnd_722052 : Nat := 4983230072969 + 3 ^ 40 * 722052 * 2
def baseEnd_722052 : Nat := 109854735863796800571659

theorem tailTrace_722052 : CollatzResearch.WordTrace tailWord_722052 prefixEnd_722052 109854735863796800571659 := by
  unfold tailWord_722052
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167699990068197754484205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17556933320090930339312273 13167699990068197754484205)
  ·
    refine ⟨4937887496275574157931577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13167699990068197754484205 4937887496275574157931577)
    ·
      refine ⟨3703415622206680618448683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4937887496275574157931577 3703415622206680618448683)
      ·
        refine ⟨5555123433310020927673025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703415622206680618448683 5555123433310020927673025)
        ·
          refine ⟨4166342574982515695754769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5555123433310020927673025 4166342574982515695754769)
          ·
            refine ⟨3124756931236886771816077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4166342574982515695754769 3124756931236886771816077)
            ·
              refine ⟨1171783849213832539431029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3124756931236886771816077 1171783849213832539431029)
              ·
                refine ⟨109854735863796800571659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1171783849213832539431029 109854735863796800571659)
                ·
                  rfl

theorem cell20_722052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_722052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722052 prefixEnd_722052 := by exact prefixLift 722052
  have htrace : WordTrace (prefixWord ++ tailWord_722052) baseStart_722052 baseEnd_722052 := by
    simpa [prefixWord, tailWord_722052, baseEnd_722052] using wordTrace_append hprefix tailTrace_722052
  have hstable : (prefixWord ++ tailWord_722052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722052).length < 2 ^ (prefixWord ++ tailWord_722052).sum := by decide
  have hdescent : baseEnd_722052 < baseStart_722052 := by decide
  rcases family_descends (prefixWord ++ tailWord_722052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722079 : List Nat := [1, 1, 2, 6, 2, 1, 2, 3, 2]
def baseStart_722079 : Nat := 118140960795 + 722079 * 2 ^ 59
def prefixEnd_722079 : Nat := 4983230072969 + 3 ^ 40 * 722079 * 2
def baseEnd_722079 : Nat := 329576531127098307814867

theorem tailTrace_722079 : CollatzResearch.WordTrace tailWord_722079 prefixEnd_722079 329576531127098307814867 := by
  unfold tailWord_722079
  simp only [CollatzResearch.WordTrace]
  refine ⟨26336384751038579120201291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17557589834025719413467527 26336384751038579120201291)
  ·
    refine ⟨39504577126557868680301937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26336384751038579120201291 39504577126557868680301937)
    ·
      refine ⟨29628432844918401510226453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39504577126557868680301937 29628432844918401510226453)
      ·
        refine ⟨1388832789605550070791865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29628432844918401510226453 1388832789605550070791865)
        ·
          refine ⟨1041624592204162553093899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388832789605550070791865 1041624592204162553093899)
          ·
            refine ⟨1562436888306243829640849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041624592204162553093899 1562436888306243829640849)
            ·
              refine ⟨1171827666229682872230637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562436888306243829640849 1171827666229682872230637)
              ·
                refine ⟨439435374836131077086489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1171827666229682872230637 439435374836131077086489)
                ·
                  refine ⟨329576531127098307814867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439435374836131077086489 329576531127098307814867)
                  ·
                    rfl

theorem cell20_722079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 2].length) (baseStart_722079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722079 prefixEnd_722079 := by exact prefixLift 722079
  have htrace : WordTrace (prefixWord ++ tailWord_722079) baseStart_722079 baseEnd_722079 := by
    simpa [prefixWord, tailWord_722079, baseEnd_722079] using wordTrace_append hprefix tailTrace_722079
  have hstable : (prefixWord ++ tailWord_722079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722079).length < 2 ^ (prefixWord ++ tailWord_722079).sum := by decide
  have hdescent : baseEnd_722079 < baseStart_722079 := by decide
  rcases family_descends (prefixWord ++ tailWord_722079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722187 : List Nat := [1, 1, 1, 1, 5, 3, 2, 6]
def baseStart_722187 : Nat := 118140960795 + 722187 * 2 ^ 59
def prefixEnd_722187 : Nat := 4983230072969 + 3 ^ 40 * 722187 * 2
def baseEnd_722187 : Nat := 109875275089976644071475

theorem tailTrace_722187 : CollatzResearch.WordTrace tailWord_722187 prefixEnd_722187 109875275089976644071475 := by
  unfold tailWord_722187
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340323834647313565132815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17560215889764875710088543 26340323834647313565132815)
  ·
    refine ⟨39510485751970970347699223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26340323834647313565132815 39510485751970970347699223)
    ·
      refine ⟨59265728627956455521548835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39510485751970970347699223 59265728627956455521548835)
      ·
        refine ⟨88898592941934683282323253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59265728627956455521548835 88898592941934683282323253)
        ·
          refine ⟨8334243088306376557717805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88898592941934683282323253 8334243088306376557717805)
          ·
            refine ⟨3125341158114891209144177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8334243088306376557717805 3125341158114891209144177)
            ·
              refine ⟨2344005868586168406858133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125341158114891209144177 2344005868586168406858133)
              ·
                refine ⟨109875275089976644071475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2344005868586168406858133 109875275089976644071475)
                ·
                  rfl

theorem cell20_722187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_722187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722187 prefixEnd_722187 := by exact prefixLift 722187
  have htrace : WordTrace (prefixWord ++ tailWord_722187) baseStart_722187 baseEnd_722187 := by
    simpa [prefixWord, tailWord_722187, baseEnd_722187] using wordTrace_append hprefix tailTrace_722187
  have hstable : (prefixWord ++ tailWord_722187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722187).length < 2 ^ (prefixWord ++ tailWord_722187).sum := by decide
  have hdescent : baseEnd_722187 < baseStart_722187 := by decide
  rcases family_descends (prefixWord ++ tailWord_722187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722197 : List Nat := [1, 3, 2, 1, 2, 1, 1, 7, 2]
def baseStart_722197 : Nat := 118140960795 + 722197 * 2 ^ 59
def prefixEnd_722197 : Nat := 4983230072969 + 3 ^ 40 * 722197 * 2
def baseEnd_722197 : Nat := 329630389542414341881051

theorem tailTrace_722197 : CollatzResearch.WordTrace tailWord_722197 prefixEnd_722197 329630389542414341881051 := by
  unfold tailWord_722197
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340688564611085272996845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17560459043074056848664563 26340688564611085272996845)
  ·
    refine ⟨9877758211729156977373817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26340688564611085272996845 9877758211729156977373817)
    ·
      refine ⟨7408318658796867733030363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9877758211729156977373817 7408318658796867733030363)
      ·
        refine ⟨11112477988195301599545545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7408318658796867733030363 11112477988195301599545545)
        ·
          refine ⟨8334358491146476199659159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11112477988195301599545545 8334358491146476199659159)
          ·
            refine ⟨12501537736719714299488739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334358491146476199659159 12501537736719714299488739)
            ·
              refine ⟨18752306605079571449233109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12501537736719714299488739 18752306605079571449233109)
              ·
                refine ⟨439507186056552455841401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18752306605079571449233109 439507186056552455841401)
                ·
                  refine ⟨329630389542414341881051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439507186056552455841401 329630389542414341881051)
                  ·
                    rfl

theorem cell20_722197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_722197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722197 prefixEnd_722197 := by exact prefixLift 722197
  have htrace : WordTrace (prefixWord ++ tailWord_722197) baseStart_722197 baseEnd_722197 := by
    simpa [prefixWord, tailWord_722197, baseEnd_722197] using wordTrace_append hprefix tailTrace_722197
  have hstable : (prefixWord ++ tailWord_722197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722197).length < 2 ^ (prefixWord ++ tailWord_722197).sum := by decide
  have hdescent : baseEnd_722197 < baseStart_722197 := by decide
  rcases family_descends (prefixWord ++ tailWord_722197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722206 : List Nat := [4, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_722206 : Nat := 118140960795 + 722206 * 2 ^ 59
def prefixEnd_722206 : Nat := 4983230072969 + 3 ^ 40 * 722206 * 2
def baseEnd_722206 : Nat := 329634497387650310581015

theorem tailTrace_722206 : CollatzResearch.WordTrace tailWord_722206 prefixEnd_722206 329634497387650310581015 := by
  unfold tailWord_722206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292627102697309976259309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17560677881052319873382981 3292627102697309976259309)
  ·
    refine ⟨1234735163511491241097241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3292627102697309976259309 1234735163511491241097241)
    ·
      refine ⟨926051372633618430822931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1234735163511491241097241 926051372633618430822931)
      ·
        refine ⟨1389077058950427646234397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926051372633618430822931 1389077058950427646234397)
        ·
          refine ⟨520903897106410367337899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1389077058950427646234397 520903897106410367337899)
          ·
            refine ⟨781355845659615551006849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520903897106410367337899 781355845659615551006849)
            ·
              refine ⟨586016884244711663255137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781355845659615551006849 586016884244711663255137)
              ·
                refine ⟨439512663183533747441353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586016884244711663255137 439512663183533747441353)
                ·
                  refine ⟨329634497387650310581015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439512663183533747441353 329634497387650310581015)
                  ·
                    rfl

theorem cell20_722206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_722206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722206 prefixEnd_722206 := by exact prefixLift 722206
  have htrace : WordTrace (prefixWord ++ tailWord_722206) baseStart_722206 baseEnd_722206 := by
    simpa [prefixWord, tailWord_722206, baseEnd_722206] using wordTrace_append hprefix tailTrace_722206
  have hstable : (prefixWord ++ tailWord_722206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722206).length < 2 ^ (prefixWord ++ tailWord_722206).sum := by decide
  have hdescent : baseEnd_722206 < baseStart_722206 := by decide
  rcases family_descends (prefixWord ++ tailWord_722206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722210 : List Nat := [3, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_722210 : Nat := 118140960795 + 722210 * 2 ^ 59
def prefixEnd_722210 : Nat := 4983230072969 + 3 ^ 40 * 722210 * 2
def baseEnd_722210 : Nat := 329636323096644074447665

theorem tailTrace_722210 : CollatzResearch.WordTrace tailWord_722210 prefixEnd_722210 329636323096644074447665 := by
  unfold tailWord_722210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6585290678390997123305021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17560775142375992328813389 6585290678390997123305021)
  ·
    refine ⟨2469484004396623921239383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6585290678390997123305021 2469484004396623921239383)
    ·
      refine ⟨3704226006594935881859075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469484004396623921239383 3704226006594935881859075)
      ·
        refine ⟨5556339009892403822788613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704226006594935881859075 5556339009892403822788613)
        ·
          refine ⟨1041813564354825716772865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5556339009892403822788613 1041813564354825716772865)
          ·
            refine ⟨781360173266119287579649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1041813564354825716772865 781360173266119287579649)
            ·
              refine ⟨586020129949589465684737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781360173266119287579649 586020129949589465684737)
              ·
                refine ⟨439515097462192099263553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586020129949589465684737 439515097462192099263553)
                ·
                  refine ⟨329636323096644074447665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439515097462192099263553 329636323096644074447665)
                  ·
                    rfl

theorem cell20_722210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_722210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722210 prefixEnd_722210 := by exact prefixLift 722210
  have htrace : WordTrace (prefixWord ++ tailWord_722210) baseStart_722210 baseEnd_722210 := by
    simpa [prefixWord, tailWord_722210, baseEnd_722210] using wordTrace_append hprefix tailTrace_722210
  have hstable : (prefixWord ++ tailWord_722210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722210).length < 2 ^ (prefixWord ++ tailWord_722210).sum := by decide
  have hdescent : baseEnd_722210 < baseStart_722210 := by decide
  rcases family_descends (prefixWord ++ tailWord_722210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722211 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 3]
def baseStart_722211 : Nat := 118140960795 + 722211 * 2 ^ 59
def prefixEnd_722211 : Nat := 4983230072969 + 3 ^ 40 * 722211 * 2
def baseEnd_722211 : Nat := 329636779523892515414327

theorem tailTrace_722211 : CollatzResearch.WordTrace tailWord_722211 prefixEnd_722211 329636779523892515414327 := by
  unfold tailWord_722211
  simp only [CollatzResearch.WordTrace]
  refine ⟨26341199186560365664006487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17560799457706910442670991 26341199186560365664006487)
  ·
    refine ⟨39511798779840548496009731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26341199186560365664006487 39511798779840548496009731)
    ·
      refine ⟨59267698169760822744014597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39511798779840548496009731 59267698169760822744014597)
      ·
        refine ⟨11112693406830154264502737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59267698169760822744014597 11112693406830154264502737)
        ·
          refine ⟨8334520055122615698377053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11112693406830154264502737 8334520055122615698377053)
          ·
            refine ⟨3125445020670980886891395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8334520055122615698377053 3125445020670980886891395)
            ·
              refine ⟨4688167531006471330337093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125445020670980886891395 4688167531006471330337093)
              ·
                refine ⟨879031412063713374438205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4688167531006471330337093 879031412063713374438205)
                ·
                  refine ⟨329636779523892515414327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879031412063713374438205 329636779523892515414327)
                  ·
                    rfl

theorem cell20_722211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_722211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722211 prefixEnd_722211 := by exact prefixLift 722211
  have htrace : WordTrace (prefixWord ++ tailWord_722211) baseStart_722211 baseEnd_722211 := by
    simpa [prefixWord, tailWord_722211, baseEnd_722211] using wordTrace_append hprefix tailTrace_722211
  have hstable : (prefixWord ++ tailWord_722211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722211).length < 2 ^ (prefixWord ++ tailWord_722211).sum := by decide
  have hdescent : baseEnd_722211 < baseStart_722211 := by decide
  rcases family_descends (prefixWord ++ tailWord_722211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722221 : List Nat := [1, 5, 3, 1, 1, 1, 3, 5]
def baseStart_722221 : Nat := 118140960795 + 722221 * 2 ^ 59
def prefixEnd_722221 : Nat := 4983230072969 + 3 ^ 40 * 722221 * 2
def baseEnd_722221 : Nat := 109880447932125641693651

theorem tailTrace_722221 : CollatzResearch.WordTrace tailWord_722221 prefixEnd_722221 109880447932125641693651 := by
  unfold tailWord_722221
  simp only [CollatzResearch.WordTrace]
  refine ⟨26341563916524137371870517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17561042611016091581247011 26341563916524137371870517)
  ·
    refine ⟨2469521617174137878612861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26341563916524137371870517 2469521617174137878612861)
    ·
      refine ⟨926070606440301704479823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2469521617174137878612861 926070606440301704479823)
      ·
        refine ⟨1389105909660452556719735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926070606440301704479823 1389105909660452556719735)
        ·
          refine ⟨2083658864490678835079603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389105909660452556719735 2083658864490678835079603)
          ·
            refine ⟨3125488296736018252619405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083658864490678835079603 3125488296736018252619405)
            ·
              refine ⟨1172058111276006844732277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3125488296736018252619405 1172058111276006844732277)
              ·
                refine ⟨109880447932125641693651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1172058111276006844732277 109880447932125641693651)
                ·
                  rfl

theorem cell20_722221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_722221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722221 prefixEnd_722221 := by exact prefixLift 722221
  have htrace : WordTrace (prefixWord ++ tailWord_722221) baseStart_722221 baseEnd_722221 := by
    simpa [prefixWord, tailWord_722221, baseEnd_722221] using wordTrace_append hprefix tailTrace_722221
  have hstable : (prefixWord ++ tailWord_722221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722221).length < 2 ^ (prefixWord ++ tailWord_722221).sum := by decide
  have hdescent : baseEnd_722221 < baseStart_722221 := by decide
  rcases family_descends (prefixWord ++ tailWord_722221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722228 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_722228 : Nat := 118140960795 + 722228 * 2 ^ 59
def prefixEnd_722228 : Nat := 4983230072969 + 3 ^ 40 * 722228 * 2
def baseEnd_722228 : Nat := 329644538787116011847591

theorem tailTrace_722228 : CollatzResearch.WordTrace tailWord_722228 prefixEnd_722228 329644538787116011847591 := by
  unfold tailWord_722228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13170909613749388783687669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17561212818332518378250225 13170909613749388783687669)
  ·
    refine ⟨1234772776289005198470719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13170909613749388783687669 1234772776289005198470719)
    ·
      refine ⟨1852159164433507797706079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1234772776289005198470719 1852159164433507797706079)
      ·
        refine ⟨2778238746650261696559119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852159164433507797706079 2778238746650261696559119)
        ·
          refine ⟨4167358119975392544838679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778238746650261696559119 4167358119975392544838679)
          ·
            refine ⟨6251037179963088817258019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4167358119975392544838679 6251037179963088817258019)
            ·
              refine ⟨9376555769944633225887029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6251037179963088817258019 9376555769944633225887029)
              ·
                refine ⟨879052103432309364926909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9376555769944633225887029 879052103432309364926909)
                ·
                  refine ⟨329644538787116011847591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879052103432309364926909 329644538787116011847591)
                  ·
                    rfl

theorem cell20_722228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_722228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722228 prefixEnd_722228 := by exact prefixLift 722228
  have htrace : WordTrace (prefixWord ++ tailWord_722228) baseStart_722228 baseEnd_722228 := by
    simpa [prefixWord, tailWord_722228, baseEnd_722228] using wordTrace_append hprefix tailTrace_722228
  have hstable : (prefixWord ++ tailWord_722228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722228).length < 2 ^ (prefixWord ++ tailWord_722228).sum := by decide
  have hdescent : baseEnd_722228 < baseStart_722228 := by decide
  rcases family_descends (prefixWord ++ tailWord_722228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722232 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_722232 : Nat := 118140960795 + 722232 * 2 ^ 59
def prefixEnd_722232 : Nat := 4983230072969 + 3 ^ 40 * 722232 * 2
def baseEnd_722232 : Nat := 329646364496109775714241

theorem tailTrace_722232 : CollatzResearch.WordTrace tailWord_722232 prefixEnd_722232 329646364496109775714241 := by
  unfold tailWord_722232
  simp only [CollatzResearch.WordTrace]
  refine ⟨13170982559742143125260475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17561310079656190833680633 13170982559742143125260475)
  ·
    refine ⟨19756473839613214687890713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13170982559742143125260475 19756473839613214687890713)
    ·
      refine ⟨14817355379709911015918035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19756473839613214687890713 14817355379709911015918035)
      ·
        refine ⟨22226033069564866523877053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14817355379709911015918035 22226033069564866523877053)
        ·
          refine ⟨8334762401086824946453895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22226033069564866523877053 8334762401086824946453895)
          ·
            refine ⟨12502143601630237419680843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334762401086824946453895 12502143601630237419680843)
            ·
              refine ⟨18753215402445356129521265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12502143601630237419680843 18753215402445356129521265)
              ·
                refine ⟨14064911551834017097140949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18753215402445356129521265 14064911551834017097140949)
                ·
                  refine ⟨329646364496109775714241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14064911551834017097140949 329646364496109775714241)
                  ·
                    rfl

theorem cell20_722232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_722232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722232 prefixEnd_722232 := by exact prefixLift 722232
  have htrace : WordTrace (prefixWord ++ tailWord_722232) baseStart_722232 baseEnd_722232 := by
    simpa [prefixWord, tailWord_722232, baseEnd_722232] using wordTrace_append hprefix tailTrace_722232
  have hstable : (prefixWord ++ tailWord_722232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722232).length < 2 ^ (prefixWord ++ tailWord_722232).sum := by decide
  have hdescent : baseEnd_722232 < baseStart_722232 := by decide
  rcases family_descends (prefixWord ++ tailWord_722232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722252 : List Nat := [2, 2, 1, 3, 2, 3, 2, 3, 2]
def baseStart_722252 : Nat := 118140960795 + 722252 * 2 ^ 59
def prefixEnd_722252 : Nat := 4983230072969 + 3 ^ 40 * 722252 * 2
def baseEnd_722252 : Nat := 329655493041078595047493

theorem tailTrace_722252 : CollatzResearch.WordTrace tailWord_722252 prefixEnd_722252 329655493041078595047493 := by
  unfold tailWord_722252
  simp only [CollatzResearch.WordTrace]
  refine ⟨13171347289705914833124505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17561796386274553110832673 13171347289705914833124505)
  ·
    refine ⟨9878510467279436124843379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13171347289705914833124505 9878510467279436124843379)
    ·
      refine ⟨14817765700919154187265069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9878510467279436124843379 14817765700919154187265069)
      ·
        refine ⟨5556662137844682820224401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14817765700919154187265069 5556662137844682820224401)
        ·
          refine ⟨4167496603383512115168301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5556662137844682820224401 4167496603383512115168301)
          ·
            refine ⟨1562811226268817043188113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4167496603383512115168301 1562811226268817043188113)
            ·
              refine ⟨1172108419701612782391085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562811226268817043188113 1172108419701612782391085)
              ·
                refine ⟨439540657388104793396657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172108419701612782391085 439540657388104793396657)
                ·
                  refine ⟨329655493041078595047493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439540657388104793396657 329655493041078595047493)
                  ·
                    rfl

theorem cell20_722252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_722252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722252 prefixEnd_722252 := by exact prefixLift 722252
  have htrace : WordTrace (prefixWord ++ tailWord_722252) baseStart_722252 baseEnd_722252 := by
    simpa [prefixWord, tailWord_722252, baseEnd_722252] using wordTrace_append hprefix tailTrace_722252
  have hstable : (prefixWord ++ tailWord_722252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722252).length < 2 ^ (prefixWord ++ tailWord_722252).sum := by decide
  have hdescent : baseEnd_722252 < baseStart_722252 := by decide
  rcases family_descends (prefixWord ++ tailWord_722252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722263 : List Nat := [1, 1, 3, 2, 3, 3, 7]
def baseStart_722263 : Nat := 118140960795 + 722263 * 2 ^ 59
def prefixEnd_722263 : Nat := 4983230072969 + 3 ^ 40 * 722263 * 2
def baseEnd_722263 : Nat := 36628945971201271742309

theorem tailTrace_722263 : CollatzResearch.WordTrace tailWord_722263 prefixEnd_722263 36628945971201271742309 := by
  unfold tailWord_722263
  simp only [CollatzResearch.WordTrace]
  refine ⟨26343095782371978544899443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17562063854914652363266295 26343095782371978544899443)
  ·
    refine ⟨39514643673557967817349165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26343095782371978544899443 39514643673557967817349165)
    ·
      refine ⟨14817991377584237931505937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39514643673557967817349165 14817991377584237931505937)
      ·
        refine ⟨11113493533188178448629453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14817991377584237931505937 11113493533188178448629453)
        ·
          refine ⟨4167560074945566918236045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11113493533188178448629453 4167560074945566918236045)
          ·
            refine ⟨1562835028104587594338517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4167560074945566918236045 1562835028104587594338517)
            ·
              refine ⟨36628945971201271742309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1562835028104587594338517 36628945971201271742309)
              ·
                rfl

theorem cell20_722263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 7].length) (baseStart_722263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722263 prefixEnd_722263 := by exact prefixLift 722263
  have htrace : WordTrace (prefixWord ++ tailWord_722263) baseStart_722263 baseEnd_722263 := by
    simpa [prefixWord, tailWord_722263, baseEnd_722263] using wordTrace_append hprefix tailTrace_722263
  have hstable : (prefixWord ++ tailWord_722263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722263).length < 2 ^ (prefixWord ++ tailWord_722263).sum := by decide
  have hdescent : baseEnd_722263 < baseStart_722263 := by decide
  rcases family_descends (prefixWord ++ tailWord_722263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722301 : List Nat := [1, 4, 1, 1, 2, 2, 3, 6]
def baseStart_722301 : Nat := 118140960795 + 722301 * 2 ^ 59
def prefixEnd_722301 : Nat := 4983230072969 + 3 ^ 40 * 722301 * 2
def baseEnd_722301 : Nat := 109892619325417400804653

theorem tailTrace_722301 : CollatzResearch.WordTrace tailWord_722301 prefixEnd_722301 109892619325417400804653 := by
  unfold tailWord_722301
  simp only [CollatzResearch.WordTrace]
  refine ⟨26344481756234311034782757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17562987837489540689855171 26344481756234311034782757)
  ·
    refine ⟨4939590329293933319021767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26344481756234311034782757 4939590329293933319021767)
    ·
      refine ⟨7409385493940899978532651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4939590329293933319021767 7409385493940899978532651)
      ·
        refine ⟨11114078240911349967798977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7409385493940899978532651 11114078240911349967798977)
        ·
          refine ⟨8335558680683512475849233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11114078240911349967798977 8335558680683512475849233)
          ·
            refine ⟨6251669010512634356886925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8335558680683512475849233 6251669010512634356886925)
            ·
              refine ⟨2344375878942237883832597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6251669010512634356886925 2344375878942237883832597)
              ·
                refine ⟨109892619325417400804653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2344375878942237883832597 109892619325417400804653)
                ·
                  rfl

theorem cell20_722301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_722301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722301 prefixEnd_722301 := by exact prefixLift 722301
  have htrace : WordTrace (prefixWord ++ tailWord_722301) baseStart_722301 baseEnd_722301 := by
    simpa [prefixWord, tailWord_722301, baseEnd_722301] using wordTrace_append hprefix tailTrace_722301
  have hstable : (prefixWord ++ tailWord_722301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722301).length < 2 ^ (prefixWord ++ tailWord_722301).sum := by decide
  have hdescent : baseEnd_722301 < baseStart_722301 := by decide
  rcases family_descends (prefixWord ++ tailWord_722301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722328 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_722328 : Nat := 118140960795 + 722328 * 2 ^ 59
def prefixEnd_722328 : Nat := 4983230072969 + 3 ^ 40 * 722328 * 2
def baseEnd_722328 : Nat := 329690181511960108513849

theorem tailTrace_722328 : CollatzResearch.WordTrace tailWord_722328 prefixEnd_722328 329690181511960108513849 := by
  unfold tailWord_722328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13172733263568247323007819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17563644351424329764010425 13172733263568247323007819)
  ·
    refine ⟨19759099895352370984511729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13172733263568247323007819 19759099895352370984511729)
    ·
      refine ⟨14819324921514278238383797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19759099895352370984511729 14819324921514278238383797)
      ·
        refine ⟨1389311711391963584848481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14819324921514278238383797 1389311711391963584848481)
        ·
          refine ⟨1041983783543972688636361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1389311711391963584848481 1041983783543972688636361)
          ·
            refine ⟨781487837657979516477271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1041983783543972688636361 781487837657979516477271)
            ·
              refine ⟨1172231756486969274715907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781487837657979516477271 1172231756486969274715907)
              ·
                refine ⟨1758347634730453912073861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172231756486969274715907 1758347634730453912073861)
                ·
                  refine ⟨329690181511960108513849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758347634730453912073861 329690181511960108513849)
                  ·
                    rfl

theorem cell20_722328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_722328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722328 prefixEnd_722328 := by exact prefixLift 722328
  have htrace : WordTrace (prefixWord ++ tailWord_722328) baseStart_722328 baseEnd_722328 := by
    simpa [prefixWord, tailWord_722328, baseEnd_722328] using wordTrace_append hprefix tailTrace_722328
  have hstable : (prefixWord ++ tailWord_722328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722328).length < 2 ^ (prefixWord ++ tailWord_722328).sum := by decide
  have hdescent : baseEnd_722328 < baseStart_722328 := by decide
  rcases family_descends (prefixWord ++ tailWord_722328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722339 : List Nat := [1, 1, 1, 4, 1, 3, 4, 5]
def baseStart_722339 : Nat := 118140960795 + 722339 * 2 ^ 59
def prefixEnd_722339 : Nat := 4983230072969 + 3 ^ 40 * 722339 * 2
def baseEnd_722339 : Nat := 109898400737230986382379

theorem tailTrace_722339 : CollatzResearch.WordTrace tailWord_722339 prefixEnd_722339 109898400737230986382379 := by
  unfold tailWord_722339
  simp only [CollatzResearch.WordTrace]
  refine ⟨26345867730096643524666071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17563911820064429016444047 26345867730096643524666071)
  ·
    refine ⟨39518801595144965286999107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26345867730096643524666071 39518801595144965286999107)
    ·
      refine ⟨59278202392717447930498661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39518801595144965286999107 59278202392717447930498661)
      ·
        refine ⟨11114662948634521486968499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59278202392717447930498661 11114662948634521486968499)
        ·
          refine ⟨16671994422951782230452749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11114662948634521486968499 16671994422951782230452749)
          ·
            refine ⟨6251997908606918336419781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16671994422951782230452749 6251997908606918336419781)
            ·
              refine ⟨1172249607863797188078709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6251997908606918336419781 1172249607863797188078709)
              ·
                refine ⟨109898400737230986382379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1172249607863797188078709 109898400737230986382379)
                ·
                  rfl

theorem cell20_722339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_722339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722339 prefixEnd_722339 := by exact prefixLift 722339
  have htrace : WordTrace (prefixWord ++ tailWord_722339) baseStart_722339 baseEnd_722339 := by
    simpa [prefixWord, tailWord_722339, baseEnd_722339] using wordTrace_append hprefix tailTrace_722339
  have hstable : (prefixWord ++ tailWord_722339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722339).length < 2 ^ (prefixWord ++ tailWord_722339).sum := by decide
  have hdescent : baseEnd_722339 < baseStart_722339 := by decide
  rcases family_descends (prefixWord ++ tailWord_722339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722380 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_722380 : Nat := 118140960795 + 722380 * 2 ^ 59
def prefixEnd_722380 : Nat := 4983230072969 + 3 ^ 40 * 722380 * 2
def baseEnd_722380 : Nat := 329713915728879038780303

theorem tailTrace_722380 : CollatzResearch.WordTrace tailWord_722380 prefixEnd_722380 329713915728879038780303 := by
  unfold tailWord_722380
  simp only [CollatzResearch.WordTrace]
  refine ⟨13173681561474053763454297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17564908748632071684605729 13173681561474053763454297)
  ·
    refine ⟨9880261171105540322590723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13173681561474053763454297 9880261171105540322590723)
    ·
      refine ⟨14820391756658310483886085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9880261171105540322590723 14820391756658310483886085)
      ·
        refine ⟨2778823454373433215728641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14820391756658310483886085 2778823454373433215728641)
        ·
          refine ⟨2084117590780074911796481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778823454373433215728641 2084117590780074911796481)
          ·
            refine ⟨1563088193085056183847361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084117590780074911796481 1563088193085056183847361)
            ·
              refine ⟨1172316144813792137885521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563088193085056183847361 1172316144813792137885521)
              ·
                refine ⟨879237108610344103414141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172316144813792137885521 879237108610344103414141)
                ·
                  refine ⟨329713915728879038780303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879237108610344103414141 329713915728879038780303)
                  ·
                    rfl

theorem cell20_722380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_722380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722380 prefixEnd_722380 := by exact prefixLift 722380
  have htrace : WordTrace (prefixWord ++ tailWord_722380) baseStart_722380 baseEnd_722380 := by
    simpa [prefixWord, tailWord_722380, baseEnd_722380] using wordTrace_append hprefix tailTrace_722380
  have hstable : (prefixWord ++ tailWord_722380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722380).length < 2 ^ (prefixWord ++ tailWord_722380).sum := by decide
  have hdescent : baseEnd_722380 < baseStart_722380 := by decide
  rcases family_descends (prefixWord ++ tailWord_722380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722391 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_722391 : Nat := 118140960795 + 722391 * 2 ^ 59
def prefixEnd_722391 : Nat := 4983230072969 + 3 ^ 40 * 722391 * 2
def baseEnd_722391 : Nat := 329718936428611889413591

theorem tailTrace_722391 : CollatzResearch.WordTrace tailWord_722391 prefixEnd_722391 329718936428611889413591 := by
  unfold tailWord_722391
  simp only [CollatzResearch.WordTrace]
  refine ⟨26347764325908256405559027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17565176217272170937039351 26347764325908256405559027)
  ·
    refine ⟨39521646488862384608338541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26347764325908256405559027 39521646488862384608338541)
    ·
      refine ⟨14820617433323394228126953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39521646488862384608338541 14820617433323394228126953)
      ·
        refine ⟨11115463074992545671095215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14820617433323394228126953 11115463074992545671095215)
        ·
          refine ⟨16673194612488818506642823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11115463074992545671095215 16673194612488818506642823)
          ·
            refine ⟨25009791918733227759964235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16673194612488818506642823 25009791918733227759964235)
            ·
              refine ⟨37514687878099841639946353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25009791918733227759964235 37514687878099841639946353)
              ·
                refine ⟨28136015908574881229959765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37514687878099841639946353 28136015908574881229959765)
                ·
                  refine ⟨329718936428611889413591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28136015908574881229959765 329718936428611889413591)
                  ·
                    rfl

theorem cell20_722391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_722391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722391 prefixEnd_722391 := by exact prefixLift 722391
  have htrace : WordTrace (prefixWord ++ tailWord_722391) baseStart_722391 baseEnd_722391 := by
    simpa [prefixWord, tailWord_722391, baseEnd_722391] using wordTrace_append hprefix tailTrace_722391
  have hstable : (prefixWord ++ tailWord_722391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722391).length < 2 ^ (prefixWord ++ tailWord_722391).sum := by decide
  have hdescent : baseEnd_722391 < baseStart_722391 := by decide
  rcases family_descends (prefixWord ++ tailWord_722391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722394 : List Nat := [3, 1, 1, 2, 3, 4, 1, 5]
def baseStart_722394 : Nat := 118140960795 + 722394 * 2 ^ 59
def prefixEnd_722394 : Nat := 4983230072969 + 3 ^ 40 * 722394 * 2
def baseEnd_722394 : Nat := 109906768570119070771193

theorem tailTrace_722394 : CollatzResearch.WordTrace tailWord_722394 prefixEnd_722394 109906768570119070771193 := by
  unfold tailWord_722394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6586968436224346979479559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17565249163264925278612157 6586968436224346979479559)
  ·
    refine ⟨9880452654336520469219339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6586968436224346979479559 9880452654336520469219339)
    ·
      refine ⟨14820678981504780703829009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9880452654336520469219339 14820678981504780703829009)
      ·
        refine ⟨11115509236128585527871757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14820678981504780703829009 11115509236128585527871757)
        ·
          refine ⟨4168315963548219572951909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11115509236128585527871757 4168315963548219572951909)
          ·
            refine ⟨781559243165291169928483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4168315963548219572951909 781559243165291169928483)
            ·
              refine ⟨1172338864747936754892725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781559243165291169928483 1172338864747936754892725)
              ·
                refine ⟨109906768570119070771193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1172338864747936754892725 109906768570119070771193)
                ·
                  rfl

theorem cell20_722394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_722394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722394 prefixEnd_722394 := by exact prefixLift 722394
  have htrace : WordTrace (prefixWord ++ tailWord_722394) baseStart_722394 baseEnd_722394 := by
    simpa [prefixWord, tailWord_722394, baseEnd_722394] using wordTrace_append hprefix tailTrace_722394
  have hstable : (prefixWord ++ tailWord_722394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722394).length < 2 ^ (prefixWord ++ tailWord_722394).sum := by decide
  have hdescent : baseEnd_722394 < baseStart_722394 := by decide
  rcases family_descends (prefixWord ++ tailWord_722394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722401 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 3]
def baseStart_722401 : Nat := 118140960795 + 722401 * 2 ^ 59
def prefixEnd_722401 : Nat := 4983230072969 + 3 ^ 40 * 722401 * 2
def baseEnd_722401 : Nat := 329723500701096299080217

theorem tailTrace_722401 : CollatzResearch.WordTrace tailWord_722401 prefixEnd_722401 329723500701096299080217 := by
  unfold tailWord_722401
  simp only [CollatzResearch.WordTrace]
  refine ⟨26348129055872028113423057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17565419370581352075615371 26348129055872028113423057)
  ·
    refine ⟨19761096791904021085067293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26348129055872028113423057 19761096791904021085067293)
    ·
      refine ⟨7410411296964007906900235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19761096791904021085067293 7410411296964007906900235)
      ·
        refine ⟨11115616945446011860350353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7410411296964007906900235 11115616945446011860350353)
        ·
          refine ⟨8336712709084508895262765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11115616945446011860350353 8336712709084508895262765)
          ·
            refine ⟨3126267265906690835723537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8336712709084508895262765 3126267265906690835723537)
            ·
              refine ⟨2344700449430018126792653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3126267265906690835723537 2344700449430018126792653)
              ·
                refine ⟨879262668536256797547245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2344700449430018126792653 879262668536256797547245)
                ·
                  refine ⟨329723500701096299080217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879262668536256797547245 329723500701096299080217)
                  ·
                    rfl

theorem cell20_722401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_722401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722401 prefixEnd_722401 := by exact prefixLift 722401
  have htrace : WordTrace (prefixWord ++ tailWord_722401) baseStart_722401 baseEnd_722401 := by
    simpa [prefixWord, tailWord_722401, baseEnd_722401] using wordTrace_append hprefix tailTrace_722401
  have hstable : (prefixWord ++ tailWord_722401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722401).length < 2 ^ (prefixWord ++ tailWord_722401).sum := by decide
  have hdescent : baseEnd_722401 < baseStart_722401 := by decide
  rcases family_descends (prefixWord ++ tailWord_722401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722408 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_722408 : Nat := 118140960795 + 722408 * 2 ^ 59
def prefixEnd_722408 : Nat := 4983230072969 + 3 ^ 40 * 722408 * 2
def baseEnd_722408 : Nat := 329726695691835385846855

theorem tailTrace_722408 : CollatzResearch.WordTrace tailWord_722408 prefixEnd_722408 329726695691835385846855 := by
  unfold tailWord_722408
  simp only [CollatzResearch.WordTrace]
  refine ⟨13174192183423334154463939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17565589577897778872618585 13174192183423334154463939)
  ·
    refine ⟨19761288275135001231695909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13174192183423334154463939 19761288275135001231695909)
    ·
      refine ⟨3705241551587812730942983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19761288275135001231695909 3705241551587812730942983)
      ·
        refine ⟨5557862327381719096414475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3705241551587812730942983 5557862327381719096414475)
        ·
          refine ⟨8336793491072578644621713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5557862327381719096414475 8336793491072578644621713)
          ·
            refine ⟨6252595118304433983466285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8336793491072578644621713 6252595118304433983466285)
            ·
              refine ⟨2344723169364162743799857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6252595118304433983466285 2344723169364162743799857)
              ·
                refine ⟨1758542377023122057849893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2344723169364162743799857 1758542377023122057849893)
                ·
                  refine ⟨329726695691835385846855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758542377023122057849893 329726695691835385846855)
                  ·
                    rfl

theorem cell20_722408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_722408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722408 prefixEnd_722408 := by exact prefixLift 722408
  have htrace : WordTrace (prefixWord ++ tailWord_722408) baseStart_722408 baseEnd_722408 := by
    simpa [prefixWord, tailWord_722408, baseEnd_722408] using wordTrace_append hprefix tailTrace_722408
  have hstable : (prefixWord ++ tailWord_722408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722408).length < 2 ^ (prefixWord ++ tailWord_722408).sum := by decide
  have hdescent : baseEnd_722408 < baseStart_722408 := by decide
  rcases family_descends (prefixWord ++ tailWord_722408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722421 : List Nat := [1, 3, 5, 1, 1, 2, 2, 3, 2]
def baseStart_722421 : Nat := 118140960795 + 722421 * 2 ^ 59
def prefixEnd_722421 : Nat := 4983230072969 + 3 ^ 40 * 722421 * 2
def baseEnd_722421 : Nat := 329732629246065118413469

theorem tailTrace_722421 : CollatzResearch.WordTrace tailWord_722421 prefixEnd_722421 329732629246065118413469 := by
  unfold tailWord_722421
  simp only [CollatzResearch.WordTrace]
  refine ⟨26348858515799571529151117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17565905677199714352767411 26348858515799571529151117)
  ·
    refine ⟨9880821943424839323431669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26348858515799571529151117 9880821943424839323431669)
    ·
      refine ⟨926327057196078686571719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9880821943424839323431669 926327057196078686571719)
      ·
        refine ⟨1389490585794118029857579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926327057196078686571719 1389490585794118029857579)
        ·
          refine ⟨2084235878691177044786369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389490585794118029857579 2084235878691177044786369)
          ·
            refine ⟨1563176909018382783589777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084235878691177044786369 1563176909018382783589777)
            ·
              refine ⟨1172382681763787087692333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563176909018382783589777 1172382681763787087692333)
              ·
                refine ⟨439643505661420157884625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172382681763787087692333 439643505661420157884625)
                ·
                  refine ⟨329732629246065118413469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439643505661420157884625 329732629246065118413469)
                  ·
                    rfl

theorem cell20_722421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_722421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722421 prefixEnd_722421 := by exact prefixLift 722421
  have htrace : WordTrace (prefixWord ++ tailWord_722421) baseStart_722421 baseEnd_722421 := by
    simpa [prefixWord, tailWord_722421, baseEnd_722421] using wordTrace_append hprefix tailTrace_722421
  have hstable : (prefixWord ++ tailWord_722421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722421).length < 2 ^ (prefixWord ++ tailWord_722421).sum := by decide
  have hdescent : baseEnd_722421 < baseStart_722421 := by decide
  rcases family_descends (prefixWord ++ tailWord_722421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722438 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_722438 : Nat := 118140960795 + 722438 * 2 ^ 59
def prefixEnd_722438 : Nat := 4983230072969 + 3 ^ 40 * 722438 * 2
def baseEnd_722438 : Nat := 329740388509288614846733

theorem tailTrace_722438 : CollatzResearch.WordTrace tailWord_722438 prefixEnd_722438 329740388509288614846733 := by
  unfold tailWord_722438
  simp only [CollatzResearch.WordTrace]
  refine ⟨823421204898061982266249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17566319037825322288346645 823421204898061982266249)
  ·
    refine ⟨617565903673546486699687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 823421204898061982266249 617565903673546486699687)
    ·
      refine ⟨926348855510319730049531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617565903673546486699687 926348855510319730049531)
      ·
        refine ⟨1389523283265479595074297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926348855510319730049531 1389523283265479595074297)
        ·
          refine ⟨1042142462449109696305723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1389523283265479595074297 1042142462449109696305723)
          ·
            refine ⟨1563213693673664544458585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042142462449109696305723 1563213693673664544458585)
            ·
              refine ⟨1172410270255248408343939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563213693673664544458585 1172410270255248408343939)
              ·
                refine ⟨1758615405382872612515909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172410270255248408343939 1758615405382872612515909)
                ·
                  refine ⟨329740388509288614846733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758615405382872612515909 329740388509288614846733)
                  ·
                    rfl

theorem cell20_722438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_722438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722438 prefixEnd_722438 := by exact prefixLift 722438
  have htrace : WordTrace (prefixWord ++ tailWord_722438) baseStart_722438 baseEnd_722438 := by
    simpa [prefixWord, tailWord_722438, baseEnd_722438] using wordTrace_append hprefix tailTrace_722438
  have hstable : (prefixWord ++ tailWord_722438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722438).length < 2 ^ (prefixWord ++ tailWord_722438).sum := by decide
  have hdescent : baseEnd_722438 < baseStart_722438 := by decide
  rcases family_descends (prefixWord ++ tailWord_722438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722439 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_722439 : Nat := 118140960795 + 722439 * 2 ^ 59
def prefixEnd_722439 : Nat := 4983230072969 + 3 ^ 40 * 722439 * 2
def baseEnd_722439 : Nat := 329740844936537055813395

theorem tailTrace_722439 : CollatzResearch.WordTrace tailWord_722439 prefixEnd_722439 329740844936537055813395 := by
  unfold tailWord_722439
  simp only [CollatzResearch.WordTrace]
  refine ⟨26349515029734360603306371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17566343353156240402204247 26349515029734360603306371)
  ·
    refine ⟨39524272544601540904959557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26349515029734360603306371 39524272544601540904959557)
    ·
      refine ⟨7410801102112788919679917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39524272544601540904959557 7410801102112788919679917)
      ·
        refine ⟨2779050413292295844879969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7410801102112788919679917 2779050413292295844879969)
        ·
          refine ⟨2084287809969221883659977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2779050413292295844879969 2084287809969221883659977)
          ·
            refine ⟨1563215857476916412744983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084287809969221883659977 1563215857476916412744983)
            ·
              refine ⟨2344823786215374619117475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563215857476916412744983 2344823786215374619117475)
              ·
                refine ⟨3517235679323061928676213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344823786215374619117475 3517235679323061928676213)
                ·
                  refine ⟨329740844936537055813395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3517235679323061928676213 329740844936537055813395)
                  ·
                    rfl

theorem cell20_722439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_722439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722439 prefixEnd_722439 := by exact prefixLift 722439
  have htrace : WordTrace (prefixWord ++ tailWord_722439) baseStart_722439 baseEnd_722439 := by
    simpa [prefixWord, tailWord_722439, baseEnd_722439] using wordTrace_append hprefix tailTrace_722439
  have hstable : (prefixWord ++ tailWord_722439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722439).length < 2 ^ (prefixWord ++ tailWord_722439).sum := by decide
  have hdescent : baseEnd_722439 < baseStart_722439 := by decide
  rcases family_descends (prefixWord ++ tailWord_722439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722452 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_722452 : Nat := 118140960795 + 722452 * 2 ^ 59
def prefixEnd_722452 : Nat := 4983230072969 + 3 ^ 40 * 722452 * 2
def baseEnd_722452 : Nat := 329746778490766788380009

theorem tailTrace_722452 : CollatzResearch.WordTrace tailWord_722452 prefixEnd_722452 329746778490766788380009 := by
  unfold tailWord_722452
  simp only [CollatzResearch.WordTrace]
  refine ⟨13174994589343631911764805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17566659452458175882353073 13174994589343631911764805)
  ·
    refine ⟨2470311485501930983455901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13174994589343631911764805 2470311485501930983455901)
    ·
      refine ⟨926366807063224118795963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2470311485501930983455901 926366807063224118795963)
      ·
        refine ⟨1389550210594836178193945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926366807063224118795963 1389550210594836178193945)
        ·
          refine ⟨1042162657946127133645459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1389550210594836178193945 1042162657946127133645459)
          ·
            refine ⟨1563243986919190700468189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042162657946127133645459 1563243986919190700468189)
            ·
              refine ⟨586216495094696512675571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1563243986919190700468189 586216495094696512675571)
              ·
                refine ⟨879324742642044769013357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586216495094696512675571 879324742642044769013357)
                ·
                  refine ⟨329746778490766788380009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879324742642044769013357 329746778490766788380009)
                  ·
                    rfl

theorem cell20_722452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_722452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722452 prefixEnd_722452 := by exact prefixLift 722452
  have htrace : WordTrace (prefixWord ++ tailWord_722452) baseStart_722452 baseEnd_722452 := by
    simpa [prefixWord, tailWord_722452, baseEnd_722452] using wordTrace_append hprefix tailTrace_722452
  have hstable : (prefixWord ++ tailWord_722452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722452).length < 2 ^ (prefixWord ++ tailWord_722452).sum := by decide
  have hdescent : baseEnd_722452 < baseStart_722452 := by decide
  rcases family_descends (prefixWord ++ tailWord_722452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722462 : List Nat := [4, 3, 3, 1, 1, 2, 2, 4]
def baseStart_722462 : Nat := 118140960795 + 722462 * 2 ^ 59
def prefixEnd_722462 : Nat := 4983230072969 + 3 ^ 40 * 722462 * 2
def baseEnd_722462 : Nat := 109917114254417066015545

theorem tailTrace_722462 : CollatzResearch.WordTrace tailWord_722462 prefixEnd_722462 109917114254417066015545 := by
  unfold tailWord_722462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293794238581379441424205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17566902605767357020929093 3293794238581379441424205)
  ·
    refine ⟨1235172839468017290534077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3293794238581379441424205 1235172839468017290534077)
    ·
      refine ⟨463189814800506483950279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1235172839468017290534077 463189814800506483950279)
      ·
        refine ⟨694784722200759725925419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463189814800506483950279 694784722200759725925419)
        ·
          refine ⟨1042177083301139588888129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694784722200759725925419 1042177083301139588888129)
          ·
            refine ⟨781632812475854691666097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042177083301139588888129 781632812475854691666097)
            ·
              refine ⟨586224609356891018749573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781632812475854691666097 586224609356891018749573)
              ·
                refine ⟨109917114254417066015545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586224609356891018749573 109917114254417066015545)
                ·
                  rfl

theorem cell20_722462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_722462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722462 prefixEnd_722462 := by exact prefixLift 722462
  have htrace : WordTrace (prefixWord ++ tailWord_722462) baseStart_722462 baseEnd_722462 := by
    simpa [prefixWord, tailWord_722462, baseEnd_722462] using wordTrace_append hprefix tailTrace_722462
  have hstable : (prefixWord ++ tailWord_722462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722462).length < 2 ^ (prefixWord ++ tailWord_722462).sum := by decide
  have hdescent : baseEnd_722462 < baseStart_722462 := by decide
  rcases family_descends (prefixWord ++ tailWord_722462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722553 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 3]
def baseStart_722553 : Nat := 118140960795 + 722553 * 2 ^ 59
def prefixEnd_722553 : Nat := 4983230072969 + 3 ^ 40 * 722553 * 2
def baseEnd_722553 : Nat := 329792877642859326012929

theorem tailTrace_722553 : CollatzResearch.WordTrace tailWord_722553 prefixEnd_722553 329792877642859326012929 := by
  unfold tailWord_722553
  simp only [CollatzResearch.WordTrace]
  refine ⟨26353672951321358072956313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17569115300880905381970875 26353672951321358072956313)
  ·
    refine ⟨19765254713491018554717235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26353672951321358072956313 19765254713491018554717235)
    ·
      refine ⟨29647882070236527832075853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19765254713491018554717235 29647882070236527832075853)
      ·
        refine ⟨11117955776338697937028445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29647882070236527832075853 11117955776338697937028445)
        ·
          refine ⟨4169233416127011726385667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11117955776338697937028445 4169233416127011726385667)
          ·
            refine ⟨6253850124190517589578501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169233416127011726385667 6253850124190517589578501)
            ·
              refine ⟨1172596898285722048045969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6253850124190517589578501 1172596898285722048045969)
              ·
                refine ⟨879447673714291536034477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172596898285722048045969 879447673714291536034477)
                ·
                  refine ⟨329792877642859326012929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879447673714291536034477 329792877642859326012929)
                  ·
                    rfl

theorem cell20_722553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_722553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722553 prefixEnd_722553 := by exact prefixLift 722553
  have htrace : WordTrace (prefixWord ++ tailWord_722553) baseStart_722553 baseEnd_722553 := by
    simpa [prefixWord, tailWord_722553, baseEnd_722553] using wordTrace_append hprefix tailTrace_722553
  have hstable : (prefixWord ++ tailWord_722553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722553).length < 2 ^ (prefixWord ++ tailWord_722553).sum := by decide
  have hdescent : baseEnd_722553 < baseStart_722553 := by decide
  rcases family_descends (prefixWord ++ tailWord_722553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722567 : List Nat := [1, 1, 4, 2, 1, 3, 3, 5]
def baseStart_722567 : Nat := 118140960795 + 722567 * 2 ^ 59
def prefixEnd_722567 : Nat := 4983230072969 + 3 ^ 40 * 722567 * 2
def baseEnd_722567 : Nat := 109933089208112499848735

theorem tailTrace_722567 : CollatzResearch.WordTrace tailWord_722567 prefixEnd_722567 109933089208112499848735 := by
  unfold tailWord_722567
  simp only [CollatzResearch.WordTrace]
  refine ⟨26354183573270638463965955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17569455715513758975977303 26354183573270638463965955)
  ·
    refine ⟨39531275359905957695948933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26354183573270638463965955 39531275359905957695948933)
    ·
      refine ⟨7412114129982367067990425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39531275359905957695948933 7412114129982367067990425)
      ·
        refine ⟨5559085597486775300992819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7412114129982367067990425 5559085597486775300992819)
        ·
          refine ⟨8338628396230162951489229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559085597486775300992819 8338628396230162951489229)
          ·
            refine ⟨3126985648586311106808461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8338628396230162951489229 3126985648586311106808461)
            ·
              refine ⟨1172619618219866665053173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3126985648586311106808461 1172619618219866665053173)
              ·
                refine ⟨109933089208112499848735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1172619618219866665053173 109933089208112499848735)
                ·
                  rfl

theorem cell20_722567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_722567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722567 prefixEnd_722567 := by exact prefixLift 722567
  have htrace : WordTrace (prefixWord ++ tailWord_722567) baseStart_722567 baseEnd_722567 := by
    simpa [prefixWord, tailWord_722567, baseEnd_722567] using wordTrace_append hprefix tailTrace_722567
  have hstable : (prefixWord ++ tailWord_722567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722567).length < 2 ^ (prefixWord ++ tailWord_722567).sum := by decide
  have hdescent : baseEnd_722567 < baseStart_722567 := by decide
  rcases family_descends (prefixWord ++ tailWord_722567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722584 : List Nat := [2, 1, 2, 4, 1, 3, 3, 4]
def baseStart_722584 : Nat := 118140960795 + 722584 * 2 ^ 59
def prefixEnd_722584 : Nat := 4983230072969 + 3 ^ 40 * 722584 * 2
def baseEnd_722584 : Nat := 109935675629186998659823

theorem tailTrace_722584 : CollatzResearch.WordTrace tailWord_722584 prefixEnd_722584 109935675629186998659823 := by
  unfold tailWord_722584
  simp only [CollatzResearch.WordTrace]
  refine ⟨13177401807104525183667403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17569869076139366911556537 13177401807104525183667403)
  ·
    refine ⟨19766102710656787775501105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13177401807104525183667403 19766102710656787775501105)
    ·
      refine ⟨14824577032992590831625829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19766102710656787775501105 14824577032992590831625829)
      ·
        refine ⟨2779608193686110780929843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14824577032992590831625829 2779608193686110780929843)
        ·
          refine ⟨4169412290529166171394765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779608193686110780929843 4169412290529166171394765)
          ·
            refine ⟨1563529608948437314273037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4169412290529166171394765 1563529608948437314273037)
            ·
              refine ⟨586323603355663992852389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1563529608948437314273037 586323603355663992852389)
              ·
                refine ⟨109935675629186998659823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586323603355663992852389 109935675629186998659823)
                ·
                  rfl

theorem cell20_722584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_722584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722584 prefixEnd_722584 := by exact prefixLift 722584
  have htrace : WordTrace (prefixWord ++ tailWord_722584) baseStart_722584 baseEnd_722584 := by
    simpa [prefixWord, tailWord_722584, baseEnd_722584] using wordTrace_append hprefix tailTrace_722584
  have hstable : (prefixWord ++ tailWord_722584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722584).length < 2 ^ (prefixWord ++ tailWord_722584).sum := by decide
  have hdescent : baseEnd_722584 < baseStart_722584 := by decide
  rcases family_descends (prefixWord ++ tailWord_722584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722605 : List Nat := [1, 5, 2, 1, 1, 1, 9]
def baseStart_722605 : Nat := 118140960795 + 722605 * 2 ^ 59
def prefixEnd_722605 : Nat := 4983230072969 + 3 ^ 40 * 722605 * 2
def baseEnd_722605 : Nat := 36646290206642028475487

theorem tailTrace_722605 : CollatzResearch.WordTrace tailWord_722605 prefixEnd_722605 36646290206642028475487 := by
  unfold tailWord_722605
  simp only [CollatzResearch.WordTrace]
  refine ⟨26355569547132970953849269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17570379698088647302566179 26355569547132970953849269)
  ·
    refine ⟨2470834645043716026923369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26355569547132970953849269 2470834645043716026923369)
    ·
      refine ⟨1853125983782787020192527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470834645043716026923369 1853125983782787020192527)
      ·
        refine ⟨2779688975674180530288791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853125983782787020192527 2779688975674180530288791)
        ·
          refine ⟨4169533463511270795433187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779688975674180530288791 4169533463511270795433187)
          ·
            refine ⟨6254300195266906193149781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169533463511270795433187 6254300195266906193149781)
            ·
              refine ⟨36646290206642028475487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6254300195266906193149781 36646290206642028475487)
              ·
                rfl

theorem cell20_722605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 9].length) (baseStart_722605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722605 prefixEnd_722605 := by exact prefixLift 722605
  have htrace : WordTrace (prefixWord ++ tailWord_722605) baseStart_722605 baseEnd_722605 := by
    simpa [prefixWord, tailWord_722605, baseEnd_722605] using wordTrace_append hprefix tailTrace_722605
  have hstable : (prefixWord ++ tailWord_722605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722605).length < 2 ^ (prefixWord ++ tailWord_722605).sum := by decide
  have hdescent : baseEnd_722605 < baseStart_722605 := by decide
  rcases family_descends (prefixWord ++ tailWord_722605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722615 : List Nat := [1, 1, 3, 1, 5, 1, 2, 4, 2]
def baseStart_722615 : Nat := 118140960795 + 722615 * 2 ^ 59
def prefixEnd_722615 : Nat := 4983230072969 + 3 ^ 40 * 722615 * 2
def baseEnd_722615 : Nat := 329821176132262665946009

theorem tailTrace_722615 : CollatzResearch.WordTrace tailWord_722615 prefixEnd_722615 329821176132262665946009 := by
  unfold tailWord_722615
  simp only [CollatzResearch.WordTrace]
  refine ⟨26355934277096742661713299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17570622851397828441142199 26355934277096742661713299)
  ·
    refine ⟨39533901415645113992569949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26355934277096742661713299 39533901415645113992569949)
    ·
      refine ⟨14825213030866917747213731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39533901415645113992569949 14825213030866917747213731)
      ·
        refine ⟨22237819546300376620820597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14825213030866917747213731 22237819546300376620820597)
        ·
          refine ⟨2084795582465660308201931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22237819546300376620820597 2084795582465660308201931)
          ·
            refine ⟨3127193373698490462302897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084795582465660308201931 3127193373698490462302897)
            ·
              refine ⟨2345395030273867846727173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3127193373698490462302897 2345395030273867846727173)
              ·
                refine ⟨439761568176350221261345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2345395030273867846727173 439761568176350221261345)
                ·
                  refine ⟨329821176132262665946009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439761568176350221261345 329821176132262665946009)
                  ·
                    rfl

theorem cell20_722615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 2].length) (baseStart_722615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722615 prefixEnd_722615 := by exact prefixLift 722615
  have htrace : WordTrace (prefixWord ++ tailWord_722615) baseStart_722615 baseEnd_722615 := by
    simpa [prefixWord, tailWord_722615, baseEnd_722615] using wordTrace_append hprefix tailTrace_722615
  have hstable : (prefixWord ++ tailWord_722615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722615).length < 2 ^ (prefixWord ++ tailWord_722615).sum := by decide
  have hdescent : baseEnd_722615 < baseStart_722615 := by decide
  rcases family_descends (prefixWord ++ tailWord_722615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722650 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_722650 : Nat := 118140960795 + 722650 * 2 ^ 59
def prefixEnd_722650 : Nat := 4983230072969 + 3 ^ 40 * 722650 * 2
def baseEnd_722650 : Nat := 329837151085958099779199

theorem tailTrace_722650 : CollatzResearch.WordTrace tailWord_722650 prefixEnd_722650 329837151085958099779199 := by
  unfold tailWord_722650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6589302707992485909809351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17571473887979962426158269 6589302707992485909809351)
  ·
    refine ⟨9883954061988728864714027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6589302707992485909809351 9883954061988728864714027)
    ·
      refine ⟨14825931092983093297071041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9883954061988728864714027 14825931092983093297071041)
      ·
        refine ⟨11119448319737319972803281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14825931092983093297071041 11119448319737319972803281)
        ·
          refine ⟨8339586239802989979602461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11119448319737319972803281 8339586239802989979602461)
          ·
            refine ⟨3127344839926121242350923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8339586239802989979602461 3127344839926121242350923)
            ·
              refine ⟨4691017259889181863526385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127344839926121242350923 4691017259889181863526385)
              ·
                refine ⟨3518262944916886397644789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4691017259889181863526385 3518262944916886397644789)
                ·
                  refine ⟨329837151085958099779199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3518262944916886397644789 329837151085958099779199)
                  ·
                    rfl

theorem cell20_722650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_722650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722650 prefixEnd_722650 := by exact prefixLift 722650
  have htrace : WordTrace (prefixWord ++ tailWord_722650) baseStart_722650 baseEnd_722650 := by
    simpa [prefixWord, tailWord_722650, baseEnd_722650] using wordTrace_append hprefix tailTrace_722650
  have hstable : (prefixWord ++ tailWord_722650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722650).length < 2 ^ (prefixWord ++ tailWord_722650).sum := by decide
  have hdescent : baseEnd_722650 < baseStart_722650 := by decide
  rcases family_descends (prefixWord ++ tailWord_722650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722670 : List Nat := [4, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_722670 : Nat := 118140960795 + 722670 * 2 ^ 59
def prefixEnd_722670 : Nat := 4983230072969 + 3 ^ 40 * 722670 * 2
def baseEnd_722670 : Nat := 329846279630926919112451

theorem tailTrace_722670 : CollatzResearch.WordTrace tailWord_722670 prefixEnd_722670 329846279630926919112451 := by
  unfold tailWord_722670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294742536487185881870683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17571960194598324703310309 3294742536487185881870683)
  ·
    refine ⟨4942113804730778822806025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3294742536487185881870683 4942113804730778822806025)
    ·
      refine ⟨3706585353548084117104519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4942113804730778822806025 3706585353548084117104519)
      ·
        refine ⟨5559878030322126175656779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706585353548084117104519 5559878030322126175656779)
        ·
          refine ⟨8339817045483189263485169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559878030322126175656779 8339817045483189263485169)
          ·
            refine ⟨6254862784112391947613877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8339817045483189263485169 6254862784112391947613877)
            ·
              refine ⟨586393386010536745088801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6254862784112391947613877 586393386010536745088801)
              ·
                refine ⟨439795039507902558816601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586393386010536745088801 439795039507902558816601)
                ·
                  refine ⟨329846279630926919112451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439795039507902558816601 329846279630926919112451)
                  ·
                    rfl

theorem cell20_722670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_722670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722670 prefixEnd_722670 := by exact prefixLift 722670
  have htrace : WordTrace (prefixWord ++ tailWord_722670) baseStart_722670 baseEnd_722670 := by
    simpa [prefixWord, tailWord_722670, baseEnd_722670] using wordTrace_append hprefix tailTrace_722670
  have hstable : (prefixWord ++ tailWord_722670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722670).length < 2 ^ (prefixWord ++ tailWord_722670).sum := by decide
  have hdescent : baseEnd_722670 < baseStart_722670 := by decide
  rcases family_descends (prefixWord ++ tailWord_722670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722688 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_722688 : Nat := 118140960795 + 722688 * 2 ^ 59
def prefixEnd_722688 : Nat := 4983230072969 + 3 ^ 40 * 722688 * 2
def baseEnd_722688 : Nat := 329854495321398856512377

theorem tailTrace_722688 : CollatzResearch.WordTrace tailWord_722688 prefixEnd_722688 329854495321398856512377 := by
  unfold tailWord_722688
  simp only [CollatzResearch.WordTrace]
  refine ⟨13179298402916138064560359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17572397870554850752747145 13179298402916138064560359)
  ·
    refine ⟨19768947604374207096840539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13179298402916138064560359 19768947604374207096840539)
    ·
      refine ⟨29653421406561310645260809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19768947604374207096840539 29653421406561310645260809)
      ·
        refine ⟨22240066054920982983945607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29653421406561310645260809 22240066054920982983945607)
        ·
          refine ⟨33360099082381474475918411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22240066054920982983945607 33360099082381474475918411)
          ·
            refine ⟨50040148623572211713877617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33360099082381474475918411 50040148623572211713877617)
            ·
              refine ⟨37530111467679158785408213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50040148623572211713877617 37530111467679158785408213)
              ·
                refine ⟨879611987523730284033005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37530111467679158785408213 879611987523730284033005)
                ·
                  refine ⟨329854495321398856512377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879611987523730284033005 329854495321398856512377)
                  ·
                    rfl

theorem cell20_722688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_722688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722688 prefixEnd_722688 := by exact prefixLift 722688
  have htrace : WordTrace (prefixWord ++ tailWord_722688) baseStart_722688 baseEnd_722688 := by
    simpa [prefixWord, tailWord_722688, baseEnd_722688] using wordTrace_append hprefix tailTrace_722688
  have hstable : (prefixWord ++ tailWord_722688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722688).length < 2 ^ (prefixWord ++ tailWord_722688).sum := by decide
  have hdescent : baseEnd_722688 < baseStart_722688 := by decide
  rcases family_descends (prefixWord ++ tailWord_722688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722718 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_722718 : Nat := 118140960795 + 722718 * 2 ^ 59
def prefixEnd_722718 : Nat := 4983230072969 + 3 ^ 40 * 722718 * 2
def baseEnd_722718 : Nat := 329868188138852085512255

theorem tailTrace_722718 : CollatzResearch.WordTrace tailWord_722718 prefixEnd_722718 329868188138852085512255 := by
  unfold tailWord_722718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294961374465448906589101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17573127330482394168475205 3294961374465448906589101)
  ·
    refine ⟨1235610515424543339970913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3294961374465448906589101 1235610515424543339970913)
    ·
      refine ⟨926707886568407504978185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1235610515424543339970913 926707886568407504978185)
      ·
        refine ⟨695030914926305628733639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 926707886568407504978185 695030914926305628733639)
        ·
          refine ⟨1042546372389458443100459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695030914926305628733639 1042546372389458443100459)
          ·
            refine ⟨1563819558584187664650689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042546372389458443100459 1563819558584187664650689)
            ·
              refine ⟨1172864668938140748488017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563819558584187664650689 1172864668938140748488017)
              ·
                refine ⟨879648501703605561366013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1172864668938140748488017 879648501703605561366013)
                ·
                  refine ⟨329868188138852085512255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879648501703605561366013 329868188138852085512255)
                  ·
                    rfl

theorem cell20_722718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_722718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722718 prefixEnd_722718 := by exact prefixLift 722718
  have htrace : WordTrace (prefixWord ++ tailWord_722718) baseStart_722718 baseEnd_722718 := by
    simpa [prefixWord, tailWord_722718, baseEnd_722718] using wordTrace_append hprefix tailTrace_722718
  have hstable : (prefixWord ++ tailWord_722718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722718).length < 2 ^ (prefixWord ++ tailWord_722718).sum := by decide
  have hdescent : baseEnd_722718 < baseStart_722718 := by decide
  rcases family_descends (prefixWord ++ tailWord_722718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722750 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_722750 : Nat := 118140960795 + 722750 * 2 ^ 59
def prefixEnd_722750 : Nat := 4983230072969 + 3 ^ 40 * 722750 * 2
def baseEnd_722750 : Nat := 329882793810802196445457

theorem tailTrace_722750 : CollatzResearch.WordTrace tailWord_722750 prefixEnd_722750 329882793810802196445457 := by
  unfold tailWord_722750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295107266450957589734713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17573905421071773811918469 3295107266450957589734713)
  ·
    refine ⟨2471330449838218192301035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3295107266450957589734713 2471330449838218192301035)
    ·
      refine ⟨3706995674757327288451553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2471330449838218192301035 3706995674757327288451553)
      ·
        refine ⟨2780246756067995466338665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3706995674757327288451553 2780246756067995466338665)
        ·
          refine ⟨2085185067050996599753999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2780246756067995466338665 2085185067050996599753999)
          ·
            refine ⟨3127777600576494899630999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085185067050996599753999 3127777600576494899630999)
            ·
              refine ⟨4691666400864742349446499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127777600576494899630999 4691666400864742349446499)
              ·
                refine ⟨7037499601297113524169749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691666400864742349446499 7037499601297113524169749)
                ·
                  refine ⟨329882793810802196445457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7037499601297113524169749 329882793810802196445457)
                  ·
                    rfl

theorem cell20_722750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_722750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722750 prefixEnd_722750 := by exact prefixLift 722750
  have htrace : WordTrace (prefixWord ++ tailWord_722750) baseStart_722750 baseEnd_722750 := by
    simpa [prefixWord, tailWord_722750, baseEnd_722750] using wordTrace_append hprefix tailTrace_722750
  have hstable : (prefixWord ++ tailWord_722750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722750).length < 2 ^ (prefixWord ++ tailWord_722750).sum := by decide
  have hdescent : baseEnd_722750 < baseStart_722750 := by decide
  rcases family_descends (prefixWord ++ tailWord_722750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722757 : List Nat := [1, 3, 1, 1, 1, 2, 7, 4]
def baseStart_722757 : Nat := 118140960795 + 722757 * 2 ^ 59
def prefixEnd_722757 : Nat := 4983230072969 + 3 ^ 40 * 722757 * 2
def baseEnd_722757 : Nat := 109961996267180427737365

theorem tailTrace_722757 : CollatzResearch.WordTrace tailWord_722757 prefixEnd_722757 109961996267180427737365 := by
  unfold tailWord_722757
  simp only [CollatzResearch.WordTrace]
  refine ⟨26361113442582300913382525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17574075628388200608921683 26361113442582300913382525)
  ·
    refine ⟨9885417540968362842518447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26361113442582300913382525 9885417540968362842518447)
    ·
      refine ⟨14828126311452544263777671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9885417540968362842518447 14828126311452544263777671)
      ·
        refine ⟨22242189467178816395666507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14828126311452544263777671 22242189467178816395666507)
        ·
          refine ⟨33363284200768224593499761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22242189467178816395666507 33363284200768224593499761)
          ·
            refine ⟨25022463150576168445124821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33363284200768224593499761 25022463150576168445124821)
            ·
              refine ⟨586463980091628947932613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25022463150576168445124821 586463980091628947932613)
              ·
                refine ⟨109961996267180427737365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586463980091628947932613 109961996267180427737365)
                ·
                  rfl

theorem cell20_722757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 4].length) (baseStart_722757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722757 prefixEnd_722757 := by exact prefixLift 722757
  have htrace : WordTrace (prefixWord ++ tailWord_722757) baseStart_722757 baseEnd_722757 := by
    simpa [prefixWord, tailWord_722757, baseEnd_722757] using wordTrace_append hprefix tailTrace_722757
  have hstable : (prefixWord ++ tailWord_722757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722757).length < 2 ^ (prefixWord ++ tailWord_722757).sum := by decide
  have hdescent : baseEnd_722757 < baseStart_722757 := by decide
  rcases family_descends (prefixWord ++ tailWord_722757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722778 : List Nat := [3, 1, 1, 2, 1, 3, 9]
def baseStart_722778 : Nat := 118140960795 + 722778 * 2 ^ 59
def prefixEnd_722778 : Nat := 4983230072969 + 3 ^ 40 * 722778 * 2
def baseEnd_722778 : Nat := 36655063752639838168001

theorem tailTrace_722778 : CollatzResearch.WordTrace tailWord_722778 prefixEnd_722778 36655063752639838168001 := by
  unfold tailWord_722778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590469843876555374974247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17574586250337480999931325 6590469843876555374974247)
  ·
    refine ⟨9885704765814833062461371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6590469843876555374974247 9885704765814833062461371)
    ·
      refine ⟨14828557148722249593692057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9885704765814833062461371 14828557148722249593692057)
      ·
        refine ⟨11121417861541687195269043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14828557148722249593692057 11121417861541687195269043)
        ·
          refine ⟨16682126792312530792903565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11121417861541687195269043 16682126792312530792903565)
          ·
            refine ⟨6255797547117199047338837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16682126792312530792903565 6255797547117199047338837)
            ·
              refine ⟨36655063752639838168001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6255797547117199047338837 36655063752639838168001)
              ·
                rfl

theorem cell20_722778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 9].length) (baseStart_722778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722778 prefixEnd_722778 := by exact prefixLift 722778
  have htrace : WordTrace (prefixWord ++ tailWord_722778) baseStart_722778 baseEnd_722778 := by
    simpa [prefixWord, tailWord_722778, baseEnd_722778] using wordTrace_append hprefix tailTrace_722778
  have hstable : (prefixWord ++ tailWord_722778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722778).length < 2 ^ (prefixWord ++ tailWord_722778).sum := by decide
  have hdescent : baseEnd_722778 < baseStart_722778 := by decide
  rcases family_descends (prefixWord ++ tailWord_722778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722809 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_722809 : Nat := 118140960795 + 722809 * 2 ^ 59
def prefixEnd_722809 : Nat := 4983230072969 + 3 ^ 40 * 722809 * 2
def baseEnd_722809 : Nat := 329909723018460213478549

theorem tailTrace_722809 : CollatzResearch.WordTrace tailWord_722809 prefixEnd_722809 329909723018460213478549 := by
  unfold tailWord_722809
  simp only [CollatzResearch.WordTrace]
  refine ⟨26363010038393913794275481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17575340025595942529516987 26363010038393913794275481)
  ·
    refine ⟨19772257528795435345706611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26363010038393913794275481 19772257528795435345706611)
    ·
      refine ⟨29658386293193153018559917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19772257528795435345706611 29658386293193153018559917)
      ·
        refine ⟨11121894859947432381959969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29658386293193153018559917 11121894859947432381959969)
        ·
          refine ⟨8341421144960574286469977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11121894859947432381959969 8341421144960574286469977)
          ·
            refine ⟨6256065858720430714852483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8341421144960574286469977 6256065858720430714852483)
            ·
              refine ⟨9384098788080646072278725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256065858720430714852483 9384098788080646072278725)
              ·
                refine ⟨1759518522765121138552261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9384098788080646072278725 1759518522765121138552261)
                ·
                  refine ⟨329909723018460213478549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759518522765121138552261 329909723018460213478549)
                  ·
                    rfl

theorem cell20_722809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_722809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722809 prefixEnd_722809 := by exact prefixLift 722809
  have htrace : WordTrace (prefixWord ++ tailWord_722809) baseStart_722809 baseEnd_722809 := by
    simpa [prefixWord, tailWord_722809, baseEnd_722809] using wordTrace_append hprefix tailTrace_722809
  have hstable : (prefixWord ++ tailWord_722809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722809).length < 2 ^ (prefixWord ++ tailWord_722809).sum := by decide
  have hdescent : baseEnd_722809 < baseStart_722809 := by decide
  rcases family_descends (prefixWord ++ tailWord_722809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722816 : List Nat := [2, 1, 1, 2, 1, 2, 5, 6]
def baseStart_722816 : Nat := 118140960795 + 722816 * 2 ^ 59
def prefixEnd_722816 : Nat := 4983230072969 + 3 ^ 40 * 722816 * 2
def baseEnd_722816 : Nat := 109970972669733100081729

theorem tailTrace_722816 : CollatzResearch.WordTrace tailWord_722816 prefixEnd_722816 109970972669733100081729 := by
  unfold tailWord_722816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13181632674684276994890151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17575510232912369326520201 13181632674684276994890151)
  ·
    refine ⟨19772449012026415492335227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13181632674684276994890151 19772449012026415492335227)
    ·
      refine ⟨29658673518039623238502841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19772449012026415492335227 29658673518039623238502841)
      ·
        refine ⟨22244005138529717428877131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29658673518039623238502841 22244005138529717428877131)
        ·
          refine ⟨33366007707794576143315697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22244005138529717428877131 33366007707794576143315697)
          ·
            refine ⟨25024505780845932107486773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33366007707794576143315697 25024505780845932107486773)
            ·
              refine ⟨2346047416954306135076885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25024505780845932107486773 2346047416954306135076885)
              ·
                refine ⟨109970972669733100081729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2346047416954306135076885 109970972669733100081729)
                ·
                  rfl

theorem cell20_722816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_722816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722816 prefixEnd_722816 := by exact prefixLift 722816
  have htrace : WordTrace (prefixWord ++ tailWord_722816) baseStart_722816 baseEnd_722816 := by
    simpa [prefixWord, tailWord_722816, baseEnd_722816] using wordTrace_append hprefix tailTrace_722816
  have hstable : (prefixWord ++ tailWord_722816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722816).length < 2 ^ (prefixWord ++ tailWord_722816).sum := by decide
  have hdescent : baseEnd_722816 < baseStart_722816 := by decide
  rcases family_descends (prefixWord ++ tailWord_722816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722850 : List Nat := [3, 3, 1, 2, 3, 1, 2, 5]
def baseStart_722850 : Nat := 118140960795 + 722850 * 2 ^ 59
def prefixEnd_722850 : Nat := 4983230072969 + 3 ^ 40 * 722850 * 2
def baseEnd_722850 : Nat := 109976145511882097703905

theorem tailTrace_722850 : CollatzResearch.WordTrace tailWord_722850 prefixEnd_722850 109976145511882097703905 := by
  unfold tailWord_722850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6591126357811344449129501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17576336954163585197678669 6591126357811344449129501)
  ·
    refine ⟨2471672384179254168423563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6591126357811344449129501 2471672384179254168423563)
    ·
      refine ⟨3707508576268881252635345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2471672384179254168423563 3707508576268881252635345)
      ·
        refine ⟨2780631432201660939476509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3707508576268881252635345 2780631432201660939476509)
        ·
          refine ⟨1042736787075622852303691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2780631432201660939476509 1042736787075622852303691)
          ·
            refine ⟨1564105180613434278455537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042736787075622852303691 1564105180613434278455537)
            ·
              refine ⟨1173078885460075708841653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1564105180613434278455537 1173078885460075708841653)
              ·
                refine ⟨109976145511882097703905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1173078885460075708841653 109976145511882097703905)
                ·
                  rfl

theorem cell20_722850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_722850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722850 prefixEnd_722850 := by exact prefixLift 722850
  have htrace : WordTrace (prefixWord ++ tailWord_722850) baseStart_722850 baseEnd_722850 := by
    simpa [prefixWord, tailWord_722850, baseEnd_722850] using wordTrace_append hprefix tailTrace_722850
  have hstable : (prefixWord ++ tailWord_722850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722850).length < 2 ^ (prefixWord ++ tailWord_722850).sum := by decide
  have hdescent : baseEnd_722850 < baseStart_722850 := by decide
  rcases family_descends (prefixWord ++ tailWord_722850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722892 : List Nat := [2, 2, 1, 4, 1, 10]
def baseStart_722892 : Nat := 118140960795 + 722892 * 2 ^ 59
def prefixEnd_722892 : Nat := 4983230072969 + 3 ^ 40 * 722892 * 2
def baseEnd_722892 : Nat := 12220281721484474581909

theorem tailTrace_722892 : CollatzResearch.WordTrace tailWord_722892 prefixEnd_722892 12220281721484474581909 := by
  unfold tailWord_722892
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183018648546609484773465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17577358198062145979697953 13183018648546609484773465)
  ·
    refine ⟨9887263986409957113580099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13183018648546609484773465 9887263986409957113580099)
    ·
      refine ⟨14830895979614935670370149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9887263986409957113580099 14830895979614935670370149)
      ·
        refine ⟨2780792996177800438194403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14830895979614935670370149 2780792996177800438194403)
        ·
          refine ⟨4171189494266700657291605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780792996177800438194403 4171189494266700657291605)
          ·
            refine ⟨12220281721484474581909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4171189494266700657291605 12220281721484474581909)
            ·
              rfl

theorem cell20_722892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 10].length) (baseStart_722892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722892 prefixEnd_722892 := by exact prefixLift 722892
  have htrace : WordTrace (prefixWord ++ tailWord_722892) baseStart_722892 baseEnd_722892 := by
    simpa [prefixWord, tailWord_722892, baseEnd_722892] using wordTrace_append hprefix tailTrace_722892
  have hstable : (prefixWord ++ tailWord_722892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722892).length < 2 ^ (prefixWord ++ tailWord_722892).sum := by decide
  have hdescent : baseEnd_722892 < baseStart_722892 := by decide
  rcases family_descends (prefixWord ++ tailWord_722892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722898 : List Nat := [3, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_722898 : Nat := 118140960795 + 722898 * 2 ^ 59
def prefixEnd_722898 : Nat := 4983230072969 + 3 ^ 40 * 722898 * 2
def baseEnd_722898 : Nat := 329950345043571459511519

theorem tailTrace_722898 : CollatzResearch.WordTrace tailWord_722898 prefixEnd_722898 329950345043571459511519 := by
  unfold tailWord_722898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6591564033767870498566337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17577504090047654662843565 6591564033767870498566337)
  ·
    refine ⟨4943673025325902873924753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6591564033767870498566337 4943673025325902873924753)
    ·
      refine ⟨3707754768994427155443565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4943673025325902873924753 3707754768994427155443565)
      ·
        refine ⟨1390408038372910183291337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3707754768994427155443565 1390408038372910183291337)
        ·
          refine ⟨1042806028779682637468503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390408038372910183291337 1042806028779682637468503)
          ·
            refine ⟨1564209043169523956202755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042806028779682637468503 1564209043169523956202755)
            ·
              refine ⟨2346313564754285934304133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564209043169523956202755 2346313564754285934304133)
              ·
                refine ⟨439933793391428612682025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2346313564754285934304133 439933793391428612682025)
                ·
                  refine ⟨329950345043571459511519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439933793391428612682025 329950345043571459511519)
                  ·
                    rfl

theorem cell20_722898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_722898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722898 prefixEnd_722898 := by exact prefixLift 722898
  have htrace : WordTrace (prefixWord ++ tailWord_722898) baseStart_722898 baseEnd_722898 := by
    simpa [prefixWord, tailWord_722898, baseEnd_722898] using wordTrace_append hprefix tailTrace_722898
  have hstable : (prefixWord ++ tailWord_722898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722898).length < 2 ^ (prefixWord ++ tailWord_722898).sum := by decide
  have hdescent : baseEnd_722898 < baseStart_722898 := by decide
  rcases family_descends (prefixWord ++ tailWord_722898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722916 : List Nat := [2, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_722916 : Nat := 118140960795 + 722916 * 2 ^ 59
def prefixEnd_722916 : Nat := 4983230072969 + 3 ^ 40 * 722916 * 2
def baseEnd_722916 : Nat := 329958560734043396911445

theorem tailTrace_722916 : CollatzResearch.WordTrace tailWord_722916 prefixEnd_722916 329958560734043396911445 := by
  unfold tailWord_722916
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183456324503135534210301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17577941766004180712280401 13183456324503135534210301)
  ·
    refine ⟨4943796121688675825328863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13183456324503135534210301 4943796121688675825328863)
    ·
      refine ⟨7415694182533013737993295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943796121688675825328863 7415694182533013737993295)
      ·
        refine ⟨11123541273799520606989943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415694182533013737993295 11123541273799520606989943)
        ·
          refine ⟨16685311910699280910484915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11123541273799520606989943 16685311910699280910484915)
          ·
            refine ⟨25027967866048921365727373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16685311910699280910484915 25027967866048921365727373)
            ·
              refine ⟨9385487949768345512147765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25027967866048921365727373 9385487949768345512147765)
              ·
                refine ⟨879889495290782391763853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9385487949768345512147765 879889495290782391763853)
                ·
                  refine ⟨329958560734043396911445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 879889495290782391763853 329958560734043396911445)
                  ·
                    rfl

theorem cell20_722916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_722916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722916 prefixEnd_722916 := by exact prefixLift 722916
  have htrace : WordTrace (prefixWord ++ tailWord_722916) baseStart_722916 baseEnd_722916 := by
    simpa [prefixWord, tailWord_722916, baseEnd_722916] using wordTrace_append hprefix tailTrace_722916
  have hstable : (prefixWord ++ tailWord_722916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722916).length < 2 ^ (prefixWord ++ tailWord_722916).sum := by decide
  have hdescent : baseEnd_722916 < baseStart_722916 := by decide
  rcases family_descends (prefixWord ++ tailWord_722916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722926 : List Nat := [4, 1, 2, 1, 3, 2, 3, 4]
def baseStart_722926 : Nat := 118140960795 + 722926 * 2 ^ 59
def prefixEnd_722926 : Nat := 4983230072969 + 3 ^ 40 * 722926 * 2
def baseEnd_722926 : Nat := 109987708335509268859357

theorem tailTrace_722926 : CollatzResearch.WordTrace tailWord_722926 prefixEnd_722926 109987708335509268859357 := by
  unfold tailWord_722926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295909672371255347035579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17578184919313361850856421 3295909672371255347035579)
  ·
    refine ⟨4943864508556883020553369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3295909672371255347035579 4943864508556883020553369)
    ·
      refine ⟨3707898381417662265415027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4943864508556883020553369 3707898381417662265415027)
      ·
        refine ⟨5561847572126493398122541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707898381417662265415027 5561847572126493398122541)
        ·
          refine ⟨2085692839547435024295953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5561847572126493398122541 2085692839547435024295953)
          ·
            refine ⟨1564269629660576268221965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2085692839547435024295953 1564269629660576268221965)
            ·
              refine ⟨586601111122716100583237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1564269629660576268221965 586601111122716100583237)
              ·
                refine ⟨109987708335509268859357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586601111122716100583237 109987708335509268859357)
                ·
                  rfl

theorem cell20_722926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_722926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722926 prefixEnd_722926 := by exact prefixLift 722926
  have htrace : WordTrace (prefixWord ++ tailWord_722926) baseStart_722926 baseEnd_722926 := by
    simpa [prefixWord, tailWord_722926, baseEnd_722926] using wordTrace_append hprefix tailTrace_722926
  have hstable : (prefixWord ++ tailWord_722926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722926).length < 2 ^ (prefixWord ++ tailWord_722926).sum := by decide
  have hdescent : baseEnd_722926 < baseStart_722926 := by decide
  rcases family_descends (prefixWord ++ tailWord_722926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722968 : List Nat := [2, 1, 2, 3, 2, 1, 2, 7]
def baseStart_722968 : Nat := 118140960795 + 722968 * 2 ^ 59
def prefixEnd_722968 : Nat := 4983230072969 + 3 ^ 40 * 722968 * 2
def baseEnd_722968 : Nat := 109994098316987442392633

theorem tailTrace_722968 : CollatzResearch.WordTrace tailWord_722968 prefixEnd_722968 109994098316987442392633 := by
  unfold tailWord_722968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13184404622408941974656779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17579206163211922632875705 13184404622408941974656779)
  ·
    refine ⟨19776606933613412961985169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13184404622408941974656779 19776606933613412961985169)
    ·
      refine ⟨14832455200210059721488877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19776606933613412961985169 14832455200210059721488877)
      ·
        refine ⟨5562170700078772395558329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14832455200210059721488877 5562170700078772395558329)
        ·
          refine ⟨4171628025059079296668747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5562170700078772395558329 4171628025059079296668747)
          ·
            refine ⟨6257442037588618945003121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171628025059079296668747 6257442037588618945003121)
            ·
              refine ⟨4693081528191464208752341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6257442037588618945003121 4693081528191464208752341)
              ·
                refine ⟨109994098316987442392633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4693081528191464208752341 109994098316987442392633)
                ·
                  rfl

theorem cell20_722968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_722968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_722968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_722968 prefixEnd_722968 := by exact prefixLift 722968
  have htrace : WordTrace (prefixWord ++ tailWord_722968) baseStart_722968 baseEnd_722968 := by
    simpa [prefixWord, tailWord_722968, baseEnd_722968] using wordTrace_append hprefix tailTrace_722968
  have hstable : (prefixWord ++ tailWord_722968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722968).length < 2 ^ (prefixWord ++ tailWord_722968).sum := by decide
  have hdescent : baseEnd_722968 < baseStart_722968 := by decide
  rcases family_descends (prefixWord ++ tailWord_722968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723044 : List Nat := [2, 3, 1, 1, 2, 1, 4, 6]
def baseStart_723044 : Nat := 118140960795 + 723044 * 2 ^ 59
def prefixEnd_723044 : Nat := 4983230072969 + 3 ^ 40 * 723044 * 2
def baseEnd_723044 : Nat := 110005661140614613548085

theorem tailTrace_723044 : CollatzResearch.WordTrace tailWord_723044 prefixEnd_723044 110005661140614613548085 := by
  unfold tailWord_723044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13185790596271274464540093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17581054128361699286053457 13185790596271274464540093)
  ·
    refine ⟨4944671473601727924202535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13185790596271274464540093 4944671473601727924202535)
    ·
      refine ⟨7417007210402591886303803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4944671473601727924202535 7417007210402591886303803)
      ·
        refine ⟨11125510815603887829455705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417007210402591886303803 11125510815603887829455705)
        ·
          refine ⟨8344133111702915872091779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11125510815603887829455705 8344133111702915872091779)
          ·
            refine ⟨12516199667554373808137669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8344133111702915872091779 12516199667554373808137669)
            ·
              refine ⟨2346787437666445089025813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12516199667554373808137669 2346787437666445089025813)
              ·
                refine ⟨110005661140614613548085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2346787437666445089025813 110005661140614613548085)
                ·
                  rfl

theorem cell20_723044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_723044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723044 prefixEnd_723044 := by exact prefixLift 723044
  have htrace : WordTrace (prefixWord ++ tailWord_723044) baseStart_723044 baseEnd_723044 := by
    simpa [prefixWord, tailWord_723044, baseEnd_723044] using wordTrace_append hprefix tailTrace_723044
  have hstable : (prefixWord ++ tailWord_723044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723044).length < 2 ^ (prefixWord ++ tailWord_723044).sum := by decide
  have hdescent : baseEnd_723044 < baseStart_723044 := by decide
  rcases family_descends (prefixWord ++ tailWord_723044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723068 : List Nat := [2, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_723068 : Nat := 118140960795 + 723068 * 2 ^ 59
def prefixEnd_723068 : Nat := 4983230072969 + 3 ^ 40 * 723068 * 2
def baseEnd_723068 : Nat := 330027937675806423844157

theorem tailTrace_723068 : CollatzResearch.WordTrace tailWord_723068 prefixEnd_723068 330027937675806423844157 := by
  unfold tailWord_723068
  simp only [CollatzResearch.WordTrace]
  refine ⟨13186228272227800513976929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17581637696303734018635905 13186228272227800513976929)
  ·
    refine ⟨9889671204170850385482697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13186228272227800513976929 9889671204170850385482697)
    ·
      refine ⟨7417253403128137789112023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9889671204170850385482697 7417253403128137789112023)
      ·
        refine ⟨11125880104692206683668035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417253403128137789112023 11125880104692206683668035)
        ·
          refine ⟨16688820157038310025502053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11125880104692206683668035 16688820157038310025502053)
          ·
            refine ⟨3129153779444683129781635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16688820157038310025502053 3129153779444683129781635)
            ·
              refine ⟨4693730669167024694672453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3129153779444683129781635 4693730669167024694672453)
              ·
                refine ⟨880074500468817130251085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4693730669167024694672453 880074500468817130251085)
                ·
                  refine ⟨330027937675806423844157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880074500468817130251085 330027937675806423844157)
                  ·
                    rfl

theorem cell20_723068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_723068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723068 prefixEnd_723068 := by exact prefixLift 723068
  have htrace : WordTrace (prefixWord ++ tailWord_723068) baseStart_723068 baseEnd_723068 := by
    simpa [prefixWord, tailWord_723068, baseEnd_723068] using wordTrace_append hprefix tailTrace_723068
  have hstable : (prefixWord ++ tailWord_723068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723068).length < 2 ^ (prefixWord ++ tailWord_723068).sum := by decide
  have hdescent : baseEnd_723068 < baseStart_723068 := by decide
  rcases family_descends (prefixWord ++ tailWord_723068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723130 : List Nat := [3, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_723130 : Nat := 118140960795 + 723130 * 2 ^ 59
def prefixEnd_723130 : Nat := 4983230072969 + 3 ^ 40 * 723130 * 2
def baseEnd_723130 : Nat := 330056236165209763777237

theorem tailTrace_723130 : CollatzResearch.WordTrace tailWord_723130 prefixEnd_723130 330056236165209763777237 := by
  unfold tailWord_723130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6593679467557746404177711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17583145246820657077807229 6593679467557746404177711)
  ·
    refine ⟨9890519201336619606266567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6593679467557746404177711 9890519201336619606266567)
    ·
      refine ⟨14835778802004929409399851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9890519201336619606266567 14835778802004929409399851)
      ·
        refine ⟨22253668203007394114099777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14835778802004929409399851 22253668203007394114099777)
        ·
          refine ⟨16690251152255545585574833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22253668203007394114099777 16690251152255545585574833)
          ·
            refine ⟨12517688364191659189181125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16690251152255545585574833 12517688364191659189181125)
            ·
              refine ⟨2347066568285936097971461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12517688364191659189181125 2347066568285936097971461)
              ·
                refine ⟨440074981553613018369649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2347066568285936097971461 440074981553613018369649)
                ·
                  refine ⟨330056236165209763777237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440074981553613018369649 330056236165209763777237)
                  ·
                    rfl

theorem cell20_723130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_723130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723130 prefixEnd_723130 := by exact prefixLift 723130
  have htrace : WordTrace (prefixWord ++ tailWord_723130) baseStart_723130 baseEnd_723130 := by
    simpa [prefixWord, tailWord_723130, baseEnd_723130] using wordTrace_append hprefix tailTrace_723130
  have hstable : (prefixWord ++ tailWord_723130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723130).length < 2 ^ (prefixWord ++ tailWord_723130).sum := by decide
  have hdescent : baseEnd_723130 < baseStart_723130 := by decide
  rcases family_descends (prefixWord ++ tailWord_723130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723140 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_723140 : Nat := 118140960795 + 723140 * 2 ^ 59
def prefixEnd_723140 : Nat := 4983230072969 + 3 ^ 40 * 723140 * 2
def baseEnd_723140 : Nat := 330060800437694173443863

theorem tailTrace_723140 : CollatzResearch.WordTrace tailWord_723140 prefixEnd_723140 330060800437694173443863 := by
  unfold tailWord_723140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13187541300097378662287437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17583388400129838216383249 13187541300097378662287437)
  ·
    refine ⟨4945327987536516998357789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13187541300097378662287437 4945327987536516998357789)
    ·
      refine ⟨1854497995326193874384171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4945327987536516998357789 1854497995326193874384171)
      ·
        refine ⟨2781746992989290811576257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854497995326193874384171 2781746992989290811576257)
        ·
          refine ⟨2086310244741968108682193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781746992989290811576257 2086310244741968108682193)
          ·
            refine ⟨1564732683556476081511645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2086310244741968108682193 1564732683556476081511645)
            ·
              refine ⟨586774756333678530566867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1564732683556476081511645 586774756333678530566867)
              ·
                refine ⟨880162134500517795850301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586774756333678530566867 880162134500517795850301)
                ·
                  refine ⟨330060800437694173443863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880162134500517795850301 330060800437694173443863)
                  ·
                    rfl

theorem cell20_723140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_723140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723140 prefixEnd_723140 := by exact prefixLift 723140
  have htrace : WordTrace (prefixWord ++ tailWord_723140) baseStart_723140 baseEnd_723140 := by
    simpa [prefixWord, tailWord_723140, baseEnd_723140] using wordTrace_append hprefix tailTrace_723140
  have hstable : (prefixWord ++ tailWord_723140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723140).length < 2 ^ (prefixWord ++ tailWord_723140).sum := by decide
  have hdescent : baseEnd_723140 < baseStart_723140 := by decide
  rcases family_descends (prefixWord ++ tailWord_723140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723154 : List Nat := [3, 2, 2, 2, 1, 4, 2, 4]
def baseStart_723154 : Nat := 118140960795 + 723154 * 2 ^ 59
def prefixEnd_723154 : Nat := 4983230072969 + 3 ^ 40 * 723154 * 2
def baseEnd_723154 : Nat := 110022396806390782325713

theorem tailTrace_723154 : CollatzResearch.WordTrace tailWord_723154 prefixEnd_723154 110022396806390782325713 := by
  unfold tailWord_723154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6593898305536009428896129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17583728814762691810389677 6593898305536009428896129)
  ·
    refine ⟨4945423729152007071672097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6593898305536009428896129 4945423729152007071672097)
    ·
      refine ⟨3709067796864005303754073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4945423729152007071672097 3709067796864005303754073)
      ·
        refine ⟨2781800847648003977815555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3709067796864005303754073 2781800847648003977815555)
        ·
          refine ⟨4172701271472005966723333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2781800847648003977815555 4172701271472005966723333)
          ·
            refine ⟨782381488401001118760625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4172701271472005966723333 782381488401001118760625)
            ·
              refine ⟨586786116300750839070469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782381488401001118760625 586786116300750839070469)
              ·
                refine ⟨110022396806390782325713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 586786116300750839070469 110022396806390782325713)
                ·
                  rfl

theorem cell20_723154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_723154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723154 prefixEnd_723154 := by exact prefixLift 723154
  have htrace : WordTrace (prefixWord ++ tailWord_723154) baseStart_723154 baseEnd_723154 := by
    simpa [prefixWord, tailWord_723154, baseEnd_723154] using wordTrace_append hprefix tailTrace_723154
  have hstable : (prefixWord ++ tailWord_723154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723154).length < 2 ^ (prefixWord ++ tailWord_723154).sum := by decide
  have hdescent : baseEnd_723154 < baseStart_723154 := by decide
  rcases family_descends (prefixWord ++ tailWord_723154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723175 : List Nat := [1, 1, 5, 3, 1, 3, 6]
def baseStart_723175 : Nat := 118140960795 + 723175 * 2 ^ 59
def prefixEnd_723175 : Nat := 4983230072969 + 3 ^ 40 * 723175 * 2
def baseEnd_723175 : Nat := 36675197265709956364117

theorem tailTrace_723175 : CollatzResearch.WordTrace tailWord_723175 prefixEnd_723175 36675197265709956364117 := by
  unfold tailWord_723175
  simp only [CollatzResearch.WordTrace]
  refine ⟨26376359155067958302098979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17584239436711972201399319 26376359155067958302098979)
  ·
    refine ⟨39564538732601937453148469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26376359155067958302098979 39564538732601937453148469)
    ·
      refine ⟨3709175506181431636232669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39564538732601937453148469 3709175506181431636232669)
      ·
        refine ⟨1390940814818036863587251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3709175506181431636232669 1390940814818036863587251)
        ·
          refine ⟨2086411222227055295380877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390940814818036863587251 2086411222227055295380877)
          ·
            refine ⟨782404208335145735767829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2086411222227055295380877 782404208335145735767829)
            ·
              refine ⟨36675197265709956364117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 782404208335145735767829 36675197265709956364117)
              ·
                rfl

theorem cell20_723175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 6].length) (baseStart_723175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723175 prefixEnd_723175 := by exact prefixLift 723175
  have htrace : WordTrace (prefixWord ++ tailWord_723175) baseStart_723175 baseEnd_723175 := by
    simpa [prefixWord, tailWord_723175, baseEnd_723175] using wordTrace_append hprefix tailTrace_723175
  have hstable : (prefixWord ++ tailWord_723175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723175).length < 2 ^ (prefixWord ++ tailWord_723175).sum := by decide
  have hdescent : baseEnd_723175 < baseStart_723175 := by decide
  rcases family_descends (prefixWord ++ tailWord_723175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723182 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_723182 : Nat := 118140960795 + 723182 * 2 ^ 59
def prefixEnd_723182 : Nat := 4983230072969 + 3 ^ 40 * 723182 * 2
def baseEnd_723182 : Nat := 330079970382128694043691

theorem tailTrace_723182 : CollatzResearch.WordTrace tailWord_723182 prefixEnd_723182 330079970382128694043691 := by
  unfold tailWord_723182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3297076808255324812200475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17584409644028398998402533 3297076808255324812200475)
  ·
    refine ⟨4945615212382987218300713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3297076808255324812200475 4945615212382987218300713)
    ·
      refine ⟨3709211409287240413725535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4945615212382987218300713 3709211409287240413725535)
      ·
        refine ⟨5563817113930860620588303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709211409287240413725535 5563817113930860620588303)
        ·
          refine ⟨8345725670896290930882455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563817113930860620588303 8345725670896290930882455)
          ·
            refine ⟨12518588506344436396323683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8345725670896290930882455 12518588506344436396323683)
            ·
              refine ⟨18777882759516654594485525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12518588506344436396323683 18777882759516654594485525)
              ·
                refine ⟨880213254352343184116509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18777882759516654594485525 880213254352343184116509)
                ·
                  refine ⟨330079970382128694043691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880213254352343184116509 330079970382128694043691)
                  ·
                    rfl

theorem cell20_723182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_723182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723182 prefixEnd_723182 := by exact prefixLift 723182
  have htrace : WordTrace (prefixWord ++ tailWord_723182) baseStart_723182 baseEnd_723182 := by
    simpa [prefixWord, tailWord_723182, baseEnd_723182] using wordTrace_append hprefix tailTrace_723182
  have hstable : (prefixWord ++ tailWord_723182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723182).length < 2 ^ (prefixWord ++ tailWord_723182).sum := by decide
  have hdescent : baseEnd_723182 < baseStart_723182 := by decide
  rcases family_descends (prefixWord ++ tailWord_723182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723196 : List Nat := [2, 2, 2, 1, 4, 1, 1, 7]
def baseStart_723196 : Nat := 118140960795 + 723196 * 2 ^ 59
def prefixEnd_723196 : Nat := 4983230072969 + 3 ^ 40 * 723196 * 2
def baseEnd_723196 : Nat := 110028786787868955858989

theorem tailTrace_723196 : CollatzResearch.WordTrace tailWord_723196 prefixEnd_723196 110028786787868955858989 := by
  unfold tailWord_723196
  simp only [CollatzResearch.WordTrace]
  refine ⟨13188562543995939444306721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17584750058661252592408961 13188562543995939444306721)
  ·
    refine ⟨9891421907996954583230041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13188562543995939444306721 9891421907996954583230041)
    ·
      refine ⟨7418566430997715937422531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9891421907996954583230041 7418566430997715937422531)
      ·
        refine ⟨11127849646496573906133797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7418566430997715937422531 11127849646496573906133797)
        ·
          refine ⟨2086471808718107607400087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11127849646496573906133797 2086471808718107607400087)
          ·
            refine ⟨3129707713077161411100131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086471808718107607400087 3129707713077161411100131)
            ·
              refine ⟨4694561569615742116650197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3129707713077161411100131 4694561569615742116650197)
              ·
                refine ⟨110028786787868955858989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4694561569615742116650197 110028786787868955858989)
                ·
                  rfl

theorem cell20_723196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_723196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723196 prefixEnd_723196 := by exact prefixLift 723196
  have htrace : WordTrace (prefixWord ++ tailWord_723196) baseStart_723196 baseEnd_723196 := by
    simpa [prefixWord, tailWord_723196, baseEnd_723196] using wordTrace_append hprefix tailTrace_723196
  have hstable : (prefixWord ++ tailWord_723196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723196).length < 2 ^ (prefixWord ++ tailWord_723196).sum := by decide
  have hdescent : baseEnd_723196 < baseStart_723196 := by decide
  rcases family_descends (prefixWord ++ tailWord_723196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723234 : List Nat := [3, 3, 1, 1, 3, 9]
def baseStart_723234 : Nat := 118140960795 + 723234 * 2 ^ 59
def prefixEnd_723234 : Nat := 4983230072969 + 3 ^ 40 * 723234 * 2
def baseEnd_723234 : Nat := 12226063133298060159635

theorem tailTrace_723234 : CollatzResearch.WordTrace tailWord_723234 prefixEnd_723234 12226063133298060159635 := by
  unfold tailWord_723234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594627765463552844624189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17585674041236140918997837 6594627765463552844624189)
  ·
    refine ⟨2472985412048832316734071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6594627765463552844624189 2472985412048832316734071)
    ·
      refine ⟨3709478118073248475101107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2472985412048832316734071 3709478118073248475101107)
      ·
        refine ⟨5564217177109872712651661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709478118073248475101107 5564217177109872712651661)
        ·
          refine ⟨2086581441416202267244373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5564217177109872712651661 2086581441416202267244373)
          ·
            refine ⟨12226063133298060159635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2086581441416202267244373 12226063133298060159635)
            ·
              rfl

theorem cell20_723234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 9].length) (baseStart_723234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723234 prefixEnd_723234 := by exact prefixLift 723234
  have htrace : WordTrace (prefixWord ++ tailWord_723234) baseStart_723234 baseEnd_723234 := by
    simpa [prefixWord, tailWord_723234, baseEnd_723234] using wordTrace_append hprefix tailTrace_723234
  have hstable : (prefixWord ++ tailWord_723234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723234).length < 2 ^ (prefixWord ++ tailWord_723234).sum := by decide
  have hdescent : baseEnd_723234 < baseStart_723234 := by decide
  rcases family_descends (prefixWord ++ tailWord_723234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723237 : List Nat := [1, 3, 1, 2, 5, 1, 2, 2, 3]
def baseStart_723237 : Nat := 118140960795 + 723237 * 2 ^ 59
def prefixEnd_723237 : Nat := 4983230072969 + 3 ^ 40 * 723237 * 2
def baseEnd_723237 : Nat := 330105073880792947210133

theorem tailTrace_723237 : CollatzResearch.WordTrace tailWord_723237 prefixEnd_723237 330105073880792947210133 := by
  unfold tailWord_723237
  simp only [CollatzResearch.WordTrace]
  refine ⟨26378620480843342890855965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17585746987228895260570643 26378620480843342890855965)
  ·
    refine ⟨9891982680316253584070987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26378620480843342890855965 9891982680316253584070987)
    ·
      refine ⟨14837974020474380376106481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9891982680316253584070987 14837974020474380376106481)
      ·
        refine ⟨11128480515355785282079861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14837974020474380376106481 11128480515355785282079861)
        ·
          refine ⟨1043295048314604870194987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11128480515355785282079861 1043295048314604870194987)
          ·
            refine ⟨1564942572471907305292481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043295048314604870194987 1564942572471907305292481)
            ·
              refine ⟨1173706929353930478969361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1564942572471907305292481 1173706929353930478969361)
              ·
                refine ⟨880280197015447859227021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173706929353930478969361 880280197015447859227021)
                ·
                  refine ⟨330105073880792947210133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880280197015447859227021 330105073880792947210133)
                  ·
                    rfl

theorem cell20_723237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_723237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723237 prefixEnd_723237 := by exact prefixLift 723237
  have htrace : WordTrace (prefixWord ++ tailWord_723237) baseStart_723237 baseEnd_723237 := by
    simpa [prefixWord, tailWord_723237, baseEnd_723237] using wordTrace_append hprefix tailTrace_723237
  have hstable : (prefixWord ++ tailWord_723237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723237).length < 2 ^ (prefixWord ++ tailWord_723237).sum := by decide
  have hdescent : baseEnd_723237 < baseStart_723237 := by decide
  rcases family_descends (prefixWord ++ tailWord_723237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723258 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_723258 : Nat := 118140960795 + 723258 * 2 ^ 59
def prefixEnd_723258 : Nat := 4983230072969 + 3 ^ 40 * 723258 * 2
def baseEnd_723258 : Nat := 330114658853010207510047

theorem tailTrace_723258 : CollatzResearch.WordTrace tailWord_723258 prefixEnd_723258 330114658853010207510047 := by
  unfold tailWord_723258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6594846603441815869342607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17586257609178175651580285 6594846603441815869342607)
  ·
    refine ⟨9892269905162723804013911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6594846603441815869342607 9892269905162723804013911)
    ·
      refine ⟨14838404857744085706020867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9892269905162723804013911 14838404857744085706020867)
      ·
        refine ⟨22257607286616128559031301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14838404857744085706020867 22257607286616128559031301)
        ·
          refine ⟨4173301366240524104818369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22257607286616128559031301 4173301366240524104818369)
          ·
            refine ⟨3129976024680393078613777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173301366240524104818369 3129976024680393078613777)
            ·
              refine ⟨2347482018510294808960333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129976024680393078613777 2347482018510294808960333)
              ·
                refine ⟨880305756941360553360125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2347482018510294808960333 880305756941360553360125)
                ·
                  refine ⟨330114658853010207510047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880305756941360553360125 330114658853010207510047)
                  ·
                    rfl

theorem cell20_723258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_723258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723258 prefixEnd_723258 := by exact prefixLift 723258
  have htrace : WordTrace (prefixWord ++ tailWord_723258) baseStart_723258 baseEnd_723258 := by
    simpa [prefixWord, tailWord_723258, baseEnd_723258] using wordTrace_append hprefix tailTrace_723258
  have hstable : (prefixWord ++ tailWord_723258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723258).length < 2 ^ (prefixWord ++ tailWord_723258).sum := by decide
  have hdescent : baseEnd_723258 < baseStart_723258 := by decide
  rcases family_descends (prefixWord ++ tailWord_723258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723282 : List Nat := [3, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_723282 : Nat := 118140960795 + 723282 * 2 ^ 59
def prefixEnd_723282 : Nat := 4983230072969 + 3 ^ 40 * 723282 * 2
def baseEnd_723282 : Nat := 330125613106972790709949

theorem tailTrace_723282 : CollatzResearch.WordTrace tailWord_723282 prefixEnd_723282 330125613106972790709949 := by
  unfold tailWord_723282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6595065441420078894061025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17586841177120210384162733 6595065441420078894061025)
  ·
    refine ⟨4946299081065059170545769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6595065441420078894061025 4946299081065059170545769)
    ·
      refine ⟨3709724310798794377909327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4946299081065059170545769 3709724310798794377909327)
      ·
        refine ⟨5564586466198191566863991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709724310798794377909327 5564586466198191566863991)
        ·
          refine ⟨8346879699297287350295987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5564586466198191566863991 8346879699297287350295987)
          ·
            refine ⟨12520319548945931025443981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8346879699297287350295987 12520319548945931025443981)
            ·
              refine ⟨4695119830854724134541493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12520319548945931025443981 4695119830854724134541493)
              ·
                refine ⟨440167484142630387613265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4695119830854724134541493 440167484142630387613265)
                ·
                  refine ⟨330125613106972790709949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440167484142630387613265 330125613106972790709949)
                  ·
                    rfl

theorem cell20_723282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_723282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723282 prefixEnd_723282 := by exact prefixLift 723282
  have htrace : WordTrace (prefixWord ++ tailWord_723282) baseStart_723282 baseEnd_723282 := by
    simpa [prefixWord, tailWord_723282, baseEnd_723282] using wordTrace_append hprefix tailTrace_723282
  have hstable : (prefixWord ++ tailWord_723282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723282).length < 2 ^ (prefixWord ++ tailWord_723282).sum := by decide
  have hdescent : baseEnd_723282 < baseStart_723282 := by decide
  rcases family_descends (prefixWord ++ tailWord_723282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723296 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_723296 : Nat := 118140960795 + 723296 * 2 ^ 59
def prefixEnd_723296 : Nat := 4983230072969 + 3 ^ 40 * 723296 * 2
def baseEnd_723296 : Nat := 330132003088450964243225

theorem tailTrace_723296 : CollatzResearch.WordTrace tailWord_723296 prefixEnd_723296 330132003088450964243225 := by
  unfold tailWord_723296
  simp only [CollatzResearch.WordTrace]
  refine ⟨13190386193814797983626871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17587181591753063978169161 13190386193814797983626871)
  ·
    refine ⟨19785579290722196975440307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13190386193814797983626871 19785579290722196975440307)
    ·
      refine ⟨29678368936083295463160461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19785579290722196975440307 29678368936083295463160461)
      ·
        refine ⟨11129388351031235798685173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29678368936083295463160461 11129388351031235798685173)
        ·
          refine ⟨1043380157909178356126735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11129388351031235798685173 1043380157909178356126735)
          ·
            refine ⟨1565070236863767534190103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043380157909178356126735 1565070236863767534190103)
            ·
              refine ⟨2347605355295651301285155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565070236863767534190103 2347605355295651301285155)
              ·
                refine ⟨3521408032943476951927733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347605355295651301285155 3521408032943476951927733)
                ·
                  refine ⟨330132003088450964243225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3521408032943476951927733 330132003088450964243225)
                  ·
                    rfl

theorem cell20_723296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_723296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723296 prefixEnd_723296 := by exact prefixLift 723296
  have htrace : WordTrace (prefixWord ++ tailWord_723296) baseStart_723296 baseEnd_723296 := by
    simpa [prefixWord, tailWord_723296, baseEnd_723296] using wordTrace_append hprefix tailTrace_723296
  have hstable : (prefixWord ++ tailWord_723296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723296).length < 2 ^ (prefixWord ++ tailWord_723296).sum := by decide
  have hdescent : baseEnd_723296 < baseStart_723296 := by decide
  rcases family_descends (prefixWord ++ tailWord_723296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723303 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_723303 : Nat := 118140960795 + 723303 * 2 ^ 59
def prefixEnd_723303 : Nat := 4983230072969 + 3 ^ 40 * 723303 * 2
def baseEnd_723303 : Nat := 330135198079190051009863

theorem tailTrace_723303 : CollatzResearch.WordTrace tailWord_723303 prefixEnd_723303 330135198079190051009863 := by
  unfold tailWord_723303
  simp only [CollatzResearch.WordTrace]
  refine ⟨26381027698604236162758563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17587351799069490775172375 26381027698604236162758563)
  ·
    refine ⟨39571541547906354244137845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26381027698604236162758563 39571541547906354244137845)
    ·
      refine ⟨3709832020116220710387923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39571541547906354244137845 3709832020116220710387923)
      ·
        refine ⟨5564748030174331065581885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3709832020116220710387923 5564748030174331065581885)
        ·
          refine ⟨2086780511315374149593207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5564748030174331065581885 2086780511315374149593207)
          ·
            refine ⟨3130170766973061224389811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086780511315374149593207 3130170766973061224389811)
            ·
              refine ⟨4695256150459591836584717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130170766973061224389811 4695256150459591836584717)
              ·
                refine ⟨1760721056422346938719269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4695256150459591836584717 1760721056422346938719269)
                ·
                  refine ⟨330135198079190051009863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760721056422346938719269 330135198079190051009863)
                  ·
                    rfl

theorem cell20_723303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_723303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723303 prefixEnd_723303 := by exact prefixLift 723303
  have htrace : WordTrace (prefixWord ++ tailWord_723303) baseStart_723303 baseEnd_723303 := by
    simpa [prefixWord, tailWord_723303, baseEnd_723303] using wordTrace_append hprefix tailTrace_723303
  have hstable : (prefixWord ++ tailWord_723303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723303).length < 2 ^ (prefixWord ++ tailWord_723303).sum := by decide
  have hdescent : baseEnd_723303 < baseStart_723303 := by decide
  rcases family_descends (prefixWord ++ tailWord_723303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723324 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_723324 : Nat := 118140960795 + 723324 * 2 ^ 59
def prefixEnd_723324 : Nat := 4983230072969 + 3 ^ 40 * 723324 * 2
def baseEnd_723324 : Nat := 330144783051407311309777

theorem tailTrace_723324 : CollatzResearch.WordTrace tailWord_723324 prefixEnd_723324 330144783051407311309777 := by
  unfold tailWord_723324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13190896815764078374636513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17587862421018771166182017 13190896815764078374636513)
  ·
    refine ⟨9893172611823058780977385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13190896815764078374636513 9893172611823058780977385)
    ·
      refine ⟨7419879458867294085733039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9893172611823058780977385 7419879458867294085733039)
      ·
        refine ⟨11129819188300941128599559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7419879458867294085733039 11129819188300941128599559)
        ·
          refine ⟨16694728782451411692899339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11129819188300941128599559 16694728782451411692899339)
          ·
            refine ⟨25042093173677117539349009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16694728782451411692899339 25042093173677117539349009)
            ·
              refine ⟨18781569880257838154511757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25042093173677117539349009 18781569880257838154511757)
              ·
                refine ⟨7043088705096689307941909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18781569880257838154511757 7043088705096689307941909)
                ·
                  refine ⟨330144783051407311309777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7043088705096689307941909 330144783051407311309777)
                  ·
                    rfl

theorem cell20_723324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_723324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723324 prefixEnd_723324 := by exact prefixLift 723324
  have htrace : WordTrace (prefixWord ++ tailWord_723324) baseStart_723324 baseEnd_723324 := by
    simpa [prefixWord, tailWord_723324, baseEnd_723324] using wordTrace_append hprefix tailTrace_723324
  have hstable : (prefixWord ++ tailWord_723324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723324).length < 2 ^ (prefixWord ++ tailWord_723324).sum := by decide
  have hdescent : baseEnd_723324 < baseStart_723324 := by decide
  rcases family_descends (prefixWord ++ tailWord_723324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723337 : List Nat := [1, 2, 1, 1, 6, 3, 1, 3, 2]
def baseStart_723337 : Nat := 118140960795 + 723337 * 2 ^ 59
def prefixEnd_723337 : Nat := 4983230072969 + 3 ^ 40 * 723337 * 2
def baseEnd_723337 : Nat := 330150716605637043876391

theorem tailTrace_723337 : CollatzResearch.WordTrace tailWord_723337 prefixEnd_723337 330150716605637043876391 := by
  unfold tailWord_723337
  simp only [CollatzResearch.WordTrace]
  refine ⟨26382267780481059969496265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17588178520320706646330843 26382267780481059969496265)
  ·
    refine ⟨19786700835360794977122199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26382267780481059969496265 19786700835360794977122199)
    ·
      refine ⟨29680051253041192465683299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19786700835360794977122199 29680051253041192465683299)
      ·
        refine ⟨44520076879561788698524949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29680051253041192465683299 44520076879561788698524949)
        ·
          refine ⟨2086878603729458845243357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44520076879561788698524949 2086878603729458845243357)
          ·
            refine ⟨782579476398547066966259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2086878603729458845243357 782579476398547066966259)
            ·
              refine ⟨1173869214597820600449389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782579476398547066966259 1173869214597820600449389)
              ·
                refine ⟨440200955474182725168521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1173869214597820600449389 440200955474182725168521)
                ·
                  refine ⟨330150716605637043876391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440200955474182725168521 330150716605637043876391)
                  ·
                    rfl

theorem cell20_723337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_723337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723337 prefixEnd_723337 := by exact prefixLift 723337
  have htrace : WordTrace (prefixWord ++ tailWord_723337) baseStart_723337 baseEnd_723337 := by
    simpa [prefixWord, tailWord_723337, baseEnd_723337] using wordTrace_append hprefix tailTrace_723337
  have hstable : (prefixWord ++ tailWord_723337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723337).length < 2 ^ (prefixWord ++ tailWord_723337).sum := by decide
  have hdescent : baseEnd_723337 < baseStart_723337 := by decide
  rcases family_descends (prefixWord ++ tailWord_723337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723350 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_723350 : Nat := 118140960795 + 723350 * 2 ^ 59
def prefixEnd_723350 : Nat := 4983230072969 + 3 ^ 40 * 723350 * 2
def baseEnd_723350 : Nat := 330156650159866776443005

theorem tailTrace_723350 : CollatzResearch.WordTrace tailWord_723350 prefixEnd_723350 330156650159866776443005 := by
  unfold tailWord_723350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648921370589622699357469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17588494619622642126479669 1648921370589622699357469)
  ·
    refine ⟨618345513971108512259051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1648921370589622699357469 618345513971108512259051)
    ·
      refine ⟨927518270956662768388577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618345513971108512259051 927518270956662768388577)
      ·
        refine ⟨695638703217497076291433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 927518270956662768388577 695638703217497076291433)
        ·
          refine ⟨521729027413122807218575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695638703217497076291433 521729027413122807218575)
          ·
            refine ⟨782593541119684210827863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521729027413122807218575 782593541119684210827863)
            ·
              refine ⟨1173890311679526316241795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782593541119684210827863 1173890311679526316241795)
              ·
                refine ⟨1760835467519289474362693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173890311679526316241795 1760835467519289474362693)
                ·
                  refine ⟨330156650159866776443005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1760835467519289474362693 330156650159866776443005)
                  ·
                    rfl

theorem cell20_723350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_723350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723350 prefixEnd_723350 := by exact prefixLift 723350
  have htrace : WordTrace (prefixWord ++ tailWord_723350) baseStart_723350 baseEnd_723350 := by
    simpa [prefixWord, tailWord_723350, baseEnd_723350] using wordTrace_append hprefix tailTrace_723350
  have hstable : (prefixWord ++ tailWord_723350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723350).length < 2 ^ (prefixWord ++ tailWord_723350).sum := by decide
  have hdescent : baseEnd_723350 < baseStart_723350 := by decide
  rcases family_descends (prefixWord ++ tailWord_723350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723368 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_723368 : Nat := 118140960795 + 723368 * 2 ^ 59
def prefixEnd_723368 : Nat := 4983230072969 + 3 ^ 40 * 723368 * 2
def baseEnd_723368 : Nat := 330164865850338713842931

theorem tailTrace_723368 : CollatzResearch.WordTrace tailWord_723368 prefixEnd_723368 330164865850338713842931 := by
  unfold tailWord_723368
  simp only [CollatzResearch.WordTrace]
  refine ⟨13191699221684376131937379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17588932295579168175916505 13191699221684376131937379)
  ·
    refine ⟨19787548832526564197906069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13191699221684376131937379 19787548832526564197906069)
    ·
      refine ⟨927541351524682696776847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19787548832526564197906069 927541351524682696776847)
      ·
        refine ⟨1391312027287024045165271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927541351524682696776847 1391312027287024045165271)
        ·
          refine ⟨2086968040930536067747907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391312027287024045165271 2086968040930536067747907)
          ·
            refine ⟨3130452061395804101621861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086968040930536067747907 3130452061395804101621861)
            ·
              refine ⟨586959761511713269054099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3130452061395804101621861 586959761511713269054099)
              ·
                refine ⟨880439642267569903581149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586959761511713269054099 880439642267569903581149)
                ·
                  refine ⟨330164865850338713842931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880439642267569903581149 330164865850338713842931)
                  ·
                    rfl

theorem cell20_723368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_723368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723368 prefixEnd_723368 := by exact prefixLift 723368
  have htrace : WordTrace (prefixWord ++ tailWord_723368) baseStart_723368 baseEnd_723368 := by
    simpa [prefixWord, tailWord_723368, baseEnd_723368] using wordTrace_append hprefix tailTrace_723368
  have hstable : (prefixWord ++ tailWord_723368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723368).length < 2 ^ (prefixWord ++ tailWord_723368).sum := by decide
  have hdescent : baseEnd_723368 < baseStart_723368 := by decide
  rcases family_descends (prefixWord ++ tailWord_723368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723413 : List Nat := [1, 3, 2, 3, 1, 2, 4, 2, 2]
def baseStart_723413 : Nat := 118140960795 + 723413 * 2 ^ 59
def prefixEnd_723413 : Nat := 4983230072969 + 3 ^ 40 * 723413 * 2
def baseEnd_723413 : Nat := 330185405076518557342747

theorem tailTrace_723413 : CollatzResearch.WordTrace tailWord_723413 prefixEnd_723413 330185405076518557342747 := by
  unfold tailWord_723413
  simp only [CollatzResearch.WordTrace]
  refine ⟨26385039728205724949262893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17590026485470483299508595 26385039728205724949262893)
  ·
    refine ⟨9894389898077146855973585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26385039728205724949262893 9894389898077146855973585)
    ·
      refine ⟨7420792423557860141980189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9894389898077146855973585 7420792423557860141980189)
      ·
        refine ⟨2782797158834197553242571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7420792423557860141980189 2782797158834197553242571)
        ·
          refine ⟨4174195738251296329863857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782797158834197553242571 4174195738251296329863857)
          ·
            refine ⟨3130646803688472247397893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4174195738251296329863857 3130646803688472247397893)
            ·
              refine ⟨586996275691588546387105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3130646803688472247397893 586996275691588546387105)
              ·
                refine ⟨440247206768691409790329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586996275691588546387105 440247206768691409790329)
                ·
                  refine ⟨330185405076518557342747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440247206768691409790329 330185405076518557342747)
                  ·
                    rfl

theorem cell20_723413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_723413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723413 prefixEnd_723413 := by exact prefixLift 723413
  have htrace : WordTrace (prefixWord ++ tailWord_723413) baseStart_723413 baseEnd_723413 := by
    simpa [prefixWord, tailWord_723413, baseEnd_723413] using wordTrace_append hprefix tailTrace_723413
  have hstable : (prefixWord ++ tailWord_723413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723413).length < 2 ^ (prefixWord ++ tailWord_723413).sum := by decide
  have hdescent : baseEnd_723413 < baseStart_723413 := by decide
  rcases family_descends (prefixWord ++ tailWord_723413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723496 : List Nat := [2, 1, 5, 2, 1, 3, 2, 4]
def baseStart_723496 : Nat := 118140960795 + 723496 * 2 ^ 59
def prefixEnd_723496 : Nat := 4983230072969 + 3 ^ 40 * 723496 * 2
def baseEnd_723496 : Nat := 110074429512713052525247

theorem tailTrace_723496 : CollatzResearch.WordTrace tailWord_723496 prefixEnd_723496 110074429512713052525247 := by
  unfold tailWord_723496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13194033493452515062267171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17592044657936686749689561 13194033493452515062267171)
  ·
    refine ⟨19791050240178772593400757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13194033493452515062267171 19791050240178772593400757)
    ·
      refine ⟨1855410960016759930631321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19791050240178772593400757 1855410960016759930631321)
      ·
        refine ⟨1391558220012569947973491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1855410960016759930631321 1391558220012569947973491)
        ·
          refine ⟨2087337330018854921960237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391558220012569947973491 2087337330018854921960237)
          ·
            refine ⟨782751498757070595735089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2087337330018854921960237 782751498757070595735089)
            ·
              refine ⟨587063624067802946801317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782751498757070595735089 587063624067802946801317)
              ·
                refine ⟨110074429512713052525247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 587063624067802946801317 110074429512713052525247)
                ·
                  rfl

theorem cell20_723496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_723496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723496 prefixEnd_723496 := by exact prefixLift 723496
  have htrace : WordTrace (prefixWord ++ tailWord_723496) baseStart_723496 baseEnd_723496 := by
    simpa [prefixWord, tailWord_723496, baseEnd_723496] using wordTrace_append hprefix tailTrace_723496
  have hstable : (prefixWord ++ tailWord_723496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723496).length < 2 ^ (prefixWord ++ tailWord_723496).sum := by decide
  have hdescent : baseEnd_723496 < baseStart_723496 := by decide
  rcases family_descends (prefixWord ++ tailWord_723496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723527 : List Nat := [1, 1, 4, 1, 4, 2, 3, 2, 2]
def baseStart_723527 : Nat := 118140960795 + 723527 * 2 ^ 59
def prefixEnd_723527 : Nat := 4983230072969 + 3 ^ 40 * 723527 * 2
def baseEnd_723527 : Nat := 330237437782840827542281

theorem tailTrace_723527 : CollatzResearch.WordTrace tailWord_723527 prefixEnd_723527 330237437782840827542281 := by
  unfold tailWord_723527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26389197649792722418912835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17592798433195148279275223 26389197649792722418912835)
  ·
    refine ⟨39583796474689083628369253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26389197649792722418912835 39583796474689083628369253)
    ·
      refine ⟨7421961839004203180319235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39583796474689083628369253 7421961839004203180319235)
      ·
        refine ⟨11132942758506304770478853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7421961839004203180319235 11132942758506304770478853)
        ·
          refine ⟨2087426767219932144464785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11132942758506304770478853 2087426767219932144464785)
          ·
            refine ⟨1565570075414949108348589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2087426767219932144464785 1565570075414949108348589)
            ·
              refine ⟨587088778280605915630721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565570075414949108348589 587088778280605915630721)
              ·
                refine ⟨440316583710454436723041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587088778280605915630721 440316583710454436723041)
                ·
                  refine ⟨330237437782840827542281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440316583710454436723041 330237437782840827542281)
                  ·
                    rfl

theorem cell20_723527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 2].length) (baseStart_723527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723527 prefixEnd_723527 := by exact prefixLift 723527
  have htrace : WordTrace (prefixWord ++ tailWord_723527) baseStart_723527 baseEnd_723527 := by
    simpa [prefixWord, tailWord_723527, baseEnd_723527] using wordTrace_append hprefix tailTrace_723527
  have hstable : (prefixWord ++ tailWord_723527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723527).length < 2 ^ (prefixWord ++ tailWord_723527).sum := by decide
  have hdescent : baseEnd_723527 < baseStart_723527 := by decide
  rcases family_descends (prefixWord ++ tailWord_723527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723531 : List Nat := [1, 1, 1, 1, 3, 1, 4, 6, 2]
def baseStart_723531 : Nat := 118140960795 + 723531 * 2 ^ 59
def prefixEnd_723531 : Nat := 4983230072969 + 3 ^ 40 * 723531 * 2
def baseEnd_723531 : Nat := 330239263491834591408931

theorem tailTrace_723531 : CollatzResearch.WordTrace tailWord_723531 prefixEnd_723531 330239263491834591408931 := by
  unfold tailWord_723531
  simp only [CollatzResearch.WordTrace]
  refine ⟨26389343541778231102058447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17592895694518820734705631 26389343541778231102058447)
  ·
    refine ⟨39584015312667346653087671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26389343541778231102058447 39584015312667346653087671)
    ·
      refine ⟨59376022969001019979631507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39584015312667346653087671 59376022969001019979631507)
      ·
        refine ⟨89064034453501529969447261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59376022969001019979631507 89064034453501529969447261)
        ·
          refine ⟨33399012920063073738542723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89064034453501529969447261 33399012920063073738542723)
          ·
            refine ⟨50098519380094610607814085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33399012920063073738542723 50098519380094610607814085)
            ·
              refine ⟨9393472383767739488965141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50098519380094610607814085 9393472383767739488965141)
              ·
                refine ⟨440319017989112788545241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9393472383767739488965141 440319017989112788545241)
                ·
                  refine ⟨330239263491834591408931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440319017989112788545241 330239263491834591408931)
                  ·
                    rfl

theorem cell20_723531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 2].length) (baseStart_723531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723531 prefixEnd_723531 := by exact prefixLift 723531
  have htrace : WordTrace (prefixWord ++ tailWord_723531) baseStart_723531 baseEnd_723531 := by
    simpa [prefixWord, tailWord_723531, baseEnd_723531] using wordTrace_append hprefix tailTrace_723531
  have hstable : (prefixWord ++ tailWord_723531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723531).length < 2 ^ (prefixWord ++ tailWord_723531).sum := by decide
  have hdescent : baseEnd_723531 < baseStart_723531 := by decide
  rcases family_descends (prefixWord ++ tailWord_723531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723538 : List Nat := [3, 2, 2, 1, 2, 1, 4, 5]
def baseStart_723538 : Nat := 118140960795 + 723538 * 2 ^ 59
def prefixEnd_723538 : Nat := 4983230072969 + 3 ^ 40 * 723538 * 2
def baseEnd_723538 : Nat := 110080819494191226058523

theorem tailTrace_723538 : CollatzResearch.WordTrace tailWord_723538 prefixEnd_723538 110080819494191226058523 := by
  unfold tailWord_723538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6597399713188217824390817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17593065901835247531708845 6597399713188217824390817)
  ·
    refine ⟨4948049784891163368293113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6597399713188217824390817 4948049784891163368293113)
    ·
      refine ⟨3711037338668372526219835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4948049784891163368293113 3711037338668372526219835)
      ·
        refine ⟨5566556008002558789329753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711037338668372526219835 5566556008002558789329753)
        ·
          refine ⟨4174917006001919091997315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5566556008002558789329753 4174917006001919091997315)
          ·
            refine ⟨6262375509002878637995973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174917006001919091997315 6262375509002878637995973)
            ·
              refine ⟨1174195407938039744624245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6262375509002878637995973 1174195407938039744624245)
              ·
                refine ⟨110080819494191226058523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1174195407938039744624245 110080819494191226058523)
                ·
                  rfl

theorem cell20_723538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_723538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723538 prefixEnd_723538 := by exact prefixLift 723538
  have htrace : WordTrace (prefixWord ++ tailWord_723538) baseStart_723538 baseEnd_723538 := by
    simpa [prefixWord, tailWord_723538, baseEnd_723538] using wordTrace_append hprefix tailTrace_723538
  have hstable : (prefixWord ++ tailWord_723538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723538).length < 2 ^ (prefixWord ++ tailWord_723538).sum := by decide
  have hdescent : baseEnd_723538 < baseStart_723538 := by decide
  rcases family_descends (prefixWord ++ tailWord_723538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723552 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_723552 : Nat := 118140960795 + 723552 * 2 ^ 59
def prefixEnd_723552 : Nat := 4983230072969 + 3 ^ 40 * 723552 * 2
def baseEnd_723552 : Nat := 330248848464051851708845

theorem tailTrace_723552 : CollatzResearch.WordTrace tailWord_723552 prefixEnd_723552 330248848464051851708845 := by
  unfold tailWord_723552
  simp only [CollatzResearch.WordTrace]
  refine ⟨13195054737351075844286455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17593406316468101125715273 13195054737351075844286455)
  ·
    refine ⟨19792582106026613766429683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13195054737351075844286455 19792582106026613766429683)
    ·
      refine ⟨29688873159039920649644525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19792582106026613766429683 29688873159039920649644525)
      ·
        refine ⟨11133327434639970243616697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29688873159039920649644525 11133327434639970243616697)
        ·
          refine ⟨8349995575979977682712523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11133327434639970243616697 8349995575979977682712523)
          ·
            refine ⟨12524993363969966524068785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8349995575979977682712523 12524993363969966524068785)
            ·
              refine ⟨9393745022977474893051589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12524993363969966524068785 9393745022977474893051589)
              ·
                refine ⟨1761327191808276542447173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9393745022977474893051589 1761327191808276542447173)
                ·
                  refine ⟨330248848464051851708845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761327191808276542447173 330248848464051851708845)
                  ·
                    rfl

theorem cell20_723552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_723552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723552 prefixEnd_723552 := by exact prefixLift 723552
  have htrace : WordTrace (prefixWord ++ tailWord_723552) baseStart_723552 baseEnd_723552 := by
    simpa [prefixWord, tailWord_723552, baseEnd_723552] using wordTrace_append hprefix tailTrace_723552
  have hstable : (prefixWord ++ tailWord_723552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723552).length < 2 ^ (prefixWord ++ tailWord_723552).sum := by decide
  have hdescent : baseEnd_723552 < baseStart_723552 := by decide
  rcases family_descends (prefixWord ++ tailWord_723552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723610 : List Nat := [3, 1, 1, 6, 1, 1, 3, 4]
def baseStart_723610 : Nat := 118140960795 + 723610 * 2 ^ 59
def prefixEnd_723610 : Nat := 4983230072969 + 3 ^ 40 * 723610 * 2
def baseEnd_723610 : Nat := 110091773748153809258425

theorem tailTrace_723610 : CollatzResearch.WordTrace tailWord_723610 prefixEnd_723610 110091773748153809258425 := by
  unfold tailWord_723610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598056227123006898546071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17594816605661351729456189 6598056227123006898546071)
  ·
    refine ⟨9897084340684510347819107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6598056227123006898546071 9897084340684510347819107)
    ·
      refine ⟨14845626511026765521728661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9897084340684510347819107 14845626511026765521728661)
      ·
        refine ⟨695888742704379633831031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14845626511026765521728661 695888742704379633831031)
        ·
          refine ⟨1043833114056569450746547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695888742704379633831031 1043833114056569450746547)
          ·
            refine ⟨1565749671084854176119821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043833114056569450746547 1565749671084854176119821)
            ·
              refine ⟨587156126656820316044933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565749671084854176119821 587156126656820316044933)
              ·
                refine ⟨110091773748153809258425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 587156126656820316044933 110091773748153809258425)
                ·
                  rfl

theorem cell20_723610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_723610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723610 prefixEnd_723610 := by exact prefixLift 723610
  have htrace : WordTrace (prefixWord ++ tailWord_723610) baseStart_723610 baseEnd_723610 := by
    simpa [prefixWord, tailWord_723610, baseEnd_723610] using wordTrace_append hprefix tailTrace_723610
  have hstable : (prefixWord ++ tailWord_723610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723610).length < 2 ^ (prefixWord ++ tailWord_723610).sum := by decide
  have hdescent : baseEnd_723610 < baseStart_723610 := by decide
  rcases family_descends (prefixWord ++ tailWord_723610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723635 : List Nat := [1, 1, 1, 2, 3, 5, 7]
def baseStart_723635 : Nat := 118140960795 + 723635 * 2 ^ 59
def prefixEnd_723635 : Nat := 4983230072969 + 3 ^ 40 * 723635 * 2
def baseEnd_723635 : Nat := 36698525769519161326871

theorem tailTrace_723635 : CollatzResearch.WordTrace tailWord_723635 prefixEnd_723635 36698525769519161326871 := by
  unfold tailWord_723635
  simp only [CollatzResearch.WordTrace]
  refine ⟨26393136733401456863844359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17595424488934304575896239 26393136733401456863844359)
  ·
    refine ⟨39589705100102185295766539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26393136733401456863844359 39589705100102185295766539)
    ·
      refine ⟨59384557650153277943649809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39589705100102185295766539 59384557650153277943649809)
      ·
        refine ⟨44538418237614958457737357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59384557650153277943649809 44538418237614958457737357)
        ·
          refine ⟨16701906839105609421651509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44538418237614958457737357 16701906839105609421651509)
          ·
            refine ⟨1565803766166150883279829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16701906839105609421651509 1565803766166150883279829)
            ·
              refine ⟨36698525769519161326871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1565803766166150883279829 36698525769519161326871)
              ·
                rfl

theorem cell20_723635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 7].length) (baseStart_723635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723635 prefixEnd_723635 := by exact prefixLift 723635
  have htrace : WordTrace (prefixWord ++ tailWord_723635) baseStart_723635 baseEnd_723635 := by
    simpa [prefixWord, tailWord_723635, baseEnd_723635] using wordTrace_append hprefix tailTrace_723635
  have hstable : (prefixWord ++ tailWord_723635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723635).length < 2 ^ (prefixWord ++ tailWord_723635).sum := by decide
  have hdescent : baseEnd_723635 < baseStart_723635 := by decide
  rcases family_descends (prefixWord ++ tailWord_723635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723645 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_723645 : Nat := 118140960795 + 723645 * 2 ^ 59
def prefixEnd_723645 : Nat := 4983230072969 + 3 ^ 40 * 723645 * 2
def baseEnd_723645 : Nat := 330291296198156861608465

theorem tailTrace_723645 : CollatzResearch.WordTrace tailWord_723645 prefixEnd_723645 330291296198156861608465 := by
  unfold tailWord_723645
  simp only [CollatzResearch.WordTrace]
  refine ⟨26393501463365228571708389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17595667642243485714472259 26393501463365228571708389)
  ·
    refine ⟨4948781524380980357195323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26393501463365228571708389 4948781524380980357195323)
    ·
      refine ⟨7423172286571470535792985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4948781524380980357195323 7423172286571470535792985)
      ·
        refine ⟨5567379214928602901844739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7423172286571470535792985 5567379214928602901844739)
        ·
          refine ⟨8351068822392904352767109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567379214928602901844739 8351068822392904352767109)
          ·
            refine ⟨1565825404198669566143833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8351068822392904352767109 1565825404198669566143833)
            ·
              refine ⟨1174369053149002174607875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1565825404198669566143833 1174369053149002174607875)
              ·
                refine ⟨1761553579723503261911813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174369053149002174607875 1761553579723503261911813)
                ·
                  refine ⟨330291296198156861608465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761553579723503261911813 330291296198156861608465)
                  ·
                    rfl

theorem cell20_723645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_723645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723645 prefixEnd_723645 := by exact prefixLift 723645
  have htrace : WordTrace (prefixWord ++ tailWord_723645) baseStart_723645 baseEnd_723645 := by
    simpa [prefixWord, tailWord_723645, baseEnd_723645] using wordTrace_append hprefix tailTrace_723645
  have hstable : (prefixWord ++ tailWord_723645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723645).length < 2 ^ (prefixWord ++ tailWord_723645).sum := by decide
  have hdescent : baseEnd_723645 < baseStart_723645 := by decide
  rcases family_descends (prefixWord ++ tailWord_723645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723669 : List Nat := [1, 3, 2, 5, 1, 1, 1, 6]
def baseStart_723669 : Nat := 118140960795 + 723669 * 2 ^ 59
def prefixEnd_723669 : Nat := 4983230072969 + 3 ^ 40 * 723669 * 2
def baseEnd_723669 : Nat := 110100750150706481602789

theorem tailTrace_723669 : CollatzResearch.WordTrace tailWord_723669 prefixEnd_723669 110100750150706481602789 := by
  unfold tailWord_723669
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394376815278280670582061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17596251210185520447054707 26394376815278280670582061)
  ·
    refine ⟨9897891305729355251468273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26394376815278280670582061 9897891305729355251468273)
    ·
      refine ⟨7423418479297016438601205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9897891305729355251468273 7423418479297016438601205)
      ·
        refine ⟨695945482434095291118863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7423418479297016438601205 695945482434095291118863)
        ·
          refine ⟨1043918223651142936678295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695945482434095291118863 1043918223651142936678295)
          ·
            refine ⟨1565877335476714405017443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043918223651142936678295 1565877335476714405017443)
            ·
              refine ⟨2348816003215071607526165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565877335476714405017443 2348816003215071607526165)
              ·
                refine ⟨110100750150706481602789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2348816003215071607526165 110100750150706481602789)
                ·
                  rfl

theorem cell20_723669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_723669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723669 prefixEnd_723669 := by exact prefixLift 723669
  have htrace : WordTrace (prefixWord ++ tailWord_723669) baseStart_723669 baseEnd_723669 := by
    simpa [prefixWord, tailWord_723669, baseEnd_723669] using wordTrace_append hprefix tailTrace_723669
  have hstable : (prefixWord ++ tailWord_723669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723669).length < 2 ^ (prefixWord ++ tailWord_723669).sum := by decide
  have hdescent : baseEnd_723669 < baseStart_723669 := by decide
  rcases family_descends (prefixWord ++ tailWord_723669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723673 : List Nat := [1, 2, 1, 2, 3, 2, 3, 6]
def baseStart_723673 : Nat := 118140960795 + 723673 * 2 ^ 59
def prefixEnd_723673 : Nat := 4983230072969 + 3 ^ 40 * 723673 * 2
def baseEnd_723673 : Nat := 110101358720371069558339

theorem tailTrace_723673 : CollatzResearch.WordTrace tailWord_723673 prefixEnd_723673 110101358720371069558339 := by
  unfold tailWord_723673
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394522707263789353727673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17596348471509192902485115 26394522707263789353727673)
  ·
    refine ⟨19795892030447842015295755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26394522707263789353727673 19795892030447842015295755)
    ·
      refine ⟨29693838045671763022943633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19795892030447842015295755 29693838045671763022943633)
      ·
        refine ⟨22270378534253822267207725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29693838045671763022943633 22270378534253822267207725)
        ·
          refine ⟨8351391950345183350202897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22270378534253822267207725 8351391950345183350202897)
          ·
            refine ⟨6263543962758887512652173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8351391950345183350202897 6263543962758887512652173)
            ·
              refine ⟨2348828986034582817244565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6263543962758887512652173 2348828986034582817244565)
              ·
                refine ⟨110101358720371069558339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2348828986034582817244565 110101358720371069558339)
                ·
                  rfl

theorem cell20_723673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_723673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723673 prefixEnd_723673 := by exact prefixLift 723673
  have htrace : WordTrace (prefixWord ++ tailWord_723673) baseStart_723673 baseEnd_723673 := by
    simpa [prefixWord, tailWord_723673, baseEnd_723673] using wordTrace_append hprefix tailTrace_723673
  have hstable : (prefixWord ++ tailWord_723673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723673).length < 2 ^ (prefixWord ++ tailWord_723673).sum := by decide
  have hdescent : baseEnd_723673 < baseStart_723673 := by decide
  rcases family_descends (prefixWord ++ tailWord_723673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723676 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_723676 : Nat := 118140960795 + 723676 * 2 ^ 59
def prefixEnd_723676 : Nat := 4983230072969 + 3 ^ 40 * 723676 * 2
def baseEnd_723676 : Nat := 330305445442858531575005

theorem tailTrace_723676 : CollatzResearch.WordTrace tailWord_723676 prefixEnd_723676 330305445442858531575005 := by
  unfold tailWord_723676
  simp only [CollatzResearch.WordTrace]
  refine ⟨13197316063126460433043441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17596421417501947244057921 13197316063126460433043441)
  ·
    refine ⟨9897987047344845324782581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13197316063126460433043441 9897987047344845324782581)
    ·
      refine ⟨927936285688579249198367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9897987047344845324782581 927936285688579249198367)
      ·
        refine ⟨1391904428532868873797551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927936285688579249198367 1391904428532868873797551)
        ·
          refine ⟨2087856642799303310696327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391904428532868873797551 2087856642799303310696327)
          ·
            refine ⟨3131784964198954966044491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087856642799303310696327 3131784964198954966044491)
            ·
              refine ⟨4697677446298432449066737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3131784964198954966044491 4697677446298432449066737)
              ·
                refine ⟨3523258084723824336800053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4697677446298432449066737 3523258084723824336800053)
                ·
                  refine ⟨330305445442858531575005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3523258084723824336800053 330305445442858531575005)
                  ·
                    rfl

theorem cell20_723676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_723676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723676 prefixEnd_723676 := by exact prefixLift 723676
  have htrace : WordTrace (prefixWord ++ tailWord_723676) baseStart_723676 baseEnd_723676 := by
    simpa [prefixWord, tailWord_723676, baseEnd_723676] using wordTrace_append hprefix tailTrace_723676
  have hstable : (prefixWord ++ tailWord_723676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723676).length < 2 ^ (prefixWord ++ tailWord_723676).sum := by decide
  have hdescent : baseEnd_723676 < baseStart_723676 := by decide
  rcases family_descends (prefixWord ++ tailWord_723676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723697 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 3]
def baseStart_723697 : Nat := 118140960795 + 723697 * 2 ^ 59
def prefixEnd_723697 : Nat := 4983230072969 + 3 ^ 40 * 723697 * 2
def baseEnd_723697 : Nat := 330315030415075791874919

theorem tailTrace_723697 : CollatzResearch.WordTrace tailWord_723697 prefixEnd_723697 330315030415075791874919 := by
  unfold tailWord_723697
  simp only [CollatzResearch.WordTrace]
  refine ⟨26395398059176841452601345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17596932039451227635067563 26395398059176841452601345)
  ·
    refine ⟨19796548544382631089451009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26395398059176841452601345 19796548544382631089451009)
    ·
      refine ⟨14847411408286973317088257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19796548544382631089451009 14847411408286973317088257)
      ·
        refine ⟨11135558556215229987816193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14847411408286973317088257 11135558556215229987816193)
        ·
          refine ⟨8351668917161422490862145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11135558556215229987816193 8351668917161422490862145)
          ·
            refine ⟨6263751687871066868146609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8351668917161422490862145 6263751687871066868146609)
            ·
              refine ⟨4697813765903300151109957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6263751687871066868146609 4697813765903300151109957)
              ·
                refine ⟨880840081106868778333117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4697813765903300151109957 880840081106868778333117)
                ·
                  refine ⟨330315030415075791874919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880840081106868778333117 330315030415075791874919)
                  ·
                    rfl

theorem cell20_723697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_723697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723697 prefixEnd_723697 := by exact prefixLift 723697
  have htrace : WordTrace (prefixWord ++ tailWord_723697) baseStart_723697 baseEnd_723697 := by
    simpa [prefixWord, tailWord_723697, baseEnd_723697] using wordTrace_append hprefix tailTrace_723697
  have hstable : (prefixWord ++ tailWord_723697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723697).length < 2 ^ (prefixWord ++ tailWord_723697).sum := by decide
  have hdescent : baseEnd_723697 < baseStart_723697 := by decide
  rcases family_descends (prefixWord ++ tailWord_723697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723710 : List Nat := [4, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_723710 : Nat := 118140960795 + 723710 * 2 ^ 59
def prefixEnd_723710 : Nat := 4983230072969 + 3 ^ 40 * 723710 * 2
def baseEnd_723710 : Nat := 330320963969305524441533

theorem tailTrace_723710 : CollatzResearch.WordTrace tailWord_723710 prefixEnd_723710 330320963969305524441533 := by
  unfold tailWord_723710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3299484026016218084103073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17597248138753163115216389 3299484026016218084103073)
  ·
    refine ⟨2474613019512163563077305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3299484026016218084103073 2474613019512163563077305)
    ·
      refine ⟨1855959764634122672307979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2474613019512163563077305 1855959764634122672307979)
      ·
        refine ⟨2783939646951184008461969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855959764634122672307979 2783939646951184008461969)
        ·
          refine ⟨2087954735213388006346477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2783939646951184008461969 2087954735213388006346477)
          ·
            refine ⟨782983025705020502379929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2087954735213388006346477 782983025705020502379929)
            ·
              refine ⟨587237269278765376784947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782983025705020502379929 587237269278765376784947)
              ·
                refine ⟨880855903918148065177421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587237269278765376784947 880855903918148065177421)
                ·
                  refine ⟨330320963969305524441533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880855903918148065177421 330320963969305524441533)
                  ·
                    rfl

theorem cell20_723710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_723710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723710 prefixEnd_723710 := by exact prefixLift 723710
  have htrace : WordTrace (prefixWord ++ tailWord_723710) baseStart_723710 baseEnd_723710 := by
    simpa [prefixWord, tailWord_723710, baseEnd_723710] using wordTrace_append hprefix tailTrace_723710
  have hstable : (prefixWord ++ tailWord_723710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723710).length < 2 ^ (prefixWord ++ tailWord_723710).sum := by decide
  have hdescent : baseEnd_723710 < baseStart_723710 := by decide
  rcases family_descends (prefixWord ++ tailWord_723710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723752 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_723752 : Nat := 118140960795 + 723752 * 2 ^ 59
def prefixEnd_723752 : Nat := 4983230072969 + 3 ^ 40 * 723752 * 2
def baseEnd_723752 : Nat := 330340133913740045041361

theorem tailTrace_723752 : CollatzResearch.WordTrace tailWord_723752 prefixEnd_723752 330340133913740045041361 := by
  unfold tailWord_723752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13198702036988792922926755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17598269382651723897235673 13198702036988792922926755)
  ·
    refine ⟨19798053055483189384390133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13198702036988792922926755 19798053055483189384390133)
    ·
      refine ⟨1856067473951549004786575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19798053055483189384390133 1856067473951549004786575)
      ·
        refine ⟨2784101210927323507179863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856067473951549004786575 2784101210927323507179863)
        ·
          refine ⟨4176151816390985260769795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2784101210927323507179863 4176151816390985260769795)
          ·
            refine ⟨6264227724586477891154693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176151816390985260769795 6264227724586477891154693)
            ·
              refine ⟨1174542698359964604591505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6264227724586477891154693 1174542698359964604591505)
              ·
                refine ⟨880907023769973453443629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174542698359964604591505 880907023769973453443629)
                ·
                  refine ⟨330340133913740045041361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880907023769973453443629 330340133913740045041361)
                  ·
                    rfl

theorem cell20_723752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_723752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723752 prefixEnd_723752 := by exact prefixLift 723752
  have htrace : WordTrace (prefixWord ++ tailWord_723752) baseStart_723752 baseEnd_723752 := by
    simpa [prefixWord, tailWord_723752, baseEnd_723752] using wordTrace_append hprefix tailTrace_723752
  have hstable : (prefixWord ++ tailWord_723752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723752).length < 2 ^ (prefixWord ++ tailWord_723752).sum := by decide
  have hdescent : baseEnd_723752 < baseStart_723752 := by decide
  rcases family_descends (prefixWord ++ tailWord_723752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723804 : List Nat := [2, 2, 4, 2, 1, 2, 7]
def baseStart_723804 : Nat := 118140960795 + 723804 * 2 ^ 59
def prefixEnd_723804 : Nat := 4983230072969 + 3 ^ 40 * 723804 * 2
def baseEnd_723804 : Nat := 36707096458962108367535

theorem tailTrace_723804 : CollatzResearch.WordTrace tailWord_723804 prefixEnd_723804 36707096458962108367535 := by
  unfold tailWord_723804
  simp only [CollatzResearch.WordTrace]
  refine ⟨13199650334894599363373233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17599533779859465817830977 13199650334894599363373233)
  ·
    refine ⟨9899737751170949522529925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13199650334894599363373233 9899737751170949522529925)
    ·
      refine ⟨1856200828344553035474361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9899737751170949522529925 1856200828344553035474361)
      ·
        refine ⟨1392150621258414776605771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1856200828344553035474361 1392150621258414776605771)
        ·
          refine ⟨2088225931887622164908657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392150621258414776605771 2088225931887622164908657)
          ·
            refine ⟨1566169448915716623681493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2088225931887622164908657 1566169448915716623681493)
            ·
              refine ⟨36707096458962108367535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1566169448915716623681493 36707096458962108367535)
              ·
                rfl

theorem cell20_723804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 7].length) (baseStart_723804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723804 prefixEnd_723804 := by exact prefixLift 723804
  have htrace : WordTrace (prefixWord ++ tailWord_723804) baseStart_723804 baseEnd_723804 := by
    simpa [prefixWord, tailWord_723804, baseEnd_723804] using wordTrace_append hprefix tailTrace_723804
  have hstable : (prefixWord ++ tailWord_723804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723804).length < 2 ^ (prefixWord ++ tailWord_723804).sum := by decide
  have hdescent : baseEnd_723804 < baseStart_723804 := by decide
  rcases family_descends (prefixWord ++ tailWord_723804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723811 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_723811 : Nat := 118140960795 + 723811 * 2 ^ 59
def prefixEnd_723811 : Nat := 4983230072969 + 3 ^ 40 * 723811 * 2
def baseEnd_723811 : Nat := 330367063121398062074453

theorem tailTrace_723811 : CollatzResearch.WordTrace tailWord_723811 prefixEnd_723811 330367063121398062074453 := by
  unfold tailWord_723811
  simp only [CollatzResearch.WordTrace]
  refine ⟨26399555980763838922251287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17599703987175892614834191 26399555980763838922251287)
  ·
    refine ⟨39599333971145758383376931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26399555980763838922251287 39599333971145758383376931)
    ·
      refine ⟨59399000956718637575065397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39599333971145758383376931 59399000956718637575065397)
      ·
        refine ⟨5568656339692372272662381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59399000956718637575065397 5568656339692372272662381)
        ·
          refine ⟨2088246127384639602248393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5568656339692372272662381 2088246127384639602248393)
          ·
            refine ⟨1566184595538479701686295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2088246127384639602248393 1566184595538479701686295)
            ·
              refine ⟨2349276893307719552529443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566184595538479701686295 2349276893307719552529443)
              ·
                refine ⟨3523915339961579328794165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349276893307719552529443 3523915339961579328794165)
                ·
                  refine ⟨330367063121398062074453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3523915339961579328794165 330367063121398062074453)
                  ·
                    rfl

theorem cell20_723811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_723811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723811 prefixEnd_723811 := by exact prefixLift 723811
  have htrace : WordTrace (prefixWord ++ tailWord_723811) baseStart_723811 baseEnd_723811 := by
    simpa [prefixWord, tailWord_723811, baseEnd_723811] using wordTrace_append hprefix tailTrace_723811
  have hstable : (prefixWord ++ tailWord_723811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723811).length < 2 ^ (prefixWord ++ tailWord_723811).sum := by decide
  have hdescent : baseEnd_723811 < baseStart_723811 := by decide
  rcases family_descends (prefixWord ++ tailWord_723811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723873 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_723873 : Nat := 118140960795 + 723873 * 2 ^ 59
def prefixEnd_723873 : Nat := 4983230072969 + 3 ^ 40 * 723873 * 2
def baseEnd_723873 : Nat := 330395361610801402007533

theorem tailTrace_723873 : CollatzResearch.WordTrace tailWord_723873 prefixEnd_723873 330395361610801402007533 := by
  unfold tailWord_723873
  simp only [CollatzResearch.WordTrace]
  refine ⟨26401817306539223511008273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17601211537692815674005515 26401817306539223511008273)
  ·
    refine ⟨19801362979904417633256205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26401817306539223511008273 19801362979904417633256205)
    ·
      refine ⟨7425511117464156612471077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19801362979904417633256205 7425511117464156612471077)
      ·
        refine ⟨1392283334524529364838327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7425511117464156612471077 1392283334524529364838327)
        ·
          refine ⟨2088425001786794047257491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392283334524529364838327 2088425001786794047257491)
          ·
            refine ⟨3132637502680191070886237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088425001786794047257491 3132637502680191070886237)
            ·
              refine ⟨1174739063505071651582339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3132637502680191070886237 1174739063505071651582339)
              ·
                refine ⟨1762108595257607477373509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174739063505071651582339 1762108595257607477373509)
                ·
                  refine ⟨330395361610801402007533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1762108595257607477373509 330395361610801402007533)
                  ·
                    rfl

theorem cell20_723873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_723873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723873 prefixEnd_723873 := by exact prefixLift 723873
  have htrace : WordTrace (prefixWord ++ tailWord_723873) baseStart_723873 baseEnd_723873 := by
    simpa [prefixWord, tailWord_723873, baseEnd_723873] using wordTrace_append hprefix tailTrace_723873
  have hstable : (prefixWord ++ tailWord_723873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723873).length < 2 ^ (prefixWord ++ tailWord_723873).sum := by decide
  have hdescent : baseEnd_723873 < baseStart_723873 := by decide
  rcases family_descends (prefixWord ++ tailWord_723873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723917 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 3]
def baseStart_723917 : Nat := 118140960795 + 723917 * 2 ^ 59
def prefixEnd_723917 : Nat := 4983230072969 + 3 ^ 40 * 723917 * 2
def baseEnd_723917 : Nat := 330415444409732804540687

theorem tailTrace_723917 : CollatzResearch.WordTrace tailWord_723917 prefixEnd_723917 330415444409732804540687 := by
  unfold tailWord_723917
  simp only [CollatzResearch.WordTrace]
  refine ⟨26403422118379819025610005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17602281412253212683740003 26403422118379819025610005)
  ·
    refine ⟨1237660411799054016825469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26403422118379819025610005 1237660411799054016825469)
    ·
      refine ⟨464122654424645256309551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1237660411799054016825469 464122654424645256309551)
      ·
        refine ⟨696183981636967884464327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464122654424645256309551 696183981636967884464327)
        ·
          refine ⟨1044275972455451826696491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696183981636967884464327 1044275972455451826696491)
          ·
            refine ⟨1566413958683177740044737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044275972455451826696491 1566413958683177740044737)
            ·
              refine ⟨1174810469012383305033553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566413958683177740044737 1174810469012383305033553)
              ·
                refine ⟨881107851759287478775165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174810469012383305033553 881107851759287478775165)
                ·
                  refine ⟨330415444409732804540687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881107851759287478775165 330415444409732804540687)
                  ·
                    rfl

theorem cell20_723917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_723917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723917 prefixEnd_723917 := by exact prefixLift 723917
  have htrace : WordTrace (prefixWord ++ tailWord_723917) baseStart_723917 baseEnd_723917 := by
    simpa [prefixWord, tailWord_723917, baseEnd_723917] using wordTrace_append hprefix tailTrace_723917
  have hstable : (prefixWord ++ tailWord_723917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723917).length < 2 ^ (prefixWord ++ tailWord_723917).sum := by decide
  have hdescent : baseEnd_723917 < baseStart_723917 := by decide
  rcases family_descends (prefixWord ++ tailWord_723917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723928 : List Nat := [2, 1, 2, 2, 2, 3, 4, 2, 2]
def baseStart_723928 : Nat := 118140960795 + 723928 * 2 ^ 59
def prefixEnd_723928 : Nat := 4983230072969 + 3 ^ 40 * 723928 * 2
def baseEnd_723928 : Nat := 330420465109465655173975

theorem tailTrace_723928 : CollatzResearch.WordTrace tailWord_723928 prefixEnd_723928 330420465109465655173975 := by
  unfold tailWord_723928
  simp only [CollatzResearch.WordTrace]
  refine ⟨13201911660669983952130219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17602548880893311936173625 13201911660669983952130219)
  ·
    refine ⟨19802867491004975928195329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13201911660669983952130219 19802867491004975928195329)
    ·
      refine ⟨14852150618253731946146497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19802867491004975928195329 14852150618253731946146497)
      ·
        refine ⟨11139112963690298959609873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14852150618253731946146497 11139112963690298959609873)
        ·
          refine ⟨8354334722767724219707405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11139112963690298959609873 8354334722767724219707405)
          ·
            refine ⟨3132875521037896582390277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8354334722767724219707405 3132875521037896582390277)
            ·
              refine ⟨587414160194605609198177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3132875521037896582390277 587414160194605609198177)
              ·
                refine ⟨440560620145954206898633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587414160194605609198177 440560620145954206898633)
                ·
                  refine ⟨330420465109465655173975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440560620145954206898633 330420465109465655173975)
                  ·
                    rfl

theorem cell20_723928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_723928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723928 prefixEnd_723928 := by exact prefixLift 723928
  have htrace : WordTrace (prefixWord ++ tailWord_723928) baseStart_723928 baseEnd_723928 := by
    simpa [prefixWord, tailWord_723928, baseEnd_723928] using wordTrace_append hprefix tailTrace_723928
  have hstable : (prefixWord ++ tailWord_723928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723928).length < 2 ^ (prefixWord ++ tailWord_723928).sum := by decide
  have hdescent : baseEnd_723928 < baseStart_723928 := by decide
  rcases family_descends (prefixWord ++ tailWord_723928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723935 : List Nat := [1, 1, 2, 3, 6, 1, 1, 5]
def baseStart_723935 : Nat := 118140960795 + 723935 * 2 ^ 59
def prefixEnd_723935 : Nat := 4983230072969 + 3 ^ 40 * 723935 * 2
def baseEnd_723935 : Nat := 110141220033401580646871

theorem tailTrace_723935 : CollatzResearch.WordTrace tailWord_723935 prefixEnd_723935 110141220033401580646871 := by
  unfold tailWord_723935
  simp only [CollatzResearch.WordTrace]
  refine ⟨26404078632314608099765259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17602719088209738733176839 26404078632314608099765259)
  ·
    refine ⟨39606117948471912149647889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26404078632314608099765259 39606117948471912149647889)
    ·
      refine ⟨29704588461353934112235917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39606117948471912149647889 29704588461353934112235917)
      ·
        refine ⟨11139220673007725292088469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29704588461353934112235917 11139220673007725292088469)
        ·
          refine ⟨522150969047237123066647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11139220673007725292088469 522150969047237123066647)
          ·
            refine ⟨783226453570855684599971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522150969047237123066647 783226453570855684599971)
            ·
              refine ⟨1174839680356283526899957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783226453570855684599971 1174839680356283526899957)
              ·
                refine ⟨110141220033401580646871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1174839680356283526899957 110141220033401580646871)
                ·
                  rfl

theorem cell20_723935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 5].length) (baseStart_723935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723935 prefixEnd_723935 := by exact prefixLift 723935
  have htrace : WordTrace (prefixWord ++ tailWord_723935) baseStart_723935 baseEnd_723935 := by
    simpa [prefixWord, tailWord_723935, baseEnd_723935] using wordTrace_append hprefix tailTrace_723935
  have hstable : (prefixWord ++ tailWord_723935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723935).length < 2 ^ (prefixWord ++ tailWord_723935).sum := by decide
  have hdescent : baseEnd_723935 < baseStart_723935 := by decide
  rcases family_descends (prefixWord ++ tailWord_723935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723980 : List Nat := [2, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_723980 : Nat := 118140960795 + 723980 * 2 ^ 59
def prefixEnd_723980 : Nat := 4983230072969 + 3 ^ 40 * 723980 * 2
def baseEnd_723980 : Nat := 330444199326384585440429

theorem tailTrace_723980 : CollatzResearch.WordTrace tailWord_723980 prefixEnd_723980 330444199326384585440429 := by
  unfold tailWord_723980
  simp only [CollatzResearch.WordTrace]
  refine ⟨13202859958575790392576697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17603813278101053856768929 13202859958575790392576697)
  ·
    refine ⟨9902144968931842794432523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13202859958575790392576697 9902144968931842794432523)
    ·
      refine ⟨14853217453397764191648785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9902144968931842794432523 14853217453397764191648785)
      ·
        refine ⟨11139913090048323143736589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14853217453397764191648785 11139913090048323143736589)
        ·
          refine ⟨4177467408768121178901221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11139913090048323143736589 4177467408768121178901221)
          ·
            refine ⟨783275139144022721043979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4177467408768121178901221 783275139144022721043979)
            ·
              refine ⟨1174912708716034081565969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783275139144022721043979 1174912708716034081565969)
              ·
                refine ⟨881184531537025561174477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174912708716034081565969 881184531537025561174477)
                ·
                  refine ⟨330444199326384585440429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881184531537025561174477 330444199326384585440429)
                  ·
                    rfl

theorem cell20_723980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_723980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723980 prefixEnd_723980 := by exact prefixLift 723980
  have htrace : WordTrace (prefixWord ++ tailWord_723980) baseStart_723980 baseEnd_723980 := by
    simpa [prefixWord, tailWord_723980, baseEnd_723980] using wordTrace_append hprefix tailTrace_723980
  have hstable : (prefixWord ++ tailWord_723980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723980).length < 2 ^ (prefixWord ++ tailWord_723980).sum := by decide
  have hdescent : baseEnd_723980 < baseStart_723980 := by decide
  rcases family_descends (prefixWord ++ tailWord_723980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723997 : List Nat := [1, 4, 2, 2, 3, 1, 3, 1, 3]
def baseStart_723997 : Nat := 118140960795 + 723997 * 2 ^ 59
def prefixEnd_723997 : Nat := 4983230072969 + 3 ^ 40 * 723997 * 2
def baseEnd_723997 : Nat := 330451958589608081873693

theorem tailTrace_723997 : CollatzResearch.WordTrace tailWord_723997 prefixEnd_723997 330451958589608081873693 := by
  unfold tailWord_723997
  simp only [CollatzResearch.WordTrace]
  refine ⟨26406339958089992688522245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17604226638726661792348163 26406339958089992688522245)
  ·
    refine ⟨4951188742141873629097921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26406339958089992688522245 4951188742141873629097921)
    ·
      refine ⟨3713391556606405221823441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4951188742141873629097921 3713391556606405221823441)
      ·
        refine ⟨2785043667454803916367581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3713391556606405221823441 2785043667454803916367581)
        ·
          refine ⟨1044391375295551468637843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2785043667454803916367581 1044391375295551468637843)
          ·
            refine ⟨1566587062943327202956765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044391375295551468637843 1566587062943327202956765)
            ·
              refine ⟨587470148603747701108787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1566587062943327202956765 587470148603747701108787)
              ·
                refine ⟨881205222905621551663181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587470148603747701108787 881205222905621551663181)
                ·
                  refine ⟨330451958589608081873693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881205222905621551663181 330451958589608081873693)
                  ·
                    rfl

theorem cell20_723997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_723997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_723997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_723997 prefixEnd_723997 := by exact prefixLift 723997
  have htrace : WordTrace (prefixWord ++ tailWord_723997) baseStart_723997 baseEnd_723997 := by
    simpa [prefixWord, tailWord_723997, baseEnd_723997] using wordTrace_append hprefix tailTrace_723997
  have hstable : (prefixWord ++ tailWord_723997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723997).length < 2 ^ (prefixWord ++ tailWord_723997).sum := by decide
  have hdescent : baseEnd_723997 < baseStart_723997 := by decide
  rcases family_descends (prefixWord ++ tailWord_723997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724038 : List Nat := [6, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_724038 : Nat := 118140960795 + 724038 * 2 ^ 59
def prefixEnd_724038 : Nat := 4983230072969 + 3 ^ 40 * 724038 * 2
def baseEnd_724038 : Nat := 330470672106794161506859

theorem tailTrace_724038 : CollatzResearch.WordTrace tailWord_724038 prefixEnd_724038 330470672106794161506859 := by
  unfold tailWord_724038
  simp only [CollatzResearch.WordTrace]
  refine ⟨825244854716920521586399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17605223567294304460509845 825244854716920521586399)
  ·
    refine ⟨1237867282075380782379599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 825244854716920521586399 1237867282075380782379599)
    ·
      refine ⟨1856800923113071173569399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1237867282075380782379599 1856800923113071173569399)
      ·
        refine ⟨2785201384669606760354099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856800923113071173569399 2785201384669606760354099)
        ·
          refine ⟨4177802077004410140531149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785201384669606760354099 4177802077004410140531149)
          ·
            refine ⟨1566675778876653802699181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4177802077004410140531149 1566675778876653802699181)
            ·
              refine ⟨587503417078745176012193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1566675778876653802699181 587503417078745176012193)
              ·
                refine ⟨440627562809058882009145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587503417078745176012193 440627562809058882009145)
                ·
                  refine ⟨330470672106794161506859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440627562809058882009145 330470672106794161506859)
                  ·
                    rfl

theorem cell20_724038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_724038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724038 prefixEnd_724038 := by exact prefixLift 724038
  have htrace : WordTrace (prefixWord ++ tailWord_724038) baseStart_724038 baseEnd_724038 := by
    simpa [prefixWord, tailWord_724038, baseEnd_724038] using wordTrace_append hprefix tailTrace_724038
  have hstable : (prefixWord ++ tailWord_724038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724038).length < 2 ^ (prefixWord ++ tailWord_724038).sum := by decide
  have hdescent : baseEnd_724038 < baseStart_724038 := by decide
  rcases family_descends (prefixWord ++ tailWord_724038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724053 : List Nat := [1, 3, 2, 2, 1, 2, 4, 5]
def baseStart_724053 : Nat := 118140960795 + 724053 * 2 ^ 59
def prefixEnd_724053 : Nat := 4983230072969 + 3 ^ 40 * 724053 * 2
def baseEnd_724053 : Nat := 110159172838506925335599

theorem tailTrace_724053 : CollatzResearch.WordTrace tailWord_724053 prefixEnd_724053 110159172838506925335599 := by
  unfold tailWord_724053
  simp only [CollatzResearch.WordTrace]
  refine ⟨26408382445887114252560813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17605588297258076168373875 26408382445887114252560813)
  ·
    refine ⟨9903143417207667844710305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26408382445887114252560813 9903143417207667844710305)
    ·
      refine ⟨7427357562905750883532729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9903143417207667844710305 7427357562905750883532729)
      ·
        refine ⟨5570518172179313162649547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7427357562905750883532729 5570518172179313162649547)
        ·
          refine ⟨8355777258268969743974321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570518172179313162649547 8355777258268969743974321)
          ·
            refine ⟨6266832943701727307980741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8355777258268969743974321 6266832943701727307980741)
            ·
              refine ⟨1175031176944073870246389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6266832943701727307980741 1175031176944073870246389)
              ·
                refine ⟨110159172838506925335599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1175031176944073870246389 110159172838506925335599)
                ·
                  rfl

theorem cell20_724053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_724053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724053 prefixEnd_724053 := by exact prefixLift 724053
  have htrace : WordTrace (prefixWord ++ tailWord_724053) baseStart_724053 baseEnd_724053 := by
    simpa [prefixWord, tailWord_724053, baseEnd_724053] using wordTrace_append hprefix tailTrace_724053
  have hstable : (prefixWord ++ tailWord_724053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724053).length < 2 ^ (prefixWord ++ tailWord_724053).sum := by decide
  have hdescent : baseEnd_724053 < baseStart_724053 := by decide
  rcases family_descends (prefixWord ++ tailWord_724053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724067 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_724067 : Nat := 118140960795 + 724067 * 2 ^ 59
def prefixEnd_724067 : Nat := 4983230072969 + 3 ^ 40 * 724067 * 2
def baseEnd_724067 : Nat := 330483908496998949540073

theorem tailTrace_724067 : CollatzResearch.WordTrace tailWord_724067 prefixEnd_724067 330483908496998949540073 := by
  unfold tailWord_724067
  simp only [CollatzResearch.WordTrace]
  refine ⟨26408893067836394643570455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17605928711890929762380303 26408893067836394643570455)
  ·
    refine ⟨39613339601754591965355683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26408893067836394643570455 39613339601754591965355683)
    ·
      refine ⟨59420009402631887948033525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39613339601754591965355683 59420009402631887948033525)
      ·
        refine ⟨5570625881496739495128143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59420009402631887948033525 5570625881496739495128143)
        ·
          refine ⟨8355938822245109242692215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5570625881496739495128143 8355938822245109242692215)
          ·
            refine ⟨12533908233367663864038323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8355938822245109242692215 12533908233367663864038323)
            ·
              refine ⟨18800862350051495796057485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12533908233367663864038323 18800862350051495796057485)
              ·
                refine ⟨7050323381269310923521557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18800862350051495796057485 7050323381269310923521557)
                ·
                  refine ⟨330483908496998949540073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7050323381269310923521557 330483908496998949540073)
                  ·
                    rfl

theorem cell20_724067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_724067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724067 prefixEnd_724067 := by exact prefixLift 724067
  have htrace : WordTrace (prefixWord ++ tailWord_724067) baseStart_724067 baseEnd_724067 := by
    simpa [prefixWord, tailWord_724067, baseEnd_724067] using wordTrace_append hprefix tailTrace_724067
  have hstable : (prefixWord ++ tailWord_724067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724067).length < 2 ^ (prefixWord ++ tailWord_724067).sum := by decide
  have hdescent : baseEnd_724067 < baseStart_724067 := by decide
  rcases family_descends (prefixWord ++ tailWord_724067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724097 : List Nat := [1, 2, 4, 2, 2, 3, 2, 2, 2]
def baseStart_724097 : Nat := 118140960795 + 724097 * 2 ^ 59
def prefixEnd_724097 : Nat := 4983230072969 + 3 ^ 40 * 724097 * 2
def baseEnd_724097 : Nat := 330497601314452178539951

theorem tailTrace_724097 : CollatzResearch.WordTrace tailWord_724097 prefixEnd_724097 330497601314452178539951 := by
  unfold tailWord_724097
  simp only [CollatzResearch.WordTrace]
  refine ⟨26409987257727709767162545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17606658171818473178108363 26409987257727709767162545)
  ·
    refine ⟨19807490443295782325371909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26409987257727709767162545 19807490443295782325371909)
    ·
      refine ⟨3713904458117959186007233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19807490443295782325371909 3713904458117959186007233)
      ·
        refine ⟨2785428343588469389505425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3713904458117959186007233 2785428343588469389505425)
        ·
          refine ⟨2089071257691352042129069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2785428343588469389505425 2089071257691352042129069)
          ·
            refine ⟨783401721634257015798401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2089071257691352042129069 783401721634257015798401)
            ·
              refine ⟨587551291225692761848801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783401721634257015798401 587551291225692761848801)
              ·
                refine ⟨440663468419269571386601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587551291225692761848801 440663468419269571386601)
                ·
                  refine ⟨330497601314452178539951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440663468419269571386601 330497601314452178539951)
                  ·
                    rfl

theorem cell20_724097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_724097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724097 prefixEnd_724097 := by exact prefixLift 724097
  have htrace : WordTrace (prefixWord ++ tailWord_724097) baseStart_724097 baseEnd_724097 := by
    simpa [prefixWord, tailWord_724097, baseEnd_724097] using wordTrace_append hprefix tailTrace_724097
  have hstable : (prefixWord ++ tailWord_724097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724097).length < 2 ^ (prefixWord ++ tailWord_724097).sum := by decide
  have hdescent : baseEnd_724097 < baseStart_724097 := by decide
  rcases family_descends (prefixWord ++ tailWord_724097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
