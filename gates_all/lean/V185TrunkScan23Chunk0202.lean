import V185TrunkScan23Chunk0201

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1195711 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_1195711 : Nat := 118140960795 + 1195711 * 2 ^ 59
def prefixEnd_1195711 : Nat := 4983230072969 + 3 ^ 40 * 1195711 * 2
def baseEnd_1195711 : Nat := 613974466868276508913531

theorem tailTrace_1195711 : CollatzResearch.WordTrace tailWord_1195711 prefixEnd_1195711 613974466868276508913531 := by
  unfold tailWord_1195711
  simp only [CollatzResearch.WordTrace]
  refine ⟨43611162971150733025826987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29074108647433822017217991 43611162971150733025826987)
  ·
    refine ⟨65416744456726099538740481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43611162971150733025826987 65416744456726099538740481)
    ·
      refine ⟨49062558342544574654055361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65416744456726099538740481 49062558342544574654055361)
      ·
        refine ⟨36796918756908430990541521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49062558342544574654055361 36796918756908430990541521)
        ·
          refine ⟨27597689067681323242906141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36796918756908430990541521 27597689067681323242906141)
          ·
            refine ⟨10349133400380496216089803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27597689067681323242906141 10349133400380496216089803)
            ·
              refine ⟨15523700100570744324134705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349133400380496216089803 15523700100570744324134705)
              ·
                refine ⟨11642775075428058243101029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15523700100570744324134705 11642775075428058243101029)
                ·
                  refine ⟨2183020326642760920581443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11642775075428058243101029 2183020326642760920581443)
                  ·
                    refine ⟨3274530489964141380872165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2183020326642760920581443 3274530489964141380872165)
                    ·
                      refine ⟨613974466868276508913531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3274530489964141380872165 613974466868276508913531)
                      ·
                        rfl

theorem cell23_1195711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_1195711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195711 prefixEnd_1195711 := by exact prefixLift 1195711
  have htrace : WordTrace (prefixWord ++ tailWord_1195711) baseStart_1195711 baseEnd_1195711 := by
    simpa [prefixWord, tailWord_1195711, baseEnd_1195711] using wordTrace_append hprefix tailTrace_1195711
  have hstable : (prefixWord ++ tailWord_1195711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195711).length < 2 ^ (prefixWord ++ tailWord_1195711).sum := by decide
  have hdescent : baseEnd_1195711 < baseStart_1195711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195725 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1195725 : Nat := 118140960795 + 1195725 * 2 ^ 59
def prefixEnd_1195725 : Nat := 4983230072969 + 3 ^ 40 * 1195725 * 2
def baseEnd_1195725 : Nat := 204660551865813151379489

theorem tailTrace_1195725 : CollatzResearch.WordTrace tailWord_1195725 prefixEnd_1195725 204660551865813151379489 := by
  unfold tailWord_1195725
  simp only [CollatzResearch.WordTrace]
  refine ⟨43611673593100013416836629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29074449062066675611224419 43611673593100013416836629)
  ·
    refine ⟨2044297199676563128914217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43611673593100013416836629 2044297199676563128914217)
    ·
      refine ⟨1533222899757422346685663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2044297199676563128914217 1533222899757422346685663)
      ·
        refine ⟨2299834349636133520028495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533222899757422346685663 2299834349636133520028495)
        ·
          refine ⟨3449751524454200280042743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299834349636133520028495 3449751524454200280042743)
          ·
            refine ⟨5174627286681300420064115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449751524454200280042743 5174627286681300420064115)
            ·
              refine ⟨7761940930021950630096173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5174627286681300420064115 7761940930021950630096173)
              ·
                refine ⟨2910727848758231486286065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7761940930021950630096173 2910727848758231486286065)
                ·
                  refine ⟨2183045886568673614714549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2910727848758231486286065 2183045886568673614714549)
                  ·
                    refine ⟨204660551865813151379489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2183045886568673614714549 204660551865813151379489)
                    ·
                      rfl

theorem cell23_1195725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1195725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195725 prefixEnd_1195725 := by exact prefixLift 1195725
  have htrace : WordTrace (prefixWord ++ tailWord_1195725) baseStart_1195725 baseEnd_1195725 := by
    simpa [prefixWord, tailWord_1195725, baseEnd_1195725] using wordTrace_append hprefix tailTrace_1195725
  have hstable : (prefixWord ++ tailWord_1195725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195725).length < 2 ^ (prefixWord ++ tailWord_1195725).sum := by decide
  have hdescent : baseEnd_1195725 < baseStart_1195725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195748 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_1195748 : Nat := 118140960795 + 1195748 * 2 ^ 59
def prefixEnd_1195748 : Nat := 4983230072969 + 3 ^ 40 * 1195748 * 2
def baseEnd_1195748 : Nat := 613993465652492864150861

theorem tailTrace_1195748 : CollatzResearch.WordTrace tailWord_1195748 prefixEnd_1195748 613993465652492864150861 := by
  unfold tailWord_1195748
  simp only [CollatzResearch.WordTrace]
  refine ⟨21806256236008344172461949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29075008314677792229949265 21806256236008344172461949)
  ·
    refine ⟨8177346088503129064673231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21806256236008344172461949 8177346088503129064673231)
    ·
      refine ⟨12266019132754693597009847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8177346088503129064673231 12266019132754693597009847)
      ·
        refine ⟨18399028699132040395514771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12266019132754693597009847 18399028699132040395514771)
        ·
          refine ⟨27598543048698060593272157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18399028699132040395514771 27598543048698060593272157)
          ·
            refine ⟨10349453643261772722477059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27598543048698060593272157 10349453643261772722477059)
            ·
              refine ⟨15524180464892659083715589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349453643261772722477059 15524180464892659083715589)
              ·
                refine ⟨2910783837167373578196673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15524180464892659083715589 2910783837167373578196673)
                ·
                  refine ⟨2183087877875530183647505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2910783837167373578196673 2183087877875530183647505)
                  ·
                    refine ⟨1637315908406647637735629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2183087877875530183647505 1637315908406647637735629)
                    ·
                      refine ⟨613993465652492864150861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1637315908406647637735629 613993465652492864150861)
                      ·
                        rfl

theorem cell23_1195748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_1195748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195748 prefixEnd_1195748 := by exact prefixLift 1195748
  have htrace : WordTrace (prefixWord ++ tailWord_1195748) baseStart_1195748 baseEnd_1195748 := by
    simpa [prefixWord, tailWord_1195748, baseEnd_1195748] using wordTrace_append hprefix tailTrace_1195748
  have hstable : (prefixWord ++ tailWord_1195748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195748).length < 2 ^ (prefixWord ++ tailWord_1195748).sum := by decide
  have hdescent : baseEnd_1195748 < baseStart_1195748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195811 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 3, 6]
def baseStart_1195811 : Nat := 118140960795 + 1195811 * 2 ^ 59
def prefixEnd_1195811 : Nat := 4983230072969 + 3 ^ 40 * 1195811 * 2
def baseEnd_1195811 : Nat := 204675271644575372554357

theorem tailTrace_1195811 : CollatzResearch.WordTrace tailWord_1195811 prefixEnd_1195811 204675271644575372554357 := by
  unfold tailWord_1195811
  simp only [CollatzResearch.WordTrace]
  refine ⟨43614810270788450104467287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29076540180525633402978191 43614810270788450104467287)
  ·
    refine ⟨65422215406182675156700931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43614810270788450104467287 65422215406182675156700931)
    ·
      refine ⟨98133323109274012735051397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65422215406182675156700931 98133323109274012735051397)
      ·
        refine ⟨18399998082988877387822137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98133323109274012735051397 18399998082988877387822137)
        ·
          refine ⟨13799998562241658040866603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18399998082988877387822137 13799998562241658040866603)
          ·
            refine ⟨20699997843362487061299905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13799998562241658040866603 20699997843362487061299905)
            ·
              refine ⟨15524998382521865295974929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20699997843362487061299905 15524998382521865295974929)
              ·
                refine ⟨11643748786891398971981197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15524998382521865295974929 11643748786891398971981197)
                ·
                  refine ⟨4366405795084274614492949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11643748786891398971981197 4366405795084274614492949)
                  ·
                    refine ⟨204675271644575372554357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4366405795084274614492949 204675271644575372554357)
                    ·
                      rfl

theorem cell23_1195811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 6].length) (baseStart_1195811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195811 prefixEnd_1195811 := by exact prefixLift 1195811
  have htrace : WordTrace (prefixWord ++ tailWord_1195811) baseStart_1195811 baseEnd_1195811 := by
    simpa [prefixWord, tailWord_1195811, baseEnd_1195811] using wordTrace_append hprefix tailTrace_1195811
  have hstable : (prefixWord ++ tailWord_1195811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195811).length < 2 ^ (prefixWord ++ tailWord_1195811).sum := by decide
  have hdescent : baseEnd_1195811 < baseStart_1195811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195812 : List Nat := [2, 3, 1, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1195812 : Nat := 118140960795 + 1195812 * 2 ^ 59
def prefixEnd_1195812 : Nat := 4983230072969 + 3 ^ 40 * 1195812 * 2
def baseEnd_1195812 : Nat := 614026328414380613750567

theorem tailTrace_1195812 : CollatzResearch.WordTrace tailWord_1195812 prefixEnd_1195812 614026328414380613750567 := by
  unfold tailWord_1195812
  simp only [CollatzResearch.WordTrace]
  refine ⟨21807423371892413637626845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29076564495856551516835793 21807423371892413637626845)
  ·
    refine ⟨8177783764459655114110067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21807423371892413637626845 8177783764459655114110067)
    ·
      refine ⟨12266675646689482671165101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8177783764459655114110067 12266675646689482671165101)
      ·
        refine ⟨4600003367508556001686913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12266675646689482671165101 4600003367508556001686913)
        ·
          refine ⟨3450002525631417001265185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4600003367508556001686913 3450002525631417001265185)
          ·
            refine ⟨2587501894223562750948889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3450002525631417001265185 2587501894223562750948889)
            ·
              refine ⟨1940626420667672063211667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2587501894223562750948889 1940626420667672063211667)
              ·
                refine ⟨2910939631001508094817501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940626420667672063211667 2910939631001508094817501)
                ·
                  refine ⟨1091602361625565535556563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2910939631001508094817501 1091602361625565535556563)
                  ·
                    refine ⟨1637403542438348303334845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1091602361625565535556563 1637403542438348303334845)
                    ·
                      refine ⟨614026328414380613750567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1637403542438348303334845 614026328414380613750567)
                      ·
                        rfl

theorem cell23_1195812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1195812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195812 prefixEnd_1195812 := by exact prefixLift 1195812
  have htrace : WordTrace (prefixWord ++ tailWord_1195812) baseStart_1195812 baseEnd_1195812 := by
    simpa [prefixWord, tailWord_1195812, baseEnd_1195812] using wordTrace_append hprefix tailTrace_1195812
  have hstable : (prefixWord ++ tailWord_1195812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195812).length < 2 ^ (prefixWord ++ tailWord_1195812).sum := by decide
  have hdescent : baseEnd_1195812 < baseStart_1195812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195858 : List Nat := [3, 2, 2, 1, 1, 5, 9]
def baseStart_1195858 : Nat := 118140960795 + 1195858 * 2 ^ 59
def prefixEnd_1195858 : Nat := 4983230072969 + 3 ^ 40 * 1195858 * 2
def baseEnd_1195858 : Nat := 7580863562030709058955

theorem tailTrace_1195858 : CollatzResearch.WordTrace tailWord_1195858 prefixEnd_1195858 7580863562030709058955 := by
  unfold tailWord_1195858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10904131125404544282857057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29077683001078784754285485 10904131125404544282857057)
  ·
    refine ⟨8178098344053408212142793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10904131125404544282857057 8178098344053408212142793)
    ·
      refine ⟨6133573758040056159107095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8178098344053408212142793 6133573758040056159107095)
      ·
        refine ⟨9200360637060084238660643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6133573758040056159107095 9200360637060084238660643)
        ·
          refine ⟨13800540955590126357990965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9200360637060084238660643 13800540955590126357990965)
          ·
            refine ⟨1293800714586574346061653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13800540955590126357990965 1293800714586574346061653)
            ·
              refine ⟨7580863562030709058955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1293800714586574346061653 7580863562030709058955)
              ·
                rfl

theorem cell23_1195858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 9].length) (baseStart_1195858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195858 prefixEnd_1195858 := by exact prefixLift 1195858
  have htrace : WordTrace (prefixWord ++ tailWord_1195858) baseStart_1195858 baseEnd_1195858 := by
    simpa [prefixWord, tailWord_1195858, baseEnd_1195858] using wordTrace_append hprefix tailTrace_1195858
  have hstable : (prefixWord ++ tailWord_1195858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195858).length < 2 ^ (prefixWord ++ tailWord_1195858).sum := by decide
  have hdescent : baseEnd_1195858 < baseStart_1195858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195891 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 8]
def baseStart_1195891 : Nat := 118140960795 + 1195891 * 2 ^ 59
def prefixEnd_1195891 : Nat := 4983230072969 + 3 ^ 40 * 1195891 * 2
def baseEnd_1195891 : Nat := 614066893386085804662703

theorem tailTrace_1195891 : CollatzResearch.WordTrace tailWord_1195891 prefixEnd_1195891 614066893386085804662703 := by
  unfold tailWord_1195891
  simp only [CollatzResearch.WordTrace]
  refine ⟨43617728110498623767379527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29078485406999082511586351 43617728110498623767379527)
  ·
    refine ⟨65426592165747935651069291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43617728110498623767379527 65426592165747935651069291)
    ·
      refine ⟨98139888248621903476603937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65426592165747935651069291 98139888248621903476603937)
      ·
        refine ⟨73604916186466427607452953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98139888248621903476603937 73604916186466427607452953)
        ·
          refine ⟨55203687139849820705589715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73604916186466427607452953 55203687139849820705589715)
          ·
            refine ⟨82805530709774731058384573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55203687139849820705589715 82805530709774731058384573)
            ·
              refine ⟨31052074016165524146894215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82805530709774731058384573 31052074016165524146894215)
              ·
                refine ⟨46578111024248286220341323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31052074016165524146894215 46578111024248286220341323)
                ·
                  refine ⟨69867166536372429330511985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46578111024248286220341323 69867166536372429330511985)
                  ·
                    refine ⟨52400374902279321997883989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69867166536372429330511985 52400374902279321997883989)
                    ·
                      refine ⟨614066893386085804662703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 52400374902279321997883989 614066893386085804662703)
                      ·
                        rfl

theorem cell23_1195891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_1195891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195891 prefixEnd_1195891 := by exact prefixLift 1195891
  have htrace : WordTrace (prefixWord ++ tailWord_1195891) baseStart_1195891 baseEnd_1195891 := by
    simpa [prefixWord, tailWord_1195891, baseEnd_1195891] using wordTrace_append hprefix tailTrace_1195891
  have hstable : (prefixWord ++ tailWord_1195891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195891).length < 2 ^ (prefixWord ++ tailWord_1195891).sum := by decide
  have hdescent : baseEnd_1195891 < baseStart_1195891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195902 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1195902 : Nat := 118140960795 + 1195902 * 2 ^ 59
def prefixEnd_1195902 : Nat := 4983230072969 + 3 ^ 40 * 1195902 * 2
def baseEnd_1195902 : Nat := 614072541673285261625153

theorem tailTrace_1195902 : CollatzResearch.WordTrace tailWord_1195902 prefixEnd_1195902 614072541673285261625153 := by
  unfold tailWord_1195902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5452266164182346580753745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29078752875639181764019973 5452266164182346580753745)
  ·
    refine ⟨4089199623136759935565309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5452266164182346580753745 4089199623136759935565309)
    ·
      refine ⟨1533449858676284975836991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4089199623136759935565309 1533449858676284975836991)
      ·
        refine ⟨2300174788014427463755487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533449858676284975836991 2300174788014427463755487)
        ·
          refine ⟨3450262182021641195633231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300174788014427463755487 3450262182021641195633231)
          ·
            refine ⟨5175393273032461793449847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3450262182021641195633231 5175393273032461793449847)
            ·
              refine ⟨7763089909548692690174771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5175393273032461793449847 7763089909548692690174771)
              ·
                refine ⟨11644634864323039035262157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7763089909548692690174771 11644634864323039035262157)
                ·
                  refine ⟨4366738074121139638223309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11644634864323039035262157 4366738074121139638223309)
                  ·
                    refine ⟨1637526777795427364333741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4366738074121139638223309 1637526777795427364333741)
                    ·
                      refine ⟨614072541673285261625153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1637526777795427364333741 614072541673285261625153)
                      ·
                        rfl

theorem cell23_1195902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1195902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195902 prefixEnd_1195902 := by exact prefixLift 1195902
  have htrace : WordTrace (prefixWord ++ tailWord_1195902) baseStart_1195902 baseEnd_1195902 := by
    simpa [prefixWord, tailWord_1195902, baseEnd_1195902] using wordTrace_append hprefix tailTrace_1195902
  have hstable : (prefixWord ++ tailWord_1195902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195902).length < 2 ^ (prefixWord ++ tailWord_1195902).sum := by decide
  have hdescent : baseEnd_1195902 < baseStart_1195902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195925 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_1195925 : Nat := 118140960795 + 1195925 * 2 ^ 59
def prefixEnd_1195925 : Nat := 4983230072969 + 3 ^ 40 * 1195925 * 2
def baseEnd_1195925 : Nat := 614084351728338671637547

theorem tailTrace_1195925 : CollatzResearch.WordTrace tailWord_1195925 prefixEnd_1195925 614084351728338671637547 := by
  unfold tailWord_1195925
  simp only [CollatzResearch.WordTrace]
  refine ⟨43618968192375447574117229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29079312128250298382744819 43618968192375447574117229)
  ·
    refine ⟨16357113072140792840293961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43618968192375447574117229 16357113072140792840293961)
    ·
      refine ⟨12267834804105594630220471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16357113072140792840293961 12267834804105594630220471)
      ·
        refine ⟨18401752206158391945330707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12267834804105594630220471 18401752206158391945330707)
        ·
          refine ⟨27602628309237587917996061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18401752206158391945330707 27602628309237587917996061)
          ·
            refine ⟨10350985615964095469248523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27602628309237587917996061 10350985615964095469248523)
            ·
              refine ⟨15526478423946143203872785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10350985615964095469248523 15526478423946143203872785)
              ·
                refine ⟨11644858817959607402904589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15526478423946143203872785 11644858817959607402904589)
                ·
                  refine ⟨4366822056734852776089221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11644858817959607402904589 4366822056734852776089221)
                  ·
                    refine ⟨818779135637784895516729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4366822056734852776089221 818779135637784895516729)
                    ·
                      refine ⟨614084351728338671637547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818779135637784895516729 614084351728338671637547)
                      ·
                        rfl

theorem cell23_1195925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_1195925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195925 prefixEnd_1195925 := by exact prefixLift 1195925
  have htrace : WordTrace (prefixWord ++ tailWord_1195925) baseStart_1195925 baseEnd_1195925 := by
    simpa [prefixWord, tailWord_1195925, baseEnd_1195925] using wordTrace_append hprefix tailTrace_1195925
  have hstable : (prefixWord ++ tailWord_1195925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195925).length < 2 ^ (prefixWord ++ tailWord_1195925).sum := by decide
  have hdescent : baseEnd_1195925 < baseStart_1195925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195926 : List Nat := [5, 3, 1, 1, 3, 1, 1, 8]
def baseStart_1195926 : Nat := 118140960795 + 1195926 * 2 ^ 59
def prefixEnd_1195926 : Nat := 4983230072969 + 3 ^ 40 * 1195926 * 2
def baseEnd_1195926 : Nat := 22743883896629376582409

theorem tailTrace_1195926 : CollatzResearch.WordTrace tailWord_1195926 prefixEnd_1195926 22743883896629376582409 := by
  unfold tailWord_1195926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2726187791585739046556477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29079336443581216496602421 2726187791585739046556477)
  ·
    refine ⟨1022320421844652142458679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2726187791585739046556477 1022320421844652142458679)
    ·
      refine ⟨1533480632766978213688019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1022320421844652142458679 1533480632766978213688019)
      ·
        refine ⟨2300220949150467320532029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533480632766978213688019 2300220949150467320532029)
        ·
          refine ⟨862582855931425245199511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2300220949150467320532029 862582855931425245199511)
          ·
            refine ⟨1293874283897137867799267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862582855931425245199511 1293874283897137867799267)
            ·
              refine ⟨1940811425845706801698901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293874283897137867799267 1940811425845706801698901)
              ·
                refine ⟨22743883896629376582409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1940811425845706801698901 22743883896629376582409)
                ·
                  rfl

theorem cell23_1195926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_1195926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195926 prefixEnd_1195926 := by exact prefixLift 1195926
  have htrace : WordTrace (prefixWord ++ tailWord_1195926) baseStart_1195926 baseEnd_1195926 := by
    simpa [prefixWord, tailWord_1195926, baseEnd_1195926] using wordTrace_append hprefix tailTrace_1195926
  have hstable : (prefixWord ++ tailWord_1195926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195926).length < 2 ^ (prefixWord ++ tailWord_1195926).sum := by decide
  have hdescent : baseEnd_1195926 < baseStart_1195926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195935 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 2, 6]
def baseStart_1195935 : Nat := 118140960795 + 1195935 * 2 ^ 59
def prefixEnd_1195935 : Nat := 4983230072969 + 3 ^ 40 * 1195935 * 2
def baseEnd_1195935 : Nat := 204696495511627877504167

theorem tailTrace_1195935 : CollatzResearch.WordTrace tailWord_1195935 prefixEnd_1195935 204696495511627877504167 := by
  unfold tailWord_1195935
  simp only [CollatzResearch.WordTrace]
  refine ⟨43619332922339219281981259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29079555281559479521320839 43619332922339219281981259)
  ·
    refine ⟨65428999383508828922971889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43619332922339219281981259 65428999383508828922971889)
    ·
      refine ⟨49071749537631621692228917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65428999383508828922971889 49071749537631621692228917)
      ·
        refine ⟨4600476519152964533646461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49071749537631621692228917 4600476519152964533646461)
        ·
          refine ⟨1725178694682361700117423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4600476519152964533646461 1725178694682361700117423)
          ·
            refine ⟨2587768042023542550176135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725178694682361700117423 2587768042023542550176135)
            ·
              refine ⟨3881652063035313825264203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587768042023542550176135 3881652063035313825264203)
              ·
                refine ⟨5822478094552970737896305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3881652063035313825264203 5822478094552970737896305)
                ·
                  refine ⟨4366858570914728053422229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5822478094552970737896305 4366858570914728053422229)
                  ·
                    refine ⟨204696495511627877504167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4366858570914728053422229 204696495511627877504167)
                    ·
                      rfl

theorem cell23_1195935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_1195935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195935 prefixEnd_1195935 := by exact prefixLift 1195935
  have htrace : WordTrace (prefixWord ++ tailWord_1195935) baseStart_1195935 baseEnd_1195935 := by
    simpa [prefixWord, tailWord_1195935, baseEnd_1195935] using wordTrace_append hprefix tailTrace_1195935
  have hstable : (prefixWord ++ tailWord_1195935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195935).length < 2 ^ (prefixWord ++ tailWord_1195935).sum := by decide
  have hdescent : baseEnd_1195935 < baseStart_1195935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195976 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_1195976 : Nat := 118140960795 + 1195976 * 2 ^ 59
def prefixEnd_1195976 : Nat := 4983230072969 + 3 ^ 40 * 1195976 * 2
def baseEnd_1195976 : Nat := 614110539241717972099813

theorem tailTrace_1195976 : CollatzResearch.WordTrace tailWord_1195976 prefixEnd_1195976 614110539241717972099813 := by
  unfold tailWord_1195976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21810414157595341642111891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29080552210127122189482521 21810414157595341642111891)
  ·
    refine ⟨32715621236393012463167837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21810414157595341642111891 32715621236393012463167837)
    ·
      refine ⟨12268357963647379673687939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32715621236393012463167837 12268357963647379673687939)
      ·
        refine ⟨18402536945471069510531909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12268357963647379673687939 18402536945471069510531909)
        ·
          refine ⟨3450475677275825533224733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18402536945471069510531909 3450475677275825533224733)
          ·
            refine ⟨1293928378978434574959275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3450475677275825533224733 1293928378978434574959275)
            ·
              refine ⟨1940892568467651862438913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293928378978434574959275 1940892568467651862438913)
              ·
                refine ⟨1455669426350738896829185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940892568467651862438913 1455669426350738896829185)
                ·
                  refine ⟨1091752069763054172621889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1455669426350738896829185 1091752069763054172621889)
                  ·
                    refine ⟨818814052322290629466417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1091752069763054172621889 818814052322290629466417)
                    ·
                      refine ⟨614110539241717972099813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818814052322290629466417 614110539241717972099813)
                      ·
                        rfl

theorem cell23_1195976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_1195976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195976 prefixEnd_1195976 := by exact prefixLift 1195976
  have htrace : WordTrace (prefixWord ++ tailWord_1195976) baseStart_1195976 baseEnd_1195976 := by
    simpa [prefixWord, tailWord_1195976, baseEnd_1195976] using wordTrace_append hprefix tailTrace_1195976
  have hstable : (prefixWord ++ tailWord_1195976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195976).length < 2 ^ (prefixWord ++ tailWord_1195976).sum := by decide
  have hdescent : baseEnd_1195976 < baseStart_1195976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195985 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 2, 5, 2]
def baseStart_1195985 : Nat := 118140960795 + 1195985 * 2 ^ 59
def prefixEnd_1195985 : Nat := 4983230072969 + 3 ^ 40 * 1195985 * 2
def baseEnd_1195985 : Nat := 614115160567608436887271

theorem tailTrace_1195985 : CollatzResearch.WordTrace tailWord_1195985 prefixEnd_1195985 614115160567608436887271 := by
  unfold tailWord_1195985
  simp only [CollatzResearch.WordTrace]
  refine ⟨43621156572158077821301409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29080771048105385214200939 43621156572158077821301409)
  ·
    refine ⟨32715867429118558365976057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43621156572158077821301409 32715867429118558365976057)
    ·
      refine ⟨24536900571838918774482043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32715867429118558365976057 24536900571838918774482043)
      ·
        refine ⟨36805350857758378161723065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24536900571838918774482043 36805350857758378161723065)
        ·
          refine ⟨27604013143318783621292299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36805350857758378161723065 27604013143318783621292299)
          ·
            refine ⟨41406019714978175431938449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27604013143318783621292299 41406019714978175431938449)
            ·
              refine ⟨31054514786233631573953837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41406019714978175431938449 31054514786233631573953837)
              ·
                refine ⟨11645443044837611840232689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31054514786233631573953837 11645443044837611840232689)
                ·
                  refine ⟨8734082283628208880174517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11645443044837611840232689 8734082283628208880174517)
                  ·
                    refine ⟨818820214090144582516361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8734082283628208880174517 818820214090144582516361)
                    ·
                      refine ⟨614115160567608436887271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818820214090144582516361 614115160567608436887271)
                      ·
                        rfl

theorem cell23_1195985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_1195985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1195985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1195985 prefixEnd_1195985 := by exact prefixLift 1195985
  have htrace : WordTrace (prefixWord ++ tailWord_1195985) baseStart_1195985 baseEnd_1195985 := by
    simpa [prefixWord, tailWord_1195985, baseEnd_1195985] using wordTrace_append hprefix tailTrace_1195985
  have hstable : (prefixWord ++ tailWord_1195985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195985).length < 2 ^ (prefixWord ++ tailWord_1195985).sum := by decide
  have hdescent : baseEnd_1195985 < baseStart_1195985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196008 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1196008 : Nat := 118140960795 + 1196008 * 2 ^ 59
def prefixEnd_1196008 : Nat := 4983230072969 + 3 ^ 40 * 1196008 * 2
def baseEnd_1196008 : Nat := 204708990207553948966555

theorem tailTrace_1196008 : CollatzResearch.WordTrace tailWord_1196008 prefixEnd_1196008 204708990207553948966555 := by
  unfold tailWord_1196008
  simp only [CollatzResearch.WordTrace]
  refine ⟨21810997725537376374694339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29081330300716501832925785 21810997725537376374694339)
  ·
    refine ⟨32716496588306064562041509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21810997725537376374694339 32716496588306064562041509)
    ·
      refine ⟨6134343110307387105382783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32716496588306064562041509 6134343110307387105382783)
      ·
        refine ⟨9201514665461080658074175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6134343110307387105382783 9201514665461080658074175)
        ·
          refine ⟨13802271998191620987111263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9201514665461080658074175 13802271998191620987111263)
          ·
            refine ⟨20703407997287431480666895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13802271998191620987111263 20703407997287431480666895)
            ·
              refine ⟨31055111995931147221000343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20703407997287431480666895 31055111995931147221000343)
              ·
                refine ⟨46582667993896720831500515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31055111995931147221000343 46582667993896720831500515)
                ·
                  refine ⟨69874001990845081247250773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46582667993896720831500515 69874001990845081247250773)
                  ·
                    refine ⟨204708990207553948966555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 69874001990845081247250773 204708990207553948966555)
                    ·
                      rfl

theorem cell23_1196008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1196008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196008 prefixEnd_1196008 := by exact prefixLift 1196008
  have htrace : WordTrace (prefixWord ++ tailWord_1196008) baseStart_1196008 baseEnd_1196008 := by
    simpa [prefixWord, tailWord_1196008, baseEnd_1196008] using wordTrace_append hprefix tailTrace_1196008
  have hstable : (prefixWord ++ tailWord_1196008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196008).length < 2 ^ (prefixWord ++ tailWord_1196008).sum := by decide
  have hdescent : baseEnd_1196008 < baseStart_1196008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196015 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_1196015 : Nat := 118140960795 + 1196015 * 2 ^ 59
def prefixEnd_1196015 : Nat := 4983230072969 + 3 ^ 40 * 1196015 * 2
def baseEnd_1196015 : Nat := 614130564987243319512133

theorem tailTrace_1196015 : CollatzResearch.WordTrace tailWord_1196015 prefixEnd_1196015 614130564987243319512133 := by
  unfold tailWord_1196015
  simp only [CollatzResearch.WordTrace]
  refine ⟨43622250762049392944893499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29081500508032928629928999 43622250762049392944893499)
  ·
    refine ⟨65433376143074089417340249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43622250762049392944893499 65433376143074089417340249)
    ·
      refine ⟨49075032107305567063005187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65433376143074089417340249 49075032107305567063005187)
      ·
        refine ⟨73612548160958350594507781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49075032107305567063005187 73612548160958350594507781)
        ·
          refine ⟨13802352780179690736470209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73612548160958350594507781 13802352780179690736470209)
          ·
            refine ⟨10351764585134768052352657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13802352780179690736470209 10351764585134768052352657)
            ·
              refine ⟨7763823438851076039264493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10351764585134768052352657 7763823438851076039264493)
              ·
                refine ⟨2911433789569153514724185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7763823438851076039264493 2911433789569153514724185)
                ·
                  refine ⟨2183575342176865136043139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2911433789569153514724185 2183575342176865136043139)
                  ·
                    refine ⟨3275363013265297704064709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2183575342176865136043139 3275363013265297704064709)
                    ·
                      refine ⟨614130564987243319512133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3275363013265297704064709 614130564987243319512133)
                      ·
                        rfl

theorem cell23_1196015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_1196015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196015 prefixEnd_1196015 := by exact prefixLift 1196015
  have htrace : WordTrace (prefixWord ++ tailWord_1196015) baseStart_1196015 baseEnd_1196015 := by
    simpa [prefixWord, tailWord_1196015, baseEnd_1196015] using wordTrace_append hprefix tailTrace_1196015
  have hstable : (prefixWord ++ tailWord_1196015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196015).length < 2 ^ (prefixWord ++ tailWord_1196015).sum := by decide
  have hdescent : baseEnd_1196015 < baseStart_1196015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196105 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_1196105 : Nat := 118140960795 + 1196105 * 2 ^ 59
def prefixEnd_1196105 : Nat := 4983230072969 + 3 ^ 40 * 1196105 * 2
def baseEnd_1196105 : Nat := 614176778246147967386719

theorem tailTrace_1196105 : CollatzResearch.WordTrace tailWord_1196105 prefixEnd_1196105 614176778246147967386719 := by
  unfold tailWord_1196105
  simp only [CollatzResearch.WordTrace]
  refine ⟨43625533331723338315669769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29083688887815558877113179 43625533331723338315669769)
  ·
    refine ⟨32719149998792503736752327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43625533331723338315669769 32719149998792503736752327)
    ·
      refine ⟨49078724998188755605128491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32719149998792503736752327 49078724998188755605128491)
      ·
        refine ⟨73618087497283133407692737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49078724998188755605128491 73618087497283133407692737)
        ·
          refine ⟨55213565622962350055769553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73618087497283133407692737 55213565622962350055769553)
          ·
            refine ⟨41410174217221762541827165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55213565622962350055769553 41410174217221762541827165)
            ·
              refine ⟨15528815331458160953185187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41410174217221762541827165 15528815331458160953185187)
              ·
                refine ⟨23293222997187241429777781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15528815331458160953185187 23293222997187241429777781)
                ·
                  refine ⟨2183739655986303884041667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23293222997187241429777781 2183739655986303884041667)
                  ·
                    refine ⟨3275609483979455826062501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2183739655986303884041667 3275609483979455826062501)
                    ·
                      refine ⟨614176778246147967386719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3275609483979455826062501 614176778246147967386719)
                      ·
                        rfl

theorem cell23_1196105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_1196105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196105 prefixEnd_1196105 := by exact prefixLift 1196105
  have htrace : WordTrace (prefixWord ++ tailWord_1196105) baseStart_1196105 baseEnd_1196105 := by
    simpa [prefixWord, tailWord_1196105, baseEnd_1196105] using wordTrace_append hprefix tailTrace_1196105
  have hstable : (prefixWord ++ tailWord_1196105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196105).length < 2 ^ (prefixWord ++ tailWord_1196105).sum := by decide
  have hdescent : baseEnd_1196105 < baseStart_1196105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196109 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_1196109 : Nat := 118140960795 + 1196109 * 2 ^ 59
def prefixEnd_1196109 : Nat := 4983230072969 + 3 ^ 40 * 1196109 * 2
def baseEnd_1196109 : Nat := 614178832168765951736701

theorem tailTrace_1196109 : CollatzResearch.WordTrace tailWord_1196109 prefixEnd_1196109 614178832168765951736701 := by
  unfold tailWord_1196109
  simp only [CollatzResearch.WordTrace]
  refine ⟨43625679223708846998815381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29083786149139231332543587 43625679223708846998815381)
  ·
    refine ⟨2044953713611352203069471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43625679223708846998815381 2044953713611352203069471)
    ·
      refine ⟨3067430570417028304604207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2044953713611352203069471 3067430570417028304604207)
      ·
        refine ⟨4601145855625542456906311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3067430570417028304604207 4601145855625542456906311)
        ·
          refine ⟨6901718783438313685359467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4601145855625542456906311 6901718783438313685359467)
          ·
            refine ⟨10352578175157470528039201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6901718783438313685359467 10352578175157470528039201)
            ·
              refine ⟨7764433631368102896029401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10352578175157470528039201 7764433631368102896029401)
              ·
                refine ⟨5823325223526077172022051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7764433631368102896029401 5823325223526077172022051)
                ·
                  refine ⟨8734987835289115758033077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5823325223526077172022051 8734987835289115758033077)
                  ·
                    refine ⟨818905109558354602315601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8734987835289115758033077 818905109558354602315601)
                    ·
                      refine ⟨614178832168765951736701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818905109558354602315601 614178832168765951736701)
                      ·
                        rfl

theorem cell23_1196109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_1196109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196109 prefixEnd_1196109 := by exact prefixLift 1196109
  have htrace : WordTrace (prefixWord ++ tailWord_1196109) baseStart_1196109 baseEnd_1196109 := by
    simpa [prefixWord, tailWord_1196109, baseEnd_1196109] using wordTrace_append hprefix tailTrace_1196109
  have hstable : (prefixWord ++ tailWord_1196109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196109).length < 2 ^ (prefixWord ++ tailWord_1196109).sum := by decide
  have hdescent : baseEnd_1196109 < baseStart_1196109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196122 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_1196122 : Nat := 118140960795 + 1196122 * 2 ^ 59
def prefixEnd_1196122 : Nat := 4983230072969 + 3 ^ 40 * 1196122 * 2
def baseEnd_1196122 : Nat := 614185507417274400874141

theorem tailTrace_1196122 : CollatzResearch.WordTrace tailWord_1196122 prefixEnd_1196122 614185507417274400874141 := by
  unfold tailWord_1196122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906538343165437554759655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29084102248441166812692413 10906538343165437554759655)
  ·
    refine ⟨16359807514748156332139483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10906538343165437554759655 16359807514748156332139483)
    ·
      refine ⟨24539711272122234498209225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16359807514748156332139483 24539711272122234498209225)
      ·
        refine ⟨18404783454091675873656919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24539711272122234498209225 18404783454091675873656919)
        ·
          refine ⟨27607175181137513810485379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18404783454091675873656919 27607175181137513810485379)
          ·
            refine ⟨41410762771706270715728069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27607175181137513810485379 41410762771706270715728069)
            ·
              refine ⟨7764518019694925759199013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41410762771706270715728069 7764518019694925759199013)
              ·
                refine ⟨1455847128692798579849815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7764518019694925759199013 1455847128692798579849815)
                ·
                  refine ⟨2183770693039197869774723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455847128692798579849815 2183770693039197869774723)
                  ·
                    refine ⟨3275656039558796804662085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2183770693039197869774723 3275656039558796804662085)
                    ·
                      refine ⟨614185507417274400874141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3275656039558796804662085 614185507417274400874141)
                      ·
                        rfl

theorem cell23_1196122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_1196122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196122 prefixEnd_1196122 := by exact prefixLift 1196122
  have htrace : WordTrace (prefixWord ++ tailWord_1196122) baseStart_1196122 baseEnd_1196122 := by
    simpa [prefixWord, tailWord_1196122, baseEnd_1196122] using wordTrace_append hprefix tailTrace_1196122
  have hstable : (prefixWord ++ tailWord_1196122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196122).length < 2 ^ (prefixWord ++ tailWord_1196122).sum := by decide
  have hdescent : baseEnd_1196122 < baseStart_1196122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196142 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1196142 : Nat := 118140960795 + 1196142 * 2 ^ 59
def prefixEnd_1196142 : Nat := 4983230072969 + 3 ^ 40 * 1196142 * 2
def baseEnd_1196142 : Nat := 614195777030364322624049

theorem tailTrace_1196142 : CollatzResearch.WordTrace tailWord_1196142 prefixEnd_1196142 614195777030364322624049 := by
  unfold tailWord_1196142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453360354073661704345835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29084588555059529089844453 5453360354073661704345835)
  ·
    refine ⟨8180040531110492556518753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5453360354073661704345835 8180040531110492556518753)
    ·
      refine ⟨6135030398332869417389065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8180040531110492556518753 6135030398332869417389065)
      ·
        refine ⟨4601272798749652063041799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6135030398332869417389065 4601272798749652063041799)
        ·
          refine ⟨6901909198124478094562699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4601272798749652063041799 6901909198124478094562699)
          ·
            refine ⟨10352863797186717141844049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6901909198124478094562699 10352863797186717141844049)
            ·
              refine ⟨7764647847890037856383037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10352863797186717141844049 7764647847890037856383037)
              ·
                refine ⟨2911742942958764196143639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7764647847890037856383037 2911742942958764196143639)
                ·
                  refine ⟨4367614414438146294215459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2911742942958764196143639 4367614414438146294215459)
                  ·
                    refine ⟨6551421621657219441323189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4367614414438146294215459 6551421621657219441323189)
                    ·
                      refine ⟨614195777030364322624049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6551421621657219441323189 614195777030364322624049)
                      ·
                        rfl

theorem cell23_1196142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1196142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196142 prefixEnd_1196142 := by exact prefixLift 1196142
  have htrace : WordTrace (prefixWord ++ tailWord_1196142) baseStart_1196142 baseEnd_1196142 := by
    simpa [prefixWord, tailWord_1196142, baseEnd_1196142] using wordTrace_append hprefix tailTrace_1196142
  have hstable : (prefixWord ++ tailWord_1196142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196142).length < 2 ^ (prefixWord ++ tailWord_1196142).sum := by decide
  have hdescent : baseEnd_1196142 < baseStart_1196142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196155 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 3]
def baseStart_1196155 : Nat := 118140960795 + 1196155 * 2 ^ 59
def prefixEnd_1196155 : Nat := 4983230072969 + 3 ^ 40 * 1196155 * 2
def baseEnd_1196155 : Nat := 614202452278872771761489

theorem tailTrace_1196155 : CollatzResearch.WordTrace tailWord_1196155 prefixEnd_1196155 614202452278872771761489 := by
  unfold tailWord_1196155
  simp only [CollatzResearch.WordTrace]
  refine ⟨43627356981542196854989919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29084904654361464569993279 43627356981542196854989919)
  ·
    refine ⟨65441035472313295282484879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43627356981542196854989919 65441035472313295282484879)
    ·
      refine ⟨98161553208469942923727319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65441035472313295282484879 98161553208469942923727319)
      ·
        refine ⟨147242329812704914385590979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98161553208469942923727319 147242329812704914385590979)
        ·
          refine ⟨220863494719057371578386469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147242329812704914385590979 220863494719057371578386469)
          ·
            refine ⟨41411905259823257170947463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220863494719057371578386469 41411905259823257170947463)
            ·
              refine ⟨62117857889734885756421195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41411905259823257170947463 62117857889734885756421195)
              ·
                refine ⟨93176786834602328634631793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62117857889734885756421195 93176786834602328634631793)
                ·
                  refine ⟨69882590125951746475973845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93176786834602328634631793 69882590125951746475973845)
                  ·
                    refine ⟨1637873206076994058030637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 69882590125951746475973845 1637873206076994058030637)
                    ·
                      refine ⟨614202452278872771761489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1637873206076994058030637 614202452278872771761489)
                      ·
                        rfl

theorem cell23_1196155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 3].length) (baseStart_1196155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196155 prefixEnd_1196155 := by exact prefixLift 1196155
  have htrace : WordTrace (prefixWord ++ tailWord_1196155) baseStart_1196155 baseEnd_1196155 := by
    simpa [prefixWord, tailWord_1196155, baseEnd_1196155] using wordTrace_append hprefix tailTrace_1196155
  have hstable : (prefixWord ++ tailWord_1196155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196155).length < 2 ^ (prefixWord ++ tailWord_1196155).sum := by decide
  have hdescent : baseEnd_1196155 < baseStart_1196155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196156 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_1196156 : Nat := 118140960795 + 1196156 * 2 ^ 59
def prefixEnd_1196156 : Nat := 4983230072969 + 3 ^ 40 * 1196156 * 2
def baseEnd_1196156 : Nat := 614202965759527267848985

theorem tailTrace_1196156 : CollatzResearch.WordTrace tailWord_1196156 prefixEnd_1196156 614202965759527267848985 := by
  unfold tailWord_1196156
  simp only [CollatzResearch.WordTrace]
  refine ⟨21813696727269287012888161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29084928969692382683850881 21813696727269287012888161)
  ·
    refine ⟨16360272545451965259666121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21813696727269287012888161 16360272545451965259666121)
    ·
      refine ⟨12270204409088973944749591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16360272545451965259666121 12270204409088973944749591)
      ·
        refine ⟨18405306613633460917124387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12270204409088973944749591 18405306613633460917124387)
        ·
          refine ⟨27607959920450191375686581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18405306613633460917124387 27607959920450191375686581)
          ·
            refine ⟨2588246242542205441470617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27607959920450191375686581 2588246242542205441470617)
            ·
              refine ⟨1941184681906654081102963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588246242542205441470617 1941184681906654081102963)
              ·
                refine ⟨2911777022859981121654445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941184681906654081102963 2911777022859981121654445)
                ·
                  refine ⟨1091916383572492920620417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2911777022859981121654445 1091916383572492920620417)
                  ·
                    refine ⟨818937287679369690465313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1091916383572492920620417 818937287679369690465313)
                    ·
                      refine ⟨614202965759527267848985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 818937287679369690465313 614202965759527267848985)
                      ·
                        rfl

theorem cell23_1196156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_1196156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196156 prefixEnd_1196156 := by exact prefixLift 1196156
  have htrace : WordTrace (prefixWord ++ tailWord_1196156) baseStart_1196156 baseEnd_1196156 := by
    simpa [prefixWord, tailWord_1196156, baseEnd_1196156] using wordTrace_append hprefix tailTrace_1196156
  have hstable : (prefixWord ++ tailWord_1196156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196156).length < 2 ^ (prefixWord ++ tailWord_1196156).sum := by decide
  have hdescent : baseEnd_1196156 < baseStart_1196156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196189 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1196189 : Nat := 118140960795 + 1196189 * 2 ^ 59
def prefixEnd_1196189 : Nat := 4983230072969 + 3 ^ 40 * 1196189 * 2
def baseEnd_1196189 : Nat := 614219910621125638736333

theorem tailTrace_1196189 : CollatzResearch.WordTrace tailWord_1196189 prefixEnd_1196189 614219910621125638736333 := by
  unfold tailWord_1196189
  simp only [CollatzResearch.WordTrace]
  refine ⟨43628597063419020661727621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29085731375612680441151747 43628597063419020661727621)
  ·
    refine ⟨8180361949391066374073929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43628597063419020661727621 8180361949391066374073929)
    ·
      refine ⟨6135271462043299780555447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8180361949391066374073929 6135271462043299780555447)
      ·
        refine ⟨9202907193064949670833171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6135271462043299780555447 9202907193064949670833171)
        ·
          refine ⟨13804360789597424506249757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9202907193064949670833171 13804360789597424506249757)
          ·
            refine ⟨5176635296099034189843659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13804360789597424506249757 5176635296099034189843659)
            ·
              refine ⟨7764952944148551284765489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5176635296099034189843659 7764952944148551284765489)
              ·
                refine ⟨5823714708111413463574117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7764952944148551284765489 5823714708111413463574117)
                ·
                  refine ⟨1091946507770890024420147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5823714708111413463574117 1091946507770890024420147)
                  ·
                    refine ⟨1637919761656335036630221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1091946507770890024420147 1637919761656335036630221)
                    ·
                      refine ⟨614219910621125638736333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1637919761656335036630221 614219910621125638736333)
                      ·
                        rfl

theorem cell23_1196189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1196189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196189 prefixEnd_1196189 := by exact prefixLift 1196189
  have htrace : WordTrace (prefixWord ++ tailWord_1196189) baseStart_1196189 baseEnd_1196189 := by
    simpa [prefixWord, tailWord_1196189, baseEnd_1196189] using wordTrace_append hprefix tailTrace_1196189
  have hstable : (prefixWord ++ tailWord_1196189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196189).length < 2 ^ (prefixWord ++ tailWord_1196189).sum := by decide
  have hdescent : baseEnd_1196189 < baseStart_1196189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196195 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1196195 : Nat := 118140960795 + 1196195 * 2 ^ 59
def prefixEnd_1196195 : Nat := 4983230072969 + 3 ^ 40 * 1196195 * 2
def baseEnd_1196195 : Nat := 614222991505052615261305

theorem tailTrace_1196195 : CollatzResearch.WordTrace tailWord_1196195 prefixEnd_1196195 614222991505052615261305 := by
  unfold tailWord_1196195
  simp only [CollatzResearch.WordTrace]
  refine ⟨43628815901397283686446039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29085877267598189124297359 43628815901397283686446039)
  ·
    refine ⟨65443223852095925529669059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43628815901397283686446039 65443223852095925529669059)
    ·
      refine ⟨98164835778143888294503589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65443223852095925529669059 98164835778143888294503589)
      ·
        refine ⟨18405906708401979055219423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98164835778143888294503589 18405906708401979055219423)
        ·
          refine ⟨27608860062602968582829135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18405906708401979055219423 27608860062602968582829135)
          ·
            refine ⟨41413290093904452874243703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27608860062602968582829135 41413290093904452874243703)
            ·
              refine ⟨62119935140856679311365555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41413290093904452874243703 62119935140856679311365555)
              ·
                refine ⟨93179902711285018967048333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62119935140856679311365555 93179902711285018967048333)
                ·
                  refine ⟨34942463516731882112643125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93179902711285018967048333 34942463516731882112643125)
                  ·
                    refine ⟨3275855954693613948060293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34942463516731882112643125 3275855954693613948060293)
                    ·
                      refine ⟨614222991505052615261305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3275855954693613948060293 614222991505052615261305)
                      ·
                        rfl

theorem cell23_1196195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1196195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196195 prefixEnd_1196195 := by exact prefixLift 1196195
  have htrace : WordTrace (prefixWord ++ tailWord_1196195) baseStart_1196195 baseEnd_1196195 := by
    simpa [prefixWord, tailWord_1196195, baseEnd_1196195] using wordTrace_append hprefix tailTrace_1196195
  have hstable : (prefixWord ++ tailWord_1196195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196195).length < 2 ^ (prefixWord ++ tailWord_1196195).sum := by decide
  have hdescent : baseEnd_1196195 < baseStart_1196195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196235 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 9]
def baseStart_1196235 : Nat := 118140960795 + 1196235 * 2 ^ 59
def prefixEnd_1196235 : Nat := 4983230072969 + 3 ^ 40 * 1196235 * 2
def baseEnd_1196235 : Nat := 68249281192359162084569

theorem tailTrace_1196235 : CollatzResearch.WordTrace tailWord_1196235 prefixEnd_1196235 68249281192359162084569 := by
  unfold tailWord_1196235
  simp only [CollatzResearch.WordTrace]
  refine ⟨43630274821252370517902159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29086849880834913678601439 43630274821252370517902159)
  ·
    refine ⟨65445412231878555776853239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43630274821252370517902159 65445412231878555776853239)
    ·
      refine ⟨98168118347817833665279859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65445412231878555776853239 98168118347817833665279859)
      ·
        refine ⟨147252177521726750497919789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98168118347817833665279859 147252177521726750497919789)
        ·
          refine ⟨55219566570647531436719921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147252177521726750497919789 55219566570647531436719921)
          ·
            refine ⟨41414674927985648577539941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55219566570647531436719921 41414674927985648577539941)
            ·
              refine ⟨7765251548997309108288739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41414674927985648577539941 7765251548997309108288739)
              ·
                refine ⟨11647877323495963662433109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7765251548997309108288739 11647877323495963662433109)
                ·
                  refine ⟨68249281192359162084569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11647877323495963662433109 68249281192359162084569)
                  ·
                    rfl

theorem cell23_1196235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 9].length) (baseStart_1196235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196235 prefixEnd_1196235 := by exact prefixLift 1196235
  have htrace : WordTrace (prefixWord ++ tailWord_1196235) baseStart_1196235 baseEnd_1196235 := by
    simpa [prefixWord, tailWord_1196235, baseEnd_1196235] using wordTrace_append hprefix tailTrace_1196235
  have hstable : (prefixWord ++ tailWord_1196235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196235).length < 2 ^ (prefixWord ++ tailWord_1196235).sum := by decide
  have hdescent : baseEnd_1196235 < baseStart_1196235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196258 : List Nat := [3, 3, 4, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1196258 : Nat := 118140960795 + 1196258 * 2 ^ 59
def prefixEnd_1196258 : Nat := 4983230072969 + 3 ^ 40 * 1196258 * 2
def baseEnd_1196258 : Nat := 614255340786285868773517

theorem tailTrace_1196258 : CollatzResearch.WordTrace tailWord_1196258 prefixEnd_1196258 614255340786285868773517 := by
  unfold tailWord_1196258
  simp only [CollatzResearch.WordTrace]
  refine ⟨10907778425042261361497357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29087409133446030297326285 10907778425042261361497357)
  ·
    refine ⟨4090416909390848010561509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10907778425042261361497357 4090416909390848010561509)
    ·
      refine ⟨766953170510784001980283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4090416909390848010561509 766953170510784001980283)
      ·
        refine ⟨1150429755766176002970425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766953170510784001980283 1150429755766176002970425)
        ·
          refine ⟨862822316824632002227819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150429755766176002970425 862822316824632002227819)
          ·
            refine ⟨1294233475236948003341729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862822316824632002227819 1294233475236948003341729)
            ·
              refine ⟨970675106427711002506297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294233475236948003341729 970675106427711002506297)
              ·
                refine ⟨728006329820783251879723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 970675106427711002506297 728006329820783251879723)
                ·
                  refine ⟨1092009494731174877819585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728006329820783251879723 1092009494731174877819585)
                  ·
                    refine ⟨819007121048381158364689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092009494731174877819585 819007121048381158364689)
                    ·
                      refine ⟨614255340786285868773517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819007121048381158364689 614255340786285868773517)
                      ·
                        rfl

theorem cell23_1196258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1196258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196258 prefixEnd_1196258 := by exact prefixLift 1196258
  have htrace : WordTrace (prefixWord ++ tailWord_1196258) baseStart_1196258 baseEnd_1196258 := by
    simpa [prefixWord, tailWord_1196258, baseEnd_1196258] using wordTrace_append hprefix tailTrace_1196258
  have hstable : (prefixWord ++ tailWord_1196258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196258).length < 2 ^ (prefixWord ++ tailWord_1196258).sum := by decide
  have hdescent : baseEnd_1196258 < baseStart_1196258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196263 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1196263 : Nat := 118140960795 + 1196263 * 2 ^ 59
def prefixEnd_1196263 : Nat := 4983230072969 + 3 ^ 40 * 1196263 * 2
def baseEnd_1196263 : Nat := 614257908189558349210993

theorem tailTrace_1196263 : CollatzResearch.WordTrace tailWord_1196263 prefixEnd_1196263 614257908189558349210993 := by
  unfold tailWord_1196263
  simp only [CollatzResearch.WordTrace]
  refine ⟨43631296065150931299921443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29087530710100620866614295 43631296065150931299921443)
  ·
    refine ⟨65446944097726396949882165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43631296065150931299921443 65446944097726396949882165)
    ·
      refine ⟨6135651009161849714051453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65446944097726396949882165 6135651009161849714051453)
      ·
        refine ⟨2300869128435693642769295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6135651009161849714051453 2300869128435693642769295)
        ·
          refine ⟨3451303692653540464153943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300869128435693642769295 3451303692653540464153943)
          ·
            refine ⟨5176955538980310696230915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451303692653540464153943 5176955538980310696230915)
            ·
              refine ⟨7765433308470466044346373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5176955538980310696230915 7765433308470466044346373)
              ·
                refine ⟨1456018745338212383314945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7765433308470466044346373 1456018745338212383314945)
                ·
                  refine ⟨1092014059003659287486209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1456018745338212383314945 1092014059003659287486209)
                  ·
                    refine ⟨819010544252744465614657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092014059003659287486209 819010544252744465614657)
                    ·
                      refine ⟨614257908189558349210993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819010544252744465614657 614257908189558349210993)
                      ·
                        rfl

theorem cell23_1196263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1196263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196263 prefixEnd_1196263 := by exact prefixLift 1196263
  have htrace : WordTrace (prefixWord ++ tailWord_1196263) baseStart_1196263 baseEnd_1196263 := by
    simpa [prefixWord, tailWord_1196263, baseEnd_1196263] using wordTrace_append hprefix tailTrace_1196263
  have hstable : (prefixWord ++ tailWord_1196263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196263).length < 2 ^ (prefixWord ++ tailWord_1196263).sum := by decide
  have hdescent : baseEnd_1196263 < baseStart_1196263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196289 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_1196289 : Nat := 118140960795 + 1196289 * 2 ^ 59
def prefixEnd_1196289 : Nat := 4983230072969 + 3 ^ 40 * 1196289 * 2
def baseEnd_1196289 : Nat := 614271258686575247485873

theorem tailTrace_1196289 : CollatzResearch.WordTrace tailWord_1196289 prefixEnd_1196289 614271258686575247485873 := by
  unfold tailWord_1196289
  simp only [CollatzResearch.WordTrace]
  refine ⟨43632244363056737740367921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29088162908704491826911947 43632244363056737740367921)
  ·
    refine ⟨32724183272292553305275941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43632244363056737740367921 32724183272292553305275941)
    ·
      refine ⟨6135784363554853744739239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32724183272292553305275941 6135784363554853744739239)
      ·
        refine ⟨9203676545332280617108859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6135784363554853744739239 9203676545332280617108859)
        ·
          refine ⟨13805514817998420925663289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9203676545332280617108859 13805514817998420925663289)
          ·
            refine ⟨10354136113498815694247467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13805514817998420925663289 10354136113498815694247467)
            ·
              refine ⟨15531204170248223541371201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10354136113498815694247467 15531204170248223541371201)
              ·
                refine ⟨11648403127686167656028401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15531204170248223541371201 11648403127686167656028401)
                ·
                  refine ⟨8736302345764625742021301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11648403127686167656028401 8736302345764625742021301)
                  ·
                    refine ⟨819028344915433663314497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8736302345764625742021301 819028344915433663314497)
                    ·
                      refine ⟨614271258686575247485873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819028344915433663314497 614271258686575247485873)
                      ·
                        rfl

theorem cell23_1196289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_1196289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196289 prefixEnd_1196289 := by exact prefixLift 1196289
  have htrace : WordTrace (prefixWord ++ tailWord_1196289) baseStart_1196289 baseEnd_1196289 := by
    simpa [prefixWord, tailWord_1196289, baseEnd_1196289] using wordTrace_append hprefix tailTrace_1196289
  have hstable : (prefixWord ++ tailWord_1196289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196289).length < 2 ^ (prefixWord ++ tailWord_1196289).sum := by decide
  have hdescent : baseEnd_1196289 < baseStart_1196289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196380 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1196380 : Nat := 118140960795 + 1196380 * 2 ^ 59
def prefixEnd_1196380 : Nat := 4983230072969 + 3 ^ 40 * 1196380 * 2
def baseEnd_1196380 : Nat := 204772661808711463815985

theorem tailTrace_1196380 : CollatzResearch.WordTrace tailWord_1196380 prefixEnd_1196380 204772661808711463815985 := by
  unfold tailWord_1196380
  simp only [CollatzResearch.WordTrace]
  refine ⟨21817781702863530140965297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29090375603818040187953729 21817781702863530140965297)
  ·
    refine ⟨16363336277147647605723973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21817781702863530140965297 16363336277147647605723973)
    ·
      refine ⟨3068125551965183926073245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16363336277147647605723973 3068125551965183926073245)
      ·
        refine ⟨1150547081986943972277467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3068125551965183926073245 1150547081986943972277467)
        ·
          refine ⟨1725820622980415958416201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150547081986943972277467 1725820622980415958416201)
          ·
            refine ⟨1294365467235311968812151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1725820622980415958416201 1294365467235311968812151)
            ·
              refine ⟨1941548200852967953218227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294365467235311968812151 1941548200852967953218227)
              ·
                refine ⟨2912322301279451929827341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941548200852967953218227 2912322301279451929827341)
                ·
                  refine ⟨1092120862979794473685253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2912322301279451929827341 1092120862979794473685253)
                  ·
                    refine ⟨204772661808711463815985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1092120862979794473685253 204772661808711463815985)
                    ·
                      rfl

theorem cell23_1196380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1196380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196380 prefixEnd_1196380 := by exact prefixLift 1196380
  have htrace : WordTrace (prefixWord ++ tailWord_1196380) baseStart_1196380 baseEnd_1196380 := by
    simpa [prefixWord, tailWord_1196380, baseEnd_1196380] using wordTrace_append hprefix tailTrace_1196380
  have hstable : (prefixWord ++ tailWord_1196380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196380).length < 2 ^ (prefixWord ++ tailWord_1196380).sum := by decide
  have hdescent : baseEnd_1196380 < baseStart_1196380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196413 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 2, 3, 2]
def baseStart_1196413 : Nat := 118140960795 + 1196413 * 2 ^ 59
def prefixEnd_1196413 : Nat := 4983230072969 + 3 ^ 40 * 1196413 * 2
def baseEnd_1196413 : Nat := 614334930287732762335303

theorem tailTrace_1196413 : CollatzResearch.WordTrace tailWord_1196413 prefixEnd_1196413 614334930287732762335303 := by
  unfold tailWord_1196413
  simp only [CollatzResearch.WordTrace]
  refine ⟨43636767014607506917881893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29091178009738337945254595 43636767014607506917881893)
  ·
    refine ⟨8181893815238907547102855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43636767014607506917881893 8181893815238907547102855)
    ·
      refine ⟨12272840722858361320654283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8181893815238907547102855 12272840722858361320654283)
      ·
        refine ⟨18409261084287541980981425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12272840722858361320654283 18409261084287541980981425)
        ·
          refine ⟨13806945813215656485736069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18409261084287541980981425 13806945813215656485736069)
          ·
            refine ⟨2588802339977935591075513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13806945813215656485736069 2588802339977935591075513)
            ·
              refine ⟨1941601754983451693306635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588802339977935591075513 1941601754983451693306635)
              ·
                refine ⟨2912402632475177539959953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941601754983451693306635 2912402632475177539959953)
                ·
                  refine ⟨2184301974356383154969965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912402632475177539959953 2184301974356383154969965)
                  ·
                    refine ⟨819113240383643683113737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184301974356383154969965 819113240383643683113737)
                    ·
                      refine ⟨614334930287732762335303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819113240383643683113737 614334930287732762335303)
                      ·
                        rfl

theorem cell23_1196413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_1196413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196413 prefixEnd_1196413 := by exact prefixLift 1196413
  have htrace : WordTrace (prefixWord ++ tailWord_1196413) baseStart_1196413 baseEnd_1196413 := by
    simpa [prefixWord, tailWord_1196413, baseEnd_1196413] using wordTrace_append hprefix tailTrace_1196413
  have hstable : (prefixWord ++ tailWord_1196413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196413).length < 2 ^ (prefixWord ++ tailWord_1196413).sum := by decide
  have hdescent : baseEnd_1196413 < baseStart_1196413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196477 : List Nat := [1, 4, 1, 2, 2, 3, 2, 3, 1, 2, 2]
def baseStart_1196477 : Nat := 118140960795 + 1196477 * 2 ^ 59
def prefixEnd_1196477 : Nat := 4983230072969 + 3 ^ 40 * 1196477 * 2
def baseEnd_1196477 : Nat := 614367793049620511935009

theorem tailTrace_1196477 : CollatzResearch.WordTrace tailWord_1196477 prefixEnd_1196477 614367793049620511935009 := by
  unfold tailWord_1196477
  simp only [CollatzResearch.WordTrace]
  refine ⟨43639101286375645848211685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29092734190917097232141123 43639101286375645848211685)
  ·
    refine ⟨8182331491195433596539691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43639101286375645848211685 8182331491195433596539691)
    ·
      refine ⟨12273497236793150394809537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8182331491195433596539691 12273497236793150394809537)
      ·
        refine ⟨9205122927594862796107153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12273497236793150394809537 9205122927594862796107153)
        ·
          refine ⟨6903842195696147097080365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9205122927594862796107153 6903842195696147097080365)
          ·
            refine ⟨2588940823386055161405137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6903842195696147097080365 2588940823386055161405137)
            ·
              refine ⟨1941705617539541371053853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588940823386055161405137 1941705617539541371053853)
              ·
                refine ⟨728139606577328014145195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1941705617539541371053853 728139606577328014145195)
                ·
                  refine ⟨1092209409865992021217793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728139606577328014145195 1092209409865992021217793)
                  ·
                    refine ⟨819157057399494015913345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092209409865992021217793 819157057399494015913345)
                    ·
                      refine ⟨614367793049620511935009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819157057399494015913345 614367793049620511935009)
                      ·
                        rfl

theorem cell23_1196477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_1196477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196477 prefixEnd_1196477 := by exact prefixLift 1196477
  have htrace : WordTrace (prefixWord ++ tailWord_1196477) baseStart_1196477 baseEnd_1196477 := by
    simpa [prefixWord, tailWord_1196477, baseEnd_1196477] using wordTrace_append hprefix tailTrace_1196477
  have hstable : (prefixWord ++ tailWord_1196477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196477).length < 2 ^ (prefixWord ++ tailWord_1196477).sum := by decide
  have hdescent : baseEnd_1196477 < baseStart_1196477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196520 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_1196520 : Nat := 118140960795 + 1196520 * 2 ^ 59
def prefixEnd_1196520 : Nat := 4983230072969 + 3 ^ 40 * 1196520 * 2
def baseEnd_1196520 : Nat := 614389872717763843697311

theorem tailTrace_1196520 : CollatzResearch.WordTrace tailWord_1196520 prefixEnd_1196520 614389872717763843697311 := by
  unfold tailWord_1196520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820334812609932096013507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29093779750146576128018009 21820334812609932096013507)
  ·
    refine ⟨32730502218914898144020261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21820334812609932096013507 32730502218914898144020261)
    ·
      refine ⟨6136969166046543402003799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32730502218914898144020261 6136969166046543402003799)
      ·
        refine ⟨9205453749069815103005699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6136969166046543402003799 9205453749069815103005699)
        ·
          refine ⟨13808180623604722654508549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9205453749069815103005699 13808180623604722654508549)
          ·
            refine ⟨2589033866925885497720353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13808180623604722654508549 2589033866925885497720353)
            ·
              refine ⟨1941775400194414123290265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2589033866925885497720353 1941775400194414123290265)
              ·
                refine ⟨1456331550145810592467699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1941775400194414123290265 1456331550145810592467699)
                ·
                  refine ⟨2184497325218715888701549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456331550145810592467699 2184497325218715888701549)
                  ·
                    refine ⟨819186496957018458263081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184497325218715888701549 819186496957018458263081)
                    ·
                      refine ⟨614389872717763843697311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819186496957018458263081 614389872717763843697311)
                      ·
                        rfl

theorem cell23_1196520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_1196520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196520 prefixEnd_1196520 := by exact prefixLift 1196520
  have htrace : WordTrace (prefixWord ++ tailWord_1196520) baseStart_1196520 baseEnd_1196520 := by
    simpa [prefixWord, tailWord_1196520, baseEnd_1196520] using wordTrace_append hprefix tailTrace_1196520
  have hstable : (prefixWord ++ tailWord_1196520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196520).length < 2 ^ (prefixWord ++ tailWord_1196520).sum := by decide
  have hdescent : baseEnd_1196520 < baseStart_1196520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196556 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 7]
def baseStart_1196556 : Nat := 118140960795 + 1196556 * 2 ^ 59
def prefixEnd_1196556 : Nat := 4983230072969 + 3 ^ 40 * 1196556 * 2
def baseEnd_1196556 : Nat := 68267595335702855871905

theorem tailTrace_1196556 : CollatzResearch.WordTrace tailWord_1196556 prefixEnd_1196556 68267595335702855871905 := by
  unfold tailWord_1196556
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820991326544721170168761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29094655102059628226891681 21820991326544721170168761)
  ·
    refine ⟨16365743494908540877626571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21820991326544721170168761 16365743494908540877626571)
    ·
      refine ⟨24548615242362811316439857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16365743494908540877626571 24548615242362811316439857)
      ·
        refine ⟨18411461431772108487329893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24548615242362811316439857 18411461431772108487329893)
        ·
          refine ⟨3452149018457270341374355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18411461431772108487329893 3452149018457270341374355)
          ·
            refine ⟨5178223527685905512061533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452149018457270341374355 5178223527685905512061533)
            ·
              refine ⟨1941833822882214567023075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5178223527685905512061533 1941833822882214567023075)
              ·
                refine ⟨2912750734323321850534613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941833822882214567023075 2912750734323321850534613)
                ·
                  refine ⟨68267595335702855871905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2912750734323321850534613 68267595335702855871905)
                  ·
                    rfl

theorem cell23_1196556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_1196556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196556 prefixEnd_1196556 := by exact prefixLift 1196556
  have htrace : WordTrace (prefixWord ++ tailWord_1196556) baseStart_1196556 baseEnd_1196556 := by
    simpa [prefixWord, tailWord_1196556, baseEnd_1196556] using wordTrace_append hprefix tailTrace_1196556
  have hstable : (prefixWord ++ tailWord_1196556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196556).length < 2 ^ (prefixWord ++ tailWord_1196556).sum := by decide
  have hdescent : baseEnd_1196556 < baseStart_1196556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196616 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 7, 4]
def baseStart_1196616 : Nat := 118140960795 + 1196616 * 2 ^ 59
def prefixEnd_1196616 : Nat := 4983230072969 + 3 ^ 40 * 1196616 * 2
def baseEnd_1196616 : Nat := 204813055620198489365623

theorem tailTrace_1196616 : CollatzResearch.WordTrace tailWord_1196616 prefixEnd_1196616 204813055620198489365623 := by
  unfold tailWord_1196616
  simp only [CollatzResearch.WordTrace]
  refine ⟨21822085516436036293760851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29096114021914715058347801 21822085516436036293760851)
  ·
    refine ⟨32733128274654054440641277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21822085516436036293760851 32733128274654054440641277)
    ·
      refine ⟨12274923102995270415240479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32733128274654054440641277 12274923102995270415240479)
      ·
        refine ⟨18412384654492905622860719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12274923102995270415240479 18412384654492905622860719)
        ·
          refine ⟨27618576981739358434291079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18412384654492905622860719 27618576981739358434291079)
          ·
            refine ⟨41427865472609037651436619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27618576981739358434291079 41427865472609037651436619)
            ·
              refine ⟨62141798208913556477154929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41427865472609037651436619 62141798208913556477154929)
              ·
                refine ⟨46606348656685167357866197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62141798208913556477154929 46606348656685167357866197)
                ·
                  refine ⟨1092336296641058609949989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 46606348656685167357866197 1092336296641058609949989)
                  ·
                    refine ⟨204813055620198489365623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1092336296641058609949989 204813055620198489365623)
                    ·
                      rfl

theorem cell23_1196616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_1196616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196616 prefixEnd_1196616 := by exact prefixLift 1196616
  have htrace : WordTrace (prefixWord ++ tailWord_1196616) baseStart_1196616 baseEnd_1196616 := by
    simpa [prefixWord, tailWord_1196616, baseEnd_1196616] using wordTrace_append hprefix tailTrace_1196616
  have hstable : (prefixWord ++ tailWord_1196616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196616).length < 2 ^ (prefixWord ++ tailWord_1196616).sum := by decide
  have hdescent : baseEnd_1196616 < baseStart_1196616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196683 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 6, 3, 2]
def baseStart_1196683 : Nat := 118140960795 + 1196683 * 2 ^ 59
def prefixEnd_1196683 : Nat := 4983230072969 + 3 ^ 40 * 1196683 * 2
def baseEnd_1196683 : Nat := 614473570064446705959061

theorem tailTrace_1196683 : CollatzResearch.WordTrace tailWord_1196683 prefixEnd_1196683 614473570064446705959061 := by
  unfold tailWord_1196683
  simp only [CollatzResearch.WordTrace]
  refine ⟨43646614723629343030210703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29097743149086228686807135 43646614723629343030210703)
  ·
    refine ⟨65469922085444014545316055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43646614723629343030210703 65469922085444014545316055)
    ·
      refine ⟨98204883128166021817974083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65469922085444014545316055 98204883128166021817974083)
      ·
        refine ⟨147307324692249032726961125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98204883128166021817974083 147307324692249032726961125)
        ·
          refine ⟨27620123379796693636305211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147307324692249032726961125 27620123379796693636305211)
          ·
            refine ⟨41430185069695040454457817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27620123379796693636305211 41430185069695040454457817)
            ·
              refine ⟨31072638802271280340843363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41430185069695040454457817 31072638802271280340843363)
              ·
                refine ⟨46608958203406920511265045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31072638802271280340843363 46608958203406920511265045)
                ·
                  refine ⟨2184794915784699398965549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46608958203406920511265045 2184794915784699398965549)
                  ·
                    refine ⟨819298093419262274612081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184794915784699398965549 819298093419262274612081)
                    ·
                      refine ⟨614473570064446705959061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819298093419262274612081 614473570064446705959061)
                      ·
                        rfl

theorem cell23_1196683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 3, 2].length) (baseStart_1196683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196683 prefixEnd_1196683 := by exact prefixLift 1196683
  have htrace : WordTrace (prefixWord ++ tailWord_1196683) baseStart_1196683 baseEnd_1196683 := by
    simpa [prefixWord, tailWord_1196683, baseEnd_1196683] using wordTrace_append hprefix tailTrace_1196683
  have hstable : (prefixWord ++ tailWord_1196683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196683).length < 2 ^ (prefixWord ++ tailWord_1196683).sum := by decide
  have hdescent : baseEnd_1196683 < baseStart_1196683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196700 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_1196700 : Nat := 118140960795 + 1196700 * 2 ^ 59
def prefixEnd_1196700 : Nat := 4983230072969 + 3 ^ 40 * 1196700 * 2
def baseEnd_1196700 : Nat := 614482299235573139446483

theorem tailTrace_1196700 : CollatzResearch.WordTrace tailWord_1196700 prefixEnd_1196700 614482299235573139446483 := by
  unfold tailWord_1196700
  simp only [CollatzResearch.WordTrace]
  refine ⟨21823617382283877466789777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29098156509711836622386369 21823617382283877466789777)
  ·
    refine ⟨16367713036712908100092333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21823617382283877466789777 16367713036712908100092333)
    ·
      refine ⟨6137892388767340537534625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16367713036712908100092333 6137892388767340537534625)
      ·
        refine ⟨4603419291575505403150969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6137892388767340537534625 4603419291575505403150969)
        ·
          refine ⟨3452564468681629052363227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4603419291575505403150969 3452564468681629052363227)
          ·
            refine ⟨5178846703022443578544841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452564468681629052363227 5178846703022443578544841)
            ·
              refine ⟨3884135027266832683908631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5178846703022443578544841 3884135027266832683908631)
              ·
                refine ⟨5826202540900249025862947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884135027266832683908631 5826202540900249025862947)
                ·
                  refine ⟨8739303811350373538794421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5826202540900249025862947 8739303811350373538794421)
                  ·
                    refine ⟨819309732314097519261977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8739303811350373538794421 819309732314097519261977)
                    ·
                      refine ⟨614482299235573139446483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819309732314097519261977 614482299235573139446483)
                      ·
                        rfl

theorem cell23_1196700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_1196700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196700 prefixEnd_1196700 := by exact prefixLift 1196700
  have htrace : WordTrace (prefixWord ++ tailWord_1196700) baseStart_1196700 baseEnd_1196700 := by
    simpa [prefixWord, tailWord_1196700, baseEnd_1196700] using wordTrace_append hprefix tailTrace_1196700
  have hstable : (prefixWord ++ tailWord_1196700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196700).length < 2 ^ (prefixWord ++ tailWord_1196700).sum := by decide
  have hdescent : baseEnd_1196700 < baseStart_1196700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196717 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_1196717 : Nat := 118140960795 + 1196717 * 2 ^ 59
def prefixEnd_1196717 : Nat := 4983230072969 + 3 ^ 40 * 1196717 * 2
def baseEnd_1196717 : Nat := 614491028406699572933905

theorem tailTrace_1196717 : CollatzResearch.WordTrace tailWord_1196717 prefixEnd_1196717 614491028406699572933905 := by
  unfold tailWord_1196717
  simp only [CollatzResearch.WordTrace]
  refine ⟨43647854805506166836948405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29098569870337444557965603 43647854805506166836948405)
  ·
    refine ⟨4091986388016203140963913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43647854805506166836948405 4091986388016203140963913)
    ·
      refine ⟨3068989791012152355722935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4091986388016203140963913 3068989791012152355722935)
      ·
        refine ⟨4603484686518228533584403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068989791012152355722935 4603484686518228533584403)
        ·
          refine ⟨6905227029777342800376605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4603484686518228533584403 6905227029777342800376605)
          ·
            refine ⟨2589460136166503550141227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6905227029777342800376605 2589460136166503550141227)
            ·
              refine ⟨3884190204249755325211841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589460136166503550141227 3884190204249755325211841)
              ·
                refine ⟨2913142653187316493908881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3884190204249755325211841 2913142653187316493908881)
                ·
                  refine ⟨2184856989890487370431661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2913142653187316493908881 2184856989890487370431661)
                  ·
                    refine ⟨819321371208932763911873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2184856989890487370431661 819321371208932763911873)
                    ·
                      refine ⟨614491028406699572933905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819321371208932763911873 614491028406699572933905)
                      ·
                        rfl

theorem cell23_1196717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_1196717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196717 prefixEnd_1196717 := by exact prefixLift 1196717
  have htrace : WordTrace (prefixWord ++ tailWord_1196717) baseStart_1196717 baseEnd_1196717 := by
    simpa [prefixWord, tailWord_1196717, baseEnd_1196717] using wordTrace_append hprefix tailTrace_1196717
  have hstable : (prefixWord ++ tailWord_1196717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196717).length < 2 ^ (prefixWord ++ tailWord_1196717).sum := by decide
  have hdescent : baseEnd_1196717 < baseStart_1196717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196723 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 4, 4]
def baseStart_1196723 : Nat := 118140960795 + 1196723 * 2 ^ 59
def prefixEnd_1196723 : Nat := 4983230072969 + 3 ^ 40 * 1196723 * 2
def baseEnd_1196723 : Nat := 204831369763542183152959

theorem tailTrace_1196723 : CollatzResearch.WordTrace tailWord_1196723 prefixEnd_1196723 204831369763542183152959 := by
  unfold tailWord_1196723
  simp only [CollatzResearch.WordTrace]
  refine ⟨43648073643484429861666823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29098715762322953241111215 43648073643484429861666823)
  ·
    refine ⟨65472110465226644792500235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43648073643484429861666823 65472110465226644792500235)
    ·
      refine ⟨98208165697839967188750353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65472110465226644792500235 98208165697839967188750353)
      ·
        refine ⟨73656124273379975391562765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98208165697839967188750353 73656124273379975391562765)
        ·
          refine ⟨27621046602517490771836037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73656124273379975391562765 27621046602517490771836037)
          ·
            refine ⟨5178946237972029519719257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27621046602517490771836037 5178946237972029519719257)
            ·
              refine ⟨3884209678479022139789443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5178946237972029519719257 3884209678479022139789443)
              ·
                refine ⟨5826314517718533209684165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884209678479022139789443 5826314517718533209684165)
                ·
                  refine ⟨1092433972072224976815781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5826314517718533209684165 1092433972072224976815781)
                  ·
                    refine ⟨204831369763542183152959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1092433972072224976815781 204831369763542183152959)
                    ·
                      rfl

theorem cell23_1196723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 4].length) (baseStart_1196723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196723 prefixEnd_1196723 := by exact prefixLift 1196723
  have htrace : WordTrace (prefixWord ++ tailWord_1196723) baseStart_1196723 baseEnd_1196723 := by
    simpa [prefixWord, tailWord_1196723, baseEnd_1196723] using wordTrace_append hprefix tailTrace_1196723
  have hstable : (prefixWord ++ tailWord_1196723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196723).length < 2 ^ (prefixWord ++ tailWord_1196723).sum := by decide
  have hdescent : baseEnd_1196723 < baseStart_1196723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196733 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_1196733 : Nat := 118140960795 + 1196733 * 2 ^ 59
def prefixEnd_1196733 : Nat := 4983230072969 + 3 ^ 40 * 1196733 * 2
def baseEnd_1196733 : Nat := 614499244097171510333831

theorem tailTrace_1196733 : CollatzResearch.WordTrace tailWord_1196733 prefixEnd_1196733 614499244097171510333831 := by
  unfold tailWord_1196733
  simp only [CollatzResearch.WordTrace]
  refine ⟨43648438373448201569530853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29098958915632134379687235 43648438373448201569530853)
  ·
    refine ⟨8184082195021537794287035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43648438373448201569530853 8184082195021537794287035)
    ·
      refine ⟨12276123292532306691430553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184082195021537794287035 12276123292532306691430553)
      ·
        refine ⟨9207092469399230018572915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12276123292532306691430553 9207092469399230018572915)
        ·
          refine ⟨13810638704098845027859373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9207092469399230018572915 13810638704098845027859373)
          ·
            refine ⟨5178989514037066885447265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13810638704098845027859373 5178989514037066885447265)
            ·
              refine ⟨3884242135527800164085449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5178989514037066885447265 3884242135527800164085449)
              ·
                refine ⟨2913181601645850123064087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3884242135527800164085449 2913181601645850123064087)
                ·
                  refine ⟨4369772402468775184596131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2913181601645850123064087 4369772402468775184596131)
                  ·
                    refine ⟨6554658603703162776894197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4369772402468775184596131 6554658603703162776894197)
                    ·
                      refine ⟨614499244097171510333831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6554658603703162776894197 614499244097171510333831)
                      ·
                        rfl

theorem cell23_1196733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_1196733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196733 prefixEnd_1196733 := by exact prefixLift 1196733
  have htrace : WordTrace (prefixWord ++ tailWord_1196733) baseStart_1196733 baseEnd_1196733 := by
    simpa [prefixWord, tailWord_1196733, baseEnd_1196733] using wordTrace_append hprefix tailTrace_1196733
  have hstable : (prefixWord ++ tailWord_1196733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196733).length < 2 ^ (prefixWord ++ tailWord_1196733).sum := by decide
  have hdescent : baseEnd_1196733 < baseStart_1196733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196736 : List Nat := [2, 1, 1, 2, 4, 2, 1, 10]
def baseStart_1196736 : Nat := 118140960795 + 1196736 * 2 ^ 59
def prefixEnd_1196736 : Nat := 4983230072969 + 3 ^ 40 * 1196736 * 2
def baseEnd_1196736 : Nat := 22759288316264259207271

theorem tailTrace_1196736 : CollatzResearch.WordTrace tailWord_1196736 prefixEnd_1196736 22759288316264259207271 := by
  unfold tailWord_1196736
  simp only [CollatzResearch.WordTrace]
  refine ⟨21824273896218666540945031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29099031861624888721260041 21824273896218666540945031)
  ·
    refine ⟨32736410844327999811417547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21824273896218666540945031 32736410844327999811417547)
    ·
      refine ⟨49104616266491999717126321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32736410844327999811417547 49104616266491999717126321)
      ·
        refine ⟨36828462199868999787844741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49104616266491999717126321 36828462199868999787844741)
        ·
          refine ⟨6905336662475437460220889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36828462199868999787844741 6905336662475437460220889)
          ·
            refine ⟨5179002496856578095165667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6905336662475437460220889 5179002496856578095165667)
            ·
              refine ⟨7768503745284867142748501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5179002496856578095165667 7768503745284867142748501)
              ·
                refine ⟨22759288316264259207271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7768503745284867142748501 22759288316264259207271)
                ·
                  rfl

theorem cell23_1196736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 10].length) (baseStart_1196736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196736 prefixEnd_1196736 := by exact prefixLift 1196736
  have htrace : WordTrace (prefixWord ++ tailWord_1196736) baseStart_1196736 baseEnd_1196736 := by
    simpa [prefixWord, tailWord_1196736, baseEnd_1196736] using wordTrace_append hprefix tailTrace_1196736
  have hstable : (prefixWord ++ tailWord_1196736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196736).length < 2 ^ (prefixWord ++ tailWord_1196736).sum := by decide
  have hdescent : baseEnd_1196736 < baseStart_1196736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196750 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_1196750 : Nat := 118140960795 + 1196750 * 2 ^ 59
def prefixEnd_1196750 : Nat := 4983230072969 + 3 ^ 40 * 1196750 * 2
def baseEnd_1196750 : Nat := 614507973268297943821253

theorem tailTrace_1196750 : CollatzResearch.WordTrace tailWord_1196750 prefixEnd_1196750 614507973268297943821253 := by
  unfold tailWord_1196750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456132301798326684112463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29099372276257742315266469 5456132301798326684112463)
  ·
    refine ⟨8184198452697490026168695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5456132301798326684112463 8184198452697490026168695)
    ·
      refine ⟨12276297679046235039253043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184198452697490026168695 12276297679046235039253043)
      ·
        refine ⟨18414446518569352558879565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12276297679046235039253043 18414446518569352558879565)
        ·
          refine ⟨6905417444463507209579837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18414446518569352558879565 6905417444463507209579837)
          ·
            refine ⟨2589531541673815203592439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6905417444463507209579837 2589531541673815203592439)
            ·
              refine ⟨3884297312510722805388659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589531541673815203592439 3884297312510722805388659)
              ·
                refine ⟨5826445968766084208082989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884297312510722805388659 5826445968766084208082989)
                ·
                  refine ⟨2184917238287281578031121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5826445968766084208082989 2184917238287281578031121)
                  ·
                    refine ⟨1638687928715461183523341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2184917238287281578031121 1638687928715461183523341)
                    ·
                      refine ⟨614507973268297943821253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1638687928715461183523341 614507973268297943821253)
                      ·
                        rfl

theorem cell23_1196750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_1196750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196750 prefixEnd_1196750 := by exact prefixLift 1196750
  have htrace : WordTrace (prefixWord ++ tailWord_1196750) baseStart_1196750 baseEnd_1196750 := by
    simpa [prefixWord, tailWord_1196750, baseEnd_1196750] using wordTrace_append hprefix tailTrace_1196750
  have hstable : (prefixWord ++ tailWord_1196750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196750).length < 2 ^ (prefixWord ++ tailWord_1196750).sum := by decide
  have hdescent : baseEnd_1196750 < baseStart_1196750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196764 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1196764 : Nat := 118140960795 + 1196764 * 2 ^ 59
def prefixEnd_1196764 : Nat := 4983230072969 + 3 ^ 40 * 1196764 * 2
def baseEnd_1196764 : Nat := 614515161997460889046189

theorem tailTrace_1196764 : CollatzResearch.WordTrace tailWord_1196764 prefixEnd_1196764 614515161997460889046189 := by
  unfold tailWord_1196764
  simp only [CollatzResearch.WordTrace]
  refine ⟨21824784518167946931954673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29099712690890595909272897 21824784518167946931954673)
  ·
    refine ⟨16368588388625960198966005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21824784518167946931954673 16368588388625960198966005)
    ·
      refine ⟨1534555161433683768653063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16368588388625960198966005 1534555161433683768653063)
      ·
        refine ⟨2301832742150525652979595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534555161433683768653063 2301832742150525652979595)
        ·
          refine ⟨3452749113225788479469393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301832742150525652979595 3452749113225788479469393)
          ·
            refine ⟨2589561834919341359602045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3452749113225788479469393 2589561834919341359602045)
            ·
              refine ⟨971085688094753009850767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2589561834919341359602045 971085688094753009850767)
              ·
                refine ⟨1456628532142129514776151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971085688094753009850767 1456628532142129514776151)
                ·
                  refine ⟨2184942798213194272164227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456628532142129514776151 2184942798213194272164227)
                  ·
                    refine ⟨3277414197319791408246341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184942798213194272164227 3277414197319791408246341)
                    ·
                      refine ⟨614515161997460889046189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3277414197319791408246341 614515161997460889046189)
                      ·
                        rfl

theorem cell23_1196764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1196764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196764 prefixEnd_1196764 := by exact prefixLift 1196764
  have htrace : WordTrace (prefixWord ++ tailWord_1196764) baseStart_1196764 baseEnd_1196764 := by
    simpa [prefixWord, tailWord_1196764, baseEnd_1196764] using wordTrace_append hprefix tailTrace_1196764
  have hstable : (prefixWord ++ tailWord_1196764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196764).length < 2 ^ (prefixWord ++ tailWord_1196764).sum := by decide
  have hdescent : baseEnd_1196764 < baseStart_1196764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196767 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 1, 2, 3]
def baseStart_1196767 : Nat := 118140960795 + 1196767 * 2 ^ 59
def prefixEnd_1196767 : Nat := 4983230072969 + 3 ^ 40 * 1196767 * 2
def baseEnd_1196767 : Nat := 614516702439424377308675

theorem tailTrace_1196767 : CollatzResearch.WordTrace tailWord_1196767 prefixEnd_1196767 614516702439424377308675 := by
  unfold tailWord_1196767
  simp only [CollatzResearch.WordTrace]
  refine ⟨43649678455325025376268555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29099785636883350250845703 43649678455325025376268555)
  ·
    refine ⟨65474517682987538064402833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43649678455325025376268555 65474517682987538064402833)
    ·
      refine ⟨49105888262240653548302125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65474517682987538064402833 49105888262240653548302125)
      ·
        refine ⟨18414708098340245080613297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49105888262240653548302125 18414708098340245080613297)
        ·
          refine ⟨13811031073755183810459973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18414708098340245080613297 13811031073755183810459973)
          ·
            refine ⟨2589568326329096964461245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13811031073755183810459973 2589568326329096964461245)
            ·
              refine ⟨971088122373411361672967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2589568326329096964461245 971088122373411361672967)
              ·
                refine ⟨1456632183560117042509451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971088122373411361672967 1456632183560117042509451)
                ·
                  refine ⟨2184948275340175563764177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456632183560117042509451 2184948275340175563764177)
                  ·
                    refine ⟨1638711206505131672823133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2184948275340175563764177 1638711206505131672823133)
                    ·
                      refine ⟨614516702439424377308675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1638711206505131672823133 614516702439424377308675)
                      ·
                        rfl

theorem cell23_1196767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_1196767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196767 prefixEnd_1196767 := by exact prefixLift 1196767
  have htrace : WordTrace (prefixWord ++ tailWord_1196767) baseStart_1196767 baseEnd_1196767 := by
    simpa [prefixWord, tailWord_1196767, baseEnd_1196767] using wordTrace_append hprefix tailTrace_1196767
  have hstable : (prefixWord ++ tailWord_1196767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196767).length < 2 ^ (prefixWord ++ tailWord_1196767).sum := by decide
  have hdescent : baseEnd_1196767 < baseStart_1196767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196807 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1196807 : Nat := 118140960795 + 1196807 * 2 ^ 59
def prefixEnd_1196807 : Nat := 4983230072969 + 3 ^ 40 * 1196807 * 2
def baseEnd_1196807 : Nat := 614537241665604220808491

theorem tailTrace_1196807 : CollatzResearch.WordTrace tailWord_1196807 prefixEnd_1196807 614537241665604220808491 := by
  unfold tailWord_1196807
  simp only [CollatzResearch.WordTrace]
  refine ⟨43651137375180112207724675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29100758250120074805149783 43651137375180112207724675)
  ·
    refine ⟨65476706062770168311587013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43651137375180112207724675 65476706062770168311587013)
    ·
      refine ⟨12276882386769406558422565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65476706062770168311587013 12276882386769406558422565)
      ·
        refine ⟨2301915447519263729704231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12276882386769406558422565 2301915447519263729704231)
        ·
          refine ⟨3452873171278895594556347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301915447519263729704231 3452873171278895594556347)
          ·
            refine ⟨5179309756918343391834521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452873171278895594556347 5179309756918343391834521)
            ·
              refine ⟨3884482317688757543875891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5179309756918343391834521 3884482317688757543875891)
              ·
                refine ⟨5826723476533136315813837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884482317688757543875891 5826723476533136315813837)
                ·
                  refine ⟨2185021303699926118430189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5826723476533136315813837 2185021303699926118430189)
                  ·
                    refine ⟨819382988887472294411321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185021303699926118430189 819382988887472294411321)
                    ·
                      refine ⟨614537241665604220808491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819382988887472294411321 614537241665604220808491)
                      ·
                        rfl

theorem cell23_1196807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1196807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196807 prefixEnd_1196807 := by exact prefixLift 1196807
  have htrace : WordTrace (prefixWord ++ tailWord_1196807) baseStart_1196807 baseEnd_1196807 := by
    simpa [prefixWord, tailWord_1196807, baseEnd_1196807] using wordTrace_append hprefix tailTrace_1196807
  have hstable : (prefixWord ++ tailWord_1196807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196807).length < 2 ^ (prefixWord ++ tailWord_1196807).sum := by decide
  have hdescent : baseEnd_1196807 < baseStart_1196807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196818 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_1196818 : Nat := 118140960795 + 1196818 * 2 ^ 59
def prefixEnd_1196818 : Nat := 4983230072969 + 3 ^ 40 * 1196818 * 2
def baseEnd_1196818 : Nat := 614542889952803677770941

theorem tailTrace_1196818 : CollatzResearch.WordTrace tailWord_1196818 prefixEnd_1196818 614542889952803677770941 := by
  unfold tailWord_1196818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10912884644535065271593777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29101025718760174057583405 10912884644535065271593777)
  ·
    refine ⟨8184663483401298953695333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10912884644535065271593777 8184663483401298953695333)
    ·
      refine ⟨1534624403137743553817875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8184663483401298953695333 1534624403137743553817875)
      ·
        refine ⟨2301936604706615330726813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534624403137743553817875 2301936604706615330726813)
        ·
          refine ⟨863226226764980749022555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2301936604706615330726813 863226226764980749022555)
          ·
            refine ⟨1294839340147471123533833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863226226764980749022555 1294839340147471123533833)
            ·
              refine ⟨971129505110603342650375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294839340147471123533833 971129505110603342650375)
              ·
                refine ⟨1456694257665905013975563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971129505110603342650375 1456694257665905013975563)
                ·
                  refine ⟨2185041386498857520963345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456694257665905013975563 2185041386498857520963345)
                  ·
                    refine ⟨1638781039874143140722509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185041386498857520963345 1638781039874143140722509)
                    ·
                      refine ⟨614542889952803677770941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1638781039874143140722509 614542889952803677770941)
                      ·
                        rfl

theorem cell23_1196818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_1196818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196818 prefixEnd_1196818 := by exact prefixLift 1196818
  have htrace : WordTrace (prefixWord ++ tailWord_1196818) baseStart_1196818 baseEnd_1196818 := by
    simpa [prefixWord, tailWord_1196818, baseEnd_1196818] using wordTrace_append hprefix tailTrace_1196818
  have hstable : (prefixWord ++ tailWord_1196818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196818).length < 2 ^ (prefixWord ++ tailWord_1196818).sum := by decide
  have hdescent : baseEnd_1196818 < baseStart_1196818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196833 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1196833 : Nat := 118140960795 + 1196833 * 2 ^ 59
def prefixEnd_1196833 : Nat := 4983230072969 + 3 ^ 40 * 1196833 * 2
def baseEnd_1196833 : Nat := 614550592162621119083371

theorem tailTrace_1196833 : CollatzResearch.WordTrace tailWord_1196833 prefixEnd_1196833 614550592162621119083371 := by
  unfold tailWord_1196833
  simp only [CollatzResearch.WordTrace]
  refine ⟨43652085673085918648171153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29101390448723945765447435 43652085673085918648171153)
  ·
    refine ⟨32739064254814438986128365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43652085673085918648171153 32739064254814438986128365)
    ·
      refine ⟨12277149095555414619798137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32739064254814438986128365 12277149095555414619798137)
      ·
        refine ⟨9207861821666560964848603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12277149095555414619798137 9207861821666560964848603)
        ·
          refine ⟨13811792732499841447272905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9207861821666560964848603 13811792732499841447272905)
          ·
            refine ⟨10358844549374881085454679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13811792732499841447272905 10358844549374881085454679)
            ·
              refine ⟨15538266824062321628182019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10358844549374881085454679 15538266824062321628182019)
              ·
                refine ⟨23307400236093482442273029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15538266824062321628182019 23307400236093482442273029)
                ·
                  refine ⟨4370137544267527957926193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23307400236093482442273029 4370137544267527957926193)
                  ·
                    refine ⟨3277603158200645968444645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4370137544267527957926193 3277603158200645968444645)
                    ·
                      refine ⟨614550592162621119083371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3277603158200645968444645 614550592162621119083371)
                      ·
                        rfl

theorem cell23_1196833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1196833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196833 prefixEnd_1196833 := by exact prefixLift 1196833
  have htrace : WordTrace (prefixWord ++ tailWord_1196833) baseStart_1196833 baseEnd_1196833 := by
    simpa [prefixWord, tailWord_1196833, baseEnd_1196833] using wordTrace_append hprefix tailTrace_1196833
  have hstable : (prefixWord ++ tailWord_1196833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196833).length < 2 ^ (prefixWord ++ tailWord_1196833).sum := by decide
  have hdescent : baseEnd_1196833 < baseStart_1196833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196837 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 4, 2, 2]
def baseStart_1196837 : Nat := 118140960795 + 1196837 * 2 ^ 59
def prefixEnd_1196837 : Nat := 4983230072969 + 3 ^ 40 * 1196837 * 2
def baseEnd_1196837 : Nat := 614552646085239103433353

theorem tailTrace_1196837 : CollatzResearch.WordTrace tailWord_1196837 prefixEnd_1196837 614552646085239103433353 := by
  unfold tailWord_1196837
  simp only [CollatzResearch.WordTrace]
  refine ⟨43652231565071427331316765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29101487710047618220877843 43652231565071427331316765)
  ·
    refine ⟨16369586836901785249243787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43652231565071427331316765 16369586836901785249243787)
    ·
      refine ⟨24554380255352677873865681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16369586836901785249243787 24554380255352677873865681)
      ·
        refine ⟨18415785191514508405399261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24554380255352677873865681 18415785191514508405399261)
        ·
          refine ⟨6905919446817940652024723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18415785191514508405399261 6905919446817940652024723)
          ·
            refine ⟨10358879170226910978037085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6905919446817940652024723 10358879170226910978037085)
            ·
              refine ⟨3884579688835091616763907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10358879170226910978037085 3884579688835091616763907)
              ·
                refine ⟨5826869533252637425145861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884579688835091616763907 5826869533252637425145861)
                ·
                  refine ⟨1092538037484869517214849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5826869533252637425145861 1092538037484869517214849)
                  ·
                    refine ⟨819403528113652137911137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092538037484869517214849 819403528113652137911137)
                    ·
                      refine ⟨614552646085239103433353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819403528113652137911137 614552646085239103433353)
                      ·
                        rfl

theorem cell23_1196837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_1196837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196837 prefixEnd_1196837 := by exact prefixLift 1196837
  have htrace : WordTrace (prefixWord ++ tailWord_1196837) baseStart_1196837 baseEnd_1196837 := by
    simpa [prefixWord, tailWord_1196837, baseEnd_1196837] using wordTrace_append hprefix tailTrace_1196837
  have hstable : (prefixWord ++ tailWord_1196837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196837).length < 2 ^ (prefixWord ++ tailWord_1196837).sum := by decide
  have hdescent : baseEnd_1196837 < baseStart_1196837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196873 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 1, 7]
def baseStart_1196873 : Nat := 118140960795 + 1196873 * 2 ^ 59
def prefixEnd_1196873 : Nat := 4983230072969 + 3 ^ 40 * 1196873 * 2
def baseEnd_1196873 : Nat := 204857043796266987527729

theorem tailTrace_1196873 : CollatzResearch.WordTrace tailWord_1196873 prefixEnd_1196873 204857043796266987527729 := by
  unfold tailWord_1196873
  simp only [CollatzResearch.WordTrace]
  refine ⟨43653544592941005479627273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29102363061960670319751515 43653544592941005479627273)
  ·
    refine ⟨32740158444705754109720455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43653544592941005479627273 32740158444705754109720455)
    ·
      refine ⟨49110237667058631164580683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32740158444705754109720455 49110237667058631164580683)
      ·
        refine ⟨73665356500587946746871025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49110237667058631164580683 73665356500587946746871025)
        ·
          refine ⟨55249017375440960060153269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73665356500587946746871025 55249017375440960060153269)
          ·
            refine ⟨5179595378947590005639369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55249017375440960060153269 5179595378947590005639369)
            ·
              refine ⟨3884696534210692504229527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5179595378947590005639369 3884696534210692504229527)
              ·
                refine ⟨5827044801316038756344291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884696534210692504229527 5827044801316038756344291)
                ·
                  refine ⟨8740567201974058134516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827044801316038756344291 8740567201974058134516437)
                  ·
                    refine ⟨204857043796266987527729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8740567201974058134516437 204857043796266987527729)
                    ·
                      rfl

theorem cell23_1196873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_1196873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196873 prefixEnd_1196873 := by exact prefixLift 1196873
  have htrace : WordTrace (prefixWord ++ tailWord_1196873) baseStart_1196873 baseEnd_1196873 := by
    simpa [prefixWord, tailWord_1196873, baseEnd_1196873] using wordTrace_append hprefix tailTrace_1196873
  have hstable : (prefixWord ++ tailWord_1196873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196873).length < 2 ^ (prefixWord ++ tailWord_1196873).sum := by decide
  have hdescent : baseEnd_1196873 < baseStart_1196873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196890 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_1196890 : Nat := 118140960795 + 1196890 * 2 ^ 59
def prefixEnd_1196890 : Nat := 4983230072969 + 3 ^ 40 * 1196890 * 2
def baseEnd_1196890 : Nat := 204859953519975798690203

theorem tailTrace_1196890 : CollatzResearch.WordTrace tailWord_1196890 prefixEnd_1196890 204859953519975798690203 := by
  unfold tailWord_1196890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10913541158469854345749031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29102776422586278255330749 10913541158469854345749031)
  ·
    refine ⟨16370311737704781518623547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10913541158469854345749031 16370311737704781518623547)
    ·
      refine ⟨24555467606557172277935321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16370311737704781518623547 24555467606557172277935321)
      ·
        refine ⟨18416600704917879208451491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24555467606557172277935321 18416600704917879208451491)
        ·
          refine ⟨27624901057376818812677237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18416600704917879208451491 27624901057376818812677237)
          ·
            refine ⟨2589834474129076763688491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27624901057376818812677237 2589834474129076763688491)
            ·
              refine ⟨3884751711193615145532737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589834474129076763688491 3884751711193615145532737)
              ·
                refine ⟨2913563783395211359149553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3884751711193615145532737 2913563783395211359149553)
                ·
                  refine ⟨2185172837546408519362165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2913563783395211359149553 2185172837546408519362165)
                  ·
                    refine ⟨204859953519975798690203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2185172837546408519362165 204859953519975798690203)
                    ·
                      rfl

theorem cell23_1196890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_1196890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196890 prefixEnd_1196890 := by exact prefixLift 1196890
  have htrace : WordTrace (prefixWord ++ tailWord_1196890) baseStart_1196890 baseEnd_1196890 := by
    simpa [prefixWord, tailWord_1196890, baseEnd_1196890] using wordTrace_append hprefix tailTrace_1196890
  have hstable : (prefixWord ++ tailWord_1196890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196890).length < 2 ^ (prefixWord ++ tailWord_1196890).sum := by decide
  have hdescent : baseEnd_1196890 < baseStart_1196890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196900 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_1196900 : Nat := 118140960795 + 1196900 * 2 ^ 59
def prefixEnd_1196900 : Nat := 4983230072969 + 3 ^ 40 * 1196900 * 2
def baseEnd_1196900 : Nat := 614584995366472356945563

theorem tailTrace_1196900 : CollatzResearch.WordTrace tailWord_1196900 prefixEnd_1196900 614584995366472356945563 := by
  unfold tailWord_1196900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21827264681921594545430077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29103019575895459393906769 21827264681921594545430077)
  ·
    refine ⟨8185224255720597954536279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21827264681921594545430077 8185224255720597954536279)
    ·
      refine ⟨12277836383580896931804419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8185224255720597954536279 12277836383580896931804419)
      ·
        refine ⟨18416754575371345397706629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12277836383580896931804419 18416754575371345397706629)
        ·
          refine ⟨3453141482882127262069993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18416754575371345397706629 3453141482882127262069993)
          ·
            refine ⟨2589856112161595446552495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453141482882127262069993 2589856112161595446552495)
            ·
              refine ⟨3884784168242393169828743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589856112161595446552495 3884784168242393169828743)
              ·
                refine ⟨5827176252363589754743115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884784168242393169828743 5827176252363589754743115)
                ·
                  refine ⟨8740764378545384632114673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5827176252363589754743115 8740764378545384632114673)
                  ·
                    refine ⟨6555573283909038474086005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8740764378545384632114673 6555573283909038474086005)
                    ·
                      refine ⟨614584995366472356945563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6555573283909038474086005 614584995366472356945563)
                      ·
                        rfl

theorem cell23_1196900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_1196900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196900 prefixEnd_1196900 := by exact prefixLift 1196900
  have htrace : WordTrace (prefixWord ++ tailWord_1196900) baseStart_1196900 baseEnd_1196900 := by
    simpa [prefixWord, tailWord_1196900, baseEnd_1196900] using wordTrace_append hprefix tailTrace_1196900
  have hstable : (prefixWord ++ tailWord_1196900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196900).length < 2 ^ (prefixWord ++ tailWord_1196900).sum := by decide
  have hdescent : baseEnd_1196900 < baseStart_1196900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196923 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 4]
def baseStart_1196923 : Nat := 118140960795 + 1196923 * 2 ^ 59
def prefixEnd_1196923 : Nat := 4983230072969 + 3 ^ 40 * 1196923 * 2
def baseEnd_1196923 : Nat := 614596805421525766957957

theorem tailTrace_1196923 : CollatzResearch.WordTrace tailWord_1196923 prefixEnd_1196923 614596805421525766957957 := by
  unfold tailWord_1196923
  simp only [CollatzResearch.WordTrace]
  refine ⟨43655368242759864018947423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29103578828506576012631615 43655368242759864018947423)
  ·
    refine ⟨65483052364139796028421135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43655368242759864018947423 65483052364139796028421135)
    ·
      refine ⟨98224578546209694042631703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65483052364139796028421135 98224578546209694042631703)
      ·
        refine ⟨147336867819314541063947555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98224578546209694042631703 147336867819314541063947555)
        ·
          refine ⟨221005301728971811595921333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147336867819314541063947555 221005301728971811595921333)
          ·
            refine ⟨20719247037091107337117625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 221005301728971811595921333 20719247037091107337117625)
            ·
              refine ⟨15539435277818330502838219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20719247037091107337117625 15539435277818330502838219)
              ·
                refine ⟨23309152916727495754257329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15539435277818330502838219 23309152916727495754257329)
                ·
                  refine ⟨17481864687545621815692997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23309152916727495754257329 17481864687545621815692997)
                  ·
                    refine ⟨3277849628914804090442437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17481864687545621815692997 3277849628914804090442437)
                    ·
                      refine ⟨614596805421525766957957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3277849628914804090442437 614596805421525766957957)
                      ·
                        rfl

theorem cell23_1196923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 4].length) (baseStart_1196923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196923 prefixEnd_1196923 := by exact prefixLift 1196923
  have htrace : WordTrace (prefixWord ++ tailWord_1196923) baseStart_1196923 baseEnd_1196923 := by
    simpa [prefixWord, tailWord_1196923, baseEnd_1196923] using wordTrace_append hprefix tailTrace_1196923
  have hstable : (prefixWord ++ tailWord_1196923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196923).length < 2 ^ (prefixWord ++ tailWord_1196923).sum := by decide
  have hdescent : baseEnd_1196923 < baseStart_1196923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196953 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_1196953 : Nat := 118140960795 + 1196953 * 2 ^ 59
def prefixEnd_1196953 : Nat := 4983230072969 + 3 ^ 40 * 1196953 * 2
def baseEnd_1196953 : Nat := 614612209841160649582819

theorem tailTrace_1196953 : CollatzResearch.WordTrace tailWord_1196953 prefixEnd_1196953 614612209841160649582819 := by
  unfold tailWord_1196953
  simp only [CollatzResearch.WordTrace]
  refine ⟨43656462432651179142539513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29104308288434119428359675 43656462432651179142539513)
  ·
    refine ⟨32742346824488384356904635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43656462432651179142539513 32742346824488384356904635)
    ·
      refine ⟨49113520236732576535356953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32742346824488384356904635 49113520236732576535356953)
      ·
        refine ⟨36835140177549432401517715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49113520236732576535356953 36835140177549432401517715)
        ·
          refine ⟨55252710266324148602276573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36835140177549432401517715 55252710266324148602276573)
          ·
            refine ⟨20719766349871555725853715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55252710266324148602276573 20719766349871555725853715)
            ·
              refine ⟨31079649524807333588780573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20719766349871555725853715 31079649524807333588780573)
              ·
                refine ⟨11654868571802750095792715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31079649524807333588780573 11654868571802750095792715)
                ·
                  refine ⟨17482302857704125143689073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11654868571802750095792715 17482302857704125143689073)
                  ·
                    refine ⟨13111727143278093857766805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17482302857704125143689073 13111727143278093857766805)
                    ·
                      refine ⟨614612209841160649582819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13111727143278093857766805 614612209841160649582819)
                      ·
                        rfl

theorem cell23_1196953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_1196953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1196953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1196953 prefixEnd_1196953 := by exact prefixLift 1196953
  have htrace : WordTrace (prefixWord ++ tailWord_1196953) baseStart_1196953 baseEnd_1196953 := by
    simpa [prefixWord, tailWord_1196953, baseEnd_1196953] using wordTrace_append hprefix tailTrace_1196953
  have hstable : (prefixWord ++ tailWord_1196953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196953).length < 2 ^ (prefixWord ++ tailWord_1196953).sum := by decide
  have hdescent : baseEnd_1196953 < baseStart_1196953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197034 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_1197034 : Nat := 118140960795 + 1197034 * 2 ^ 59
def prefixEnd_1197034 : Nat := 4983230072969 + 3 ^ 40 * 1197034 * 2
def baseEnd_1197034 : Nat := 614653801774174832669947

theorem tailTrace_1197034 : CollatzResearch.WordTrace tailWord_1197034 prefixEnd_1197034 614653801774174832669947 := by
  unfold tailWord_1197034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10914854186339432494059539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29106277830238486650825437 10914854186339432494059539)
  ·
    refine ⟨16372281279509148741089309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10914854186339432494059539 16372281279509148741089309)
    ·
      refine ⟨6139605479815930777908491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16372281279509148741089309 6139605479815930777908491)
      ·
        refine ⟨9209408219723896166862737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6139605479815930777908491 9209408219723896166862737)
        ·
          refine ⟨6907056164792922125147053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9209408219723896166862737 6907056164792922125147053)
          ·
            refine ⟨2590146061797345796930145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6907056164792922125147053 2590146061797345796930145)
            ·
              refine ⟨1942609546348009347697609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590146061797345796930145 1942609546348009347697609)
              ·
                refine ⟨1456957159761007010773207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942609546348009347697609 1456957159761007010773207)
                ·
                  refine ⟨2185435739641510516159811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1456957159761007010773207 2185435739641510516159811)
                  ·
                    refine ⟨3278153609462265774239717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2185435739641510516159811 3278153609462265774239717)
                    ·
                      refine ⟨614653801774174832669947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3278153609462265774239717 614653801774174832669947)
                      ·
                        rfl

theorem cell23_1197034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_1197034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197034 prefixEnd_1197034 := by exact prefixLift 1197034
  have htrace : WordTrace (prefixWord ++ tailWord_1197034) baseStart_1197034 baseEnd_1197034 := by
    simpa [prefixWord, tailWord_1197034, baseEnd_1197034] using wordTrace_append hprefix tailTrace_1197034
  have hstable : (prefixWord ++ tailWord_1197034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197034).length < 2 ^ (prefixWord ++ tailWord_1197034).sum := by decide
  have hdescent : baseEnd_1197034 < baseStart_1197034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197088 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1197088 : Nat := 118140960795 + 1197088 * 2 ^ 59
def prefixEnd_1197088 : Nat := 4983230072969 + 3 ^ 40 * 1197088 * 2
def baseEnd_1197088 : Nat := 614681529729517621394699

theorem tailTrace_1197088 : CollatzResearch.WordTrace tailWord_1197088 prefixEnd_1197088 614681529729517621394699 := by
  unfold tailWord_1197088
  simp only [CollatzResearch.WordTrace]
  refine ⟨21830693143581048599351959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29107590858108064799135945 21830693143581048599351959)
  ·
    refine ⟨32746039715371572899027939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21830693143581048599351959 32746039715371572899027939)
    ·
      refine ⟨49119059573057359348541909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32746039715371572899027939 49119059573057359348541909)
      ·
        refine ⟨1151227958743531859731451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49119059573057359348541909 1151227958743531859731451)
        ·
          refine ⟨1726841938115297789597177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151227958743531859731451 1726841938115297789597177)
          ·
            refine ⟨1295131453586473342197883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1726841938115297789597177 1295131453586473342197883)
            ·
              refine ⟨1942697180379710013296825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295131453586473342197883 1942697180379710013296825)
              ·
                refine ⟨1457022885284782509972619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942697180379710013296825 1457022885284782509972619)
                ·
                  refine ⟨2185534327927173764958929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457022885284782509972619 2185534327927173764958929)
                  ·
                    refine ⟨1639150745945380323719197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185534327927173764958929 1639150745945380323719197)
                    ·
                      refine ⟨614681529729517621394699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1639150745945380323719197 614681529729517621394699)
                      ·
                        rfl

theorem cell23_1197088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1197088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197088 prefixEnd_1197088 := by exact prefixLift 1197088
  have htrace : WordTrace (prefixWord ++ tailWord_1197088) baseStart_1197088 baseEnd_1197088 := by
    simpa [prefixWord, tailWord_1197088, baseEnd_1197088] using wordTrace_append hprefix tailTrace_1197088
  have hstable : (prefixWord ++ tailWord_1197088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197088).length < 2 ^ (prefixWord ++ tailWord_1197088).sum := by decide
  have hdescent : baseEnd_1197088 < baseStart_1197088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197118 : List Nat := [4, 2, 1, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1197118 : Nat := 118140960795 + 1197118 * 2 ^ 59
def prefixEnd_1197118 : Nat := 4983230072969 + 3 ^ 40 * 1197118 * 2
def baseEnd_1197118 : Nat := 614696934149152504019561

theorem tailTrace_1197118 : CollatzResearch.WordTrace tailWord_1197118 prefixEnd_1197118 614696934149152504019561 := by
  unfold tailWord_1197118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457810059631676540287001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29108320318035608214864005 5457810059631676540287001)
  ·
    refine ⟨4093357544723757405215251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5457810059631676540287001 4093357544723757405215251)
    ·
      refine ⟨6140036317085636107822877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4093357544723757405215251 6140036317085636107822877)
      ·
        refine ⟨2302513618907113540433579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6140036317085636107822877 2302513618907113540433579)
        ·
          refine ⟨3453770428360670310650369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302513618907113540433579 3453770428360670310650369)
          ·
            refine ⟨2590327821270502732987777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453770428360670310650369 2590327821270502732987777)
            ·
              refine ⟨1942745865952877049740833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590327821270502732987777 1942745865952877049740833)
              ·
                refine ⟨1457059399464657787305625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942745865952877049740833 1457059399464657787305625)
                ·
                  refine ⟨1092794549598493340479219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457059399464657787305625 1092794549598493340479219)
                  ·
                    refine ⟨1639191824397740010718829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1092794549598493340479219 1639191824397740010718829)
                    ·
                      refine ⟨614696934149152504019561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1639191824397740010718829 614696934149152504019561)
                      ·
                        rfl

theorem cell23_1197118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1197118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197118 prefixEnd_1197118 := by exact prefixLift 1197118
  have htrace : WordTrace (prefixWord ++ tailWord_1197118) baseStart_1197118 baseEnd_1197118 := by
    simpa [prefixWord, tailWord_1197118, baseEnd_1197118] using wordTrace_append hprefix tailTrace_1197118
  have hstable : (prefixWord ++ tailWord_1197118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197118).length < 2 ^ (prefixWord ++ tailWord_1197118).sum := by decide
  have hdescent : baseEnd_1197118 < baseStart_1197118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197127 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_1197127 : Nat := 118140960795 + 1197127 * 2 ^ 59
def prefixEnd_1197127 : Nat := 4983230072969 + 3 ^ 40 * 1197127 * 2
def baseEnd_1197127 : Nat := 614701555475042968807019

theorem tailTrace_1197127 : CollatzResearch.WordTrace tailWord_1197127 prefixEnd_1197127 614701555475042968807019 := by
  unfold tailWord_1197127
  simp only [CollatzResearch.WordTrace]
  refine ⟨43662808734020806859373635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29108539156013871239582423 43662808734020806859373635)
  ·
    refine ⟨65494213101031210289060453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43662808734020806859373635 65494213101031210289060453)
    ·
      refine ⟨12280164956443351929198835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65494213101031210289060453 12280164956443351929198835)
      ·
        refine ⟨18420247434665027893798253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12280164956443351929198835 18420247434665027893798253)
        ·
          refine ⟨6907592787999385460174345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18420247434665027893798253 6907592787999385460174345)
          ·
            refine ⟨5180694590999539095130759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6907592787999385460174345 5180694590999539095130759)
            ·
              refine ⟨7771041886499308642696139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5180694590999539095130759 7771041886499308642696139)
              ·
                refine ⟨11656562829748962964044209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7771041886499308642696139 11656562829748962964044209)
                ·
                  refine ⟨8742422122311722223033157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11656562829748962964044209 8742422122311722223033157)
                  ·
                    refine ⟨1639204147933447916818717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8742422122311722223033157 1639204147933447916818717)
                    ·
                      refine ⟨614701555475042968807019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1639204147933447916818717 614701555475042968807019)
                      ·
                        rfl

theorem cell23_1197127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_1197127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197127 prefixEnd_1197127 := by exact prefixLift 1197127
  have htrace : WordTrace (prefixWord ++ tailWord_1197127) baseStart_1197127 baseEnd_1197127 := by
    simpa [prefixWord, tailWord_1197127, baseEnd_1197127] using wordTrace_append hprefix tailTrace_1197127
  have hstable : (prefixWord ++ tailWord_1197127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197127).length < 2 ^ (prefixWord ++ tailWord_1197127).sum := by decide
  have hdescent : baseEnd_1197127 < baseStart_1197127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197141 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_1197141 : Nat := 118140960795 + 1197141 * 2 ^ 59
def prefixEnd_1197141 : Nat := 4983230072969 + 3 ^ 40 * 1197141 * 2
def baseEnd_1197141 : Nat := 614708744204205914031955

theorem tailTrace_1197141 : CollatzResearch.WordTrace tailWord_1197141 prefixEnd_1197141 614708744204205914031955 := by
  unfold tailWord_1197141
  simp only [CollatzResearch.WordTrace]
  refine ⟨43663319355970087250383277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29108879570646724833588851 43663319355970087250383277)
  ·
    refine ⟨16373744758488782718893729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43663319355970087250383277 16373744758488782718893729)
    ·
      refine ⟨12280308568866587039170297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16373744758488782718893729 12280308568866587039170297)
      ·
        refine ⟨9210231426649940279377723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12280308568866587039170297 9210231426649940279377723)
        ·
          refine ⟨13815347139974910419066585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9210231426649940279377723 13815347139974910419066585)
          ·
            refine ⟨10361510354981182814299939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13815347139974910419066585 10361510354981182814299939)
            ·
              refine ⟨15542265532471774221449909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10361510354981182814299939 15542265532471774221449909)
              ·
                refine ⟨1457087393669228833260929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15542265532471774221449909 1457087393669228833260929)
                ·
                  refine ⟨1092815545251921624945697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457087393669228833260929 1092815545251921624945697)
                  ·
                    refine ⟨819611658938941218709273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092815545251921624945697 819611658938941218709273)
                    ·
                      refine ⟨614708744204205914031955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819611658938941218709273 614708744204205914031955)
                      ·
                        rfl

theorem cell23_1197141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_1197141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197141 prefixEnd_1197141 := by exact prefixLift 1197141
  have htrace : WordTrace (prefixWord ++ tailWord_1197141) baseStart_1197141 baseEnd_1197141 := by
    simpa [prefixWord, tailWord_1197141, baseEnd_1197141] using wordTrace_append hprefix tailTrace_1197141
  have hstable : (prefixWord ++ tailWord_1197141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197141).length < 2 ^ (prefixWord ++ tailWord_1197141).sum := by decide
  have hdescent : baseEnd_1197141 < baseStart_1197141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197157 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_1197157 : Nat := 118140960795 + 1197157 * 2 ^ 59
def prefixEnd_1197157 : Nat := 4983230072969 + 3 ^ 40 * 1197157 * 2
def baseEnd_1197157 : Nat := 614716959894677851431881

theorem tailTrace_1197157 : CollatzResearch.WordTrace tailWord_1197157 prefixEnd_1197157 614716959894677851431881 := by
  unfold tailWord_1197157
  simp only [CollatzResearch.WordTrace]
  refine ⟨43663902923912121982965725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29109268615941414655310483 43663902923912121982965725)
  ·
    refine ⟨16373963596467045743612147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43663902923912121982965725 16373963596467045743612147)
    ·
      refine ⟨24560945394700568615418221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16373963596467045743612147 24560945394700568615418221)
      ·
        refine ⟨9210354523012713230781833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24560945394700568615418221 9210354523012713230781833)
        ·
          refine ⟨6907765892259534923086375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9210354523012713230781833 6907765892259534923086375)
          ·
            refine ⟨10361648838389302384629563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6907765892259534923086375 10361648838389302384629563)
            ·
              refine ⟨15542473257583953576944345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10361648838389302384629563 15542473257583953576944345)
              ·
                refine ⟨11656854943187965182708259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15542473257583953576944345 11656854943187965182708259)
                ·
                  refine ⟨17485282414781947774062389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11656854943187965182708259 17485282414781947774062389)
                  ·
                    refine ⟨1639245226385807603818349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17485282414781947774062389 1639245226385807603818349)
                    ·
                      refine ⟨614716959894677851431881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1639245226385807603818349 614716959894677851431881)
                      ·
                        rfl

theorem cell23_1197157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_1197157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197157 prefixEnd_1197157 := by exact prefixLift 1197157
  have htrace : WordTrace (prefixWord ++ tailWord_1197157) baseStart_1197157 baseEnd_1197157 := by
    simpa [prefixWord, tailWord_1197157, baseEnd_1197157] using wordTrace_append hprefix tailTrace_1197157
  have hstable : (prefixWord ++ tailWord_1197157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197157).length < 2 ^ (prefixWord ++ tailWord_1197157).sum := by decide
  have hdescent : baseEnd_1197157 < baseStart_1197157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197164 : List Nat := [2, 2, 1, 1, 3, 2, 4, 3, 5]
def baseStart_1197164 : Nat := 118140960795 + 1197164 * 2 ^ 59
def prefixEnd_1197164 : Nat := 4983230072969 + 3 ^ 40 * 1197164 * 2
def baseEnd_1197164 : Nat := 68302283806584369338261

theorem tailTrace_1197164 : CollatzResearch.WordTrace tailWord_1197164 prefixEnd_1197164 68302283806584369338261 := by
  unfold tailWord_1197164
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832079117443381089235273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29109438823257841452313697 21832079117443381089235273)
  ·
    refine ⟨16374059338082535816926455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21832079117443381089235273 16374059338082535816926455)
    ·
      refine ⟨24561089007123803725389683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16374059338082535816926455 24561089007123803725389683)
      ·
        refine ⟨36841633510685705588084525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24561089007123803725389683 36841633510685705588084525)
        ·
          refine ⟨13815612566507139595531697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36841633510685705588084525 13815612566507139595531697)
          ·
            refine ⟨10361709424880354696648773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13815612566507139595531697 10361709424880354696648773)
            ·
              refine ⟨1942820517165066505621645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10361709424880354696648773 1942820517165066505621645)
              ·
                refine ⟨728557693936899939608117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1942820517165066505621645 728557693936899939608117)
                ·
                  refine ⟨68302283806584369338261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 728557693936899939608117 68302283806584369338261)
                  ·
                    rfl

theorem cell23_1197164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_1197164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197164 prefixEnd_1197164 := by exact prefixLift 1197164
  have htrace : WordTrace (prefixWord ++ tailWord_1197164) baseStart_1197164 baseEnd_1197164 := by
    simpa [prefixWord, tailWord_1197164, baseEnd_1197164] using wordTrace_append hprefix tailTrace_1197164
  have hstable : (prefixWord ++ tailWord_1197164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197164).length < 2 ^ (prefixWord ++ tailWord_1197164).sum := by decide
  have hdescent : baseEnd_1197164 < baseStart_1197164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197174 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1197174 : Nat := 118140960795 + 1197174 * 2 ^ 59
def prefixEnd_1197174 : Nat := 4983230072969 + 3 ^ 40 * 1197174 * 2
def baseEnd_1197174 : Nat := 614725689065804284919303

theorem tailTrace_1197174 : CollatzResearch.WordTrace tailWord_1197174 prefixEnd_1197174 614725689065804284919303 := by
  unfold tailWord_1197174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729032685303158367895911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29109681976567022590889717 2729032685303158367895911)
  ·
    refine ⟨4093549027954737551843867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2729032685303158367895911 4093549027954737551843867)
    ·
      refine ⟨6140323541932106327765801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4093549027954737551843867 6140323541932106327765801)
      ·
        refine ⟨4605242656449079745824351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6140323541932106327765801 4605242656449079745824351)
        ·
          refine ⟨6907863984673619618736527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4605242656449079745824351 6907863984673619618736527)
          ·
            refine ⟨10361795977010429428104791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6907863984673619618736527 10361795977010429428104791)
            ·
              refine ⟨15542693965515644142157187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10361795977010429428104791 15542693965515644142157187)
              ·
                refine ⟨23314040948273466213235781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15542693965515644142157187 23314040948273466213235781)
                ·
                  refine ⟨4371382677801274914981709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23314040948273466213235781 4371382677801274914981709)
                  ·
                    refine ⟨1639268504175478093118141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4371382677801274914981709 1639268504175478093118141)
                    ·
                      refine ⟨614725689065804284919303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1639268504175478093118141 614725689065804284919303)
                      ·
                        rfl

theorem cell23_1197174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1197174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197174 prefixEnd_1197174 := by exact prefixLift 1197174
  have htrace : WordTrace (prefixWord ++ tailWord_1197174) baseStart_1197174 baseEnd_1197174 := by
    simpa [prefixWord, tailWord_1197174, baseEnd_1197174] using wordTrace_append hprefix tailTrace_1197174
  have hstable : (prefixWord ++ tailWord_1197174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197174).length < 2 ^ (prefixWord ++ tailWord_1197174).sum := by decide
  have hdescent : baseEnd_1197174 < baseStart_1197174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197234 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_1197234 : Nat := 118140960795 + 1197234 * 2 ^ 59
def prefixEnd_1197234 : Nat := 4983230072969 + 3 ^ 40 * 1197234 * 2
def baseEnd_1197234 : Nat := 614756497905074050169027

theorem tailTrace_1197234 : CollatzResearch.WordTrace tailWord_1197234 prefixEnd_1197234 614756497905074050169027 := by
  unfold tailWord_1197234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10916677836158291033379689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29111140896422109422345837 10916677836158291033379689)
  ·
    refine ⟨8187508377118718275034767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10916677836158291033379689 8187508377118718275034767)
    ·
      refine ⟨12281262565678077412552151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8187508377118718275034767 12281262565678077412552151)
      ·
        refine ⟨18421893848517116118828227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12281262565678077412552151 18421893848517116118828227)
        ·
          refine ⟨27632840772775674178242341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18421893848517116118828227 27632840772775674178242341)
          ·
            refine ⟨5181157644895438908420439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27632840772775674178242341 5181157644895438908420439)
            ·
              refine ⟨7771736467343158362630659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181157644895438908420439 7771736467343158362630659)
              ·
                refine ⟨11657604701014737543945989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7771736467343158362630659 11657604701014737543945989)
                ·
                  refine ⟨2185800881440263289489873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11657604701014737543945989 2185800881440263289489873)
                  ·
                    refine ⟨1639350661080197467117405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2185800881440263289489873 1639350661080197467117405)
                    ·
                      refine ⟨614756497905074050169027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1639350661080197467117405 614756497905074050169027)
                      ·
                        rfl

theorem cell23_1197234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_1197234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197234 prefixEnd_1197234 := by exact prefixLift 1197234
  have htrace : WordTrace (prefixWord ++ tailWord_1197234) baseStart_1197234 baseEnd_1197234 := by
    simpa [prefixWord, tailWord_1197234, baseEnd_1197234] using wordTrace_append hprefix tailTrace_1197234
  have hstable : (prefixWord ++ tailWord_1197234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197234).length < 2 ^ (prefixWord ++ tailWord_1197234).sum := by decide
  have hdescent : baseEnd_1197234 < baseStart_1197234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197238 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1197238 : Nat := 118140960795 + 1197238 * 2 ^ 59
def prefixEnd_1197238 : Nat := 4983230072969 + 3 ^ 40 * 1197238 * 2
def baseEnd_1197238 : Nat := 614758551827692034519009

theorem tailTrace_1197238 : CollatzResearch.WordTrace tailWord_1197238 prefixEnd_1197238 614758551827692034519009 := by
  unfold tailWord_1197238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729178577288667051041523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29111238157745781877776245 2729178577288667051041523)
  ·
    refine ⟨4093767865933000576562285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2729178577288667051041523 4093767865933000576562285)
    ·
      refine ⟨1535162949724875216210857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4093767865933000576562285 1535162949724875216210857)
      ·
        refine ⟨1151372212293656412158143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1535162949724875216210857 1151372212293656412158143)
        ·
          refine ⟨1727058318440484618237215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151372212293656412158143 1727058318440484618237215)
          ·
            refine ⟨2590587477660726927355823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727058318440484618237215 2590587477660726927355823)
            ·
              refine ⟨3885881216491090391033735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590587477660726927355823 3885881216491090391033735)
              ·
                refine ⟨5828821824736635586550603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3885881216491090391033735 5828821824736635586550603)
                ·
                  refine ⟨8743232737104953379825905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5828821824736635586550603 8743232737104953379825905)
                  ·
                    refine ⟨6557424552828715034869429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8743232737104953379825905 6557424552828715034869429)
                    ·
                      refine ⟨614758551827692034519009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6557424552828715034869429 614758551827692034519009)
                      ·
                        rfl

theorem cell23_1197238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1197238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197238 prefixEnd_1197238 := by exact prefixLift 1197238
  have htrace : WordTrace (prefixWord ++ tailWord_1197238) baseStart_1197238 baseEnd_1197238 := by
    simpa [prefixWord, tailWord_1197238, baseEnd_1197238] using wordTrace_append hprefix tailTrace_1197238
  have hstable : (prefixWord ++ tailWord_1197238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197238).length < 2 ^ (prefixWord ++ tailWord_1197238).sum := by decide
  have hdescent : baseEnd_1197238 < baseStart_1197238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197241 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 3, 4]
def baseStart_1197241 : Nat := 118140960795 + 1197241 * 2 ^ 59
def prefixEnd_1197241 : Nat := 4983230072969 + 3 ^ 40 * 1197241 * 2
def baseEnd_1197241 : Nat := 204920030756551840927165

theorem tailTrace_1197241 : CollatzResearch.WordTrace tailWord_1197241 prefixEnd_1197241 204920030756551840927165 := by
  unfold tailWord_1197241
  simp only [CollatzResearch.WordTrace]
  refine ⟨43666966655607804329023577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29111311103738536219349051 43666966655607804329023577)
  ·
    refine ⟨32750224991705853246767683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43666966655607804329023577 32750224991705853246767683)
    ·
      refine ⟨49125337487558779870151525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32750224991705853246767683 49125337487558779870151525)
      ·
        refine ⟨9211000778917271225653411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49125337487558779870151525 9211000778917271225653411)
        ·
          refine ⟨13816501168375906838480117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9211000778917271225653411 13816501168375906838480117)
          ·
            refine ⟨1295296984535241266107511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13816501168375906838480117 1295296984535241266107511)
            ·
              refine ⟨1942945476802861899161267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295296984535241266107511 1942945476802861899161267)
              ·
                refine ⟨2914418215204292848741901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1942945476802861899161267 2914418215204292848741901)
                ·
                  refine ⟨1092906830701609818278213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2914418215204292848741901 1092906830701609818278213)
                  ·
                    refine ⟨204920030756551840927165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1092906830701609818278213 204920030756551840927165)
                    ·
                      rfl

theorem cell23_1197241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 3, 4].length) (baseStart_1197241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197241 prefixEnd_1197241 := by exact prefixLift 1197241
  have htrace : WordTrace (prefixWord ++ tailWord_1197241) baseStart_1197241 baseEnd_1197241 := by
    simpa [prefixWord, tailWord_1197241, baseEnd_1197241] using wordTrace_append hprefix tailTrace_1197241
  have hstable : (prefixWord ++ tailWord_1197241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197241).length < 2 ^ (prefixWord ++ tailWord_1197241).sum := by decide
  have hdescent : baseEnd_1197241 < baseStart_1197241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197267 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 3, 5]
def baseStart_1197267 : Nat := 118140960795 + 1197267 * 2 ^ 59
def prefixEnd_1197267 : Nat := 4983230072969 + 3 ^ 40 * 1197267 * 2
def baseEnd_1197267 : Nat := 204924480922224140352125

theorem tailTrace_1197267 : CollatzResearch.WordTrace tailWord_1197267 prefixEnd_1197267 204924480922224140352125 := by
  unfold tailWord_1197267
  simp only [CollatzResearch.WordTrace]
  refine ⟨43667914953513610769470055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29111943302342407179646703 43667914953513610769470055)
  ·
    refine ⟨65501872430270416154205083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43667914953513610769470055 65501872430270416154205083)
    ·
      refine ⟨98252808645405624231307625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65501872430270416154205083 98252808645405624231307625)
      ·
        refine ⟨73689606484054218173480719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98252808645405624231307625 73689606484054218173480719)
        ·
          refine ⟨110534409726081327260221079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73689606484054218173480719 110534409726081327260221079)
          ·
            refine ⟨165801614589121990890331619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110534409726081327260221079 165801614589121990890331619)
            ·
              refine ⟨248702421883682986335497429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165801614589121990890331619 248702421883682986335497429)
              ·
                refine ⟨5828963012898819992238221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 248702421883682986335497429 5828963012898819992238221)
                ·
                  refine ⟨2185861129837057497089333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5828963012898819992238221 2185861129837057497089333)
                  ·
                    refine ⟨204924480922224140352125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2185861129837057497089333 204924480922224140352125)
                    ·
                      rfl

theorem cell23_1197267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 5].length) (baseStart_1197267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197267 prefixEnd_1197267 := by exact prefixLift 1197267
  have htrace : WordTrace (prefixWord ++ tailWord_1197267) baseStart_1197267 baseEnd_1197267 := by
    simpa [prefixWord, tailWord_1197267, baseEnd_1197267] using wordTrace_append hprefix tailTrace_1197267
  have hstable : (prefixWord ++ tailWord_1197267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197267).length < 2 ^ (prefixWord ++ tailWord_1197267).sum := by decide
  have hdescent : baseEnd_1197267 < baseStart_1197267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197284 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_1197284 : Nat := 118140960795 + 1197284 * 2 ^ 59
def prefixEnd_1197284 : Nat := 4983230072969 + 3 ^ 40 * 1197284 * 2
def baseEnd_1197284 : Nat := 204927390645932951514599

theorem tailTrace_1197284 : CollatzResearch.WordTrace tailWord_1197284 prefixEnd_1197284 204927390645932951514599 := by
  unfold tailWord_1197284
  simp only [CollatzResearch.WordTrace]
  refine ⟨21834267497226011336419453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29112356662968015115225937 21834267497226011336419453)
  ·
    refine ⟨8187850311459754251157295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21834267497226011336419453 8187850311459754251157295)
    ·
      refine ⟨12281775467189631376735943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8187850311459754251157295 12281775467189631376735943)
      ·
        refine ⟨18422663200784447065103915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12281775467189631376735943 18422663200784447065103915)
        ·
          refine ⟨27633994801176670597655873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18422663200784447065103915 27633994801176670597655873)
          ·
            refine ⟨20725496100882502948241905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27633994801176670597655873 20725496100882502948241905)
            ·
              refine ⟨15544122075661877211181429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20725496100882502948241905 15544122075661877211181429)
              ·
                refine ⟨1457261444593300988548259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15544122075661877211181429 1457261444593300988548259)
                ·
                  refine ⟨2185892166889951482822389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457261444593300988548259 2185892166889951482822389)
                  ·
                    refine ⟨204927390645932951514599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2185892166889951482822389 204927390645932951514599)
                    ·
                      rfl

theorem cell23_1197284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_1197284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197284 prefixEnd_1197284 := by exact prefixLift 1197284
  have htrace : WordTrace (prefixWord ++ tailWord_1197284) baseStart_1197284 baseEnd_1197284 := by
    simpa [prefixWord, tailWord_1197284, baseEnd_1197284] using wordTrace_append hprefix tailTrace_1197284
  have hstable : (prefixWord ++ tailWord_1197284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197284).length < 2 ^ (prefixWord ++ tailWord_1197284).sum := by decide
  have hdescent : baseEnd_1197284 < baseStart_1197284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197291 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 2, 3, 2]
def baseStart_1197291 : Nat := 118140960795 + 1197291 * 2 ^ 59
def prefixEnd_1197291 : Nat := 4983230072969 + 3 ^ 40 * 1197291 * 2
def baseEnd_1197291 : Nat := 614785766302380327156265

theorem tailTrace_1197291 : CollatzResearch.WordTrace tailWord_1197291 prefixEnd_1197291 614785766302380327156265 := by
  unfold tailWord_1197291
  simp only [CollatzResearch.WordTrace]
  refine ⟨43668790305426662868343727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29112526870284441912229151 43668790305426662868343727)
  ·
    refine ⟨65503185458139994302515591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43668790305426662868343727 65503185458139994302515591)
    ·
      refine ⟨98254778187209991453773387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65503185458139994302515591 98254778187209991453773387)
      ·
        refine ⟨147382167280814987180660081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98254778187209991453773387 147382167280814987180660081)
        ·
          refine ⟨110536625460611240385495061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147382167280814987180660081 110536625460611240385495061)
          ·
            refine ⟨5181404318466151893070081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110536625460611240385495061 5181404318466151893070081)
            ·
              refine ⟨3886053238849613919802561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5181404318466151893070081 3886053238849613919802561)
              ·
                refine ⟨2914539929137210439851921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3886053238849613919802561 2914539929137210439851921)
                ·
                  refine ⟨2185904946852907829888941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2914539929137210439851921 2185904946852907829888941)
                  ·
                    refine ⟨819714355069840436208353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185904946852907829888941 819714355069840436208353)
                    ·
                      refine ⟨614785766302380327156265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819714355069840436208353 614785766302380327156265)
                      ·
                        rfl

theorem cell23_1197291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 3, 2].length) (baseStart_1197291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197291 prefixEnd_1197291 := by exact prefixLift 1197291
  have htrace : WordTrace (prefixWord ++ tailWord_1197291) baseStart_1197291 baseEnd_1197291 := by
    simpa [prefixWord, tailWord_1197291, baseEnd_1197291] using wordTrace_append hprefix tailTrace_1197291
  have hstable : (prefixWord ++ tailWord_1197291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197291).length < 2 ^ (prefixWord ++ tailWord_1197291).sum := by decide
  have hdescent : baseEnd_1197291 < baseStart_1197291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197297 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 5, 6]
def baseStart_1197297 : Nat := 118140960795 + 1197297 * 2 ^ 59
def prefixEnd_1197297 : Nat := 4983230072969 + 3 ^ 40 * 1197297 * 2
def baseEnd_1197297 : Nat := 204929615728769101227079

theorem tailTrace_1197297 : CollatzResearch.WordTrace tailWord_1197297 prefixEnd_1197297 204929615728769101227079 := by
  unfold tailWord_1197297
  simp only [CollatzResearch.WordTrace]
  refine ⟨43669009143404925893062145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29112672762269950595374763 43669009143404925893062145)
  ·
    refine ⟨32751756857553694419796609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43669009143404925893062145 32751756857553694419796609)
    ·
      refine ⟨24563817643165270814847457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32751756857553694419796609 24563817643165270814847457)
      ·
        refine ⟨18422863232373953111135593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24563817643165270814847457 18422863232373953111135593)
        ·
          refine ⟨13817147424280464833351695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18422863232373953111135593 13817147424280464833351695)
          ·
            refine ⟨20725721136420697250027543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13817147424280464833351695 20725721136420697250027543)
            ·
              refine ⟨31088581704631045875041315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20725721136420697250027543 31088581704631045875041315)
              ·
                refine ⟨46632872556946568812561973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31088581704631045875041315 46632872556946568812561973)
                ·
                  refine ⟨4371831802213740826177685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46632872556946568812561973 4371831802213740826177685)
                  ·
                    refine ⟨204929615728769101227079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4371831802213740826177685 204929615728769101227079)
                    ·
                      rfl

theorem cell23_1197297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_1197297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197297 prefixEnd_1197297 := by exact prefixLift 1197297
  have htrace : WordTrace (prefixWord ++ tailWord_1197297) baseStart_1197297 baseEnd_1197297 := by
    simpa [prefixWord, tailWord_1197297, baseEnd_1197297] using wordTrace_append hprefix tailTrace_1197297
  have hstable : (prefixWord ++ tailWord_1197297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197297).length < 2 ^ (prefixWord ++ tailWord_1197297).sum := by decide
  have hdescent : baseEnd_1197297 < baseStart_1197297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197304 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 4, 6, 2]
def baseStart_1197304 : Nat := 118140960795 + 1197304 * 2 ^ 59
def prefixEnd_1197304 : Nat := 4983230072969 + 3 ^ 40 * 1197304 * 2
def baseEnd_1197304 : Nat := 614792441550888776293705

theorem tailTrace_1197304 : CollatzResearch.WordTrace tailWord_1197304 prefixEnd_1197304 614792441550888776293705 := by
  unfold tailWord_1197304
  simp only [CollatzResearch.WordTrace]
  refine ⟨21834632227189783044283483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29112842969586377392377977 21834632227189783044283483)
  ·
    refine ⟨32751948340784674566425225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21834632227189783044283483 32751948340784674566425225)
    ·
      refine ⟨24563961255588505924818919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32751948340784674566425225 24563961255588505924818919)
      ·
        refine ⟨36845941883382758887228379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24563961255588505924818919 36845941883382758887228379)
        ·
          refine ⟨55268912825074138330842569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36845941883382758887228379 55268912825074138330842569)
          ·
            refine ⟨41451684618805603748131927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55268912825074138330842569 41451684618805603748131927)
            ·
              refine ⟨62177526928208405622197891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41451684618805603748131927 62177526928208405622197891)
              ·
                refine ⟨93266290392312608433296837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62177526928208405622197891 93266290392312608433296837)
                ·
                  refine ⟨17487429448558614081243157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93266290392312608433296837 17487429448558614081243157)
                  ·
                    refine ⟨819723255401185035058273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17487429448558614081243157 819723255401185035058273)
                    ·
                      refine ⟨614792441550888776293705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819723255401185035058273 614792441550888776293705)
                      ·
                        rfl

theorem cell23_1197304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_1197304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197304 prefixEnd_1197304 := by exact prefixLift 1197304
  have htrace : WordTrace (prefixWord ++ tailWord_1197304) baseStart_1197304 baseEnd_1197304 := by
    simpa [prefixWord, tailWord_1197304, baseEnd_1197304] using wordTrace_append hprefix tailTrace_1197304
  have hstable : (prefixWord ++ tailWord_1197304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197304).length < 2 ^ (prefixWord ++ tailWord_1197304).sum := by decide
  have hdescent : baseEnd_1197304 < baseStart_1197304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197338 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4]
def baseStart_1197338 : Nat := 118140960795 + 1197338 * 2 ^ 59
def prefixEnd_1197338 : Nat := 4983230072969 + 3 ^ 40 * 1197338 * 2
def baseEnd_1197338 : Nat := 614809899893141643268549

theorem tailTrace_1197338 : CollatzResearch.WordTrace tailWord_1197338 prefixEnd_1197338 614809899893141643268549 := by
  unfold tailWord_1197338
  simp only [CollatzResearch.WordTrace]
  refine ⟨10917626134064097473826167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29113669690837593263536445 10917626134064097473826167)
  ·
    refine ⟨16376439201096146210739251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10917626134064097473826167 16376439201096146210739251)
    ·
      refine ⟨24564658801644219316108877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16376439201096146210739251 24564658801644219316108877)
      ·
        refine ⟨9211747050616582243540829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24564658801644219316108877 9211747050616582243540829)
        ·
          refine ⟨3454405143981218341327811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9211747050616582243540829 3454405143981218341327811)
          ·
            refine ⟨5181607715971827511991717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3454405143981218341327811 5181607715971827511991717)
            ·
              refine ⟨971551446744717658498447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5181607715971827511991717 971551446744717658498447)
              ·
                refine ⟨1457327170117076487747671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971551446744717658498447 1457327170117076487747671)
                ·
                  refine ⟨2185990755175614731621507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1457327170117076487747671 2185990755175614731621507)
                  ·
                    refine ⟨3278986132763422097432261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2185990755175614731621507 3278986132763422097432261)
                    ·
                      refine ⟨614809899893141643268549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3278986132763422097432261 614809899893141643268549)
                      ·
                        rfl

theorem cell23_1197338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_1197338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197338 prefixEnd_1197338 := by exact prefixLift 1197338
  have htrace : WordTrace (prefixWord ++ tailWord_1197338) baseStart_1197338 baseEnd_1197338 := by
    simpa [prefixWord, tailWord_1197338, baseEnd_1197338] using wordTrace_append hprefix tailTrace_1197338
  have hstable : (prefixWord ++ tailWord_1197338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197338).length < 2 ^ (prefixWord ++ tailWord_1197338).sum := by decide
  have hdescent : baseEnd_1197338 < baseStart_1197338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197344 : List Nat := [2, 1, 1, 5, 3, 1, 10]
def baseStart_1197344 : Nat := 118140960795 + 1197344 * 2 ^ 59
def prefixEnd_1197344 : Nat := 4983230072969 + 3 ^ 40 * 1197344 * 2
def baseEnd_1197344 : Nat := 7590283713297143454241

theorem tailTrace_1197344 : CollatzResearch.WordTrace tailWord_1197344 prefixEnd_1197344 7590283713297143454241 := by
  unfold tailWord_1197344
  simp only [CollatzResearch.WordTrace]
  refine ⟨21835361687117326460011543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29113815582823101946682057 21835361687117326460011543)
  ·
    refine ⟨32753042530675989690017315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21835361687117326460011543 32753042530675989690017315)
    ·
      refine ⟨49129563796013984535025973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32753042530675989690017315 49129563796013984535025973)
      ·
        refine ⟨4605896605876311050158685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49129563796013984535025973 4605896605876311050158685)
        ·
          refine ⟨1727211227203616643809507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4605896605876311050158685 1727211227203616643809507)
          ·
            refine ⟨2590816840805424965714261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727211227203616643809507 2590816840805424965714261)
            ·
              refine ⟨7590283713297143454241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2590816840805424965714261 7590283713297143454241)
              ·
                rfl

theorem cell23_1197344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 10].length) (baseStart_1197344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197344 prefixEnd_1197344 := by exact prefixLift 1197344
  have htrace : WordTrace (prefixWord ++ tailWord_1197344) baseStart_1197344 baseEnd_1197344 := by
    simpa [prefixWord, tailWord_1197344, baseEnd_1197344] using wordTrace_append hprefix tailTrace_1197344
  have hstable : (prefixWord ++ tailWord_1197344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197344).length < 2 ^ (prefixWord ++ tailWord_1197344).sum := by decide
  have hdescent : baseEnd_1197344 < baseStart_1197344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197381 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 3, 3, 2]
def baseStart_1197381 : Nat := 118140960795 + 1197381 * 2 ^ 59
def prefixEnd_1197381 : Nat := 4983230072969 + 3 ^ 40 * 1197381 * 2
def baseEnd_1197381 : Nat := 614831979561284975030851

theorem tailTrace_1197381 : CollatzResearch.WordTrace tailWord_1197381 prefixEnd_1197381 614831979561284975030851 := by
  unfold tailWord_1197381
  simp only [CollatzResearch.WordTrace]
  refine ⟨43672072875100608239119997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29114715250067072159413331 43672072875100608239119997)
  ·
    refine ⟨16377027328162728089669999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43672072875100608239119997 16377027328162728089669999)
    ·
      refine ⟨24565540992244092134504999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16377027328162728089669999 24565540992244092134504999)
      ·
        refine ⟨36848311488366138201757499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24565540992244092134504999 36848311488366138201757499)
        ·
          refine ⟨55272467232549207302636249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36848311488366138201757499 55272467232549207302636249)
          ·
            refine ⟨41454350424411905476977187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55272467232549207302636249 41454350424411905476977187)
            ·
              refine ⟨62181525636617858215465781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41454350424411905476977187 62181525636617858215465781)
              ·
                refine ⟨5829518028432924207699917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62181525636617858215465781 5829518028432924207699917)
                ·
                  refine ⟨2186069260662346577887469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5829518028432924207699917 2186069260662346577887469)
                  ·
                    refine ⟨819775972748379966707801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2186069260662346577887469 819775972748379966707801)
                    ·
                      refine ⟨614831979561284975030851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819775972748379966707801 614831979561284975030851)
                      ·
                        rfl

theorem cell23_1197381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_1197381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197381 prefixEnd_1197381 := by exact prefixLift 1197381
  have htrace : WordTrace (prefixWord ++ tailWord_1197381) baseStart_1197381 baseEnd_1197381 := by
    simpa [prefixWord, tailWord_1197381, baseEnd_1197381] using wordTrace_append hprefix tailTrace_1197381
  have hstable : (prefixWord ++ tailWord_1197381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197381).length < 2 ^ (prefixWord ++ tailWord_1197381).sum := by decide
  have hdescent : baseEnd_1197381 < baseStart_1197381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197394 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1197394 : Nat := 118140960795 + 1197394 * 2 ^ 59
def prefixEnd_1197394 : Nat := 4983230072969 + 3 ^ 40 * 1197394 * 2
def baseEnd_1197394 : Nat := 614838654809793424168291

theorem tailTrace_1197394 : CollatzResearch.WordTrace tailWord_1197394 prefixEnd_1197394 614838654809793424168291 := by
  unfold tailWord_1197394
  simp only [CollatzResearch.WordTrace]
  refine ⟨10918136756013377864835809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29115031349369007639562157 10918136756013377864835809)
  ·
    refine ⟨8188602567010033398626857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10918136756013377864835809 8188602567010033398626857)
    ·
      refine ⟨6141451925257525048970143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8188602567010033398626857 6141451925257525048970143)
      ·
        refine ⟨9212177887886287573455215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6141451925257525048970143 9212177887886287573455215)
        ·
          refine ⟨13818266831829431360182823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9212177887886287573455215 13818266831829431360182823)
          ·
            refine ⟨20727400247744147040274235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13818266831829431360182823 20727400247744147040274235)
            ·
              refine ⟨31091100371616220560411353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20727400247744147040274235 31091100371616220560411353)
              ·
                refine ⟨23318325278712165420308515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31091100371616220560411353 23318325278712165420308515)
                ·
                  refine ⟨34977487918068248130462773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23318325278712165420308515 34977487918068248130462773)
                  ·
                    refine ⟨3279139492318898262230885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34977487918068248130462773 3279139492318898262230885)
                    ·
                      refine ⟨614838654809793424168291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3279139492318898262230885 614838654809793424168291)
                      ·
                        rfl

theorem cell23_1197394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1197394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197394 prefixEnd_1197394 := by exact prefixLift 1197394
  have htrace : WordTrace (prefixWord ++ tailWord_1197394) baseStart_1197394 baseEnd_1197394 := by
    simpa [prefixWord, tailWord_1197394, baseEnd_1197394] using wordTrace_append hprefix tailTrace_1197394
  have hstable : (prefixWord ++ tailWord_1197394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197394).length < 2 ^ (prefixWord ++ tailWord_1197394).sum := by decide
  have hdescent : baseEnd_1197394 < baseStart_1197394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197422 : List Nat := [4, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1197422 : Nat := 118140960795 + 1197422 * 2 ^ 59
def prefixEnd_1197422 : Nat := 4983230072969 + 3 ^ 40 * 1197422 * 2
def baseEnd_1197422 : Nat := 614853032268119314618163

theorem tailTrace_1197422 : CollatzResearch.WordTrace tailWord_1197422 prefixEnd_1197422 614853032268119314618163 := by
  unfold tailWord_1197422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459196033494009030170315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29115712178634714827575013 5459196033494009030170315)
  ·
    refine ⟨8188794050241013545255473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5459196033494009030170315 8188794050241013545255473)
    ·
      refine ⟨6141595537680760158941605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8188794050241013545255473 6141595537680760158941605)
      ·
        refine ⟨1151549163315142529801551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6141595537680760158941605 1151549163315142529801551)
        ·
          refine ⟨1727323744972713794702327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151549163315142529801551 1727323744972713794702327)
          ·
            refine ⟨2590985617459070692053491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727323744972713794702327 2590985617459070692053491)
            ·
              refine ⟨3886478426188606038080237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590985617459070692053491 3886478426188606038080237)
              ·
                refine ⟨1457429409820727264280089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3886478426188606038080237 1457429409820727264280089)
                ·
                  refine ⟨1093072057365545448210067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457429409820727264280089 1093072057365545448210067)
                  ·
                    refine ⟨1639608086048318172315101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1093072057365545448210067 1639608086048318172315101)
                    ·
                      refine ⟨614853032268119314618163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1639608086048318172315101 614853032268119314618163)
                      ·
                        rfl

theorem cell23_1197422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1197422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197422 prefixEnd_1197422 := by exact prefixLift 1197422
  have htrace : WordTrace (prefixWord ++ tailWord_1197422) baseStart_1197422 baseEnd_1197422 := by
    simpa [prefixWord, tailWord_1197422, baseEnd_1197422] using wordTrace_append hprefix tailTrace_1197422
  have hstable : (prefixWord ++ tailWord_1197422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197422).length < 2 ^ (prefixWord ++ tailWord_1197422).sum := by decide
  have hdescent : baseEnd_1197422 < baseStart_1197422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197424 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_1197424 : Nat := 118140960795 + 1197424 * 2 ^ 59
def prefixEnd_1197424 : Nat := 4983230072969 + 3 ^ 40 * 1197424 * 2
def baseEnd_1197424 : Nat := 614854059229428306793153

theorem tailTrace_1197424 : CollatzResearch.WordTrace tailWord_1197424 prefixEnd_1197424 614854059229428306793153 := by
  unfold tailWord_1197424
  simp only [CollatzResearch.WordTrace]
  refine ⟨21836820606972413291467663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29115760809296551055290217 21836820606972413291467663)
  ·
    refine ⟨32755230910458619937201495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21836820606972413291467663 32755230910458619937201495)
    ·
      refine ⟨49132846365687929905802243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32755230910458619937201495 49132846365687929905802243)
      ·
        refine ⟨73699269548531894858703365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49132846365687929905802243 73699269548531894858703365)
        ·
          refine ⟨13818613040349730286006881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73699269548531894858703365 13818613040349730286006881)
          ·
            refine ⟨10363959780262297714505161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13818613040349730286006881 10363959780262297714505161)
            ·
              refine ⟨7772969835196723285878871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10363959780262297714505161 7772969835196723285878871)
              ·
                refine ⟨11659454752795084928818307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7772969835196723285878871 11659454752795084928818307)
                ·
                  refine ⟨17489182129192627393227461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11659454752795084928818307 17489182129192627393227461)
                  ·
                    refine ⟨3279221649223617636230149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17489182129192627393227461 3279221649223617636230149)
                    ·
                      refine ⟨614854059229428306793153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3279221649223617636230149 614854059229428306793153)
                      ·
                        rfl

theorem cell23_1197424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_1197424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197424 prefixEnd_1197424 := by exact prefixLift 1197424
  have htrace : WordTrace (prefixWord ++ tailWord_1197424) baseStart_1197424 baseEnd_1197424 := by
    simpa [prefixWord, tailWord_1197424, baseEnd_1197424] using wordTrace_append hprefix tailTrace_1197424
  have hstable : (prefixWord ++ tailWord_1197424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197424).length < 2 ^ (prefixWord ++ tailWord_1197424).sum := by decide
  have hdescent : baseEnd_1197424 < baseStart_1197424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197451 : List Nat := [1, 1, 1, 1, 4, 3, 2, 5, 5]
def baseStart_1197451 : Nat := 118140960795 + 1197451 * 2 ^ 59
def prefixEnd_1197451 : Nat := 4983230072969 + 3 ^ 40 * 1197451 * 2
def baseEnd_1197451 : Nat := 68318658134122189017281

theorem tailTrace_1197451 : CollatzResearch.WordTrace tailWord_1197451 prefixEnd_1197451 68318658134122189017281 := by
  unfold tailWord_1197451
  simp only [CollatzResearch.WordTrace]
  refine ⟨43674625984847010194168207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29116417323231340129445471 43674625984847010194168207)
  ·
    refine ⟨65511938977270515291252311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43674625984847010194168207 65511938977270515291252311)
    ·
      refine ⟨98267908465905772936878467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65511938977270515291252311 98267908465905772936878467)
      ·
        refine ⟨147401862698858659405317701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98267908465905772936878467 147401862698858659405317701)
        ·
          refine ⟨27637849256035998638497069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147401862698858659405317701 27637849256035998638497069)
          ·
            refine ⟨10364193471013499489436401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27637849256035998638497069 10364193471013499489436401)
            ·
              refine ⟨7773145103260124617077301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10364193471013499489436401 7773145103260124617077301)
              ·
                refine ⟨728732353430636682850997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7773145103260124617077301 728732353430636682850997)
                ·
                  refine ⟨68318658134122189017281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 728732353430636682850997 68318658134122189017281)
                  ·
                    rfl

theorem cell23_1197451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 5].length) (baseStart_1197451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197451 prefixEnd_1197451 := by exact prefixLift 1197451
  have htrace : WordTrace (prefixWord ++ tailWord_1197451) baseStart_1197451 baseEnd_1197451 := by
    simpa [prefixWord, tailWord_1197451, baseEnd_1197451] using wordTrace_append hprefix tailTrace_1197451
  have hstable : (prefixWord ++ tailWord_1197451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197451).length < 2 ^ (prefixWord ++ tailWord_1197451).sum := by decide
  have hdescent : baseEnd_1197451 < baseStart_1197451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197501 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_1197501 : Nat := 118140960795 + 1197501 * 2 ^ 59
def prefixEnd_1197501 : Nat := 4983230072969 + 3 ^ 40 * 1197501 * 2
def baseEnd_1197501 : Nat := 614893597239824505530299

theorem tailTrace_1197501 : CollatzResearch.WordTrace tailWord_1197501 prefixEnd_1197501 614893597239824505530299 := by
  unfold tailWord_1197501
  simp only [CollatzResearch.WordTrace]
  refine ⟨43676449634665868733488357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29117633089777245822325571 43676449634665868733488357)
  ·
    refine ⟨8189334306499850387529067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43676449634665868733488357 8189334306499850387529067)
    ·
      refine ⟨12284001459749775581293601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8189334306499850387529067 12284001459749775581293601)
      ·
        refine ⟨9213001094812331685970201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12284001459749775581293601 9213001094812331685970201)
        ·
          refine ⟨6909750821109248764477651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9213001094812331685970201 6909750821109248764477651)
          ·
            refine ⟨10364626231663873146716477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6909750821109248764477651 10364626231663873146716477)
            ·
              refine ⟨3886734836873952430018679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10364626231663873146716477 3886734836873952430018679)
              ·
                refine ⟨5830102255310928645028019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886734836873952430018679 5830102255310928645028019)
                ·
                  refine ⟨8745153382966392967542029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5830102255310928645028019 8745153382966392967542029)
                  ·
                    refine ⟨3279432518612397362828261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8745153382966392967542029 3279432518612397362828261)
                    ·
                      refine ⟨614893597239824505530299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3279432518612397362828261 614893597239824505530299)
                      ·
                        rfl

theorem cell23_1197501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_1197501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197501 prefixEnd_1197501 := by exact prefixLift 1197501
  have htrace : WordTrace (prefixWord ++ tailWord_1197501) baseStart_1197501 baseEnd_1197501 := by
    simpa [prefixWord, tailWord_1197501, baseEnd_1197501] using wordTrace_append hprefix tailTrace_1197501
  have hstable : (prefixWord ++ tailWord_1197501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197501).length < 2 ^ (prefixWord ++ tailWord_1197501).sum := by decide
  have hdescent : baseEnd_1197501 < baseStart_1197501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197511 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 5, 4]
def baseStart_1197511 : Nat := 118140960795 + 1197511 * 2 ^ 59
def prefixEnd_1197511 : Nat := 4983230072969 + 3 ^ 40 * 1197511 * 2
def baseEnd_1197511 : Nat := 204966244015456488801751

theorem tailTrace_1197511 : CollatzResearch.WordTrace tailWord_1197511 prefixEnd_1197511 204966244015456488801751 := by
  unfold tailWord_1197511
  simp only [CollatzResearch.WordTrace]
  refine ⟨43676814364629640441352387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29117876243086426960901591 43676814364629640441352387)
  ·
    refine ⟨65515221546944460662028581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43676814364629640441352387 65515221546944460662028581)
    ·
      refine ⟨12284104040052086374130359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65515221546944460662028581 12284104040052086374130359)
      ·
        refine ⟨18426156060078129561195539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12284104040052086374130359 18426156060078129561195539)
        ·
          refine ⟨27639234090117194341793309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18426156060078129561195539 27639234090117194341793309)
          ·
            refine ⟨10364712783793947878172491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27639234090117194341793309 10364712783793947878172491)
            ·
              refine ⟨15547069175690921817258737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10364712783793947878172491 15547069175690921817258737)
              ·
                refine ⟨11660301881768191362944053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15547069175690921817258737 11660301881768191362944053)
                ·
                  refine ⟨1093153301415767940276005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11660301881768191362944053 1093153301415767940276005)
                  ·
                    refine ⟨204966244015456488801751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1093153301415767940276005 204966244015456488801751)
                    ·
                      rfl

theorem cell23_1197511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_1197511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197511 prefixEnd_1197511 := by exact prefixLift 1197511
  have htrace : WordTrace (prefixWord ++ tailWord_1197511) baseStart_1197511 baseEnd_1197511 := by
    simpa [prefixWord, tailWord_1197511, baseEnd_1197511] using wordTrace_append hprefix tailTrace_1197511
  have hstable : (prefixWord ++ tailWord_1197511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197511).length < 2 ^ (prefixWord ++ tailWord_1197511).sum := by decide
  have hdescent : baseEnd_1197511 < baseStart_1197511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197518 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_1197518 : Nat := 118140960795 + 1197518 * 2 ^ 59
def prefixEnd_1197518 : Nat := 4983230072969 + 3 ^ 40 * 1197518 * 2
def baseEnd_1197518 : Nat := 614902326410950939017721

theorem tailTrace_1197518 : CollatzResearch.WordTrace tailWord_1197518 prefixEnd_1197518 614902326410950939017721 := by
  unfold tailWord_1197518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459633709450535079607151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29118046450402853757904805 5459633709450535079607151)
  ·
    refine ⟨8189450564175802619410727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5459633709450535079607151 8189450564175802619410727)
    ·
      refine ⟨12284175846263703929116091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8189450564175802619410727 12284175846263703929116091)
      ·
        refine ⟨18426263769395555893674137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12284175846263703929116091 18426263769395555893674137)
        ·
          refine ⟨13819697827046666920255603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18426263769395555893674137 13819697827046666920255603)
          ·
            refine ⟨20729546740570000380383405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13819697827046666920255603 20729546740570000380383405)
            ·
              refine ⟨7773580027713750142643777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20729546740570000380383405 7773580027713750142643777)
              ·
                refine ⟨5830185020785312606982833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7773580027713750142643777 5830185020785312606982833)
                ·
                  refine ⟨4372638765588984455237125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5830185020785312606982833 4372638765588984455237125)
                  ·
                    refine ⟨819869768547934585356961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4372638765588984455237125 819869768547934585356961)
                    ·
                      refine ⟨614902326410950939017721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 819869768547934585356961 614902326410950939017721)
                      ·
                        rfl

theorem cell23_1197518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_1197518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197518 prefixEnd_1197518 := by exact prefixLift 1197518
  have htrace : WordTrace (prefixWord ++ tailWord_1197518) baseStart_1197518 baseEnd_1197518 := by
    simpa [prefixWord, tailWord_1197518, baseEnd_1197518] using wordTrace_append hprefix tailTrace_1197518
  have hstable : (prefixWord ++ tailWord_1197518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197518).length < 2 ^ (prefixWord ++ tailWord_1197518).sum := by decide
  have hdescent : baseEnd_1197518 < baseStart_1197518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197592 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 6]
def baseStart_1197592 : Nat := 118140960795 + 1197592 * 2 ^ 59
def prefixEnd_1197592 : Nat := 4983230072969 + 3 ^ 40 * 1197592 * 2
def baseEnd_1197592 : Nat := 68326702664375961054709

theorem tailTrace_1197592 : CollatzResearch.WordTrace tailWord_1197592 prefixEnd_1197592 68326702664375961054709 := by
  unfold tailWord_1197592
  simp only [CollatzResearch.WordTrace]
  refine ⟨21839884338668095637525515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29119845784890794183367353 21839884338668095637525515)
  ·
    refine ⟨32759826508002143456288273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21839884338668095637525515 32759826508002143456288273)
    ·
      refine ⟨24569869881001607592216205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32759826508002143456288273 24569869881001607592216205)
      ·
        refine ⟨9213701205375602847081077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24569869881001607592216205 9213701205375602847081077)
        ·
          refine ⟨863784488003962766913851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9213701205375602847081077 863784488003962766913851)
          ·
            refine ⟨1295676732005944150370777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863784488003962766913851 1295676732005944150370777)
            ·
              refine ⟨971757549004458112778083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295676732005944150370777 971757549004458112778083)
              ·
                refine ⟨1457636323506687169167125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971757549004458112778083 1457636323506687169167125)
                ·
                  refine ⟨68326702664375961054709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1457636323506687169167125 68326702664375961054709)
                  ·
                    rfl

theorem cell23_1197592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 6].length) (baseStart_1197592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197592 prefixEnd_1197592 := by exact prefixLift 1197592
  have htrace : WordTrace (prefixWord ++ tailWord_1197592) baseStart_1197592 baseEnd_1197592 := by
    simpa [prefixWord, tailWord_1197592, baseEnd_1197592] using wordTrace_append hprefix tailTrace_1197592
  have hstable : (prefixWord ++ tailWord_1197592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197592).length < 2 ^ (prefixWord ++ tailWord_1197592).sum := by decide
  have hdescent : baseEnd_1197592 < baseStart_1197592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197691 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 4, 6]
def baseStart_1197691 : Nat := 118140960795 + 1197691 * 2 ^ 59
def prefixEnd_1197691 : Nat := 4983230072969 + 3 ^ 40 * 1197691 * 2
def baseEnd_1197691 : Nat := 204997052854726254051475

theorem tailTrace_1197691 : CollatzResearch.WordTrace tailWord_1197691 prefixEnd_1197691 204997052854726254051475 := by
  unfold tailWord_1197691
  simp only [CollatzResearch.WordTrace]
  refine ⟨43683379503977531182904927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29122253002651687455269951 43683379503977531182904927)
  ·
    refine ⟨65525069255966296774357391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43683379503977531182904927 65525069255966296774357391)
    ·
      refine ⟨98287603883949445161536087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65525069255966296774357391 98287603883949445161536087)
      ·
        refine ⟨147431405825924167742304131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98287603883949445161536087 147431405825924167742304131)
        ·
          refine ⟨221147108738886251613456197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147431405825924167742304131 221147108738886251613456197)
          ·
            refine ⟨41465082888541172177523037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 221147108738886251613456197 41465082888541172177523037)
            ·
              refine ⟨15549406083202939566571139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41465082888541172177523037 15549406083202939566571139)
              ·
                refine ⟨23324109124804409349856709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15549406083202939566571139 23324109124804409349856709)
                ·
                  refine ⟨4373270460900826753098133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23324109124804409349856709 4373270460900826753098133)
                  ·
                    refine ⟨204997052854726254051475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4373270460900826753098133 204997052854726254051475)
                    ·
                      rfl

theorem cell23_1197691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 6].length) (baseStart_1197691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197691 prefixEnd_1197691 := by exact prefixLift 1197691
  have htrace : WordTrace (prefixWord ++ tailWord_1197691) baseStart_1197691 baseEnd_1197691 := by
    simpa [prefixWord, tailWord_1197691, baseEnd_1197691] using wordTrace_append hprefix tailTrace_1197691
  have hstable : (prefixWord ++ tailWord_1197691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197691).length < 2 ^ (prefixWord ++ tailWord_1197691).sum := by decide
  have hdescent : baseEnd_1197691 < baseStart_1197691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197715 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 8, 2, 2]
def baseStart_1197715 : Nat := 118140960795 + 1197715 * 2 ^ 59
def prefixEnd_1197715 : Nat := 4983230072969 + 3 ^ 40 * 1197715 * 2
def baseEnd_1197715 : Nat := 615003482099886668254315

theorem tailTrace_1197715 : CollatzResearch.WordTrace tailWord_1197715 prefixEnd_1197715 615003482099886668254315 := by
  unfold tailWord_1197715
  simp only [CollatzResearch.WordTrace]
  refine ⟨43684254855890583281778599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29122836570593722187852399 43684254855890583281778599)
  ·
    refine ⟨65526382283835874922667899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43684254855890583281778599 65526382283835874922667899)
    ·
      refine ⟨98289573425753812384001849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65526382283835874922667899 98289573425753812384001849)
      ·
        refine ⟨73717180069315359288001387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98289573425753812384001849 73717180069315359288001387)
        ·
          refine ⟨110575770103973038932002081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73717180069315359288001387 110575770103973038932002081)
          ·
            refine ⟨82931827577979779199001561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110575770103973038932002081 82931827577979779199001561)
            ·
              refine ⟨62198870683484834399251171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82931827577979779199001561 62198870683484834399251171)
              ·
                refine ⟨93298306025227251598876757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62198870683484834399251171 93298306025227251598876757)
                ·
                  refine ⟨1093339523733131854674337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 93298306025227251598876757 1093339523733131854674337)
                  ·
                    refine ⟨820004642799848891005753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1093339523733131854674337 820004642799848891005753)
                    ·
                      refine ⟨615003482099886668254315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820004642799848891005753 615003482099886668254315)
                      ·
                        rfl

theorem cell23_1197715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 2, 2].length) (baseStart_1197715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197715 prefixEnd_1197715 := by exact prefixLift 1197715
  have htrace : WordTrace (prefixWord ++ tailWord_1197715) baseStart_1197715 baseEnd_1197715 := by
    simpa [prefixWord, tailWord_1197715, baseEnd_1197715] using wordTrace_append hprefix tailTrace_1197715
  have hstable : (prefixWord ++ tailWord_1197715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197715).length < 2 ^ (prefixWord ++ tailWord_1197715).sum := by decide
  have hdescent : baseEnd_1197715 < baseStart_1197715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197721 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 9]
def baseStart_1197721 : Nat := 118140960795 + 1197721 * 2 ^ 59
def prefixEnd_1197721 : Nat := 4983230072969 + 3 ^ 40 * 1197721 * 2
def baseEnd_1197721 : Nat := 68334062553757071642143

theorem tailTrace_1197721 : CollatzResearch.WordTrace tailWord_1197721 prefixEnd_1197721 68334062553757071642143 := by
  unfold tailWord_1197721
  simp only [CollatzResearch.WordTrace]
  refine ⟨43684473693868846306497017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29122982462579230870998011 43684473693868846306497017)
  ·
    refine ⟨32763355270401634729872763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43684473693868846306497017 32763355270401634729872763)
    ·
      refine ⟨49145032905602452094809145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32763355270401634729872763 49145032905602452094809145)
      ·
        refine ⟨36858774679201839071106859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49145032905602452094809145 36858774679201839071106859)
        ·
          refine ⟨55288162018802758606660289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36858774679201839071106859 55288162018802758606660289)
          ·
            refine ⟨41466121514102068954995217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55288162018802758606660289 41466121514102068954995217)
            ·
              refine ⟨31099591135576551716246413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41466121514102068954995217 31099591135576551716246413)
              ·
                refine ⟨11662346675841206893592405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31099591135576551716246413 11662346675841206893592405)
                ·
                  refine ⟨68334062553757071642143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11662346675841206893592405 68334062553757071642143)
                  ·
                    rfl

theorem cell23_1197721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 9].length) (baseStart_1197721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197721 prefixEnd_1197721 := by exact prefixLift 1197721
  have htrace : WordTrace (prefixWord ++ tailWord_1197721) baseStart_1197721 baseEnd_1197721 := by
    simpa [prefixWord, tailWord_1197721, baseEnd_1197721] using wordTrace_append hprefix tailTrace_1197721
  have hstable : (prefixWord ++ tailWord_1197721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197721).length < 2 ^ (prefixWord ++ tailWord_1197721).sum := by decide
  have hdescent : baseEnd_1197721 < baseStart_1197721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197732 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_1197732 : Nat := 118140960795 + 1197732 * 2 ^ 59
def prefixEnd_1197732 : Nat := 4983230072969 + 3 ^ 40 * 1197732 * 2
def baseEnd_1197732 : Nat := 615012211271013101741737

theorem tailTrace_1197732 : CollatzResearch.WordTrace tailWord_1197732 prefixEnd_1197732 615012211271013101741737 := by
  unfold tailWord_1197732
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842437448414497592573725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29123249931219330123431633 21842437448414497592573725)
  ·
    refine ⟨8190914043155436597215147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21842437448414497592573725 8190914043155436597215147)
    ·
      refine ⟨12286371064733154895822721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8190914043155436597215147 12286371064733154895822721)
      ·
        refine ⟨9214778298549866171867041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12286371064733154895822721 9214778298549866171867041)
        ·
          refine ⟨6911083723912399628900281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9214778298549866171867041 6911083723912399628900281)
          ·
            refine ⟨5183312792934299721675211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6911083723912399628900281 5183312792934299721675211)
            ·
              refine ⟨7774969189401449582512817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5183312792934299721675211 7774969189401449582512817)
              ·
                refine ⟨5831226892051087186884613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7774969189401449582512817 5831226892051087186884613)
                ·
                  refine ⟨1093355042259578847540865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5831226892051087186884613 1093355042259578847540865)
                  ·
                    refine ⟨820016281694684135655649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1093355042259578847540865 820016281694684135655649)
                    ·
                      refine ⟨615012211271013101741737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820016281694684135655649 615012211271013101741737)
                      ·
                        rfl

theorem cell23_1197732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_1197732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197732 prefixEnd_1197732 := by exact prefixLift 1197732
  have htrace : WordTrace (prefixWord ++ tailWord_1197732) baseStart_1197732 baseEnd_1197732 := by
    simpa [prefixWord, tailWord_1197732, baseEnd_1197732] using wordTrace_append hprefix tailTrace_1197732
  have hstable : (prefixWord ++ tailWord_1197732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197732).length < 2 ^ (prefixWord ++ tailWord_1197732).sum := by decide
  have hdescent : baseEnd_1197732 < baseStart_1197732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197768 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 4, 5]
def baseStart_1197768 : Nat := 118140960795 + 1197768 * 2 ^ 59
def prefixEnd_1197768 : Nat := 4983230072969 + 3 ^ 40 * 1197768 * 2
def baseEnd_1197768 : Nat := 205010232191524986963857

theorem tailTrace_1197768 : CollatzResearch.WordTrace tailWord_1197768 prefixEnd_1197768 205010232191524986963857 := by
  unfold tailWord_1197768
  simp only [CollatzResearch.WordTrace]
  refine ⟨21843093962349286666728979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29124125283132382222305305 21843093962349286666728979)
  ·
    refine ⟨32764640943523930000093469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21843093962349286666728979 32764640943523930000093469)
    ·
      refine ⟨12286740353821473750035051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32764640943523930000093469 12286740353821473750035051)
      ·
        refine ⟨18430110530732210625052577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12286740353821473750035051 18430110530732210625052577)
        ·
          refine ⟨13822582898049157968789433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18430110530732210625052577 13822582898049157968789433)
          ·
            refine ⟨10366937173536868476592075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13822582898049157968789433 10366937173536868476592075)
            ·
              refine ⟨15550405760305302714888113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10366937173536868476592075 15550405760305302714888113)
              ·
                refine ⟨11662804320228977036166085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15550405760305302714888113 11662804320228977036166085)
                ·
                  refine ⟨2186775810042933194281141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11662804320228977036166085 2186775810042933194281141)
                  ·
                    refine ⟨205010232191524986963857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2186775810042933194281141 205010232191524986963857)
                    ·
                      rfl

theorem cell23_1197768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_1197768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197768 prefixEnd_1197768 := by exact prefixLift 1197768
  have htrace : WordTrace (prefixWord ++ tailWord_1197768) baseStart_1197768 baseEnd_1197768 := by
    simpa [prefixWord, tailWord_1197768, baseEnd_1197768] using wordTrace_append hprefix tailTrace_1197768
  have hstable : (prefixWord ++ tailWord_1197768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197768).length < 2 ^ (prefixWord ++ tailWord_1197768).sum := by decide
  have hdescent : baseEnd_1197768 < baseStart_1197768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197785 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 2, 5]
def baseStart_1197785 : Nat := 118140960795 + 1197785 * 2 ^ 59
def prefixEnd_1197785 : Nat := 4983230072969 + 3 ^ 40 * 1197785 * 2
def baseEnd_1197785 : Nat := 205013141915233798126331

theorem tailTrace_1197785 : CollatzResearch.WordTrace tailWord_1197785 prefixEnd_1197785 205013141915233798126331 := by
  unfold tailWord_1197785
  simp only [CollatzResearch.WordTrace]
  refine ⟨43686807965636985236826809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29124538643757990157884539 43686807965636985236826809)
  ·
    refine ⟨32765105974227738927620107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43686807965636985236826809 32765105974227738927620107)
    ·
      refine ⟨49147658961341608391430161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32765105974227738927620107 49147658961341608391430161)
      ·
        refine ⟨36860744221006206293572621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49147658961341608391430161 36860744221006206293572621)
        ·
          refine ⟨13822779082877327360089733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36860744221006206293572621 13822779082877327360089733)
          ·
            refine ⟨2591771078039498880016825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13822779082877327360089733 2591771078039498880016825)
            ·
              refine ⟨1943828308529624160012619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2591771078039498880016825 1943828308529624160012619)
              ·
                refine ⟨2915742462794436240018929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943828308529624160012619 2915742462794436240018929)
                ·
                  refine ⟨2186806847095827180014197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2915742462794436240018929 2186806847095827180014197)
                  ·
                    refine ⟨205013141915233798126331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2186806847095827180014197 205013141915233798126331)
                    ·
                      rfl

theorem cell23_1197785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_1197785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197785 prefixEnd_1197785 := by exact prefixLift 1197785
  have htrace : WordTrace (prefixWord ++ tailWord_1197785) baseStart_1197785 baseEnd_1197785 := by
    simpa [prefixWord, tailWord_1197785, baseEnd_1197785] using wordTrace_append hprefix tailTrace_1197785
  have hstable : (prefixWord ++ tailWord_1197785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197785).length < 2 ^ (prefixWord ++ tailWord_1197785).sum := by decide
  have hdescent : baseEnd_1197785 < baseStart_1197785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197818 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_1197818 : Nat := 118140960795 + 1197818 * 2 ^ 59
def prefixEnd_1197818 : Nat := 4983230072969 + 3 ^ 40 * 1197818 * 2
def baseEnd_1197818 : Nat := 615056370607299765266341

theorem tailTrace_1197818 : CollatzResearch.WordTrace tailWord_1197818 prefixEnd_1197818 615056370607299765266341 := by
  unfold tailWord_1197818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10922002893629357968194527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29125341049678287915185405 10922002893629357968194527)
  ·
    refine ⟨16383004340444036952291791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10922002893629357968194527 16383004340444036952291791)
    ·
      refine ⟨24574506510666055428437687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16383004340444036952291791 24574506510666055428437687)
      ·
        refine ⟨36861759765999083142656531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24574506510666055428437687 36861759765999083142656531)
        ·
          refine ⟨55292639648998624713984797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36861759765999083142656531 55292639648998624713984797)
          ·
            refine ⟨20734739868374484267744299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55292639648998624713984797 20734739868374484267744299)
            ·
              refine ⟨31102109802561726401616449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20734739868374484267744299 31102109802561726401616449)
              ·
                refine ⟨23326582351921294801212337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31102109802561726401616449 23326582351921294801212337)
                ·
                  refine ⟨17494936763940971100909253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23326582351921294801212337 17494936763940971100909253)
                  ·
                    refine ⟨3280300643238932081420485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17494936763940971100909253 3280300643238932081420485)
                    ·
                      refine ⟨615056370607299765266341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3280300643238932081420485 615056370607299765266341)
                      ·
                        rfl

theorem cell23_1197818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_1197818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197818 prefixEnd_1197818 := by exact prefixLift 1197818
  have htrace : WordTrace (prefixWord ++ tailWord_1197818) baseStart_1197818 baseEnd_1197818 := by
    simpa [prefixWord, tailWord_1197818, baseEnd_1197818] using wordTrace_append hprefix tailTrace_1197818
  have hstable : (prefixWord ++ tailWord_1197818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197818).length < 2 ^ (prefixWord ++ tailWord_1197818).sum := by decide
  have hdescent : baseEnd_1197818 < baseStart_1197818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197825 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1197825 : Nat := 118140960795 + 1197825 * 2 ^ 59
def prefixEnd_1197825 : Nat := 4983230072969 + 3 ^ 40 * 1197825 * 2
def baseEnd_1197825 : Nat := 615059964971881237878809

theorem tailTrace_1197825 : CollatzResearch.WordTrace tailWord_1197825 prefixEnd_1197825 615059964971881237878809 := by
  unfold tailWord_1197825
  simp only [CollatzResearch.WordTrace]
  refine ⟨43688266885492072068282929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29125511256994714712188619 43688266885492072068282929)
  ·
    refine ⟨32766200164119054051212197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43688266885492072068282929 32766200164119054051212197)
    ·
      refine ⟨6143662530772322634602287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32766200164119054051212197 6143662530772322634602287)
      ·
        refine ⟨9215493796158483951903431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6143662530772322634602287 9215493796158483951903431)
        ·
          refine ⟨13823240694237725927855147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9215493796158483951903431 13823240694237725927855147)
          ·
            refine ⟨20734861041356588891782721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13823240694237725927855147 20734861041356588891782721)
            ·
              refine ⟨15551145781017441668837041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20734861041356588891782721 15551145781017441668837041)
              ·
                refine ⟨11663359335763081251627781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15551145781017441668837041 11663359335763081251627781)
                ·
                  refine ⟨2186879875455577734680209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11663359335763081251627781 2186879875455577734680209)
                  ·
                    refine ⟨1640159906591683301010157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2186879875455577734680209 1640159906591683301010157)
                    ·
                      refine ⟨615059964971881237878809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640159906591683301010157 615059964971881237878809)
                      ·
                        rfl

theorem cell23_1197825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1197825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197825 prefixEnd_1197825 := by exact prefixLift 1197825
  have htrace : WordTrace (prefixWord ++ tailWord_1197825) baseStart_1197825 baseEnd_1197825 := by
    simpa [prefixWord, tailWord_1197825, baseEnd_1197825] using wordTrace_append hprefix tailTrace_1197825
  have hstable : (prefixWord ++ tailWord_1197825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197825).length < 2 ^ (prefixWord ++ tailWord_1197825).sum := by decide
  have hdescent : baseEnd_1197825 < baseStart_1197825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197865 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 5, 5, 2]
def baseStart_1197865 : Nat := 118140960795 + 1197865 * 2 ^ 59
def prefixEnd_1197865 : Nat := 4983230072969 + 3 ^ 40 * 1197865 * 2
def baseEnd_1197865 : Nat := 615080504198061081378625

theorem tailTrace_1197865 : CollatzResearch.WordTrace tailWord_1197865 prefixEnd_1197865 615080504198061081378625 := by
  unfold tailWord_1197865
  simp only [CollatzResearch.WordTrace]
  refine ⟨43689725805347158899739049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29126483870231439266492699 43689725805347158899739049)
  ·
    refine ⟨32767294354010369174804287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43689725805347158899739049 32767294354010369174804287)
    ·
      refine ⟨49150941531015553762206431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32767294354010369174804287 49150941531015553762206431)
      ·
        refine ⟨73726412296523330643309647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49150941531015553762206431 73726412296523330643309647)
        ·
          refine ⟨110589618444784995964964471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73726412296523330643309647 110589618444784995964964471)
          ·
            refine ⟨165884427667177493947446707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110589618444784995964964471 165884427667177493947446707)
            ·
              refine ⟨248826641500766240921170061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165884427667177493947446707 248826641500766240921170061)
              ·
                refine ⟨93309990562787340345438773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248826641500766240921170061 93309990562787340345438773)
                ·
                  refine ⟨8747811615261313157384885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93309990562787340345438773 8747811615261313157384885)
                  ·
                    refine ⟨820107338930748108504833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8747811615261313157384885 820107338930748108504833)
                    ·
                      refine ⟨615080504198061081378625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820107338930748108504833 615080504198061081378625)
                      ·
                        rfl

theorem cell23_1197865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 5, 2].length) (baseStart_1197865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197865 prefixEnd_1197865 := by exact prefixLift 1197865
  have htrace : WordTrace (prefixWord ++ tailWord_1197865) baseStart_1197865 baseEnd_1197865 := by
    simpa [prefixWord, tailWord_1197865, baseEnd_1197865] using wordTrace_append hprefix tailTrace_1197865
  have hstable : (prefixWord ++ tailWord_1197865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197865).length < 2 ^ (prefixWord ++ tailWord_1197865).sum := by decide
  have hdescent : baseEnd_1197865 < baseStart_1197865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197882 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2]
def baseStart_1197882 : Nat := 118140960795 + 1197882 * 2 ^ 59
def prefixEnd_1197882 : Nat := 4983230072969 + 3 ^ 40 * 1197882 * 2
def baseEnd_1197882 : Nat := 615089233369187514866047

theorem tailTrace_1197882 : CollatzResearch.WordTrace tailWord_1197882 prefixEnd_1197882 615089233369187514866047 := by
  unfold tailWord_1197882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10922586461571392700776975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29126897230857047202071933 10922586461571392700776975)
  ·
    refine ⟨16383879692357089051165463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10922586461571392700776975 16383879692357089051165463)
    ·
      refine ⟨24575819538535633576748195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16383879692357089051165463 24575819538535633576748195)
      ·
        refine ⟨36863729307803450365122293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24575819538535633576748195 36863729307803450365122293)
        ·
          refine ⟨3455974622606573471730215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36863729307803450365122293 3455974622606573471730215)
          ·
            refine ⟨5183961933909860207595323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455974622606573471730215 5183961933909860207595323)
            ·
              refine ⟨7775942900864790311392985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5183961933909860207595323 7775942900864790311392985)
              ·
                refine ⟨5831957175648592733544739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7775942900864790311392985 5831957175648592733544739)
                ·
                  refine ⟨8747935763472889100317109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5831957175648592733544739 8747935763472889100317109)
                  ·
                    refine ⟨820118977825583353154729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8747935763472889100317109 820118977825583353154729)
                    ·
                      refine ⟨615089233369187514866047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820118977825583353154729 615089233369187514866047)
                      ·
                        rfl

theorem cell23_1197882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_1197882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197882 prefixEnd_1197882 := by exact prefixLift 1197882
  have htrace : WordTrace (prefixWord ++ tailWord_1197882) baseStart_1197882 baseEnd_1197882 := by
    simpa [prefixWord, tailWord_1197882, baseEnd_1197882] using wordTrace_append hprefix tailTrace_1197882
  have hstable : (prefixWord ++ tailWord_1197882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197882).length < 2 ^ (prefixWord ++ tailWord_1197882).sum := by decide
  have hdescent : baseEnd_1197882 < baseStart_1197882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197895 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1197895 : Nat := 118140960795 + 1197895 * 2 ^ 59
def prefixEnd_1197895 : Nat := 4983230072969 + 3 ^ 40 * 1197895 * 2
def baseEnd_1197895 : Nat := 615095908617695964003487

theorem tailTrace_1197895 : CollatzResearch.WordTrace tailWord_1197895 prefixEnd_1197895 615095908617695964003487 := by
  unfold tailWord_1197895
  simp only [CollatzResearch.WordTrace]
  refine ⟨43690819995238474023331139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29127213330158982682220759 43690819995238474023331139)
  ·
    refine ⟨65536229992857711034996709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43690819995238474023331139 65536229992857711034996709)
    ·
      refine ⟨12288043123660820819061883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65536229992857711034996709 12288043123660820819061883)
      ·
        refine ⟨18432064685491231228592825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12288043123660820819061883 18432064685491231228592825)
        ·
          refine ⟨13824048514118423421444619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18432064685491231228592825 13824048514118423421444619)
          ·
            refine ⟨20736072771177635132166929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13824048514118423421444619 20736072771177635132166929)
            ·
              refine ⟨15552054578383226349125197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20736072771177635132166929 15552054578383226349125197)
              ·
                refine ⟨5832020466893709880921949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15552054578383226349125197 5832020466893709880921949)
                ·
                  refine ⟨2187007675085141205345731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5832020466893709880921949 2187007675085141205345731)
                  ·
                    refine ⟨3280511512627711808018597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2187007675085141205345731 3280511512627711808018597)
                    ·
                      refine ⟨615095908617695964003487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3280511512627711808018597 615095908617695964003487)
                      ·
                        rfl

theorem cell23_1197895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1197895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197895 prefixEnd_1197895 := by exact prefixLift 1197895
  have htrace : WordTrace (prefixWord ++ tailWord_1197895) baseStart_1197895 baseEnd_1197895 := by
    simpa [prefixWord, tailWord_1197895, baseEnd_1197895] using wordTrace_append hprefix tailTrace_1197895
  have hstable : (prefixWord ++ tailWord_1197895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197895).length < 2 ^ (prefixWord ++ tailWord_1197895).sum := by decide
  have hdescent : baseEnd_1197895 < baseStart_1197895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197906 : List Nat := [3, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_1197906 : Nat := 118140960795 + 1197906 * 2 ^ 59
def prefixEnd_1197906 : Nat := 4983230072969 + 3 ^ 40 * 1197906 * 2
def baseEnd_1197906 : Nat := 615101556904895420965937

theorem tailTrace_1197906 : CollatzResearch.WordTrace tailWord_1197906 prefixEnd_1197906 615101556904895420965937 := by
  unfold tailWord_1197906
  simp only [CollatzResearch.WordTrace]
  refine ⟨10922805299549655725495393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29127480798799081934654381 10922805299549655725495393)
  ·
    refine ⟨8192103974662241794121545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10922805299549655725495393 8192103974662241794121545)
    ·
      refine ⟨6144077980996681345591159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8192103974662241794121545 6144077980996681345591159)
      ·
        refine ⟨9216116971495022018386739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6144077980996681345591159 9216116971495022018386739)
        ·
          refine ⟨13824175457242533027580109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9216116971495022018386739 13824175457242533027580109)
          ·
            refine ⟨5184065796465949885342541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13824175457242533027580109 5184065796465949885342541)
            ·
              refine ⟨1944024673674731207003453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5184065796465949885342541 1944024673674731207003453)
              ·
                refine ⟨729009252628024202626295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1944024673674731207003453 729009252628024202626295)
                ·
                  refine ⟨1093513878942036303939443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729009252628024202626295 1093513878942036303939443)
                  ·
                    refine ⟨1640270818413054455909165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1093513878942036303939443 1640270818413054455909165)
                    ·
                      refine ⟨615101556904895420965937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640270818413054455909165 615101556904895420965937)
                      ·
                        rfl

theorem cell23_1197906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_1197906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197906 prefixEnd_1197906 := by exact prefixLift 1197906
  have htrace : WordTrace (prefixWord ++ tailWord_1197906) baseStart_1197906 baseEnd_1197906 := by
    simpa [prefixWord, tailWord_1197906, baseEnd_1197906] using wordTrace_append hprefix tailTrace_1197906
  have hstable : (prefixWord ++ tailWord_1197906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197906).length < 2 ^ (prefixWord ++ tailWord_1197906).sum := by decide
  have hdescent : baseEnd_1197906 < baseStart_1197906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197916 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_1197916 : Nat := 118140960795 + 1197916 * 2 ^ 59
def prefixEnd_1197916 : Nat := 4983230072969 + 3 ^ 40 * 1197916 * 2
def baseEnd_1197916 : Nat := 615106691711440381840891

theorem tailTrace_1197916 : CollatzResearch.WordTrace tailWord_1197916 prefixEnd_1197916 615106691711440381840891 := by
  unfold tailWord_1197916
  simp only [CollatzResearch.WordTrace]
  refine ⟨21845792964081197304922801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29127723952108263073230401 21845792964081197304922801)
  ·
    refine ⟨16384344723060897978692101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21845792964081197304922801 16384344723060897978692101)
    ·
      refine ⟨3072064635573918371004769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16384344723060897978692101 3072064635573918371004769)
      ·
        refine ⟨2304048476680438778253577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3072064635573918371004769 2304048476680438778253577)
        ·
          refine ⟨1728036357510329083690183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2304048476680438778253577 1728036357510329083690183)
          ·
            refine ⟨2592054536265493625535275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728036357510329083690183 2592054536265493625535275)
            ·
              refine ⟨3888081804398240438302913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592054536265493625535275 3888081804398240438302913)
              ·
                refine ⟨2916061353298680328727185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888081804398240438302913 2916061353298680328727185)
                ·
                  refine ⟨2187046014974010246545389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2916061353298680328727185 2187046014974010246545389)
                  ·
                    refine ⟨820142255615253842454521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2187046014974010246545389 820142255615253842454521)
                    ·
                      refine ⟨615106691711440381840891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820142255615253842454521 615106691711440381840891)
                      ·
                        rfl

theorem cell23_1197916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_1197916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197916 prefixEnd_1197916 := by exact prefixLift 1197916
  have htrace : WordTrace (prefixWord ++ tailWord_1197916) baseStart_1197916 baseEnd_1197916 := by
    simpa [prefixWord, tailWord_1197916, baseEnd_1197916] using wordTrace_append hprefix tailTrace_1197916
  have hstable : (prefixWord ++ tailWord_1197916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197916).length < 2 ^ (prefixWord ++ tailWord_1197916).sum := by decide
  have hdescent : baseEnd_1197916 < baseStart_1197916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197923 : List Nat := [1, 1, 1, 5, 4, 1, 3, 2, 1, 1, 3]
def baseStart_1197923 : Nat := 118140960795 + 1197923 * 2 ^ 59
def prefixEnd_1197923 : Nat := 4983230072969 + 3 ^ 40 * 1197923 * 2
def baseEnd_1197923 : Nat := 615110286076021854453359

theorem tailTrace_1197923 : CollatzResearch.WordTrace tailWord_1197923 prefixEnd_1197923 615110286076021854453359 := by
  unfold tailWord_1197923
  simp only [CollatzResearch.WordTrace]
  refine ⟨43691841239137034805350423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29127894159424689870233615 43691841239137034805350423)
  ·
    refine ⟨65537761858705552208025635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43691841239137034805350423 65537761858705552208025635)
    ·
      refine ⟨98306642788058328312038453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65537761858705552208025635 98306642788058328312038453)
      ·
        refine ⟨9216247761380468279253605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98306642788058328312038453 9216247761380468279253605)
        ·
          refine ⟨1728046455258837802360051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9216247761380468279253605 1728046455258837802360051)
          ·
            refine ⟨2592069682888256703540077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728046455258837802360051 2592069682888256703540077)
            ·
              refine ⟨972026131083096263827529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2592069682888256703540077 972026131083096263827529)
              ·
                refine ⟨729019598312322197870647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972026131083096263827529 729019598312322197870647)
                ·
                  refine ⟨1093529397468483296805971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729019598312322197870647 1093529397468483296805971)
                  ·
                    refine ⟨1640294096202724945208957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1093529397468483296805971 1640294096202724945208957)
                    ·
                      refine ⟨615110286076021854453359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640294096202724945208957 615110286076021854453359)
                      ·
                        rfl

theorem cell23_1197923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_1197923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197923 prefixEnd_1197923 := by exact prefixLift 1197923
  have htrace : WordTrace (prefixWord ++ tailWord_1197923) baseStart_1197923 baseEnd_1197923 := by
    simpa [prefixWord, tailWord_1197923, baseEnd_1197923] using wordTrace_append hprefix tailTrace_1197923
  have hstable : (prefixWord ++ tailWord_1197923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197923).length < 2 ^ (prefixWord ++ tailWord_1197923).sum := by decide
  have hdescent : baseEnd_1197923 < baseStart_1197923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197966 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1197966 : Nat := 118140960795 + 1197966 * 2 ^ 59
def prefixEnd_1197966 : Nat := 4983230072969 + 3 ^ 40 * 1197966 * 2
def baseEnd_1197966 : Nat := 615132365744165186215661

theorem tailTrace_1197966 : CollatzResearch.WordTrace tailWord_1197966 prefixEnd_1197966 615132365744165186215661 := by
  unfold tailWord_1197966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461676197247656643645719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29128939718654168766110501 5461676197247656643645719)
  ·
    refine ⟨8192514295871484965468579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5461676197247656643645719 8192514295871484965468579)
    ·
      refine ⟨12288771443807227448202869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8192514295871484965468579 12288771443807227448202869)
      ·
        refine ⟨1152072322856927573269019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12288771443807227448202869 1152072322856927573269019)
        ·
          refine ⟨1728108484285391359903529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152072322856927573269019 1728108484285391359903529)
          ·
            refine ⟨1296081363214043519927647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728108484285391359903529 1296081363214043519927647)
            ·
              refine ⟨1944122044821065279891471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296081363214043519927647 1944122044821065279891471)
              ·
                refine ⟨2916183067231597919837207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944122044821065279891471 2916183067231597919837207)
                ·
                  refine ⟨4374274600847396879755811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916183067231597919837207 4374274600847396879755811)
                  ·
                    refine ⟨6561411901271095319633717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4374274600847396879755811 6561411901271095319633717)
                    ·
                      refine ⟨615132365744165186215661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6561411901271095319633717 615132365744165186215661)
                      ·
                        rfl

theorem cell23_1197966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1197966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197966 prefixEnd_1197966 := by exact prefixLift 1197966
  have htrace : WordTrace (prefixWord ++ tailWord_1197966) baseStart_1197966 baseEnd_1197966 := by
    simpa [prefixWord, tailWord_1197966, baseEnd_1197966] using wordTrace_append hprefix tailTrace_1197966
  have hstable : (prefixWord ++ tailWord_1197966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197966).length < 2 ^ (prefixWord ++ tailWord_1197966).sum := by decide
  have hdescent : baseEnd_1197966 < baseStart_1197966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197974 : List Nat := [5, 3, 1, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1197974 : Nat := 118140960795 + 1197974 * 2 ^ 59
def prefixEnd_1197974 : Nat := 4983230072969 + 3 ^ 40 * 1197974 * 2
def baseEnd_1197974 : Nat := 615136473589401154915625

theorem tailTrace_1197974 : CollatzResearch.WordTrace tailWord_1197974 prefixEnd_1197974 615136473589401154915625 := by
  unfold tailWord_1197974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730856335122016907216061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29129134241301513676971317 2730856335122016907216061)
  ·
    refine ⟨1024071125670756340206023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2730856335122016907216061 1024071125670756340206023)
    ·
      refine ⟨1536106688506134510309035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024071125670756340206023 1536106688506134510309035)
      ·
        refine ⟨2304160032759201765463553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536106688506134510309035 2304160032759201765463553)
        ·
          refine ⟨1728120024569401324097665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2304160032759201765463553 1728120024569401324097665)
          ·
            refine ⟨1296090018427050993073249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728120024569401324097665 1296090018427050993073249)
            ·
              refine ⟨972067513820288244804937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1296090018427050993073249 972067513820288244804937)
              ·
                refine ⟨729050635365216183603703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972067513820288244804937 729050635365216183603703)
                ·
                  refine ⟨1093575953047824275405555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729050635365216183603703 1093575953047824275405555)
                  ·
                    refine ⟨1640363929571736413108333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1093575953047824275405555 1640363929571736413108333)
                    ·
                      refine ⟨615136473589401154915625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640363929571736413108333 615136473589401154915625)
                      ·
                        rfl

theorem cell23_1197974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1197974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197974 prefixEnd_1197974 := by exact prefixLift 1197974
  have htrace : WordTrace (prefixWord ++ tailWord_1197974) baseStart_1197974 baseEnd_1197974 := by
    simpa [prefixWord, tailWord_1197974, baseEnd_1197974] using wordTrace_append hprefix tailTrace_1197974
  have hstable : (prefixWord ++ tailWord_1197974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197974).length < 2 ^ (prefixWord ++ tailWord_1197974).sum := by decide
  have hdescent : baseEnd_1197974 < baseStart_1197974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197980 : List Nat := [2, 2, 3, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1197980 : Nat := 118140960795 + 1197980 * 2 ^ 59
def prefixEnd_1197980 : Nat := 4983230072969 + 3 ^ 40 * 1197980 * 2
def baseEnd_1197980 : Nat := 615139554473328131440597

theorem tailTrace_1197980 : CollatzResearch.WordTrace tailWord_1197980 prefixEnd_1197980 615139554473328131440597 := by
  unfold tailWord_1197980
  simp only [CollatzResearch.WordTrace]
  refine ⟨21846960099965266770087697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29129280133287022360116929 21846960099965266770087697)
  ·
    refine ⟨16385220074973950077565773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21846960099965266770087697 16385220074973950077565773)
    ·
      refine ⟨6144457528115231279087165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16385220074973950077565773 6144457528115231279087165)
      ·
        refine ⟨2304171573043211729657687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6144457528115231279087165 2304171573043211729657687)
        ·
          refine ⟨3456257359564817594486531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304171573043211729657687 3456257359564817594486531)
          ·
            refine ⟨5184386039347226391729797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3456257359564817594486531 5184386039347226391729797)
            ·
              refine ⟨972072382377604948449337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5184386039347226391729797 972072382377604948449337)
              ·
                refine ⟨729054286783203711337003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972072382377604948449337 729054286783203711337003)
                ·
                  refine ⟨1093581430174805567005505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729054286783203711337003 1093581430174805567005505)
                  ·
                    refine ⟨820186072631104175254129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1093581430174805567005505 820186072631104175254129)
                    ·
                      refine ⟨615139554473328131440597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820186072631104175254129 615139554473328131440597)
                      ·
                        rfl

theorem cell23_1197980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1197980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1197980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1197980 prefixEnd_1197980 := by exact prefixLift 1197980
  have htrace : WordTrace (prefixWord ++ tailWord_1197980) baseStart_1197980 baseEnd_1197980 := by
    simpa [prefixWord, tailWord_1197980, baseEnd_1197980] using wordTrace_append hprefix tailTrace_1197980
  have hstable : (prefixWord ++ tailWord_1197980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197980).length < 2 ^ (prefixWord ++ tailWord_1197980).sum := by decide
  have hdescent : baseEnd_1197980 < baseStart_1197980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198015 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_1198015 : Nat := 118140960795 + 1198015 * 2 ^ 59
def prefixEnd_1198015 : Nat := 4983230072969 + 3 ^ 40 * 1198015 * 2
def baseEnd_1198015 : Nat := 615157526296235494502935

theorem tailTrace_1198015 : CollatzResearch.WordTrace tailWord_1198015 prefixEnd_1198015 615157526296235494502935 := by
  unfold tailWord_1198015
  simp only [CollatzResearch.WordTrace]
  refine ⟨43695196754803734517699499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29130131169869156345132999 43695196754803734517699499)
  ·
    refine ⟨65542795132205601776549249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43695196754803734517699499 65542795132205601776549249)
    ·
      refine ⟨49157096349154201332411937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65542795132205601776549249 49157096349154201332411937)
      ·
        refine ⟨36867822261865650999308953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49157096349154201332411937 36867822261865650999308953)
        ·
          refine ⟨27650866696399238249481715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36867822261865650999308953 27650866696399238249481715)
          ·
            refine ⟨41476300044598857374222573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27650866696399238249481715 41476300044598857374222573)
            ·
              refine ⟨15553612516724571515333465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41476300044598857374222573 15553612516724571515333465)
              ·
                refine ⟨11665209387543428636500099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15553612516724571515333465 11665209387543428636500099)
                ·
                  refine ⟨17497814081315142954750149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11665209387543428636500099 17497814081315142954750149)
                  ·
                    refine ⟨3280840140246589304015653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17497814081315142954750149 3280840140246589304015653)
                    ·
                      refine ⟨615157526296235494502935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3280840140246589304015653 615157526296235494502935)
                      ·
                        rfl

theorem cell23_1198015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_1198015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198015 prefixEnd_1198015 := by exact prefixLift 1198015
  have htrace : WordTrace (prefixWord ++ tailWord_1198015) baseStart_1198015 baseEnd_1198015 := by
    simpa [prefixWord, tailWord_1198015, baseEnd_1198015] using wordTrace_append hprefix tailTrace_1198015
  have hstable : (prefixWord ++ tailWord_1198015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198015).length < 2 ^ (prefixWord ++ tailWord_1198015).sum := by decide
  have hdescent : baseEnd_1198015 < baseStart_1198015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198036 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_1198036 : Nat := 118140960795 + 1198036 * 2 ^ 59
def prefixEnd_1198036 : Nat := 4983230072969 + 3 ^ 40 * 1198036 * 2
def baseEnd_1198036 : Nat := 615168309389979912340339

theorem tailTrace_1198036 : CollatzResearch.WordTrace tailWord_1198036 prefixEnd_1198036 615168309389979912340339 := by
  unfold tailWord_1198036
  simp only [CollatzResearch.WordTrace]
  refine ⟨21847981343863827552106981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29130641791818436736142641 21847981343863827552106981)
  ·
    refine ⟨4096496501974467666020059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21847981343863827552106981 4096496501974467666020059)
    ·
      refine ⟨6144744752961701499030089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096496501974467666020059 6144744752961701499030089)
      ·
        refine ⟨4608558564721276124272567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6144744752961701499030089 4608558564721276124272567)
        ·
          refine ⟨6912837847081914186408851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608558564721276124272567 6912837847081914186408851)
          ·
            refine ⟨10369256770622871279613277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6912837847081914186408851 10369256770622871279613277)
            ·
              refine ⟨3888471288983576729854979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10369256770622871279613277 3888471288983576729854979)
              ·
                refine ⟨5832706933475365094782469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3888471288983576729854979 5832706933475365094782469)
                ·
                  refine ⟨1093632550026630955271713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5832706933475365094782469 1093632550026630955271713)
                  ·
                    refine ⟨820224412519973216453785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1093632550026630955271713 820224412519973216453785)
                    ·
                      refine ⟨615168309389979912340339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820224412519973216453785 615168309389979912340339)
                      ·
                        rfl

theorem cell23_1198036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_1198036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198036 prefixEnd_1198036 := by exact prefixLift 1198036
  have htrace : WordTrace (prefixWord ++ tailWord_1198036) baseStart_1198036 baseEnd_1198036 := by
    simpa [prefixWord, tailWord_1198036, baseEnd_1198036] using wordTrace_append hprefix tailTrace_1198036
  have hstable : (prefixWord ++ tailWord_1198036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198036).length < 2 ^ (prefixWord ++ tailWord_1198036).sum := by decide
  have hdescent : baseEnd_1198036 < baseStart_1198036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198052 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_1198052 : Nat := 118140960795 + 1198052 * 2 ^ 59
def prefixEnd_1198052 : Nat := 4983230072969 + 3 ^ 40 * 1198052 * 2
def baseEnd_1198052 : Nat := 615176525080451849740265

theorem tailTrace_1198052 : CollatzResearch.WordTrace tailWord_1198052 prefixEnd_1198052 615176525080451849740265 := by
  unfold tailWord_1198052
  simp only [CollatzResearch.WordTrace]
  refine ⟨21848273127834844918398205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29131030837113126557864273 21848273127834844918398205)
  ·
    refine ⟨8193102422938066844399327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21848273127834844918398205 8193102422938066844399327)
    ·
      refine ⟨12289653634407100266598991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8193102422938066844399327 12289653634407100266598991)
      ·
        refine ⟨18434480451610650399898487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12289653634407100266598991 18434480451610650399898487)
        ·
          refine ⟨27651720677415975599847731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18434480451610650399898487 27651720677415975599847731)
          ·
            refine ⟨41477581016123963399771597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27651720677415975599847731 41477581016123963399771597)
            ·
              refine ⟨15554092881046486274914349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41477581016123963399771597 15554092881046486274914349)
              ·
                refine ⟨5832784830392432353092881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15554092881046486274914349 5832784830392432353092881)
                ·
                  refine ⟨4374588622794324264819661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5832784830392432353092881 4374588622794324264819661)
                  ·
                    refine ⟨1640470733547871599307373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4374588622794324264819661 1640470733547871599307373)
                    ·
                      refine ⟨615176525080451849740265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640470733547871599307373 615176525080451849740265)
                      ·
                        rfl

theorem cell23_1198052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_1198052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198052 prefixEnd_1198052 := by exact prefixLift 1198052
  have htrace : WordTrace (prefixWord ++ tailWord_1198052) baseStart_1198052 baseEnd_1198052 := by
    simpa [prefixWord, tailWord_1198052, baseEnd_1198052] using wordTrace_append hprefix tailTrace_1198052
  have hstable : (prefixWord ++ tailWord_1198052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198052).length < 2 ^ (prefixWord ++ tailWord_1198052).sum := by decide
  have hdescent : baseEnd_1198052 < baseStart_1198052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198126 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1198126 : Nat := 118140960795 + 1198126 * 2 ^ 59
def prefixEnd_1198126 : Nat := 4983230072969 + 3 ^ 40 * 1198126 * 2
def baseEnd_1198126 : Nat := 615214522648884560214925

theorem tailTrace_1198126 : CollatzResearch.WordTrace tailWord_1198126 prefixEnd_1198126 615214522648884560214925 := by
  unfold tailWord_1198126
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462405657175200059373779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29132830171601066983326821 5462405657175200059373779)
  ·
    refine ⟨8193608485762800089060669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5462405657175200059373779 8193608485762800089060669)
    ·
      refine ⟨3072603182161050033397751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8193608485762800089060669 3072603182161050033397751)
      ·
        refine ⟨4608904773241575050096627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072603182161050033397751 4608904773241575050096627)
        ·
          refine ⟨6913357159862362575144941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608904773241575050096627 6913357159862362575144941)
          ·
            refine ⟨2592508934948385965679353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6913357159862362575144941 2592508934948385965679353)
            ·
              refine ⟨1944381701211289474259515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592508934948385965679353 1944381701211289474259515)
              ·
                refine ⟨2916572551816934211389273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944381701211289474259515 2916572551816934211389273)
                ·
                  refine ⟨2187429413862700658541955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2916572551816934211389273 2187429413862700658541955)
                  ·
                    refine ⟨3281144120794050987812933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2187429413862700658541955 3281144120794050987812933)
                    ·
                      refine ⟨615214522648884560214925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3281144120794050987812933 615214522648884560214925)
                      ·
                        rfl

theorem cell23_1198126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1198126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198126 prefixEnd_1198126 := by exact prefixLift 1198126
  have htrace : WordTrace (prefixWord ++ tailWord_1198126) baseStart_1198126 baseEnd_1198126 := by
    simpa [prefixWord, tailWord_1198126, baseEnd_1198126] using wordTrace_append hprefix tailTrace_1198126
  have hstable : (prefixWord ++ tailWord_1198126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198126).length < 2 ^ (prefixWord ++ tailWord_1198126).sum := by decide
  have hdescent : baseEnd_1198126 < baseStart_1198126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198129 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_1198129 : Nat := 118140960795 + 1198129 * 2 ^ 59
def prefixEnd_1198129 : Nat := 4983230072969 + 3 ^ 40 * 1198129 * 2
def baseEnd_1198129 : Nat := 615216063090848048477411

theorem tailTrace_1198129 : CollatzResearch.WordTrace tailWord_1198129 prefixEnd_1198129 615216063090848048477411 := by
  unfold tailWord_1198129
  simp only [CollatzResearch.WordTrace]
  refine ⟨43699354676390731987349441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29132903117593821324899627 43699354676390731987349441)
  ·
    refine ⟨32774516007293048990512081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43699354676390731987349441 32774516007293048990512081)
    ·
      refine ⟨24580887005469786742884061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32774516007293048990512081 24580887005469786742884061)
      ·
        refine ⟨9217832627051170028581523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24580887005469786742884061 9217832627051170028581523)
        ·
          refine ⟨13826748940576755042872285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9217832627051170028581523 13826748940576755042872285)
          ·
            refine ⟨5185030852716283141077107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13826748940576755042872285 5185030852716283141077107)
            ·
              refine ⟨7777546279074424711615661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5185030852716283141077107 7777546279074424711615661)
              ·
                refine ⟨2916579854652909266855873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7777546279074424711615661 2916579854652909266855873)
                ·
                  refine ⟨2187434890989681950141905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2916579854652909266855873 2187434890989681950141905)
                  ·
                    refine ⟨1640576168242261462606429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2187434890989681950141905 1640576168242261462606429)
                    ·
                      refine ⟨615216063090848048477411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640576168242261462606429 615216063090848048477411)
                      ·
                        rfl

theorem cell23_1198129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_1198129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198129 prefixEnd_1198129 := by exact prefixLift 1198129
  have htrace : WordTrace (prefixWord ++ tailWord_1198129) baseStart_1198129 baseEnd_1198129 := by
    simpa [prefixWord, tailWord_1198129, baseEnd_1198129] using wordTrace_append hprefix tailTrace_1198129
  have hstable : (prefixWord ++ tailWord_1198129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198129).length < 2 ^ (prefixWord ++ tailWord_1198129).sum := by decide
  have hdescent : baseEnd_1198129 < baseStart_1198129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198169 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 1, 5, 2]
def baseStart_1198169 : Nat := 118140960795 + 1198169 * 2 ^ 59
def prefixEnd_1198169 : Nat := 4983230072969 + 3 ^ 40 * 1198169 * 2
def baseEnd_1198169 : Nat := 615236602317027891977227

theorem tailTrace_1198169 : CollatzResearch.WordTrace tailWord_1198169 prefixEnd_1198169 615236602317027891977227 := by
  unfold tailWord_1198169
  simp only [CollatzResearch.WordTrace]
  refine ⟨43700813596245818818805561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29133875730830545879203707 43700813596245818818805561)
  ·
    refine ⟨32775610197184364114104171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43700813596245818818805561 32775610197184364114104171)
    ·
      refine ⟨49163415295776546171156257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32775610197184364114104171 49163415295776546171156257)
      ·
        refine ⟨36872561471832409628367193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49163415295776546171156257 36872561471832409628367193)
        ·
          refine ⟨27654421103874307221275395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36872561471832409628367193 27654421103874307221275395)
          ·
            refine ⟨41481631655811460831913093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27654421103874307221275395 41481631655811460831913093)
            ·
              refine ⟨7777805935464648905983705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41481631655811460831913093 7777805935464648905983705)
              ·
                refine ⟨5833354451598486679487779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7777805935464648905983705 5833354451598486679487779)
                ·
                  refine ⟨8750031677397730019231669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5833354451598486679487779 8750031677397730019231669)
                  ·
                    refine ⟨820315469756037189302969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8750031677397730019231669 820315469756037189302969)
                    ·
                      refine ⟨615236602317027891977227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820315469756037189302969 615236602317027891977227)
                      ·
                        rfl

theorem cell23_1198169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_1198169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198169 prefixEnd_1198169 := by exact prefixLift 1198169
  have htrace : WordTrace (prefixWord ++ tailWord_1198169) baseStart_1198169 baseEnd_1198169 := by
    simpa [prefixWord, tailWord_1198169, baseEnd_1198169] using wordTrace_append hprefix tailTrace_1198169
  have hstable : (prefixWord ++ tailWord_1198169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198169).length < 2 ^ (prefixWord ++ tailWord_1198169).sum := by decide
  have hdescent : baseEnd_1198169 < baseStart_1198169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198176 : List Nat := [2, 1, 1, 3, 2, 4, 1, 2, 3, 1, 3]
def baseStart_1198176 : Nat := 118140960795 + 1198176 * 2 ^ 59
def prefixEnd_1198176 : Nat := 4983230072969 + 3 ^ 40 * 1198176 * 2
def baseEnd_1198176 : Nat := 615240196681609364589695

theorem tailTrace_1198176 : CollatzResearch.WordTrace tailWord_1198176 prefixEnd_1198176 615240196681609364589695 := by
  unfold tailWord_1198176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21850534453610229507155191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29134045938146972676206921 21850534453610229507155191)
  ·
    refine ⟨32775801680415344260732787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21850534453610229507155191 32775801680415344260732787)
    ·
      refine ⟨49163702520623016391099181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32775801680415344260732787 49163702520623016391099181)
      ·
        refine ⟨18436388445233631146662193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49163702520623016391099181 18436388445233631146662193)
        ·
          refine ⟨13827291333925223359996645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18436388445233631146662193 13827291333925223359996645)
          ·
            refine ⟨2592617125110979379999371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13827291333925223359996645 2592617125110979379999371)
            ·
              refine ⟨3888925687666469069999057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592617125110979379999371 3888925687666469069999057)
              ·
                refine ⟨2916694265749851802499293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888925687666469069999057 2916694265749851802499293)
                ·
                  refine ⟨1093760349656194425937235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2916694265749851802499293 1093760349656194425937235)
                  ·
                    refine ⟨1640640524484291638905853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1093760349656194425937235 1640640524484291638905853)
                    ·
                      refine ⟨615240196681609364589695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640640524484291638905853 615240196681609364589695)
                      ·
                        rfl

theorem cell23_1198176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_1198176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198176 prefixEnd_1198176 := by exact prefixLift 1198176
  have htrace : WordTrace (prefixWord ++ tailWord_1198176) baseStart_1198176 baseEnd_1198176 := by
    simpa [prefixWord, tailWord_1198176, baseEnd_1198176] using wordTrace_append hprefix tailTrace_1198176
  have hstable : (prefixWord ++ tailWord_1198176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198176).length < 2 ^ (prefixWord ++ tailWord_1198176).sum := by decide
  have hdescent : baseEnd_1198176 < baseStart_1198176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198193 : List Nat := [1, 2, 2, 2, 1, 1, 6, 3, 1, 1, 3]
def baseStart_1198193 : Nat := 118140960795 + 1198193 * 2 ^ 59
def prefixEnd_1198193 : Nat := 4983230072969 + 3 ^ 40 * 1198193 * 2
def baseEnd_1198193 : Nat := 615248925852735798077117

theorem tailTrace_1198193 : CollatzResearch.WordTrace tailWord_1198193 prefixEnd_1198193 615248925852735798077117 := by
  unfold tailWord_1198193
  simp only [CollatzResearch.WordTrace]
  refine ⟨43701688948158870917679233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29134459298772580611786155 43701688948158870917679233)
  ·
    refine ⟨32776266711119153188259425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43701688948158870917679233 32776266711119153188259425)
    ·
      refine ⟨24582200033339364891194569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32776266711119153188259425 24582200033339364891194569)
      ·
        refine ⟨18436650025004523668395927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24582200033339364891194569 18436650025004523668395927)
        ·
          refine ⟨27654975037506785502593891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18436650025004523668395927 27654975037506785502593891)
          ·
            refine ⟨41482462556260178253890837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27654975037506785502593891 41482462556260178253890837)
            ·
              refine ⟨1944490432324695855651133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41482462556260178253890837 1944490432324695855651133)
              ·
                refine ⟨729183912121760945869175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1944490432324695855651133 729183912121760945869175)
                ·
                  refine ⟨1093775868182641418803763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729183912121760945869175 1093775868182641418803763)
                  ·
                    refine ⟨1640663802273962128205645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1093775868182641418803763 1640663802273962128205645)
                    ·
                      refine ⟨615248925852735798077117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640663802273962128205645 615248925852735798077117)
                      ·
                        rfl

theorem cell23_1198193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_1198193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198193 prefixEnd_1198193 := by exact prefixLift 1198193
  have htrace : WordTrace (prefixWord ++ tailWord_1198193) baseStart_1198193 baseEnd_1198193 := by
    simpa [prefixWord, tailWord_1198193, baseEnd_1198193] using wordTrace_append hprefix tailTrace_1198193
  have hstable : (prefixWord ++ tailWord_1198193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198193).length < 2 ^ (prefixWord ++ tailWord_1198193).sum := by decide
  have hdescent : baseEnd_1198193 < baseStart_1198193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198202 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_1198202 : Nat := 118140960795 + 1198202 * 2 ^ 59
def prefixEnd_1198202 : Nat := 4983230072969 + 3 ^ 40 * 1198202 * 2
def baseEnd_1198202 : Nat := 615253547178626262864575

theorem tailTrace_1198202 : CollatzResearch.WordTrace tailWord_1198202 prefixEnd_1198202 615253547178626262864575 := by
  unfold tailWord_1198202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10925504301281566363689215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29134678136750843636504573 10925504301281566363689215)
  ·
    refine ⟨16388256451922349545533823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10925504301281566363689215 16388256451922349545533823)
    ·
      refine ⟨24582384677883524318300735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16388256451922349545533823 24582384677883524318300735)
      ·
        refine ⟨36873577016825286477451103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24582384677883524318300735 36873577016825286477451103)
        ·
          refine ⟨55310365525237929716176655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36873577016825286477451103 55310365525237929716176655)
          ·
            refine ⟨82965548287856894574264983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55310365525237929716176655 82965548287856894574264983)
            ·
              refine ⟨124448322431785341861397475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82965548287856894574264983 124448322431785341861397475)
              ·
                refine ⟨186672483647678012792096213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124448322431785341861397475 186672483647678012792096213)
                ·
                  refine ⟨4375136335492453424814755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 186672483647678012792096213 4375136335492453424814755)
                  ·
                    refine ⟨6562704503238680137222133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4375136335492453424814755 6562704503238680137222133)
                    ·
                      refine ⟨615253547178626262864575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6562704503238680137222133 615253547178626262864575)
                      ·
                        rfl

theorem cell23_1198202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_1198202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198202 prefixEnd_1198202 := by exact prefixLift 1198202
  have htrace : WordTrace (prefixWord ++ tailWord_1198202) baseStart_1198202 baseEnd_1198202 := by
    simpa [prefixWord, tailWord_1198202, baseEnd_1198202] using wordTrace_append hprefix tailTrace_1198202
  have hstable : (prefixWord ++ tailWord_1198202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198202).length < 2 ^ (prefixWord ++ tailWord_1198202).sum := by decide
  have hdescent : baseEnd_1198202 < baseStart_1198202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198239 : List Nat := [1, 1, 2, 6, 1, 2, 1, 9]
def baseStart_1198239 : Nat := 118140960795 + 1198239 * 2 ^ 59
def prefixEnd_1198239 : Nat := 4983230072969 + 3 ^ 40 * 1198239 * 2
def baseEnd_1198239 : Nat := 22787872072697874744515

theorem tailTrace_1198239 : CollatzResearch.WordTrace tailWord_1198239 prefixEnd_1198239 22787872072697874744515 := by
  unfold tailWord_1198239
  simp only [CollatzResearch.WordTrace]
  refine ⟨43703366705992220773853771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29135577803994813849235847 43703366705992220773853771)
  ·
    refine ⟨65555050058988331160780657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43703366705992220773853771 65555050058988331160780657)
    ·
      refine ⟨49166287544241248370585493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65555050058988331160780657 49166287544241248370585493)
      ·
        refine ⟨2304669728636308517371195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49166287544241248370585493 2304669728636308517371195)
        ·
          refine ⟨3457004592954462776056793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304669728636308517371195 3457004592954462776056793)
          ·
            refine ⟨2592753444715847082042595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3457004592954462776056793 2592753444715847082042595)
            ·
              refine ⟨3889130167073770623063893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592753444715847082042595 3889130167073770623063893)
              ·
                refine ⟨22787872072697874744515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3889130167073770623063893 22787872072697874744515)
                ·
                  rfl

theorem cell23_1198239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 9].length) (baseStart_1198239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198239 prefixEnd_1198239 := by exact prefixLift 1198239
  have htrace : WordTrace (prefixWord ++ tailWord_1198239) baseStart_1198239 baseEnd_1198239 := by
    simpa [prefixWord, tailWord_1198239, baseEnd_1198239] using wordTrace_append hprefix tailTrace_1198239
  have hstable : (prefixWord ++ tailWord_1198239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198239).length < 2 ^ (prefixWord ++ tailWord_1198239).sum := by decide
  have hdescent : baseEnd_1198239 < baseStart_1198239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198253 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1198253 : Nat := 118140960795 + 1198253 * 2 ^ 59
def prefixEnd_1198253 : Nat := 4983230072969 + 3 ^ 40 * 1198253 * 2
def baseEnd_1198253 : Nat := 615279734692005563326841

theorem tailTrace_1198253 : CollatzResearch.WordTrace tailWord_1198253 prefixEnd_1198253 615279734692005563326841 := by
  unfold tailWord_1198253
  simp only [CollatzResearch.WordTrace]
  refine ⟨43703877327941501164863413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29135918218627667443242275 43703877327941501164863413)
  ·
    refine ⟨4097238499494515734205945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43703877327941501164863413 4097238499494515734205945)
    ·
      refine ⟨3072928874620886800654459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4097238499494515734205945 3072928874620886800654459)
      ·
        refine ⟨4609393311931330200981689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072928874620886800654459 4609393311931330200981689)
        ·
          refine ⟨3457044983948497650736267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4609393311931330200981689 3457044983948497650736267)
          ·
            refine ⟨5185567475922746476104401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457044983948497650736267 5185567475922746476104401)
            ·
              refine ⟨3889175606942059857078301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5185567475922746476104401 3889175606942059857078301)
              ·
                refine ⟨1458440852603272446404363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3889175606942059857078301 1458440852603272446404363)
                ·
                  refine ⟨2187661278904908669606545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458440852603272446404363 2187661278904908669606545)
                  ·
                    refine ⟨1640745959178681502204909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2187661278904908669606545 1640745959178681502204909)
                    ·
                      refine ⟨615279734692005563326841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640745959178681502204909 615279734692005563326841)
                      ·
                        rfl

theorem cell23_1198253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1198253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198253 prefixEnd_1198253 := by exact prefixLift 1198253
  have htrace : WordTrace (prefixWord ++ tailWord_1198253) baseStart_1198253 baseEnd_1198253 := by
    simpa [prefixWord, tailWord_1198253, baseEnd_1198253] using wordTrace_append hprefix tailTrace_1198253
  have hstable : (prefixWord ++ tailWord_1198253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198253).length < 2 ^ (prefixWord ++ tailWord_1198253).sum := by decide
  have hdescent : baseEnd_1198253 < baseStart_1198253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198266 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_1198266 : Nat := 118140960795 + 1198266 * 2 ^ 59
def prefixEnd_1198266 : Nat := 4983230072969 + 3 ^ 40 * 1198266 * 2
def baseEnd_1198266 : Nat := 615286409940514012464281

theorem tailTrace_1198266 : CollatzResearch.WordTrace tailWord_1198266 prefixEnd_1198266 615286409940514012464281 := by
  unfold tailWord_1198266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10926087869223601096271663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29136234317929602923391101 10926087869223601096271663)
  ·
    refine ⟨16389131803835401644407495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10926087869223601096271663 16389131803835401644407495)
    ·
      refine ⟨24583697705753102466611243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16389131803835401644407495 24583697705753102466611243)
      ·
        refine ⟨36875546558629653699916865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24583697705753102466611243 36875546558629653699916865)
        ·
          refine ⟨27656659918972240274937649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36875546558629653699916865 27656659918972240274937649)
          ·
            refine ⟨20742494939229180206203237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27656659918972240274937649 20742494939229180206203237)
            ·
              refine ⟨3889217801105471288663107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20742494939229180206203237 3889217801105471288663107)
              ·
                refine ⟨5833826701658206932994661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889217801105471288663107 5833826701658206932994661)
                ·
                  refine ⟨1093842506560913799936499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5833826701658206932994661 1093842506560913799936499)
                  ·
                    refine ⟨1640763759841370699904749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1093842506560913799936499 1640763759841370699904749)
                    ·
                      refine ⟨615286409940514012464281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640763759841370699904749 615286409940514012464281)
                      ·
                        rfl

theorem cell23_1198266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_1198266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198266 prefixEnd_1198266 := by exact prefixLift 1198266
  have htrace : WordTrace (prefixWord ++ tailWord_1198266) baseStart_1198266 baseEnd_1198266 := by
    simpa [prefixWord, tailWord_1198266, baseEnd_1198266] using wordTrace_append hprefix tailTrace_1198266
  have hstable : (prefixWord ++ tailWord_1198266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198266).length < 2 ^ (prefixWord ++ tailWord_1198266).sum := by decide
  have hdescent : baseEnd_1198266 < baseStart_1198266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198300 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1198300 : Nat := 118140960795 + 1198300 * 2 ^ 59
def prefixEnd_1198300 : Nat := 4983230072969 + 3 ^ 40 * 1198300 * 2
def baseEnd_1198300 : Nat := 615303868282766879439125

theorem tailTrace_1198300 : CollatzResearch.WordTrace tailWord_1198300 prefixEnd_1198300 615303868282766879439125 := by
  unfold tailWord_1198300
  simp only [CollatzResearch.WordTrace]
  refine ⟨21852795779385614095912177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29137061039180818794549569 21852795779385614095912177)
  ·
    refine ⟨16389596834539210571934133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21852795779385614095912177 16389596834539210571934133)
    ·
      refine ⟨1536524703238050991118825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16389596834539210571934133 1536524703238050991118825)
      ·
        refine ⟨1152393527428538243339119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1536524703238050991118825 1152393527428538243339119)
        ·
          refine ⟨1728590291142807365008679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152393527428538243339119 1728590291142807365008679)
          ·
            refine ⟨2592885436714211047513019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728590291142807365008679 2592885436714211047513019)
            ·
              refine ⟨3889328155071316571269529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592885436714211047513019 3889328155071316571269529)
              ·
                refine ⟨2916996116303487428452147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3889328155071316571269529 2916996116303487428452147)
                ·
                  refine ⟨4375494174455231142678221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916996116303487428452147 4375494174455231142678221)
                  ·
                    refine ⟨1640810315420711678504333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4375494174455231142678221 1640810315420711678504333)
                    ·
                      refine ⟨615303868282766879439125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640810315420711678504333 615303868282766879439125)
                      ·
                        rfl

theorem cell23_1198300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1198300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198300 prefixEnd_1198300 := by exact prefixLift 1198300
  have htrace : WordTrace (prefixWord ++ tailWord_1198300) baseStart_1198300 baseEnd_1198300 := by
    simpa [prefixWord, tailWord_1198300, baseEnd_1198300] using wordTrace_append hprefix tailTrace_1198300
  have hstable : (prefixWord ++ tailWord_1198300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198300).length < 2 ^ (prefixWord ++ tailWord_1198300).sum := by decide
  have hdescent : baseEnd_1198300 < baseStart_1198300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198326 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1198326 : Nat := 118140960795 + 1198326 * 2 ^ 59
def prefixEnd_1198326 : Nat := 4983230072969 + 3 ^ 40 * 1198326 * 2
def baseEnd_1198326 : Nat := 615317218779783777714005

theorem tailTrace_1198326 : CollatzResearch.WordTrace tailWord_1198326 prefixEnd_1198326 615317218779783777714005 := by
  unfold tailWord_1198326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731658741042314664516927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29137693237784689754847221 2731658741042314664516927)
  ·
    refine ⟨4097488111563471996775391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2731658741042314664516927 4097488111563471996775391)
    ·
      refine ⟨6146232167345207995163087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4097488111563471996775391 6146232167345207995163087)
      ·
        refine ⟨9219348251017811992744631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6146232167345207995163087 9219348251017811992744631)
        ·
          refine ⟨13829022376526717989116947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9219348251017811992744631 13829022376526717989116947)
          ·
            refine ⟨20743533564790076983675421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13829022376526717989116947 20743533564790076983675421)
            ·
              refine ⟨7778825086796278868878283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20743533564790076983675421 7778825086796278868878283)
              ·
                refine ⟨11668237630194418303317425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7778825086796278868878283 11668237630194418303317425)
                ·
                  refine ⟨8751178222645813727488069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11668237630194418303317425 8751178222645813727488069)
                  ·
                    refine ⟨1640845916746090073904013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8751178222645813727488069 1640845916746090073904013)
                    ·
                      refine ⟨615317218779783777714005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640845916746090073904013 615317218779783777714005)
                      ·
                        rfl

theorem cell23_1198326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1198326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198326 prefixEnd_1198326 := by exact prefixLift 1198326
  have htrace : WordTrace (prefixWord ++ tailWord_1198326) baseStart_1198326 baseEnd_1198326 := by
    simpa [prefixWord, tailWord_1198326, baseEnd_1198326] using wordTrace_append hprefix tailTrace_1198326
  have hstable : (prefixWord ++ tailWord_1198326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198326).length < 2 ^ (prefixWord ++ tailWord_1198326).sum := by decide
  have hdescent : baseEnd_1198326 < baseStart_1198326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198340 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_1198340 : Nat := 118140960795 + 1198340 * 2 ^ 59
def prefixEnd_1198340 : Nat := 4983230072969 + 3 ^ 40 * 1198340 * 2
def baseEnd_1198340 : Nat := 615324407508946722938941

theorem tailTrace_1198340 : CollatzResearch.WordTrace tailWord_1198340 prefixEnd_1198340 615324407508946722938941 := by
  unfold tailWord_1198340
  simp only [CollatzResearch.WordTrace]
  refine ⟨21853525239313157511640237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29138033652417543348853649 21853525239313157511640237)
  ·
    refine ⟨8195071964742434066865089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21853525239313157511640237 8195071964742434066865089)
    ·
      refine ⟨6146303973556825550148817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8195071964742434066865089 6146303973556825550148817)
      ·
        refine ⟨4609727980167619162611613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6146303973556825550148817 4609727980167619162611613)
        ·
          refine ⟨1728647992562857185979355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4609727980167619162611613 1728647992562857185979355)
          ·
            refine ⟨2592971988844285778969033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728647992562857185979355 2592971988844285778969033)
            ·
              refine ⟨1944728991633214334226775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592971988844285778969033 1944728991633214334226775)
              ·
                refine ⟨2917093487449821501340163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944728991633214334226775 2917093487449821501340163)
                ·
                  refine ⟨4375640231174732252010245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917093487449821501340163 4375640231174732252010245)
                  ·
                    refine ⟨820432543345262297251921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4375640231174732252010245 820432543345262297251921)
                    ·
                      refine ⟨615324407508946722938941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820432543345262297251921 615324407508946722938941)
                      ·
                        rfl

theorem cell23_1198340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_1198340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198340 prefixEnd_1198340 := by exact prefixLift 1198340
  have htrace : WordTrace (prefixWord ++ tailWord_1198340) baseStart_1198340 baseEnd_1198340 := by
    simpa [prefixWord, tailWord_1198340, baseEnd_1198340] using wordTrace_append hprefix tailTrace_1198340
  have hstable : (prefixWord ++ tailWord_1198340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198340).length < 2 ^ (prefixWord ++ tailWord_1198340).sum := by decide
  have hdescent : baseEnd_1198340 < baseStart_1198340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198369 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1198369 : Nat := 118140960795 + 1198369 * 2 ^ 59
def prefixEnd_1198369 : Nat := 4983230072969 + 3 ^ 40 * 1198369 * 2
def baseEnd_1198369 : Nat := 615339298447927109476307

theorem tailTrace_1198369 : CollatzResearch.WordTrace tailWord_1198369 prefixEnd_1198369 615339298447927109476307 := by
  unfold tailWord_1198369
  simp only [CollatzResearch.WordTrace]
  refine ⟨43708108195521252976086161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29138738797014168650724107 43708108195521252976086161)
  ·
    refine ⟨32781081146640939732064621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43708108195521252976086161 32781081146640939732064621)
    ·
      refine ⟨12292905429990352399524233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32781081146640939732064621 12292905429990352399524233)
      ·
        refine ⟨9219679072492764299643175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12292905429990352399524233 9219679072492764299643175)
        ·
          refine ⟨13829518608739146449464763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9219679072492764299643175 13829518608739146449464763)
          ·
            refine ⟨20744277913108719674197145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13829518608739146449464763 20744277913108719674197145)
            ·
              refine ⟨15558208434831539755647859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20744277913108719674197145 15558208434831539755647859)
              ·
                refine ⟨23337312652247309633471789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15558208434831539755647859 23337312652247309633471789)
                ·
                  refine ⟨8751492244592741112551921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23337312652247309633471789 8751492244592741112551921)
                  ·
                    refine ⟨6563619183444555834413941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8751492244592741112551921 6563619183444555834413941)
                    ·
                      refine ⟨615339298447927109476307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6563619183444555834413941 615339298447927109476307)
                      ·
                        rfl

theorem cell23_1198369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1198369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198369 prefixEnd_1198369 := by exact prefixLift 1198369
  have htrace : WordTrace (prefixWord ++ tailWord_1198369) baseStart_1198369 baseEnd_1198369 := by
    simpa [prefixWord, tailWord_1198369, baseEnd_1198369] using wordTrace_append hprefix tailTrace_1198369
  have hstable : (prefixWord ++ tailWord_1198369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198369).length < 2 ^ (prefixWord ++ tailWord_1198369).sum := by decide
  have hdescent : baseEnd_1198369 < baseStart_1198369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198409 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_1198409 : Nat := 118140960795 + 1198409 * 2 ^ 59
def prefixEnd_1198409 : Nat := 4983230072969 + 3 ^ 40 * 1198409 * 2
def baseEnd_1198409 : Nat := 615359837674106952976123

theorem tailTrace_1198409 : CollatzResearch.WordTrace tailWord_1198409 prefixEnd_1198409 615359837674106952976123 := by
  unfold tailWord_1198409
  simp only [CollatzResearch.WordTrace]
  refine ⟨43709567115376339807542281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29139711410250893205028187 43709567115376339807542281)
  ·
    refine ⟨32782175336532254855656711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43709567115376339807542281 32782175336532254855656711)
    ·
      refine ⟨49173263004798382283485067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32782175336532254855656711 49173263004798382283485067)
      ·
        refine ⟨73759894507197573425227601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49173263004798382283485067 73759894507197573425227601)
        ·
          refine ⟨55319920880398180068920701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73759894507197573425227601 55319920880398180068920701)
          ·
            refine ⟨20744970330149317525845263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55319920880398180068920701 20744970330149317525845263)
            ·
              refine ⟨31117455495223976288767895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20744970330149317525845263 31117455495223976288767895)
              ·
                refine ⟨46676183242835964433151843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31117455495223976288767895 46676183242835964433151843)
                ·
                  refine ⟨70014274864253946649727765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46676183242835964433151843 70014274864253946649727765)
                  ·
                    refine ⟨3281919134261903749205989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70014274864253946649727765 3281919134261903749205989)
                    ·
                      refine ⟨615359837674106952976123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3281919134261903749205989 615359837674106952976123)
                      ·
                        rfl

theorem cell23_1198409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_1198409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198409 prefixEnd_1198409 := by exact prefixLift 1198409
  have htrace : WordTrace (prefixWord ++ tailWord_1198409) baseStart_1198409 baseEnd_1198409 := by
    simpa [prefixWord, tailWord_1198409, baseEnd_1198409] using wordTrace_append hprefix tailTrace_1198409
  have hstable : (prefixWord ++ tailWord_1198409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198409).length < 2 ^ (prefixWord ++ tailWord_1198409).sum := by decide
  have hdescent : baseEnd_1198409 < baseStart_1198409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198416 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 3]
def baseStart_1198416 : Nat := 118140960795 + 1198416 * 2 ^ 59
def prefixEnd_1198416 : Nat := 4983230072969 + 3 ^ 40 * 1198416 * 2
def baseEnd_1198416 : Nat := 615363432038688425588591

theorem tailTrace_1198416 : CollatzResearch.WordTrace tailWord_1198416 prefixEnd_1198416 615363432038688425588591 := by
  unfold tailWord_1198416
  simp only [CollatzResearch.WordTrace]
  refine ⟨21854911213175490001523551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29139881617567320002031401 21854911213175490001523551)
  ·
    refine ⟨32782366819763235002285327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21854911213175490001523551 32782366819763235002285327)
    ·
      refine ⟨49173550229644852503427991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32782366819763235002285327 49173550229644852503427991)
      ·
        refine ⟨73760325344467278755141987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49173550229644852503427991 73760325344467278755141987)
        ·
          refine ⟨110640488016700918132712981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73760325344467278755141987 110640488016700918132712981)
          ·
            refine ⟨5186272875782855537470921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110640488016700918132712981 5186272875782855537470921)
            ·
              refine ⟨3889704656837141653103191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5186272875782855537470921 3889704656837141653103191)
              ·
                refine ⟨5834556985255712479654787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889704656837141653103191 5834556985255712479654787)
                ·
                  refine ⟨8751835477883568719482181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5834556985255712479654787 8751835477883568719482181)
                  ·
                    refine ⟨1640969152103169134902909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8751835477883568719482181 1640969152103169134902909)
                    ·
                      refine ⟨615363432038688425588591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1640969152103169134902909 615363432038688425588591)
                      ·
                        rfl

theorem cell23_1198416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_1198416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198416 prefixEnd_1198416 := by exact prefixLift 1198416
  have htrace : WordTrace (prefixWord ++ tailWord_1198416) baseStart_1198416 baseEnd_1198416 := by
    simpa [prefixWord, tailWord_1198416, baseEnd_1198416] using wordTrace_append hprefix tailTrace_1198416
  have hstable : (prefixWord ++ tailWord_1198416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198416).length < 2 ^ (prefixWord ++ tailWord_1198416).sum := by decide
  have hdescent : baseEnd_1198416 < baseStart_1198416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198436 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 6]
def baseStart_1198436 : Nat := 118140960795 + 1198436 * 2 ^ 59
def prefixEnd_1198436 : Nat := 4983230072969 + 3 ^ 40 * 1198436 * 2
def baseEnd_1198436 : Nat := 68374855739086483037611

theorem tailTrace_1198436 : CollatzResearch.WordTrace tailWord_1198436 prefixEnd_1198436 68374855739086483037611 := by
  unfold tailWord_1198436
  simp only [CollatzResearch.WordTrace]
  refine ⟨21855275943139261709387581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29140367924185682279183441 21855275943139261709387581)
  ·
    refine ⟨8195728478677223141020343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21855275943139261709387581 8195728478677223141020343)
    ·
      refine ⟨12293592718015834711530515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8195728478677223141020343 12293592718015834711530515)
      ·
        refine ⟨18440389077023752067295773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12293592718015834711530515 18440389077023752067295773)
        ·
          refine ⟨6915145903883907025235915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18440389077023752067295773 6915145903883907025235915)
          ·
            refine ⟨10372718855825860537853873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915145903883907025235915 10372718855825860537853873)
            ·
              refine ⟨7779539141869395403390405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10372718855825860537853873 7779539141869395403390405)
              ·
                refine ⟨1458663589100511638135701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7779539141869395403390405 1458663589100511638135701)
                ·
                  refine ⟨68374855739086483037611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1458663589100511638135701 68374855739086483037611)
                  ·
                    rfl

theorem cell23_1198436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_1198436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198436 prefixEnd_1198436 := by exact prefixLift 1198436
  have htrace : WordTrace (prefixWord ++ tailWord_1198436) baseStart_1198436 baseEnd_1198436 := by
    simpa [prefixWord, tailWord_1198436, baseEnd_1198436] using wordTrace_append hprefix tailTrace_1198436
  have hstable : (prefixWord ++ tailWord_1198436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198436).length < 2 ^ (prefixWord ++ tailWord_1198436).sum := by decide
  have hdescent : baseEnd_1198436 < baseStart_1198436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198440 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1198440 : Nat := 118140960795 + 1198440 * 2 ^ 59
def prefixEnd_1198440 : Nat := 4983230072969 + 3 ^ 40 * 1198440 * 2
def baseEnd_1198440 : Nat := 205125251858132110562827

theorem tailTrace_1198440 : CollatzResearch.WordTrace tailWord_1198440 prefixEnd_1198440 205125251858132110562827 := by
  unfold tailWord_1198440
  simp only [CollatzResearch.WordTrace]
  refine ⟨21855348889132016050960387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29140465185509354734613849 21855348889132016050960387)
  ·
    refine ⟨32783023333698024076440581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21855348889132016050960387 32783023333698024076440581)
    ·
      refine ⟨6146816875068379514332609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32783023333698024076440581 6146816875068379514332609)
      ·
        refine ⟨4610112656301284635749457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6146816875068379514332609 4610112656301284635749457)
        ·
          refine ⟨3457584492225963476812093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4610112656301284635749457 3457584492225963476812093)
          ·
            refine ⟨1296594184584736303804535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3457584492225963476812093 1296594184584736303804535)
            ·
              refine ⟨1944891276877104455706803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296594184584736303804535 1944891276877104455706803)
              ·
                refine ⟨2917336915315656683560205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944891276877104455706803 2917336915315656683560205)
                ·
                  refine ⟨1094001343243371256335077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2917336915315656683560205 1094001343243371256335077)
                  ·
                    refine ⟨205125251858132110562827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1094001343243371256335077 205125251858132110562827)
                    ·
                      rfl

theorem cell23_1198440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1198440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198440 prefixEnd_1198440 := by exact prefixLift 1198440
  have htrace : WordTrace (prefixWord ++ tailWord_1198440) baseStart_1198440 baseEnd_1198440 := by
    simpa [prefixWord, tailWord_1198440, baseEnd_1198440] using wordTrace_append hprefix tailTrace_1198440
  have hstable : (prefixWord ++ tailWord_1198440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198440).length < 2 ^ (prefixWord ++ tailWord_1198440).sum := by decide
  have hdescent : baseEnd_1198440 < baseStart_1198440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198449 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 2, 9]
def baseStart_1198449 : Nat := 118140960795 + 1198449 * 2 ^ 59
def prefixEnd_1198449 : Nat := 4983230072969 + 3 ^ 40 * 1198449 * 2
def baseEnd_1198449 : Nat := 205126792300095598825313

theorem tailTrace_1198449 : CollatzResearch.WordTrace tailWord_1198449 prefixEnd_1198449 205126792300095598825313 := by
  unfold tailWord_1198449
  simp only [CollatzResearch.WordTrace]
  refine ⟨43711026035231426638998401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29140684023487617759332267 43711026035231426638998401)
  ·
    refine ⟨32783269526423569979248801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43711026035231426638998401 32783269526423569979248801)
    ·
      refine ⟨24587452144817677484436601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32783269526423569979248801 24587452144817677484436601)
      ·
        refine ⟨18440589108613258113327451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24587452144817677484436601 18440589108613258113327451)
        ·
          refine ⟨27660883662919887169991177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18440589108613258113327451 27660883662919887169991177)
          ·
            refine ⟨20745662747189915377493383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27660883662919887169991177 20745662747189915377493383)
            ·
              refine ⟨31118494120784873066240075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20745662747189915377493383 31118494120784873066240075)
              ·
                refine ⟨46677741181177309599360113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31118494120784873066240075 46677741181177309599360113)
                ·
                  refine ⟨35008305885882982199520085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46677741181177309599360113 35008305885882982199520085)
                  ·
                    refine ⟨205126792300095598825313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 35008305885882982199520085 205126792300095598825313)
                    ·
                      rfl

theorem cell23_1198449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_1198449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198449 prefixEnd_1198449 := by exact prefixLift 1198449
  have htrace : WordTrace (prefixWord ++ tailWord_1198449) baseStart_1198449 baseEnd_1198449 := by
    simpa [prefixWord, tailWord_1198449, baseEnd_1198449] using wordTrace_append hprefix tailTrace_1198449
  have hstable : (prefixWord ++ tailWord_1198449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198449).length < 2 ^ (prefixWord ++ tailWord_1198449).sum := by decide
  have hdescent : baseEnd_1198449 < baseStart_1198449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198453 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 6]
def baseStart_1198453 : Nat := 118140960795 + 1198453 * 2 ^ 59
def prefixEnd_1198453 : Nat := 4983230072969 + 3 ^ 40 * 1198453 * 2
def baseEnd_1198453 : Nat := 68375825646989420091769

theorem tailTrace_1198453 : CollatzResearch.WordTrace tailWord_1198453 prefixEnd_1198453 68375825646989420091769 := by
  unfold tailWord_1198453
  simp only [CollatzResearch.WordTrace]
  refine ⟨43711171927216935322144013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29140781284811290214762675 43711171927216935322144013)
  ·
    refine ⟨16391689472706350745804005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43711171927216935322144013 16391689472706350745804005)
    ·
      refine ⟨3073441776132440764838251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16391689472706350745804005 3073441776132440764838251)
      ·
        refine ⟨4610162664198661147257377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3073441776132440764838251 4610162664198661147257377)
        ·
          refine ⟨3457621998148995860443033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4610162664198661147257377 3457621998148995860443033)
          ·
            refine ⟨2593216498611746895332275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3457621998148995860443033 2593216498611746895332275)
            ·
              refine ⟨3889824747917620342998413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2593216498611746895332275 3889824747917620342998413)
              ·
                refine ⟨1458684280469107628624405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3889824747917620342998413 1458684280469107628624405)
                ·
                  refine ⟨68375825646989420091769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1458684280469107628624405 68375825646989420091769)
                  ·
                    rfl

theorem cell23_1198453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_1198453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198453 prefixEnd_1198453 := by exact prefixLift 1198453
  have htrace : WordTrace (prefixWord ++ tailWord_1198453) baseStart_1198453 baseEnd_1198453 := by
    simpa [prefixWord, tailWord_1198453, baseEnd_1198453] using wordTrace_append hprefix tailTrace_1198453
  have hstable : (prefixWord ++ tailWord_1198453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198453).length < 2 ^ (prefixWord ++ tailWord_1198453).sum := by decide
  have hdescent : baseEnd_1198453 < baseStart_1198453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198490 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2]
def baseStart_1198490 : Nat := 118140960795 + 1198490 * 2 ^ 59
def prefixEnd_1198490 : Nat := 4983230072969 + 3 ^ 40 * 1198490 * 2
def baseEnd_1198490 : Nat := 615401429607121136063251

theorem tailTrace_1198490 : CollatzResearch.WordTrace tailWord_1198490 prefixEnd_1198490 615401429607121136063251 := by
  unfold tailWord_1198490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10928130357020722660310231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29141680952055260427493949 10928130357020722660310231)
  ·
    refine ⟨16392195535531083990465347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10928130357020722660310231 16392195535531083990465347)
    ·
      refine ⟨24588293303296625985698021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16392195535531083990465347 24588293303296625985698021)
      ·
        refine ⟨4610304994368117372318379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24588293303296625985698021 4610304994368117372318379)
        ·
          refine ⟨6915457491552176058477569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610304994368117372318379 6915457491552176058477569)
          ·
            refine ⟨5186593118664132043858177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6915457491552176058477569 5186593118664132043858177)
            ·
              refine ⟨3889944838998099032893633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5186593118664132043858177 3889944838998099032893633)
              ·
                refine ⟨2917458629248574274670225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3889944838998099032893633 2917458629248574274670225)
                ·
                  refine ⟨2188093971936430706002669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2917458629248574274670225 2188093971936430706002669)
                  ·
                    refine ⟨820535239476161514751001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2188093971936430706002669 820535239476161514751001)
                    ·
                      refine ⟨615401429607121136063251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820535239476161514751001 615401429607121136063251)
                      ·
                        rfl

theorem cell23_1198490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_1198490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198490 prefixEnd_1198490 := by exact prefixLift 1198490
  have htrace : WordTrace (prefixWord ++ tailWord_1198490) baseStart_1198490 baseEnd_1198490 := by
    simpa [prefixWord, tailWord_1198490, baseEnd_1198490] using wordTrace_append hprefix tailTrace_1198490
  have hstable : (prefixWord ++ tailWord_1198490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198490).length < 2 ^ (prefixWord ++ tailWord_1198490).sum := by decide
  have hdescent : baseEnd_1198490 < baseStart_1198490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198503 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1198503 : Nat := 118140960795 + 1198503 * 2 ^ 59
def prefixEnd_1198503 : Nat := 4983230072969 + 3 ^ 40 * 1198503 * 2
def baseEnd_1198503 : Nat := 615408104855629585200691

theorem tailTrace_1198503 : CollatzResearch.WordTrace tailWord_1198503 prefixEnd_1198503 615408104855629585200691 := by
  unfold tailWord_1198503
  simp only [CollatzResearch.WordTrace]
  refine ⟨43712995577035793861464163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29141997051357195907642775 43712995577035793861464163)
  ·
    refine ⟨65569493365553690792196245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43712995577035793861464163 65569493365553690792196245)
    ·
      refine ⟨3073570001510329255884199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65569493365553690792196245 3073570001510329255884199)
      ·
        refine ⟨4610355002265493883826299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3073570001510329255884199 4610355002265493883826299)
        ·
          refine ⟨6915532503398240825739449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610355002265493883826299 6915532503398240825739449)
          ·
            refine ⟨5186649377548680619304587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6915532503398240825739449 5186649377548680619304587)
            ·
              refine ⟨7779974066323020928956881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186649377548680619304587 7779974066323020928956881)
              ·
                refine ⟨5834980549742265696717661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7779974066323020928956881 5834980549742265696717661)
                ·
                  refine ⟨2188117706153349636269123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5834980549742265696717661 2188117706153349636269123)
                  ·
                    refine ⟨3282176559230024454403685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188117706153349636269123 3282176559230024454403685)
                    ·
                      refine ⟨615408104855629585200691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3282176559230024454403685 615408104855629585200691)
                      ·
                        rfl

theorem cell23_1198503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1198503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198503 prefixEnd_1198503 := by exact prefixLift 1198503
  have htrace : WordTrace (prefixWord ++ tailWord_1198503) baseStart_1198503 baseEnd_1198503 := by
    simpa [prefixWord, tailWord_1198503, baseEnd_1198503] using wordTrace_append hprefix tailTrace_1198503
  have hstable : (prefixWord ++ tailWord_1198503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198503).length < 2 ^ (prefixWord ++ tailWord_1198503).sum := by decide
  have hdescent : baseEnd_1198503 < baseStart_1198503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198513 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 1, 6]
def baseStart_1198513 : Nat := 118140960795 + 1198513 * 2 ^ 59
def prefixEnd_1198513 : Nat := 4983230072969 + 3 ^ 40 * 1198513 * 2
def baseEnd_1198513 : Nat := 205137746554058182025215

theorem tailTrace_1198513 : CollatzResearch.WordTrace tailWord_1198513 prefixEnd_1198513 205137746554058182025215 := by
  unfold tailWord_1198513
  simp only [CollatzResearch.WordTrace]
  refine ⟨43713360306999565569328193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29142240204666377046218795 43713360306999565569328193)
  ·
    refine ⟨32785020230249674176996145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43713360306999565569328193 32785020230249674176996145)
    ·
      refine ⟨24588765172687255632747109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32785020230249674176996145 24588765172687255632747109)
      ·
        refine ⟨4610393469878860431140083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24588765172687255632747109 4610393469878860431140083)
        ·
          refine ⟨6915590204818290646710125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610393469878860431140083 6915590204818290646710125)
          ·
            refine ⟨2593346326806858992516297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6915590204818290646710125 2593346326806858992516297)
            ·
              refine ⟨1945009745105144244387223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2593346326806858992516297 1945009745105144244387223)
              ·
                refine ⟨2917514617657716366580835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945009745105144244387223 2917514617657716366580835)
                ·
                  refine ⟨4376271926486574549871253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917514617657716366580835 4376271926486574549871253)
                  ·
                    refine ⟨205137746554058182025215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4376271926486574549871253 205137746554058182025215)
                    ·
                      rfl

theorem cell23_1198513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_1198513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198513 prefixEnd_1198513 := by exact prefixLift 1198513
  have htrace : WordTrace (prefixWord ++ tailWord_1198513) baseStart_1198513 baseEnd_1198513 := by
    simpa [prefixWord, tailWord_1198513, baseEnd_1198513] using wordTrace_append hprefix tailTrace_1198513
  have hstable : (prefixWord ++ tailWord_1198513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198513).length < 2 ^ (prefixWord ++ tailWord_1198513).sum := by decide
  have hdescent : baseEnd_1198513 < baseStart_1198513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198526 : List Nat := [4, 2, 1, 1, 1, 1, 2, 11]
def baseStart_1198526 : Nat := 118140960795 + 1198526 * 2 ^ 59
def prefixEnd_1198526 : Nat := 4983230072969 + 3 ^ 40 * 1198526 * 2
def baseEnd_1198526 : Nat := 22793330181877147970855

theorem tailTrace_1198526 : CollatzResearch.WordTrace tailWord_1198526 prefixEnd_1198526 22793330181877147970855 := by
  unfold tailWord_1198526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464229306994058598693929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29142556303968312526367621 5464229306994058598693929)
  ·
    refine ⟨4098171980245543949020447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5464229306994058598693929 4098171980245543949020447)
    ·
      refine ⟨6147257970368315923530671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4098171980245543949020447 6147257970368315923530671)
      ·
        refine ⟨9220886955552473885296007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6147257970368315923530671 9220886955552473885296007)
        ·
          refine ⟨13831330433328710827944011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9220886955552473885296007 13831330433328710827944011)
          ·
            refine ⟨20746995649993066241916017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13831330433328710827944011 20746995649993066241916017)
            ·
              refine ⟨15560246737494799681437013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20746995649993066241916017 15560246737494799681437013)
              ·
                refine ⟨22793330181877147970855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 15560246737494799681437013 22793330181877147970855)
                ·
                  rfl

theorem cell23_1198526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_1198526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198526 prefixEnd_1198526 := by exact prefixLift 1198526
  have htrace : WordTrace (prefixWord ++ tailWord_1198526) baseStart_1198526 baseEnd_1198526 := by
    simpa [prefixWord, tailWord_1198526, baseEnd_1198526] using wordTrace_append hprefix tailTrace_1198526
  have hstable : (prefixWord ++ tailWord_1198526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198526).length < 2 ^ (prefixWord ++ tailWord_1198526).sum := by decide
  have hdescent : baseEnd_1198526 < baseStart_1198526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198537 : List Nat := [1, 2, 1, 1, 2, 1, 5, 5, 1, 2, 2]
def baseStart_1198537 : Nat := 118140960795 + 1198537 * 2 ^ 59
def prefixEnd_1198537 : Nat := 4983230072969 + 3 ^ 40 * 1198537 * 2
def baseEnd_1198537 : Nat := 615425563197882452175535

theorem tailTrace_1198537 : CollatzResearch.WordTrace tailWord_1198537 prefixEnd_1198537 615425563197882452175535 := by
  unfold tailWord_1198537
  simp only [CollatzResearch.WordTrace]
  refine ⟨43714235658912617668201865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29142823772608411778801243 43714235658912617668201865)
  ·
    refine ⟨32785676744184463251151399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43714235658912617668201865 32785676744184463251151399)
    ·
      refine ⟨49178515116276694876727099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32785676744184463251151399 49178515116276694876727099)
      ·
        refine ⟨73767772674415042315090649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49178515116276694876727099 73767772674415042315090649)
        ·
          refine ⟨55325829505811281736317987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73767772674415042315090649 55325829505811281736317987)
          ·
            refine ⟨82988744258716922604476981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55325829505811281736317987 82988744258716922604476981)
            ·
              refine ⟨7780194774254711494169717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82988744258716922604476981 7780194774254711494169717)
              ·
                refine ⟨729393260086379202578411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7780194774254711494169717 729393260086379202578411)
                ·
                  refine ⟨1094089890129568803867617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729393260086379202578411 1094089890129568803867617)
                  ·
                    refine ⟨820567417597176602900713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1094089890129568803867617 820567417597176602900713)
                    ·
                      refine ⟨615425563197882452175535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820567417597176602900713 615425563197882452175535)
                      ·
                        rfl

theorem cell23_1198537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 2, 2].length) (baseStart_1198537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198537 prefixEnd_1198537 := by exact prefixLift 1198537
  have htrace : WordTrace (prefixWord ++ tailWord_1198537) baseStart_1198537 baseEnd_1198537 := by
    simpa [prefixWord, tailWord_1198537, baseEnd_1198537] using wordTrace_append hprefix tailTrace_1198537
  have hstable : (prefixWord ++ tailWord_1198537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198537).length < 2 ^ (prefixWord ++ tailWord_1198537).sum := by decide
  have hdescent : baseEnd_1198537 < baseStart_1198537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198570 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1198570 : Nat := 118140960795 + 1198570 * 2 ^ 59
def prefixEnd_1198570 : Nat := 4983230072969 + 3 ^ 40 * 1198570 * 2
def baseEnd_1198570 : Nat := 615442508059480823062883

theorem tailTrace_1198570 : CollatzResearch.WordTrace tailWord_1198570 prefixEnd_1198570 615442508059480823062883 := by
  unfold tailWord_1198570
  simp only [CollatzResearch.WordTrace]
  refine ⟨10928859816948266076038291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29143626178528709536102109 10928859816948266076038291)
  ·
    refine ⟨16393289725422399114057437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10928859816948266076038291 16393289725422399114057437)
    ·
      refine ⟨6147483647033399667771539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16393289725422399114057437 6147483647033399667771539)
      ·
        refine ⟨9221225470550099501657309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6147483647033399667771539 9221225470550099501657309)
        ·
          refine ⟨3457959551456287313121491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9221225470550099501657309 3457959551456287313121491)
          ·
            refine ⟨5186939327184430969682237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457959551456287313121491 5186939327184430969682237)
            ·
              refine ⟨1945102247694161613630839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5186939327184430969682237 1945102247694161613630839)
              ·
                refine ⟨2917653371541242420446259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945102247694161613630839 2917653371541242420446259)
                ·
                  refine ⟨4376480057311863630669389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917653371541242420446259 4376480057311863630669389)
                  ·
                    refine ⟨1641180021491948861501021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4376480057311863630669389 1641180021491948861501021)
                    ·
                      refine ⟨615442508059480823062883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1641180021491948861501021 615442508059480823062883)
                      ·
                        rfl

theorem cell23_1198570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1198570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198570 prefixEnd_1198570 := by exact prefixLift 1198570
  have htrace : WordTrace (prefixWord ++ tailWord_1198570) baseStart_1198570 baseEnd_1198570 := by
    simpa [prefixWord, tailWord_1198570, baseEnd_1198570] using wordTrace_append hprefix tailTrace_1198570
  have hstable : (prefixWord ++ tailWord_1198570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198570).length < 2 ^ (prefixWord ++ tailWord_1198570).sum := by decide
  have hdescent : baseEnd_1198570 < baseStart_1198570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198586 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_1198586 : Nat := 118140960795 + 1198586 * 2 ^ 59
def prefixEnd_1198586 : Nat := 4983230072969 + 3 ^ 40 * 1198586 * 2
def baseEnd_1198586 : Nat := 205150241249984253487603

theorem tailTrace_1198586 : CollatzResearch.WordTrace tailWord_1198586 prefixEnd_1198586 205150241249984253487603 := by
  unfold tailWord_1198586
  simp only [CollatzResearch.WordTrace]
  refine ⟨10929005708933774759183903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29144015223823399357823741 10929005708933774759183903)
  ·
    refine ⟨16393508563400662138775855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10929005708933774759183903 16393508563400662138775855)
    ·
      refine ⟨24590262845100993208163783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16393508563400662138775855 24590262845100993208163783)
      ·
        refine ⟨36885394267651489812245675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24590262845100993208163783 36885394267651489812245675)
        ·
          refine ⟨55328091401477234718368513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36885394267651489812245675 55328091401477234718368513)
          ·
            refine ⟨41496068551107926038776385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55328091401477234718368513 41496068551107926038776385)
            ·
              refine ⟨31122051413330944529082289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41496068551107926038776385 31122051413330944529082289)
              ·
                refine ⟨23341538559998208396811717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31122051413330944529082289 23341538559998208396811717)
                ·
                  refine ⟨4376538479999664074402197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23341538559998208396811717 4376538479999664074402197)
                  ·
                    refine ⟨205150241249984253487603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4376538479999664074402197 205150241249984253487603)
                    ·
                      rfl

theorem cell23_1198586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_1198586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198586 prefixEnd_1198586 := by exact prefixLift 1198586
  have htrace : WordTrace (prefixWord ++ tailWord_1198586) baseStart_1198586 baseEnd_1198586 := by
    simpa [prefixWord, tailWord_1198586, baseEnd_1198586] using wordTrace_append hprefix tailTrace_1198586
  have hstable : (prefixWord ++ tailWord_1198586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198586).length < 2 ^ (prefixWord ++ tailWord_1198586).sum := by decide
  have hdescent : baseEnd_1198586 < baseStart_1198586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198605 : List Nat := [1, 7, 1, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1198605 : Nat := 118140960795 + 1198605 * 2 ^ 59
def prefixEnd_1198605 : Nat := 4983230072969 + 3 ^ 40 * 1198605 * 2
def baseEnd_1198605 : Nat := 615460479882388186125223

theorem tailTrace_1198605 : CollatzResearch.WordTrace tailWord_1198605 prefixEnd_1198605 615460479882388186125223 := by
  unfold tailWord_1198605
  simp only [CollatzResearch.WordTrace]
  refine ⟨43716715822666265281677269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29144477215110843521118179 43716715822666265281677269)
  ·
    refine ⟨1024610527093740592539311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 43716715822666265281677269 1024610527093740592539311)
    ·
      refine ⟨1536915790640610888808967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024610527093740592539311 1536915790640610888808967)
      ·
        refine ⟨2305373685960916333213451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536915790640610888808967 2305373685960916333213451)
        ·
          refine ⟨3458060528941374499820177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305373685960916333213451 3458060528941374499820177)
          ·
            refine ⟨2593545396706030874865133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458060528941374499820177 2593545396706030874865133)
            ·
              refine ⟨972579523764761578074425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2593545396706030874865133 972579523764761578074425)
              ·
                refine ⟨729434642823571183555819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972579523764761578074425 729434642823571183555819)
                ·
                  refine ⟨1094151964235356775333729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729434642823571183555819 1094151964235356775333729)
                  ·
                    refine ⟨820613973176517581500297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1094151964235356775333729 820613973176517581500297)
                    ·
                      refine ⟨615460479882388186125223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820613973176517581500297 615460479882388186125223)
                      ·
                        rfl

theorem cell23_1198605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1198605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198605 prefixEnd_1198605 := by exact prefixLift 1198605
  have htrace : WordTrace (prefixWord ++ tailWord_1198605) baseStart_1198605 baseEnd_1198605 := by
    simpa [prefixWord, tailWord_1198605, baseEnd_1198605] using wordTrace_append hprefix tailTrace_1198605
  have hstable : (prefixWord ++ tailWord_1198605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198605).length < 2 ^ (prefixWord ++ tailWord_1198605).sum := by decide
  have hdescent : baseEnd_1198605 < baseStart_1198605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198613 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1198613 : Nat := 118140960795 + 1198613 * 2 ^ 59
def prefixEnd_1198613 : Nat := 4983230072969 + 3 ^ 40 * 1198613 * 2
def baseEnd_1198613 : Nat := 615464587727624154825185

theorem tailTrace_1198613 : CollatzResearch.WordTrace tailWord_1198613 prefixEnd_1198613 615464587727624154825185 := by
  unfold tailWord_1198613
  simp only [CollatzResearch.WordTrace]
  refine ⟨43717007606637282647968493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29144671737758188431978995 43717007606637282647968493)
  ·
    refine ⟨16393877852488980992988185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43717007606637282647968493 16393877852488980992988185)
    ·
      refine ⟨12295408389366735744741139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16393877852488980992988185 12295408389366735744741139)
      ·
        refine ⟨18443112584050103617111709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12295408389366735744741139 18443112584050103617111709)
        ·
          refine ⟨6916167219018788856416891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18443112584050103617111709 6916167219018788856416891)
          ·
            refine ⟨10374250828528183284625337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916167219018788856416891 10374250828528183284625337)
            ·
              refine ⟨7780688121396137463469003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10374250828528183284625337 7780688121396137463469003)
              ·
                refine ⟨11671032182094206195203505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7780688121396137463469003 11671032182094206195203505)
                ·
                  refine ⟨8753274136570654646402629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11671032182094206195203505 8753274136570654646402629)
                  ·
                    refine ⟨1641238900606997746200493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8753274136570654646402629 1641238900606997746200493)
                    ·
                      refine ⟨615464587727624154825185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1641238900606997746200493 615464587727624154825185)
                      ·
                        rfl

theorem cell23_1198613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1198613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198613 prefixEnd_1198613 := by exact prefixLift 1198613
  have htrace : WordTrace (prefixWord ++ tailWord_1198613) baseStart_1198613 baseEnd_1198613 := by
    simpa [prefixWord, tailWord_1198613, baseEnd_1198613] using wordTrace_append hprefix tailTrace_1198613
  have hstable : (prefixWord ++ tailWord_1198613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198613).length < 2 ^ (prefixWord ++ tailWord_1198613).sum := by decide
  have hdescent : baseEnd_1198613 < baseStart_1198613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198636 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_1198636 : Nat := 118140960795 + 1198636 * 2 ^ 59
def prefixEnd_1198636 : Nat := 4983230072969 + 3 ^ 40 * 1198636 * 2
def baseEnd_1198636 : Nat := 615476397782677564837579

theorem tailTrace_1198636 : CollatzResearch.WordTrace tailWord_1198636 prefixEnd_1198636 615476397782677564837579 := by
  unfold tailWord_1198636
  simp only [CollatzResearch.WordTrace]
  refine ⟨21858923242776978788027881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29145230990369305050703841 21858923242776978788027881)
  ·
    refine ⟨16394192432082734091020911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21858923242776978788027881 16394192432082734091020911)
    ·
      refine ⟨24591288648124101136531367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16394192432082734091020911 24591288648124101136531367)
      ·
        refine ⟨36886932972186151704797051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24591288648124101136531367 36886932972186151704797051)
        ·
          refine ⟨55330399458279227557195577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36886932972186151704797051 55330399458279227557195577)
          ·
            refine ⟨41497799593709420667896683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55330399458279227557195577 41497799593709420667896683)
            ·
              refine ⟨62246699390564131001845025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41497799593709420667896683 62246699390564131001845025)
              ·
                refine ⟨46685024542923098251383769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62246699390564131001845025 46685024542923098251383769)
                ·
                  refine ⟨35013768407192323688537827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46685024542923098251383769 35013768407192323688537827)
                  ·
                    refine ⟨52520652610788485532806741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35013768407192323688537827 52520652610788485532806741)
                    ·
                      refine ⟨615476397782677564837579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 52520652610788485532806741 615476397782677564837579)
                      ·
                        rfl

theorem cell23_1198636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_1198636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198636 prefixEnd_1198636 := by exact prefixLift 1198636
  have htrace : WordTrace (prefixWord ++ tailWord_1198636) baseStart_1198636 baseEnd_1198636 := by
    simpa [prefixWord, tailWord_1198636, baseEnd_1198636] using wordTrace_append hprefix tailTrace_1198636
  have hstable : (prefixWord ++ tailWord_1198636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198636).length < 2 ^ (prefixWord ++ tailWord_1198636).sum := by decide
  have hdescent : baseEnd_1198636 < baseStart_1198636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198670 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_1198670 : Nat := 118140960795 + 1198670 * 2 ^ 59
def prefixEnd_1198670 : Nat := 4983230072969 + 3 ^ 40 * 1198670 * 2
def baseEnd_1198670 : Nat := 615493856124930431812423

theorem tailTrace_1198670 : CollatzResearch.WordTrace tailWord_1198670 prefixEnd_1198670 615493856124930431812423 := by
  unfold tailWord_1198670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464885820928847672849183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29146057711620520921862309 5464885820928847672849183)
  ·
    refine ⟨8197328731393271509273775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5464885820928847672849183 8197328731393271509273775)
    ·
      refine ⟨12295993097089907263910663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8197328731393271509273775 12295993097089907263910663)
      ·
        refine ⟨18443989645634860895865995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12295993097089907263910663 18443989645634860895865995)
        ·
          refine ⟨27665984468452291343798993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18443989645634860895865995 27665984468452291343798993)
          ·
            refine ⟨20749488351339218507849245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27665984468452291343798993 20749488351339218507849245)
            ·
              refine ⟨7781058131752206940443467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20749488351339218507849245 7781058131752206940443467)
              ·
                refine ⟨11671587197628310410665201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7781058131752206940443467 11671587197628310410665201)
                ·
                  refine ⟨8753690398221232807998901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11671587197628310410665201 8753690398221232807998901)
                  ·
                    refine ⟨820658474833240575749897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8753690398221232807998901 820658474833240575749897)
                    ·
                      refine ⟨615493856124930431812423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820658474833240575749897 615493856124930431812423)
                      ·
                        rfl

theorem cell23_1198670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_1198670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198670 prefixEnd_1198670 := by exact prefixLift 1198670
  have htrace : WordTrace (prefixWord ++ tailWord_1198670) baseStart_1198670 baseEnd_1198670 := by
    simpa [prefixWord, tailWord_1198670, baseEnd_1198670] using wordTrace_append hprefix tailTrace_1198670
  have hstable : (prefixWord ++ tailWord_1198670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198670).length < 2 ^ (prefixWord ++ tailWord_1198670).sum := by decide
  have hdescent : baseEnd_1198670 < baseStart_1198670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198673 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_1198673 : Nat := 118140960795 + 1198673 * 2 ^ 59
def prefixEnd_1198673 : Nat := 4983230072969 + 3 ^ 40 * 1198673 * 2
def baseEnd_1198673 : Nat := 615495396566893920074909

theorem tailTrace_1198673 : CollatzResearch.WordTrace tailWord_1198673 prefixEnd_1198673 615495396566893920074909 := by
  unfold tailWord_1198673
  simp only [CollatzResearch.WordTrace]
  refine ⟨43719195986419912895152673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29146130657613275263435115 43719195986419912895152673)
  ·
    refine ⟨32789396989814934671364505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43719195986419912895152673 32789396989814934671364505)
    ·
      refine ⟨24592047742361201003523379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32789396989814934671364505 24592047742361201003523379)
      ·
        refine ⟨36888071613541801505285069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24592047742361201003523379 36888071613541801505285069)
        ·
          refine ⟨13833026855078175564481901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36888071613541801505285069 13833026855078175564481901)
          ·
            refine ⟨5187385070654315836680713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13833026855078175564481901 5187385070654315836680713)
            ·
              refine ⟨3890538802990736877510535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5187385070654315836680713 3890538802990736877510535)
              ·
                refine ⟨5835808204486105316265803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3890538802990736877510535 5835808204486105316265803)
                ·
                  refine ⟨8753712306729157974398705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5835808204486105316265803 8753712306729157974398705)
                  ·
                    refine ⟨6565284230046868480799029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8753712306729157974398705 6565284230046868480799029)
                    ·
                      refine ⟨615495396566893920074909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6565284230046868480799029 615495396566893920074909)
                      ·
                        rfl

theorem cell23_1198673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_1198673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198673 prefixEnd_1198673 := by exact prefixLift 1198673
  have htrace : WordTrace (prefixWord ++ tailWord_1198673) baseStart_1198673 baseEnd_1198673 := by
    simpa [prefixWord, tailWord_1198673, baseEnd_1198673] using wordTrace_append hprefix tailTrace_1198673
  have hstable : (prefixWord ++ tailWord_1198673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198673).length < 2 ^ (prefixWord ++ tailWord_1198673).sum := by decide
  have hdescent : baseEnd_1198673 < baseStart_1198673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198700 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_1198700 : Nat := 118140960795 + 1198700 * 2 ^ 59
def prefixEnd_1198700 : Nat := 4983230072969 + 3 ^ 40 * 1198700 * 2
def baseEnd_1198700 : Nat := 615509260544565314437285

theorem tailTrace_1198700 : CollatzResearch.WordTrace tailWord_1198700 prefixEnd_1198700 615509260544565314437285 := by
  unfold tailWord_1198700
  simp only [CollatzResearch.WordTrace]
  refine ⟨21860090378661048253192777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29146787171548064337590369 21860090378661048253192777)
  ·
    refine ⟨16395067783995786189894583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21860090378661048253192777 16395067783995786189894583)
    ·
      refine ⟨24592601675993679284841875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16395067783995786189894583 24592601675993679284841875)
      ·
        refine ⟨36888902513990518927262813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24592601675993679284841875 36888902513990518927262813)
        ·
          refine ⟨13833338442746444597723555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36888902513990518927262813 13833338442746444597723555)
          ·
            refine ⟨20750007664119666896585333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13833338442746444597723555 20750007664119666896585333)
            ·
              refine ⟨1945313218511218771554875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20750007664119666896585333 1945313218511218771554875)
              ·
                refine ⟨2917969827766828157332313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945313218511218771554875 2917969827766828157332313)
                ·
                  refine ⟨2188477370825121117999235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2917969827766828157332313 2188477370825121117999235)
                  ·
                    refine ⟨3282716056237681676998853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188477370825121117999235 3282716056237681676998853)
                    ·
                      refine ⟨615509260544565314437285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3282716056237681676998853 615509260544565314437285)
                      ·
                        rfl

theorem cell23_1198700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_1198700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198700 prefixEnd_1198700 := by exact prefixLift 1198700
  have htrace : WordTrace (prefixWord ++ tailWord_1198700) baseStart_1198700 baseEnd_1198700 := by
    simpa [prefixWord, tailWord_1198700, baseEnd_1198700] using wordTrace_append hprefix tailTrace_1198700
  have hstable : (prefixWord ++ tailWord_1198700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198700).length < 2 ^ (prefixWord ++ tailWord_1198700).sum := by decide
  have hdescent : baseEnd_1198700 < baseStart_1198700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198713 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1198713 : Nat := 118140960795 + 1198713 * 2 ^ 59
def prefixEnd_1198713 : Nat := 4983230072969 + 3 ^ 40 * 1198713 * 2
def baseEnd_1198713 : Nat := 615515935793073763574725

theorem tailTrace_1198713 : CollatzResearch.WordTrace tailWord_1198713 prefixEnd_1198713 615515935793073763574725 := by
  unfold tailWord_1198713
  simp only [CollatzResearch.WordTrace]
  refine ⟨43720654906274999726608793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29147103270849999817739195 43720654906274999726608793)
  ·
    refine ⟨32790491179706249794956595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43720654906274999726608793 32790491179706249794956595)
    ·
      refine ⟨49185736769559374692434893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32790491179706249794956595 49185736769559374692434893)
      ·
        refine ⟨18444651288584765509663085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49185736769559374692434893 18444651288584765509663085)
        ·
          refine ⟨6916744233219287066123657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18444651288584765509663085 6916744233219287066123657)
          ·
            refine ⟨5187558174914465299592743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6916744233219287066123657 5187558174914465299592743)
            ·
              refine ⟨7781337262371697949389115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5187558174914465299592743 7781337262371697949389115)
              ·
                refine ⟨11672005893557546924083673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7781337262371697949389115 11672005893557546924083673)
                ·
                  refine ⟨8754004420168160193062755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11672005893557546924083673 8754004420168160193062755)
                  ·
                    refine ⟨13131006630252240289594133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8754004420168160193062755 13131006630252240289594133)
                    ·
                      refine ⟨615515935793073763574725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13131006630252240289594133 615515935793073763574725)
                      ·
                        rfl

theorem cell23_1198713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1198713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198713 prefixEnd_1198713 := by exact prefixLift 1198713
  have htrace : WordTrace (prefixWord ++ tailWord_1198713) baseStart_1198713 baseEnd_1198713 := by
    simpa [prefixWord, tailWord_1198713, baseEnd_1198713] using wordTrace_append hprefix tailTrace_1198713
  have hstable : (prefixWord ++ tailWord_1198713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198713).length < 2 ^ (prefixWord ++ tailWord_1198713).sum := by decide
  have hdescent : baseEnd_1198713 < baseStart_1198713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198727 : List Nat := [1, 1, 4, 2, 1, 2, 1, 6, 1, 4]
def baseStart_1198727 : Nat := 118140960795 + 1198727 * 2 ^ 59
def prefixEnd_1198727 : Nat := 4983230072969 + 3 ^ 40 * 1198727 * 2
def baseEnd_1198727 : Nat := 205174374840745569599887

theorem tailTrace_1198727 : CollatzResearch.WordTrace tailWord_1198727 prefixEnd_1198727 205174374840745569599887 := by
  unfold tailWord_1198727
  simp only [CollatzResearch.WordTrace]
  refine ⟨43721165528224280117618435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29147443685482853411745623 43721165528224280117618435)
  ·
    refine ⟨65581748292336420176427653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43721165528224280117618435 65581748292336420176427653)
    ·
      refine ⟨12296577804813078783080185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65581748292336420176427653 12296577804813078783080185)
      ·
        refine ⟨9222433353609809087310139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12296577804813078783080185 9222433353609809087310139)
        ·
          refine ⟨13833650030414713630965209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9222433353609809087310139 13833650030414713630965209)
          ·
            refine ⟨10375237522811035223223907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13833650030414713630965209 10375237522811035223223907)
            ·
              refine ⟨15562856284216552834835861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10375237522811035223223907 15562856284216552834835861)
              ·
                refine ⟨729508888322650914132931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15562856284216552834835861 729508888322650914132931)
                ·
                  refine ⟨1094263332483976371199397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729508888322650914132931 1094263332483976371199397)
                  ·
                    refine ⟨205174374840745569599887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1094263332483976371199397 205174374840745569599887)
                    ·
                      rfl

theorem cell23_1198727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_1198727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198727 prefixEnd_1198727 := by exact prefixLift 1198727
  have htrace : WordTrace (prefixWord ++ tailWord_1198727) baseStart_1198727 baseEnd_1198727 := by
    simpa [prefixWord, tailWord_1198727, baseEnd_1198727] using wordTrace_append hprefix tailTrace_1198727
  have hstable : (prefixWord ++ tailWord_1198727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198727).length < 2 ^ (prefixWord ++ tailWord_1198727).sum := by decide
  have hdescent : baseEnd_1198727 < baseStart_1198727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198743 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1198743 : Nat := 118140960795 + 1198743 * 2 ^ 59
def prefixEnd_1198743 : Nat := 4983230072969 + 3 ^ 40 * 1198743 * 2
def baseEnd_1198743 : Nat := 615531340212708646199587

theorem tailTrace_1198743 : CollatzResearch.WordTrace tailWord_1198743 prefixEnd_1198743 615531340212708646199587 := by
  unfold tailWord_1198743
  simp only [CollatzResearch.WordTrace]
  refine ⟨43721749096166314850200883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29147832730777543233467255 43721749096166314850200883)
  ·
    refine ⟨65582623644249472275301325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43721749096166314850200883 65582623644249472275301325)
    ·
      refine ⟨24593483866593552103237997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65582623644249472275301325 24593483866593552103237997)
      ·
        refine ⟨9222556449972582038714249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24593483866593552103237997 9222556449972582038714249)
        ·
          refine ⟨6916917337479436529035687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9222556449972582038714249 6916917337479436529035687)
          ·
            refine ⟨10375376006219154793553531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916917337479436529035687 10375376006219154793553531)
            ·
              refine ⟨15563064009328732190330297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10375376006219154793553531 15563064009328732190330297)
              ·
                refine ⟨11672298006996549142747723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15563064009328732190330297 11672298006996549142747723)
                ·
                  refine ⟨17508447010494823714121585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11672298006996549142747723 17508447010494823714121585)
                  ·
                    refine ⟨13131335257871117785591189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17508447010494823714121585 13131335257871117785591189)
                    ·
                      refine ⟨615531340212708646199587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13131335257871117785591189 615531340212708646199587)
                      ·
                        rfl

theorem cell23_1198743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1198743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198743 prefixEnd_1198743 := by exact prefixLift 1198743
  have htrace : WordTrace (prefixWord ++ tailWord_1198743) baseStart_1198743 baseEnd_1198743 := by
    simpa [prefixWord, tailWord_1198743, baseEnd_1198743] using wordTrace_append hprefix tailTrace_1198743
  have hstable : (prefixWord ++ tailWord_1198743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198743).length < 2 ^ (prefixWord ++ tailWord_1198743).sum := by decide
  have hdescent : baseEnd_1198743 < baseStart_1198743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198784 : List Nat := [2, 1, 1, 2, 4, 4, 1, 1, 3, 1, 3]
def baseStart_1198784 : Nat := 118140960795 + 1198784 * 2 ^ 59
def prefixEnd_1198784 : Nat := 4983230072969 + 3 ^ 40 * 1198784 * 2
def baseEnd_1198784 : Nat := 615552392919542985786899

theorem tailTrace_1198784 : CollatzResearch.WordTrace tailWord_1198784 prefixEnd_1198784 615552392919542985786899 := by
  unfold tailWord_1198784
  simp only [CollatzResearch.WordTrace]
  refine ⟨21861622244508889426221703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29148829659345185901628937 21861622244508889426221703)
  ·
    refine ⟨32792433366763334139332555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21861622244508889426221703 32792433366763334139332555)
    ·
      refine ⟨49188650050145001208998833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32792433366763334139332555 49188650050145001208998833)
      ·
        refine ⟨36891487537608750906749125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49188650050145001208998833 36891487537608750906749125)
        ·
          refine ⟨6917153913301640795015461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36891487537608750906749125 6917153913301640795015461)
          ·
            refine ⟨1296966358744057649065399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6917153913301640795015461 1296966358744057649065399)
            ·
              refine ⟨1945449538116086473598099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296966358744057649065399 1945449538116086473598099)
              ·
                refine ⟨2918174307174129710397149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945449538116086473598099 2918174307174129710397149)
                ·
                  refine ⟨1094315365190298641398931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2918174307174129710397149 1094315365190298641398931)
                  ·
                    refine ⟨1641473047785447962098397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1094315365190298641398931 1641473047785447962098397)
                    ·
                      refine ⟨615552392919542985786899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1641473047785447962098397 615552392919542985786899)
                      ·
                        rfl

theorem cell23_1198784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_1198784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198784 prefixEnd_1198784 := by exact prefixLift 1198784
  have htrace : WordTrace (prefixWord ++ tailWord_1198784) baseStart_1198784 baseEnd_1198784 := by
    simpa [prefixWord, tailWord_1198784, baseEnd_1198784] using wordTrace_append hprefix tailTrace_1198784
  have hstable : (prefixWord ++ tailWord_1198784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198784).length < 2 ^ (prefixWord ++ tailWord_1198784).sum := by decide
  have hdescent : baseEnd_1198784 < baseStart_1198784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198803 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 4]
def baseStart_1198803 : Nat := 118140960795 + 1198803 * 2 ^ 59
def prefixEnd_1198803 : Nat := 4983230072969 + 3 ^ 40 * 1198803 * 2
def baseEnd_1198803 : Nat := 615562149051978411449311

theorem tailTrace_1198803 : CollatzResearch.WordTrace tailWord_1198803 prefixEnd_1198803 615562149051978411449311 := by
  unfold tailWord_1198803
  simp only [CollatzResearch.WordTrace]
  refine ⟨43723937475948945097385063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29149291650632630064923375 43723937475948945097385063)
  ·
    refine ⟨65585906213923417646077595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43723937475948945097385063 65585906213923417646077595)
    ·
      refine ⟨98378859320885126469116393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65585906213923417646077595 98378859320885126469116393)
      ·
        refine ⟨73784144490663844851837295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98378859320885126469116393 73784144490663844851837295)
        ·
          refine ⟨110676216735995767277755943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73784144490663844851837295 110676216735995767277755943)
          ·
            refine ⟨166014325103993650916633915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110676216735995767277755943 166014325103993650916633915)
            ·
              refine ⟨249021487655990476374950873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166014325103993650916633915 249021487655990476374950873)
              ·
                refine ⟨186766115741992857281213155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249021487655990476374950873 186766115741992857281213155)
                ·
                  refine ⟨280149173612989285921819733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186766115741992857281213155 280149173612989285921819733)
                  ·
                    refine ⟨3282998128277218194396325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 280149173612989285921819733 3282998128277218194396325)
                    ·
                      refine ⟨615562149051978411449311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3282998128277218194396325 615562149051978411449311)
                      ·
                        rfl

theorem cell23_1198803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_1198803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198803 prefixEnd_1198803 := by exact prefixLift 1198803
  have htrace : WordTrace (prefixWord ++ tailWord_1198803) baseStart_1198803 baseEnd_1198803 := by
    simpa [prefixWord, tailWord_1198803, baseEnd_1198803] using wordTrace_append hprefix tailTrace_1198803
  have hstable : (prefixWord ++ tailWord_1198803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198803).length < 2 ^ (prefixWord ++ tailWord_1198803).sum := by decide
  have hdescent : baseEnd_1198803 < baseStart_1198803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198807 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_1198807 : Nat := 118140960795 + 1198807 * 2 ^ 59
def prefixEnd_1198807 : Nat := 4983230072969 + 3 ^ 40 * 1198807 * 2
def baseEnd_1198807 : Nat := 615564202974596395799293

theorem tailTrace_1198807 : CollatzResearch.WordTrace tailWord_1198807 prefixEnd_1198807 615564202974596395799293 := by
  unfold tailWord_1198807
  simp only [CollatzResearch.WordTrace]
  refine ⟨43724083367934453780530675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29149388911956302520353783 43724083367934453780530675)
  ·
    refine ⟨65586125051901680670796013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43724083367934453780530675 65586125051901680670796013)
    ·
      refine ⟨24594796894463130251548505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65586125051901680670796013 24594796894463130251548505)
      ·
        refine ⟨18446097670847347688661379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24594796894463130251548505 18446097670847347688661379)
        ·
          refine ⟨27669146506271021532992069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18446097670847347688661379 27669146506271021532992069)
          ·
            refine ⟨5187964969925816537436013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27669146506271021532992069 5187964969925816537436013)
            ·
              refine ⟨1945486863722181201538505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5187964969925816537436013 1945486863722181201538505)
              ·
                refine ⟨1459115147791635901153879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1945486863722181201538505 1459115147791635901153879)
                ·
                  refine ⟨2188672721687453851730819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459115147791635901153879 2188672721687453851730819)
                  ·
                    refine ⟨3283009082531180777596229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188672721687453851730819 3283009082531180777596229)
                    ·
                      refine ⟨615564202974596395799293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3283009082531180777596229 615564202974596395799293)
                      ·
                        rfl

theorem cell23_1198807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_1198807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198807 prefixEnd_1198807 := by exact prefixLift 1198807
  have htrace : WordTrace (prefixWord ++ tailWord_1198807) baseStart_1198807 baseEnd_1198807 := by
    simpa [prefixWord, tailWord_1198807, baseEnd_1198807] using wordTrace_append hprefix tailTrace_1198807
  have hstable : (prefixWord ++ tailWord_1198807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198807).length < 2 ^ (prefixWord ++ tailWord_1198807).sum := by decide
  have hdescent : baseEnd_1198807 < baseStart_1198807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198820 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_1198820 : Nat := 118140960795 + 1198820 * 2 ^ 59
def prefixEnd_1198820 : Nat := 4983230072969 + 3 ^ 40 * 1198820 * 2
def baseEnd_1198820 : Nat := 615570878223104844936733

theorem tailTrace_1198820 : CollatzResearch.WordTrace tailWord_1198820 prefixEnd_1198820 615570878223104844936733 := by
  unfold tailWord_1198820
  simp only [CollatzResearch.WordTrace]
  refine ⟨21862278758443678500376957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29149705011258238000502609 21862278758443678500376957)
  ·
    refine ⟨8198354534416379437641359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21862278758443678500376957 8198354534416379437641359)
    ·
      refine ⟨12297531801624569156462039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8198354534416379437641359 12297531801624569156462039)
      ·
        refine ⟨18446297702436853734693059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12297531801624569156462039 18446297702436853734693059)
        ·
          refine ⟨27669446553655280602039589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18446297702436853734693059 27669446553655280602039589)
          ·
            refine ⟨5188021228810365112882423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27669446553655280602039589 5188021228810365112882423)
            ·
              refine ⟨7782031843215547669323635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5188021228810365112882423 7782031843215547669323635)
              ·
                refine ⟨11673047764823321503985453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782031843215547669323635 11673047764823321503985453)
                ·
                  refine ⟨4377392911808745563994545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11673047764823321503985453 4377392911808745563994545)
                  ·
                    refine ⟨3283044683856559172995909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4377392911808745563994545 3283044683856559172995909)
                    ·
                      refine ⟨615570878223104844936733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3283044683856559172995909 615570878223104844936733)
                      ·
                        rfl

theorem cell23_1198820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_1198820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198820 prefixEnd_1198820 := by exact prefixLift 1198820
  have htrace : WordTrace (prefixWord ++ tailWord_1198820) baseStart_1198820 baseEnd_1198820 := by
    simpa [prefixWord, tailWord_1198820, baseEnd_1198820] using wordTrace_append hprefix tailTrace_1198820
  have hstable : (prefixWord ++ tailWord_1198820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198820).length < 2 ^ (prefixWord ++ tailWord_1198820).sum := by decide
  have hdescent : baseEnd_1198820 < baseStart_1198820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198834 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_1198834 : Nat := 118140960795 + 1198834 * 2 ^ 59
def prefixEnd_1198834 : Nat := 4983230072969 + 3 ^ 40 * 1198834 * 2
def baseEnd_1198834 : Nat := 205192688984089263387223

theorem tailTrace_1198834 : CollatzResearch.WordTrace tailWord_1198834 prefixEnd_1198834 205192688984089263387223 := by
  unfold tailWord_1198834
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931267034709159347940889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29150045425891091594509037 10931267034709159347940889)
  ·
    refine ⟨8198450276031869510955667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10931267034709159347940889 8198450276031869510955667)
    ·
      refine ⟨12297675414047804266433501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8198450276031869510955667 12297675414047804266433501)
      ·
        refine ⟨4611628280267926599912563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12297675414047804266433501 4611628280267926599912563)
        ·
          refine ⟨6917442420401889899868845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611628280267926599912563 6917442420401889899868845)
          ·
            refine ⟨2594040907650708712450817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6917442420401889899868845 2594040907650708712450817)
            ·
              refine ⟨1945530680738031534338113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594040907650708712450817 1945530680738031534338113)
              ·
                refine ⟨1459148010553523650753585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1945530680738031534338113 1459148010553523650753585)
                ·
                  refine ⟨1094361007915142738065189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1459148010553523650753585 1094361007915142738065189)
                  ·
                    refine ⟨205192688984089263387223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1094361007915142738065189 205192688984089263387223)
                    ·
                      rfl

theorem cell23_1198834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_1198834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198834 prefixEnd_1198834 := by exact prefixLift 1198834
  have htrace : WordTrace (prefixWord ++ tailWord_1198834) baseStart_1198834 baseEnd_1198834 := by
    simpa [prefixWord, tailWord_1198834, baseEnd_1198834] using wordTrace_append hprefix tailTrace_1198834
  have hstable : (prefixWord ++ tailWord_1198834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198834).length < 2 ^ (prefixWord ++ tailWord_1198834).sum := by decide
  have hdescent : baseEnd_1198834 < baseStart_1198834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198840 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_1198840 : Nat := 118140960795 + 1198840 * 2 ^ 59
def prefixEnd_1198840 : Nat := 4983230072969 + 3 ^ 40 * 1198840 * 2
def baseEnd_1198840 : Nat := 615581147836194766686641

theorem tailTrace_1198840 : CollatzResearch.WordTrace tailWord_1198840 prefixEnd_1198840 615581147836194766686641 := by
  unfold tailWord_1198840
  simp only [CollatzResearch.WordTrace]
  refine ⟨21862643488407450208240987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29150191317876600277654649 21862643488407450208240987)
  ·
    refine ⟨32793965232611175312361481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21862643488407450208240987 32793965232611175312361481)
    ·
      refine ⟨24595473924458381484271111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32793965232611175312361481 24595473924458381484271111)
      ·
        refine ⟨36893210886687572226406667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24595473924458381484271111 36893210886687572226406667)
        ·
          refine ⟨55339816330031358339610001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36893210886687572226406667 55339816330031358339610001)
          ·
            refine ⟨41504862247523518754707501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55339816330031358339610001 41504862247523518754707501)
            ·
              refine ⟨15564323342821319533015313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41504862247523518754707501 15564323342821319533015313)
              ·
                refine ⟨11673242507115989649761485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15564323342821319533015313 11673242507115989649761485)
                ·
                  refine ⟨4377465940168496118660557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11673242507115989649761485 4377465940168496118660557)
                  ·
                    refine ⟨1641549727563186044497709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4377465940168496118660557 1641549727563186044497709)
                    ·
                      refine ⟨615581147836194766686641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1641549727563186044497709 615581147836194766686641)
                      ·
                        rfl

theorem cell23_1198840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_1198840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198840 prefixEnd_1198840 := by exact prefixLift 1198840
  have htrace : WordTrace (prefixWord ++ tailWord_1198840) baseStart_1198840 baseEnd_1198840 := by
    simpa [prefixWord, tailWord_1198840, baseEnd_1198840] using wordTrace_append hprefix tailTrace_1198840
  have hstable : (prefixWord ++ tailWord_1198840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198840).length < 2 ^ (prefixWord ++ tailWord_1198840).sum := by decide
  have hdescent : baseEnd_1198840 < baseStart_1198840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198867 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 3, 3, 2]
def baseStart_1198867 : Nat := 118140960795 + 1198867 * 2 ^ 59
def prefixEnd_1198867 : Nat := 4983230072969 + 3 ^ 40 * 1198867 * 2
def baseEnd_1198867 : Nat := 615595011813866161049017

theorem tailTrace_1198867 : CollatzResearch.WordTrace tailWord_1198867 prefixEnd_1198867 615595011813866161049017 := by
  unfold tailWord_1198867
  simp only [CollatzResearch.WordTrace]
  refine ⟨43726271747717084027714855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29150847831811389351809903 43726271747717084027714855)
  ·
    refine ⟨65589407621575626041572283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43726271747717084027714855 65589407621575626041572283)
    ·
      refine ⟨98384111432363439062358425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65589407621575626041572283 98384111432363439062358425)
      ·
        refine ⟨73788083574272579296768819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98384111432363439062358425 73788083574272579296768819)
        ·
          refine ⟨110682125361408868945153229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73788083574272579296768819 110682125361408868945153229)
          ·
            refine ⟨41505797010528325854432461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110682125361408868945153229 41505797010528325854432461)
            ·
              refine ⟨15564673878948122195412173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41505797010528325854432461 15564673878948122195412173)
              ·
                refine ⟨5836752704605545823279565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15564673878948122195412173 5836752704605545823279565)
                ·
                  refine ⟨2188782264227079683729837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5836752704605545823279565 2188782264227079683729837)
                  ·
                    refine ⟨820793349085154881398689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2188782264227079683729837 820793349085154881398689)
                    ·
                      refine ⟨615595011813866161049017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820793349085154881398689 615595011813866161049017)
                      ·
                        rfl

theorem cell23_1198867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 3, 2].length) (baseStart_1198867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198867 prefixEnd_1198867 := by exact prefixLift 1198867
  have htrace : WordTrace (prefixWord ++ tailWord_1198867) baseStart_1198867 baseEnd_1198867 := by
    simpa [prefixWord, tailWord_1198867, baseEnd_1198867] using wordTrace_append hprefix tailTrace_1198867
  have hstable : (prefixWord ++ tailWord_1198867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198867).length < 2 ^ (prefixWord ++ tailWord_1198867).sum := by decide
  have hdescent : baseEnd_1198867 < baseStart_1198867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198920 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 7]
def baseStart_1198920 : Nat := 118140960795 + 1198920 * 2 ^ 59
def prefixEnd_1198920 : Nat := 4983230072969 + 3 ^ 40 * 1198920 * 2
def baseEnd_1198920 : Nat := 68402469587617161520697

theorem tailTrace_1198920 : CollatzResearch.WordTrace tailWord_1198920 prefixEnd_1198920 68402469587617161520697 := by
  unfold tailWord_1198920
  simp only [CollatzResearch.WordTrace]
  refine ⟨21864102408262537039697107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29152136544350049386262809 21864102408262537039697107)
  ·
    refine ⟨32796153612393805559545661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21864102408262537039697107 32796153612393805559545661)
    ·
      refine ⟨12298557604647677084829623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32796153612393805559545661 12298557604647677084829623)
      ·
        refine ⟨18447836406971515627244435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12298557604647677084829623 18447836406971515627244435)
        ·
          refine ⟨27671754610457273440866653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18447836406971515627244435 27671754610457273440866653)
          ·
            refine ⟨10376907978921477540324995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27671754610457273440866653 10376907978921477540324995)
            ·
              refine ⟨15565361968382216310487493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10376907978921477540324995 15565361968382216310487493)
              ·
                refine ⟨2918505369071665558216405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15565361968382216310487493 2918505369071665558216405)
                ·
                  refine ⟨68402469587617161520697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2918505369071665558216405 68402469587617161520697)
                  ·
                    rfl

theorem cell23_1198920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 7].length) (baseStart_1198920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198920 prefixEnd_1198920 := by exact prefixLift 1198920
  have htrace : WordTrace (prefixWord ++ tailWord_1198920) baseStart_1198920 baseEnd_1198920 := by
    simpa [prefixWord, tailWord_1198920, baseEnd_1198920] using wordTrace_append hprefix tailTrace_1198920
  have hstable : (prefixWord ++ tailWord_1198920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198920).length < 2 ^ (prefixWord ++ tailWord_1198920).sum := by decide
  have hdescent : baseEnd_1198920 < baseStart_1198920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198960 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_1198960 : Nat := 118140960795 + 1198960 * 2 ^ 59
def prefixEnd_1198960 : Nat := 4983230072969 + 3 ^ 40 * 1198960 * 2
def baseEnd_1198960 : Nat := 615642765514734297186089

theorem tailTrace_1198960 : CollatzResearch.WordTrace tailWord_1198960 prefixEnd_1198960 615642765514734297186089 := by
  unfold tailWord_1198960
  simp only [CollatzResearch.WordTrace]
  refine ⟨21864831868190080455425167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29153109157586773940566889 21864831868190080455425167)
  ·
    refine ⟨32797247802285120683137751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21864831868190080455425167 32797247802285120683137751)
    ·
      refine ⟨49195871703427681024706627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32797247802285120683137751 49195871703427681024706627)
      ·
        refine ⟨73793807555141521537059941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49195871703427681024706627 73793807555141521537059941)
        ·
          refine ⟨13836338916589035288198739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73793807555141521537059941 13836338916589035288198739)
          ·
            refine ⟨20754508374883552932298109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13836338916589035288198739 20754508374883552932298109)
            ·
              refine ⟨7782940640581332349611791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20754508374883552932298109 7782940640581332349611791)
              ·
                refine ⟨11674410960871998524417687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7782940640581332349611791 11674410960871998524417687)
                ·
                  refine ⟨17511616441307997786626531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11674410960871998524417687 17511616441307997786626531)
                  ·
                    refine ⟨26267424661961996679939797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17511616441307997786626531 26267424661961996679939797)
                    ·
                      refine ⟨615642765514734297186089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26267424661961996679939797 615642765514734297186089)
                      ·
                        rfl

theorem cell23_1198960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_1198960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198960 prefixEnd_1198960 := by exact prefixLift 1198960
  have htrace : WordTrace (prefixWord ++ tailWord_1198960) baseStart_1198960 baseEnd_1198960 := by
    simpa [prefixWord, tailWord_1198960, baseEnd_1198960] using wordTrace_append hprefix tailTrace_1198960
  have hstable : (prefixWord ++ tailWord_1198960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198960).length < 2 ^ (prefixWord ++ tailWord_1198960).sum := by decide
  have hdescent : baseEnd_1198960 < baseStart_1198960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198965 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_1198965 : Nat := 118140960795 + 1198965 * 2 ^ 59
def prefixEnd_1198965 : Nat := 4983230072969 + 3 ^ 40 * 1198965 * 2
def baseEnd_1198965 : Nat := 615645332918006777623567

theorem tailTrace_1198965 : CollatzResearch.WordTrace tailWord_1198965 prefixEnd_1198965 615645332918006777623567 := by
  unfold tailWord_1198965
  simp only [CollatzResearch.WordTrace]
  refine ⟨43729846101362046764782349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29153230734241364509854899 43729846101362046764782349)
  ·
    refine ⟨16398692288010767536793381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43729846101362046764782349 16398692288010767536793381)
    ·
      refine ⟨3074754804002018913148759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16398692288010767536793381 3074754804002018913148759)
      ·
        refine ⟨4612132206003028369723139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3074754804002018913148759 4612132206003028369723139)
        ·
          refine ⟨6918198309004542554584709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4612132206003028369723139 6918198309004542554584709)
          ·
            refine ⟨1297162182938351728984633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6918198309004542554584709 1297162182938351728984633)
            ·
              refine ⟨972871637203763796738475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297162182938351728984633 972871637203763796738475)
              ·
                refine ⟨1459307455805645695107713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972871637203763796738475 1459307455805645695107713)
                ·
                  refine ⟨1094480591854234271330785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1459307455805645695107713 1094480591854234271330785)
                  ·
                    refine ⟨820860443890675703498089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1094480591854234271330785 820860443890675703498089)
                    ·
                      refine ⟨615645332918006777623567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820860443890675703498089 615645332918006777623567)
                      ·
                        rfl

theorem cell23_1198965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_1198965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198965 prefixEnd_1198965 := by exact prefixLift 1198965
  have htrace : WordTrace (prefixWord ++ tailWord_1198965) baseStart_1198965 baseEnd_1198965 := by
    simpa [prefixWord, tailWord_1198965, baseEnd_1198965] using wordTrace_append hprefix tailTrace_1198965
  have hstable : (prefixWord ++ tailWord_1198965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198965).length < 2 ^ (prefixWord ++ tailWord_1198965).sum := by decide
  have hdescent : baseEnd_1198965 < baseStart_1198965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198984 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1198984 : Nat := 118140960795 + 1198984 * 2 ^ 59
def prefixEnd_1198984 : Nat := 4983230072969 + 3 ^ 40 * 1198984 * 2
def baseEnd_1198984 : Nat := 205218363016814067761993

theorem tailTrace_1198984 : CollatzResearch.WordTrace tailWord_1198984 prefixEnd_1198984 205218363016814067761993 := by
  unfold tailWord_1198984
  simp only [CollatzResearch.WordTrace]
  refine ⟨21865269544146606504862003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29153692725528808673149337 21865269544146606504862003)
  ·
    refine ⟨32797904316219909757293005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21865269544146606504862003 32797904316219909757293005)
    ·
      refine ⟨12299214118582466158984877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32797904316219909757293005 12299214118582466158984877)
      ·
        refine ⟨4612205294468424809619329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12299214118582466158984877 4612205294468424809619329)
        ·
          refine ⟨3459153970851318607214497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4612205294468424809619329 3459153970851318607214497)
          ·
            refine ⟨2594365478138488955410873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459153970851318607214497 2594365478138488955410873)
            ·
              refine ⟨1945774108603866716558155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594365478138488955410873 1945774108603866716558155)
              ·
                refine ⟨2918661162905800074837233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945774108603866716558155 2918661162905800074837233)
                ·
                  refine ⟨2188995872179350056127925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2918661162905800074837233 2188995872179350056127925)
                  ·
                    refine ⟨205218363016814067761993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2188995872179350056127925 205218363016814067761993)
                    ·
                      rfl

theorem cell23_1198984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1198984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198984 prefixEnd_1198984 := by exact prefixLift 1198984
  have htrace : WordTrace (prefixWord ++ tailWord_1198984) baseStart_1198984 baseEnd_1198984 := by
    simpa [prefixWord, tailWord_1198984, baseEnd_1198984] using wordTrace_append hprefix tailTrace_1198984
  have hstable : (prefixWord ++ tailWord_1198984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198984).length < 2 ^ (prefixWord ++ tailWord_1198984).sum := by decide
  have hdescent : baseEnd_1198984 < baseStart_1198984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198987 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 4]
def baseStart_1198987 : Nat := 118140960795 + 1198987 * 2 ^ 59
def prefixEnd_1198987 : Nat := 4983230072969 + 3 ^ 40 * 1198987 * 2
def baseEnd_1198987 : Nat := 615656629492405691548465

theorem tailTrace_1198987 : CollatzResearch.WordTrace tailWord_1198987 prefixEnd_1198987 615656629492405691548465 := by
  unfold tailWord_1198987
  simp only [CollatzResearch.WordTrace]
  refine ⟨43730648507282344522083215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29153765671521563014722143 43730648507282344522083215)
  ·
    refine ⟨65595972760923516783124823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43730648507282344522083215 65595972760923516783124823)
    ·
      refine ⟨98393959141385275174687235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65595972760923516783124823 98393959141385275174687235)
      ·
        refine ⟨147590938712077912762030853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98393959141385275174687235 147590938712077912762030853)
        ·
          refine ⟨27673301008514608642880785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147590938712077912762030853 27673301008514608642880785)
          ·
            refine ⟨20754975756385956482160589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27673301008514608642880785 20754975756385956482160589)
            ·
              refine ⟨7783115908644733680810221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20754975756385956482160589 7783115908644733680810221)
              ·
                refine ⟨2918668465741775130303833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7783115908644733680810221 2918668465741775130303833)
                ·
                  refine ⟨2189001349306331347727875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2918668465741775130303833 2189001349306331347727875)
                  ·
                    refine ⟨3283502023959497021591813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2189001349306331347727875 3283502023959497021591813)
                    ·
                      refine ⟨615656629492405691548465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3283502023959497021591813 615656629492405691548465)
                      ·
                        rfl

theorem cell23_1198987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 1, 4].length) (baseStart_1198987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1198987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1198987 prefixEnd_1198987 := by exact prefixLift 1198987
  have htrace : WordTrace (prefixWord ++ tailWord_1198987) baseStart_1198987 baseEnd_1198987 := by
    simpa [prefixWord, tailWord_1198987, baseEnd_1198987] using wordTrace_append hprefix tailTrace_1198987
  have hstable : (prefixWord ++ tailWord_1198987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198987).length < 2 ^ (prefixWord ++ tailWord_1198987).sum := by decide
  have hdescent : baseEnd_1198987 < baseStart_1198987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199048 : List Nat := [2, 1, 3, 1, 5, 1, 2, 3, 1, 4]
def baseStart_1199048 : Nat := 118140960795 + 1199048 * 2 ^ 59
def prefixEnd_1199048 : Nat := 4983230072969 + 3 ^ 40 * 1199048 * 2
def baseEnd_1199048 : Nat := 205229317270776650961895

theorem tailTrace_1199048 : CollatzResearch.WordTrace tailWord_1199048 prefixEnd_1199048 205229317270776650961895 := by
  unfold tailWord_1199048
  simp only [CollatzResearch.WordTrace]
  refine ⟨21866436680030675970026899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29155248906707567960035865 21866436680030675970026899)
  ·
    refine ⟨32799655020046013955040349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21866436680030675970026899 32799655020046013955040349)
    ·
      refine ⟨12299870632517255233140131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32799655020046013955040349 12299870632517255233140131)
      ·
        refine ⟨18449805948775882849710197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12299870632517255233140131 18449805948775882849710197)
        ·
          refine ⟨1729669307697739017160331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18449805948775882849710197 1729669307697739017160331)
          ·
            refine ⟨2594503961546608525740497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729669307697739017160331 2594503961546608525740497)
            ·
              refine ⟨1945877971159956394305373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594503961546608525740497 1945877971159956394305373)
              ·
                refine ⟨729704239184983647864515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1945877971159956394305373 729704239184983647864515)
                ·
                  refine ⟨1094556358777475471796773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729704239184983647864515 1094556358777475471796773)
                  ·
                    refine ⟨205229317270776650961895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1094556358777475471796773 205229317270776650961895)
                    ·
                      rfl

theorem cell23_1199048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_1199048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199048 prefixEnd_1199048 := by exact prefixLift 1199048
  have htrace : WordTrace (prefixWord ++ tailWord_1199048) baseStart_1199048 baseEnd_1199048 := by
    simpa [prefixWord, tailWord_1199048, baseEnd_1199048] using wordTrace_append hprefix tailTrace_1199048
  have hstable : (prefixWord ++ tailWord_1199048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199048).length < 2 ^ (prefixWord ++ tailWord_1199048).sum := by decide
  have hdescent : baseEnd_1199048 < baseStart_1199048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199061 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 6]
def baseStart_1199061 : Nat := 118140960795 + 1199061 * 2 ^ 59
def prefixEnd_1199061 : Nat := 4983230072969 + 3 ^ 40 * 1199061 * 2
def baseEnd_1199061 : Nat := 68410514117870933558125

theorem tailTrace_1199061 : CollatzResearch.WordTrace tailWord_1199061 prefixEnd_1199061 68410514117870933558125 := by
  unfold tailWord_1199061
  simp only [CollatzResearch.WordTrace]
  refine ⟨43733347509014255160277037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29155565006009503440184691 43733347509014255160277037)
  ·
    refine ⟨16400005315880345685103889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43733347509014255160277037 16400005315880345685103889)
    ·
      refine ⟨12300003986910259263827917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16400005315880345685103889 12300003986910259263827917)
      ·
        refine ⟨4612501495091347223935469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12300003986910259263827917 4612501495091347223935469)
        ·
          refine ⟨1729688060659255208975801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4612501495091347223935469 1729688060659255208975801)
          ·
            refine ⟨1297266045494441406731851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1729688060659255208975801 1297266045494441406731851)
            ·
              refine ⟨1945899068241662110097777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297266045494441406731851 1945899068241662110097777)
              ·
                refine ⟨1459424301181246582573333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1945899068241662110097777 1459424301181246582573333)
                ·
                  refine ⟨68410514117870933558125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1459424301181246582573333 68410514117870933558125)
                  ·
                    rfl

theorem cell23_1199061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_1199061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199061 prefixEnd_1199061 := by exact prefixLift 1199061
  have htrace : WordTrace (prefixWord ++ tailWord_1199061) baseStart_1199061 baseEnd_1199061 := by
    simpa [prefixWord, tailWord_1199061, baseEnd_1199061] using wordTrace_append hprefix tailTrace_1199061
  have hstable : (prefixWord ++ tailWord_1199061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199061).length < 2 ^ (prefixWord ++ tailWord_1199061).sum := by decide
  have hdescent : baseEnd_1199061 < baseStart_1199061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199097 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1199097 : Nat := 118140960795 + 1199097 * 2 ^ 59
def prefixEnd_1199097 : Nat := 4983230072969 + 3 ^ 40 * 1199097 * 2
def baseEnd_1199097 : Nat := 615713112364400261172959

theorem tailTrace_1199097 : CollatzResearch.WordTrace tailWord_1199097 prefixEnd_1199097 615713112364400261172959 := by
  unfold tailWord_1199097
  simp only [CollatzResearch.WordTrace]
  refine ⟨43734660536883833308587545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29156440357922555539058363 43734660536883833308587545)
  ·
    refine ⟨32800995402662874981440659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43734660536883833308587545 32800995402662874981440659)
    ·
      refine ⟨49201493103994312472160989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32800995402662874981440659 49201493103994312472160989)
      ·
        refine ⟨18450559913997867177060371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49201493103994312472160989 18450559913997867177060371)
        ·
          refine ⟨27675839870996800765590557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18450559913997867177060371 27675839870996800765590557)
          ·
            refine ⟨10378439951623800287096459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27675839870996800765590557 10378439951623800287096459)
            ·
              refine ⟨15567659927435700430644689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10378439951623800287096459 15567659927435700430644689)
              ·
                refine ⟨11675744945576775322983517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15567659927435700430644689 11675744945576775322983517)
                ·
                  refine ⟨4378404354591290746118819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11675744945576775322983517 4378404354591290746118819)
                  ·
                    refine ⟨6567606531886936119178229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4378404354591290746118819 6567606531886936119178229)
                    ·
                      refine ⟨615713112364400261172959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6567606531886936119178229 615713112364400261172959)
                      ·
                        rfl

theorem cell23_1199097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1199097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199097 prefixEnd_1199097 := by exact prefixLift 1199097
  have htrace : WordTrace (prefixWord ++ tailWord_1199097) baseStart_1199097 baseEnd_1199097 := by
    simpa [prefixWord, tailWord_1199097, baseEnd_1199097] using wordTrace_append hprefix tailTrace_1199097
  have hstable : (prefixWord ++ tailWord_1199097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199097).length < 2 ^ (prefixWord ++ tailWord_1199097).sum := by decide
  have hdescent : baseEnd_1199097 < baseStart_1199097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199105 : List Nat := [1, 2, 4, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_1199105 : Nat := 118140960795 + 1199105 * 2 ^ 59
def prefixEnd_1199105 : Nat := 4983230072969 + 3 ^ 40 * 1199105 * 2
def baseEnd_1199105 : Nat := 615717220209636229872923

theorem tailTrace_1199105 : CollatzResearch.WordTrace tailWord_1199105 prefixEnd_1199105 615717220209636229872923 := by
  unfold tailWord_1199105
  simp only [CollatzResearch.WordTrace]
  refine ⟨43734952320854850674878769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29156634880569900449919179 43734952320854850674878769)
  ·
    refine ⟨32801214240641138006159077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43734952320854850674878769 32801214240641138006159077)
    ·
      refine ⟨6150227670120213376154827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32801214240641138006159077 6150227670120213376154827)
      ·
        refine ⟨9225341505180320064232241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6150227670120213376154827 9225341505180320064232241)
        ·
          refine ⟨6919006128885240048174181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9225341505180320064232241 6919006128885240048174181)
          ·
            refine ⟨1297313649165982509032659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6919006128885240048174181 1297313649165982509032659)
            ·
              refine ⟨1945970473748973763548989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297313649165982509032659 1945970473748973763548989)
              ·
                refine ⟨729738927655865161330871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1945970473748973763548989 729738927655865161330871)
                ·
                  refine ⟨1094608391483797741996307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729738927655865161330871 1094608391483797741996307)
                  ·
                    refine ⟨1641912587225696612994461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1094608391483797741996307 1641912587225696612994461)
                    ·
                      refine ⟨615717220209636229872923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1641912587225696612994461 615717220209636229872923)
                      ·
                        rfl

theorem cell23_1199105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_1199105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199105 prefixEnd_1199105 := by exact prefixLift 1199105
  have htrace : WordTrace (prefixWord ++ tailWord_1199105) baseStart_1199105 baseEnd_1199105 := by
    simpa [prefixWord, tailWord_1199105, baseEnd_1199105] using wordTrace_append hprefix tailTrace_1199105
  have hstable : (prefixWord ++ tailWord_1199105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199105).length < 2 ^ (prefixWord ++ tailWord_1199105).sum := by decide
  have hdescent : baseEnd_1199105 < baseStart_1199105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199114 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1199114 : Nat := 118140960795 + 1199114 * 2 ^ 59
def prefixEnd_1199114 : Nat := 4983230072969 + 3 ^ 40 * 1199114 * 2
def baseEnd_1199114 : Nat := 615721841535526694660381

theorem tailTrace_1199114 : CollatzResearch.WordTrace tailWord_1199114 prefixEnd_1199114 615721841535526694660381 := by
  unfold tailWord_1199114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10933820144455561302989099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29156853718548163474637597 10933820144455561302989099)
  ·
    refine ⟨16400730216683341954483649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10933820144455561302989099 16400730216683341954483649)
    ·
      refine ⟨12300547662512506465862737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16400730216683341954483649 12300547662512506465862737)
      ·
        refine ⟨9225410746884379849397053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12300547662512506465862737 9225410746884379849397053)
        ·
          refine ⟨3459529030081642443523895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9225410746884379849397053 3459529030081642443523895)
          ·
            refine ⟨5189293545122463665285843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459529030081642443523895 5189293545122463665285843)
            ·
              refine ⟨7783940317683695497928765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5189293545122463665285843 7783940317683695497928765)
              ·
                refine ⟨2918977619131385811723287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7783940317683695497928765 2918977619131385811723287)
                ·
                  refine ⟨4378466428697078717584931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2918977619131385811723287 4378466428697078717584931)
                  ·
                    refine ⟨6567699643045618076377397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4378466428697078717584931 6567699643045618076377397)
                    ·
                      refine ⟨615721841535526694660381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6567699643045618076377397 615721841535526694660381)
                      ·
                        rfl

theorem cell23_1199114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1199114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199114 prefixEnd_1199114 := by exact prefixLift 1199114
  have htrace : WordTrace (prefixWord ++ tailWord_1199114) baseStart_1199114 baseEnd_1199114 := by
    simpa [prefixWord, tailWord_1199114, baseEnd_1199114] using wordTrace_append hprefix tailTrace_1199114
  have hstable : (prefixWord ++ tailWord_1199114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199114).length < 2 ^ (prefixWord ++ tailWord_1199114).sum := by decide
  have hdescent : baseEnd_1199114 < baseStart_1199114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199128 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 3, 2, 2]
def baseStart_1199128 : Nat := 118140960795 + 1199128 * 2 ^ 59
def prefixEnd_1199128 : Nat := 4983230072969 + 3 ^ 40 * 1199128 * 2
def baseEnd_1199128 : Nat := 615729030264689639885317

theorem tailTrace_1199128 : CollatzResearch.WordTrace tailWord_1199128 prefixEnd_1199128 615729030264689639885317 := by
  unfold tailWord_1199128
  simp only [CollatzResearch.WordTrace]
  refine ⟨21867895599885762801483019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29157194133181017068644025 21867895599885762801483019)
  ·
    refine ⟨32801843399828644202224529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21867895599885762801483019 32801843399828644202224529)
    ·
      refine ⟨24601382549871483151668397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32801843399828644202224529 24601382549871483151668397)
      ·
        refine ⟨9225518456201806181875649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24601382549871483151668397 9225518456201806181875649)
        ·
          refine ⟨6919138842151354636406737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9225518456201806181875649 6919138842151354636406737)
          ·
            refine ⟨5189354131613515977305053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6919138842151354636406737 5189354131613515977305053)
            ·
              refine ⟨1946007799355068491489395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5189354131613515977305053 1946007799355068491489395)
              ·
                refine ⟨2919011699032602737234093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946007799355068491489395 2919011699032602737234093)
                ·
                  refine ⟨1094629387137226026462785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2919011699032602737234093 1094629387137226026462785)
                  ·
                    refine ⟨820972040352919519847089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1094629387137226026462785 820972040352919519847089)
                    ·
                      refine ⟨615729030264689639885317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 820972040352919519847089 615729030264689639885317)
                      ·
                        rfl

theorem cell23_1199128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_1199128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199128 prefixEnd_1199128 := by exact prefixLift 1199128
  have htrace : WordTrace (prefixWord ++ tailWord_1199128) baseStart_1199128 baseEnd_1199128 := by
    simpa [prefixWord, tailWord_1199128, baseEnd_1199128] using wordTrace_append hprefix tailTrace_1199128
  have hstable : (prefixWord ++ tailWord_1199128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199128).length < 2 ^ (prefixWord ++ tailWord_1199128).sum := by decide
  have hdescent : baseEnd_1199128 < baseStart_1199128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199138 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1199138 : Nat := 118140960795 + 1199138 * 2 ^ 59
def prefixEnd_1199138 : Nat := 4983230072969 + 3 ^ 40 * 1199138 * 2
def baseEnd_1199138 : Nat := 205244721690411533586757

theorem tailTrace_1199138 : CollatzResearch.WordTrace tailWord_1199138 prefixEnd_1199138 205244721690411533586757 := by
  unfold tailWord_1199138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934038982433824327707517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29157437286490198207220045 10934038982433824327707517)
  ·
    refine ⟨4100264618412684122890319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10934038982433824327707517 4100264618412684122890319)
    ·
      refine ⟨6150396927619026184335479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4100264618412684122890319 6150396927619026184335479)
      ·
        refine ⟨9225595391428539276503219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6150396927619026184335479 9225595391428539276503219)
        ·
          refine ⟨13838393087142808914754829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225595391428539276503219 13838393087142808914754829)
          ·
            refine ⟨5189397407678553343033061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13838393087142808914754829 5189397407678553343033061)
            ·
              refine ⟨973012013939728751818699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5189397407678553343033061 973012013939728751818699)
              ·
                refine ⟨1459518020909593127728049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973012013939728751818699 1459518020909593127728049)
                ·
                  refine ⟨1094638515682194845796037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1459518020909593127728049 1094638515682194845796037)
                  ·
                    refine ⟨205244721690411533586757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1094638515682194845796037 205244721690411533586757)
                    ·
                      rfl

theorem cell23_1199138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1199138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199138 prefixEnd_1199138 := by exact prefixLift 1199138
  have htrace : WordTrace (prefixWord ++ tailWord_1199138) baseStart_1199138 baseEnd_1199138 := by
    simpa [prefixWord, tailWord_1199138, baseEnd_1199138] using wordTrace_append hprefix tailTrace_1199138
  have hstable : (prefixWord ++ tailWord_1199138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199138).length < 2 ^ (prefixWord ++ tailWord_1199138).sum := by decide
  have hdescent : baseEnd_1199138 < baseStart_1199138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199161 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1199161 : Nat := 118140960795 + 1199161 * 2 ^ 59
def prefixEnd_1199161 : Nat := 4983230072969 + 3 ^ 40 * 1199161 * 2
def baseEnd_1199161 : Nat := 615745975126288010772665

theorem tailTrace_1199161 : CollatzResearch.WordTrace tailWord_1199161 prefixEnd_1199161 615745975126288010772665 := by
  unfold tailWord_1199161
  simp only [CollatzResearch.WordTrace]
  refine ⟨43736994808651972238917337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29157996539101314825944891 43736994808651972238917337)
  ·
    refine ⟨32802746106488979179188003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43736994808651972238917337 32802746106488979179188003)
    ·
      refine ⟨49204119159733468768782005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32802746106488979179188003 49204119159733468768782005)
      ·
        refine ⟨4612886171225012697073313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49204119159733468768782005 4612886171225012697073313)
        ·
          refine ⟨3459664628418759522804985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4612886171225012697073313 3459664628418759522804985)
          ·
            refine ⟨2594748471314069642103739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459664628418759522804985 2594748471314069642103739)
            ·
              refine ⟨3892122706971104463155609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594748471314069642103739 3892122706971104463155609)
              ·
                refine ⟨2919092030228328347366707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3892122706971104463155609 2919092030228328347366707)
                ·
                  refine ⟨4378638045342492521050061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919092030228328347366707 4378638045342492521050061)
                  ·
                    refine ⟨1641989267003434695393773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4378638045342492521050061 1641989267003434695393773)
                    ·
                      refine ⟨615745975126288010772665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1641989267003434695393773 615745975126288010772665)
                      ·
                        rfl

theorem cell23_1199161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1199161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199161 prefixEnd_1199161 := by exact prefixLift 1199161
  have htrace : WordTrace (prefixWord ++ tailWord_1199161) baseStart_1199161 baseEnd_1199161 := by
    simpa [prefixWord, tailWord_1199161, baseEnd_1199161] using wordTrace_append hprefix tailTrace_1199161
  have hstable : (prefixWord ++ tailWord_1199161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199161).length < 2 ^ (prefixWord ++ tailWord_1199161).sum := by decide
  have hdescent : baseEnd_1199161 < baseStart_1199161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199187 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 5]
def baseStart_1199187 : Nat := 118140960795 + 1199187 * 2 ^ 59
def prefixEnd_1199187 : Nat := 4983230072969 + 3 ^ 40 * 1199187 * 2
def baseEnd_1199187 : Nat := 615759325623304909047545

theorem tailTrace_1199187 : CollatzResearch.WordTrace tailWord_1199187 prefixEnd_1199187 615759325623304909047545 := by
  unfold tailWord_1199187
  simp only [CollatzResearch.WordTrace]
  refine ⟨43737943106557778679363815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29158628737705185786242543 43737943106557778679363815)
  ·
    refine ⟨65606914659836668019045723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43737943106557778679363815 65606914659836668019045723)
    ·
      refine ⟨98410371989755002028568585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65606914659836668019045723 98410371989755002028568585)
      ·
        refine ⟨73807778992316251521426439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98410371989755002028568585 73807778992316251521426439)
        ·
          refine ⟨110711668488474377282139659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73807778992316251521426439 110711668488474377282139659)
          ·
            refine ⟨166067502732711565923209489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110711668488474377282139659 166067502732711565923209489)
            ·
              refine ⟨124550627049533674442407117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166067502732711565923209489 124550627049533674442407117)
              ·
                refine ⟨46706485143575127915902669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124550627049533674442407117 46706485143575127915902669)
                ·
                  refine ⟨17514931928840672968463501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46706485143575127915902669 17514931928840672968463501)
                  ·
                    refine ⟨6568099473315252363173813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17514931928840672968463501 6568099473315252363173813)
                    ·
                      refine ⟨615759325623304909047545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6568099473315252363173813 615759325623304909047545)
                      ·
                        rfl

theorem cell23_1199187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_1199187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199187 prefixEnd_1199187 := by exact prefixLift 1199187
  have htrace : WordTrace (prefixWord ++ tailWord_1199187) baseStart_1199187 baseEnd_1199187 := by
    simpa [prefixWord, tailWord_1199187, baseEnd_1199187] using wordTrace_append hprefix tailTrace_1199187
  have hstable : (prefixWord ++ tailWord_1199187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199187).length < 2 ^ (prefixWord ++ tailWord_1199187).sum := by decide
  have hdescent : baseEnd_1199187 < baseStart_1199187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199201 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_1199201 : Nat := 118140960795 + 1199201 * 2 ^ 59
def prefixEnd_1199201 : Nat := 4983230072969 + 3 ^ 40 * 1199201 * 2
def baseEnd_1199201 : Nat := 615766514352467854272481

theorem tailTrace_1199201 : CollatzResearch.WordTrace tailWord_1199201 prefixEnd_1199201 615766514352467854272481 := by
  unfold tailWord_1199201
  simp only [CollatzResearch.WordTrace]
  refine ⟨43738453728507059070373457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29158969152338039380248971 43738453728507059070373457)
  ·
    refine ⟨32803840296380294302780093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43738453728507059070373457 32803840296380294302780093)
    ·
      refine ⟨12301440111142610363542535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32803840296380294302780093 12301440111142610363542535)
      ·
        refine ⟨18452160166713915545313803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12301440111142610363542535 18452160166713915545313803)
        ·
          refine ⟨27678240250070873317970705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18452160166713915545313803 27678240250070873317970705)
          ·
            refine ⟨20758680187553154988478029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27678240250070873317970705 20758680187553154988478029)
            ·
              refine ⟨7784505070332433120679261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20758680187553154988478029 7784505070332433120679261)
              ·
                refine ⟨2919189401374662420254723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7784505070332433120679261 2919189401374662420254723)
                ·
                  refine ⟨4378784102061993630382085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919189401374662420254723 4378784102061993630382085)
                  ·
                    refine ⟨821022019136623805696641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4378784102061993630382085 821022019136623805696641)
                    ·
                      refine ⟨615766514352467854272481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821022019136623805696641 615766514352467854272481)
                      ·
                        rfl

theorem cell23_1199201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_1199201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199201 prefixEnd_1199201 := by exact prefixLift 1199201
  have htrace : WordTrace (prefixWord ++ tailWord_1199201) baseStart_1199201 baseEnd_1199201 := by
    simpa [prefixWord, tailWord_1199201, baseEnd_1199201] using wordTrace_append hprefix tailTrace_1199201
  have hstable : (prefixWord ++ tailWord_1199201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199201).length < 2 ^ (prefixWord ++ tailWord_1199201).sum := by decide
  have hdescent : baseEnd_1199201 < baseStart_1199201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199204 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_1199204 : Nat := 118140960795 + 1199204 * 2 ^ 59
def prefixEnd_1199204 : Nat := 4983230072969 + 3 ^ 40 * 1199204 * 2
def baseEnd_1199204 : Nat := 615768054794431342534967

theorem tailTrace_1199204 : CollatzResearch.WordTrace tailWord_1199204 prefixEnd_1199204 615768054794431342534967 := by
  unfold tailWord_1199204
  simp only [CollatzResearch.WordTrace]
  refine ⟨21869281573748095291366333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29159042098330793721821777 21869281573748095291366333)
  ·
    refine ⟨8200980590155535734262375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21869281573748095291366333 8200980590155535734262375)
    ·
      refine ⟨12301470885233303601393563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8200980590155535734262375 12301470885233303601393563)
      ·
        refine ⟨18452206327849955402090345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12301470885233303601393563 18452206327849955402090345)
        ·
          refine ⟨13839154745887466551567759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18452206327849955402090345 13839154745887466551567759)
          ·
            refine ⟨20758732118831199827351639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13839154745887466551567759 20758732118831199827351639)
            ·
              refine ⟨31138098178246799741027459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20758732118831199827351639 31138098178246799741027459)
              ·
                refine ⟨46707147267370199611541189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31138098178246799741027459 46707147267370199611541189)
                ·
                  refine ⟨8757590112631912427163973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46707147267370199611541189 8757590112631912427163973)
                  ·
                    refine ⟨1642048146118483580093245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8757590112631912427163973 1642048146118483580093245)
                    ·
                      refine ⟨615768054794431342534967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1642048146118483580093245 615768054794431342534967)
                      ·
                        rfl

theorem cell23_1199204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_1199204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199204 prefixEnd_1199204 := by exact prefixLift 1199204
  have htrace : WordTrace (prefixWord ++ tailWord_1199204) baseStart_1199204 baseEnd_1199204 := by
    simpa [prefixWord, tailWord_1199204, baseEnd_1199204] using wordTrace_append hprefix tailTrace_1199204
  have hstable : (prefixWord ++ tailWord_1199204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199204).length < 2 ^ (prefixWord ++ tailWord_1199204).sum := by decide
  have hdescent : baseEnd_1199204 < baseStart_1199204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199218 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_1199218 : Nat := 118140960795 + 1199218 * 2 ^ 59
def prefixEnd_1199218 : Nat := 4983230072969 + 3 ^ 40 * 1199218 * 2
def baseEnd_1199218 : Nat := 615775243523594287759903

theorem tailTrace_1199218 : CollatzResearch.WordTrace tailWord_1199218 prefixEnd_1199218 615775243523594287759903 := by
  unfold tailWord_1199218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934768442361367743435577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29159382512963647315828205 10934768442361367743435577)
  ·
    refine ⟨8201076331771025807576683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10934768442361367743435577 8201076331771025807576683)
    ·
      refine ⟨12301614497656538711365025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8201076331771025807576683 12301614497656538711365025)
      ·
        refine ⟨9226210873242404033523769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12301614497656538711365025 9226210873242404033523769)
        ·
          refine ⟨6919658154931803025142827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9226210873242404033523769 6919658154931803025142827)
          ·
            refine ⟨10379487232397704537714241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6919658154931803025142827 10379487232397704537714241)
            ·
              refine ⟨7784615424298278403285681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10379487232397704537714241 7784615424298278403285681)
              ·
                refine ⟨5838461568223708802464261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7784615424298278403285681 5838461568223708802464261)
                ·
                  refine ⟨1094711544041945400462049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5838461568223708802464261 1094711544041945400462049)
                  ·
                    refine ⟨821033658031459050346537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1094711544041945400462049 821033658031459050346537)
                    ·
                      refine ⟨615775243523594287759903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821033658031459050346537 615775243523594287759903)
                      ·
                        rfl

theorem cell23_1199218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_1199218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199218 prefixEnd_1199218 := by exact prefixLift 1199218
  have htrace : WordTrace (prefixWord ++ tailWord_1199218) baseStart_1199218 baseEnd_1199218 := by
    simpa [prefixWord, tailWord_1199218, baseEnd_1199218] using wordTrace_append hprefix tailTrace_1199218
  have hstable : (prefixWord ++ tailWord_1199218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199218).length < 2 ^ (prefixWord ++ tailWord_1199218).sum := by decide
  have hdescent : baseEnd_1199218 < baseStart_1199218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199241 : List Nat := [1, 2, 1, 1, 4, 3, 2, 4, 5]
def baseStart_1199241 : Nat := 118140960795 + 1199241 * 2 ^ 59
def prefixEnd_1199241 : Nat := 4983230072969 + 3 ^ 40 * 1199241 * 2
def baseEnd_1199241 : Nat := 68420783730960855308033

theorem tailTrace_1199241 : CollatzResearch.WordTrace tailWord_1199241 prefixEnd_1199241 68420783730960855308033 := by
  unfold tailWord_1199241
  simp only [CollatzResearch.WordTrace]
  refine ⟨43739912648362145901829577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29159941765574763934553051 43739912648362145901829577)
  ·
    refine ⟨32804934486271609426372183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43739912648362145901829577 32804934486271609426372183)
    ·
      refine ⟨49207401729407414139558275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32804934486271609426372183 49207401729407414139558275)
      ·
        refine ⟨73811102594111121209337413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49207401729407414139558275 73811102594111121209337413)
        ·
          refine ⟨13839581736395835226750765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73811102594111121209337413 13839581736395835226750765)
          ·
            refine ⟨5189843151148438210031537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13839581736395835226750765 5189843151148438210031537)
            ·
              refine ⟨3892382363361328657523653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5189843151148438210031537 3892382363361328657523653)
              ·
                refine ⟨729821693130249123285685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3892382363361328657523653 729821693130249123285685)
                ·
                  refine ⟨68420783730960855308033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 729821693130249123285685 68420783730960855308033)
                  ·
                    rfl

theorem cell23_1199241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 5].length) (baseStart_1199241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199241 prefixEnd_1199241 := by exact prefixLift 1199241
  have htrace : WordTrace (prefixWord ++ tailWord_1199241) baseStart_1199241 baseEnd_1199241 := by
    simpa [prefixWord, tailWord_1199241, baseEnd_1199241] using wordTrace_append hprefix tailTrace_1199241
  have hstable : (prefixWord ++ tailWord_1199241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199241).length < 2 ^ (prefixWord ++ tailWord_1199241).sum := by decide
  have hdescent : baseEnd_1199241 < baseStart_1199241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199271 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 1, 7]
def baseStart_1199271 : Nat := 118140960795 + 1199271 * 2 ^ 59
def prefixEnd_1199271 : Nat := 4983230072969 + 3 ^ 40 * 1199271 * 2
def baseEnd_1199271 : Nat := 205267485999427526799053

theorem tailTrace_1199271 : CollatzResearch.WordTrace tailWord_1199271 prefixEnd_1199271 205267485999427526799053 := by
  unfold tailWord_1199271
  simp only [CollatzResearch.WordTrace]
  refine ⟨43741006838253461025421667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29160671225502307350281111 43741006838253461025421667)
  ·
    refine ⟨65611510257380191538132501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43741006838253461025421667 65611510257380191538132501)
    ·
      refine ⟨3075539543314696478349961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65611510257380191538132501 3075539543314696478349961)
      ·
        refine ⟨2306654657486022358762471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3075539543314696478349961 2306654657486022358762471)
        ·
          refine ⟨3459981986229033538143707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306654657486022358762471 3459981986229033538143707)
          ·
            refine ⟨5189972979343550307215561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459981986229033538143707 5189972979343550307215561)
            ·
              refine ⟨3892479734507662730411671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5189972979343550307215561 3892479734507662730411671)
              ·
                refine ⟨5838719601761494095617507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3892479734507662730411671 5838719601761494095617507)
                ·
                  refine ⟨8758079402642241143426261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5838719601761494095617507 8758079402642241143426261)
                  ·
                    refine ⟨205267485999427526799053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8758079402642241143426261 205267485999427526799053)
                    ·
                      rfl

theorem cell23_1199271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_1199271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199271 prefixEnd_1199271 := by exact prefixLift 1199271
  have htrace : WordTrace (prefixWord ++ tailWord_1199271) baseStart_1199271 baseEnd_1199271 := by
    simpa [prefixWord, tailWord_1199271, baseEnd_1199271] using wordTrace_append hprefix tailTrace_1199271
  have hstable : (prefixWord ++ tailWord_1199271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199271).length < 2 ^ (prefixWord ++ tailWord_1199271).sum := by decide
  have hdescent : baseEnd_1199271 < baseStart_1199271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199291 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 2, 4, 2]
def baseStart_1199291 : Nat := 118140960795 + 1199291 * 2 ^ 59
def prefixEnd_1199291 : Nat := 4983230072969 + 3 ^ 40 * 1199291 * 2
def baseEnd_1199291 : Nat := 615812727611372502147067

theorem tailTrace_1199291 : CollatzResearch.WordTrace tailWord_1199291 prefixEnd_1199291 615812727611372502147067 := by
  unfold tailWord_1199291
  simp only [CollatzResearch.WordTrace]
  refine ⟨43741736298181004441149727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29161157532120669627433151 43741736298181004441149727)
  ·
    refine ⟨65612604447271506661724591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43741736298181004441149727 65612604447271506661724591)
    ·
      refine ⟨98418906670907259992586887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65612604447271506661724591 98418906670907259992586887)
      ·
        refine ⟨147628360006360889988880331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98418906670907259992586887 147628360006360889988880331)
        ·
          refine ⟨221442540009541334983320497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147628360006360889988880331 221442540009541334983320497)
          ·
            refine ⟨166081905007156001237490373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221442540009541334983320497 166081905007156001237490373)
            ·
              refine ⟨31140357188841750232029445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166081905007156001237490373 31140357188841750232029445)
              ·
                refine ⟨5838816972907828168505521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31140357188841750232029445 5838816972907828168505521)
                ·
                  refine ⟨4379112729680871126379141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5838816972907828168505521 4379112729680871126379141)
                  ·
                    refine ⟨821083636815163336196089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4379112729680871126379141 821083636815163336196089)
                    ·
                      refine ⟨615812727611372502147067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821083636815163336196089 615812727611372502147067)
                      ·
                        rfl

theorem cell23_1199291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 4, 2].length) (baseStart_1199291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199291 prefixEnd_1199291 := by exact prefixLift 1199291
  have htrace : WordTrace (prefixWord ++ tailWord_1199291) baseStart_1199291 baseEnd_1199291 := by
    simpa [prefixWord, tailWord_1199291, baseEnd_1199291] using wordTrace_append hprefix tailTrace_1199291
  have hstable : (prefixWord ++ tailWord_1199291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199291).length < 2 ^ (prefixWord ++ tailWord_1199291).sum := by decide
  have hdescent : baseEnd_1199291 < baseStart_1199291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199304 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1199304 : Nat := 118140960795 + 1199304 * 2 ^ 59
def prefixEnd_1199304 : Nat := 4983230072969 + 3 ^ 40 * 1199304 * 2
def baseEnd_1199304 : Nat := 615819402859880951284507

theorem tailTrace_1199304 : CollatzResearch.WordTrace tailWord_1199304 prefixEnd_1199304 615819402859880951284507 := by
  unfold tailWord_1199304
  simp only [CollatzResearch.WordTrace]
  refine ⟨21871105223566953830686483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29161473631422605107581977 21871105223566953830686483)
  ·
    refine ⟨32806657835350430746029725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21871105223566953830686483 32806657835350430746029725)
    ·
      refine ⟨12302496688256411529761147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32806657835350430746029725 12302496688256411529761147)
      ·
        refine ⟨18453745032384617294641721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12302496688256411529761147 18453745032384617294641721)
        ·
          refine ⟨13840308774288462970981291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18453745032384617294641721 13840308774288462970981291)
          ·
            refine ⟨20760463161432694456471937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13840308774288462970981291 20760463161432694456471937)
            ·
              refine ⟨15570347371074520842353953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20760463161432694456471937 15570347371074520842353953)
              ·
                refine ⟨11677760528305890631765465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15570347371074520842353953 11677760528305890631765465)
                ·
                  refine ⟨8758320396229417973824099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11677760528305890631765465 8758320396229417973824099)
                  ·
                    refine ⟨13137480594344126960736149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8758320396229417973824099 13137480594344126960736149)
                    ·
                      refine ⟨615819402859880951284507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13137480594344126960736149 615819402859880951284507)
                      ·
                        rfl

theorem cell23_1199304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1199304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199304 prefixEnd_1199304 := by exact prefixLift 1199304
  have htrace : WordTrace (prefixWord ++ tailWord_1199304) baseStart_1199304 baseEnd_1199304 := by
    simpa [prefixWord, tailWord_1199304, baseEnd_1199304] using wordTrace_append hprefix tailTrace_1199304
  have hstable : (prefixWord ++ tailWord_1199304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199304).length < 2 ^ (prefixWord ++ tailWord_1199304).sum := by decide
  have hdescent : baseEnd_1199304 < baseStart_1199304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199325 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1199325 : Nat := 118140960795 + 1199325 * 2 ^ 59
def prefixEnd_1199325 : Nat := 4983230072969 + 3 ^ 40 * 1199325 * 2
def baseEnd_1199325 : Nat := 615830185953625369121911

theorem tailTrace_1199325 : CollatzResearch.WordTrace tailWord_1199325 prefixEnd_1199325 615830185953625369121911 := by
  unfold tailWord_1199325
  simp only [CollatzResearch.WordTrace]
  refine ⟨43742976380057828247887429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29161984253371885498591619 43742976380057828247887429)
  ·
    refine ⟨8201808071260842796478893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43742976380057828247887429 8201808071260842796478893)
    ·
      refine ⟨3075678026722816048679585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8201808071260842796478893 3075678026722816048679585)
      ·
        refine ⟨2306758520042112036509689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3075678026722816048679585 2306758520042112036509689)
        ·
          refine ⟨1730068890031584027382267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2306758520042112036509689 1730068890031584027382267)
          ·
            refine ⟨2595103335047376041073401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730068890031584027382267 2595103335047376041073401)
            ·
              refine ⟨1946327501285532030805051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2595103335047376041073401 1946327501285532030805051)
              ·
                refine ⟨2919491251928298046207577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946327501285532030805051 2919491251928298046207577)
                ·
                  refine ⟨2189618438946223534655683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2919491251928298046207577 2189618438946223534655683)
                  ·
                    refine ⟨3284427658419335301983525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2189618438946223534655683 3284427658419335301983525)
                    ·
                      refine ⟨615830185953625369121911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3284427658419335301983525 615830185953625369121911)
                      ·
                        rfl

theorem cell23_1199325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1199325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199325 prefixEnd_1199325 := by exact prefixLift 1199325
  have htrace : WordTrace (prefixWord ++ tailWord_1199325) baseStart_1199325 baseEnd_1199325 := by
    simpa [prefixWord, tailWord_1199325, baseEnd_1199325] using wordTrace_append hprefix tailTrace_1199325
  have hstable : (prefixWord ++ tailWord_1199325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199325).length < 2 ^ (prefixWord ++ tailWord_1199325).sum := by decide
  have hdescent : baseEnd_1199325 < baseStart_1199325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199328 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 3]
def baseStart_1199328 : Nat := 118140960795 + 1199328 * 2 ^ 59
def prefixEnd_1199328 : Nat := 4983230072969 + 3 ^ 40 * 1199328 * 2
def baseEnd_1199328 : Nat := 615831726395588857384397

theorem tailTrace_1199328 : CollatzResearch.WordTrace tailWord_1199328 prefixEnd_1199328 615831726395588857384397 := by
  unfold tailWord_1199328
  simp only [CollatzResearch.WordTrace]
  refine ⟨21871542899523479880123319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29162057199364639840164425 21871542899523479880123319)
  ·
    refine ⟨32807314349285219820184979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21871542899523479880123319 32807314349285219820184979)
    ·
      refine ⟨49210971523927829730277469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32807314349285219820184979 49210971523927829730277469)
      ·
        refine ⟨18454114321472936148854051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49210971523927829730277469 18454114321472936148854051)
        ·
          refine ⟨27681171482209404223281077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18454114321472936148854051 27681171482209404223281077)
          ·
            refine ⟨2595109826457131645932601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27681171482209404223281077 2595109826457131645932601)
            ·
              refine ⟨1946332369842848734449451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2595109826457131645932601 1946332369842848734449451)
              ·
                refine ⟨2919498554764273101674177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946332369842848734449451 2919498554764273101674177)
                ·
                  refine ⟨2189623916073204826255633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2919498554764273101674177 2189623916073204826255633)
                  ·
                    refine ⟨1642217937054903619691725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2189623916073204826255633 1642217937054903619691725)
                    ·
                      refine ⟨615831726395588857384397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1642217937054903619691725 615831726395588857384397)
                      ·
                        rfl

theorem cell23_1199328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_1199328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199328 prefixEnd_1199328 := by exact prefixLift 1199328
  have htrace : WordTrace (prefixWord ++ tailWord_1199328) baseStart_1199328 baseEnd_1199328 := by
    simpa [prefixWord, tailWord_1199328, baseEnd_1199328] using wordTrace_append hprefix tailTrace_1199328
  have hstable : (prefixWord ++ tailWord_1199328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199328).length < 2 ^ (prefixWord ++ tailWord_1199328).sum := by decide
  have hdescent : baseEnd_1199328 < baseStart_1199328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199361 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1199361 : Nat := 118140960795 + 1199361 * 2 ^ 59
def prefixEnd_1199361 : Nat := 4983230072969 + 3 ^ 40 * 1199361 * 2
def baseEnd_1199361 : Nat := 205282890419062409423915

theorem tailTrace_1199361 : CollatzResearch.WordTrace tailWord_1199361 prefixEnd_1199361 205282890419062409423915 := by
  unfold tailWord_1199361
  simp only [CollatzResearch.WordTrace]
  refine ⟨43744289407927406396197937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29162859605284937597465291 43744289407927406396197937)
  ·
    refine ⟨32808217055945554797148453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43744289407927406396197937 32808217055945554797148453)
    ·
      refine ⟨6151540697989791524465335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32808217055945554797148453 6151540697989791524465335)
      ·
        refine ⟨9227311046984687286698003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6151540697989791524465335 9227311046984687286698003)
        ·
          refine ⟨13840966570477030930047005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9227311046984687286698003 13840966570477030930047005)
          ·
            refine ⟨5190362463928886598767627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13840966570477030930047005 5190362463928886598767627)
            ·
              refine ⟨7785543695893329898151441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5190362463928886598767627 7785543695893329898151441)
              ·
                refine ⟨5839157771919997423613581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7785543695893329898151441 5839157771919997423613581)
                ·
                  refine ⟨2189684164469999033855093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5839157771919997423613581 2189684164469999033855093)
                  ·
                    refine ⟨205282890419062409423915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2189684164469999033855093 205282890419062409423915)
                    ·
                      rfl

theorem cell23_1199361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1199361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199361 prefixEnd_1199361 := by exact prefixLift 1199361
  have htrace : WordTrace (prefixWord ++ tailWord_1199361) baseStart_1199361 baseEnd_1199361 := by
    simpa [prefixWord, tailWord_1199361, baseEnd_1199361] using wordTrace_append hprefix tailTrace_1199361
  have hstable : (prefixWord ++ tailWord_1199361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199361).length < 2 ^ (prefixWord ++ tailWord_1199361).sum := by decide
  have hdescent : baseEnd_1199361 < baseStart_1199361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199395 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 1, 5]
def baseStart_1199395 : Nat := 118140960795 + 1199395 * 2 ^ 59
def prefixEnd_1199395 : Nat := 4983230072969 + 3 ^ 40 * 1199395 * 2
def baseEnd_1199395 : Nat := 205288709866480031748863

theorem tailTrace_1199395 : CollatzResearch.WordTrace tailWord_1199395 prefixEnd_1199395 205288709866480031748863 := by
  unfold tailWord_1199395
  simp only [CollatzResearch.WordTrace]
  refine ⟨43745529489804230202935639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29163686326536153468623759 43745529489804230202935639)
  ·
    refine ⟨65618294234706345304403459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43745529489804230202935639 65618294234706345304403459)
    ·
      refine ⟨98427441352059517956605189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65618294234706345304403459 98427441352059517956605189)
      ·
        refine ⟨18455145253511159616863473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98427441352059517956605189 18455145253511159616863473)
        ·
          refine ⟨13841358940133369712647605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18455145253511159616863473 13841358940133369712647605)
          ·
            refine ⟨1297627400637503410560713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13841358940133369712647605 1297627400637503410560713)
            ·
              refine ⟨973220550478127557920535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297627400637503410560713 973220550478127557920535)
              ·
                refine ⟨1459830825717191336880803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973220550478127557920535 1459830825717191336880803)
                ·
                  refine ⟨2189746238575787005321205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459830825717191336880803 2189746238575787005321205)
                  ·
                    refine ⟨205288709866480031748863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2189746238575787005321205 205288709866480031748863)
                    ·
                      rfl

theorem cell23_1199395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 1, 5].length) (baseStart_1199395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199395 prefixEnd_1199395 := by exact prefixLift 1199395
  have htrace : WordTrace (prefixWord ++ tailWord_1199395) baseStart_1199395 baseEnd_1199395 := by
    simpa [prefixWord, tailWord_1199395, baseEnd_1199395] using wordTrace_append hprefix tailTrace_1199395
  have hstable : (prefixWord ++ tailWord_1199395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199395).length < 2 ^ (prefixWord ++ tailWord_1199395).sum := by decide
  have hdescent : baseEnd_1199395 < baseStart_1199395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199425 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1199425 : Nat := 118140960795 + 1199425 * 2 ^ 59
def prefixEnd_1199425 : Nat := 4983230072969 + 3 ^ 40 * 1199425 * 2
def baseEnd_1199425 : Nat := 205293844673024992623817

theorem tailTrace_1199425 : CollatzResearch.WordTrace tailWord_1199425 prefixEnd_1199425 205293844673024992623817 := by
  unfold tailWord_1199425
  simp only [CollatzResearch.WordTrace]
  refine ⟨43746623679695545326527729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29164415786463696884351819 43746623679695545326527729)
  ·
    refine ⟨32809967759771658994895797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43746623679695545326527729 32809967759771658994895797)
    ·
      refine ⟨3075934477478593030771481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32809967759771658994895797 3075934477478593030771481)
      ·
        refine ⟨2306950858108944773078611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3075934477478593030771481 2306950858108944773078611)
        ·
          refine ⟨3460426287163417159617917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306950858108944773078611 3460426287163417159617917)
          ·
            refine ⟨1297659857686281434856719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3460426287163417159617917 1297659857686281434856719)
            ·
              refine ⟨1946489786529422152285079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297659857686281434856719 1946489786529422152285079)
              ·
                refine ⟨2919734679794133228427619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946489786529422152285079 2919734679794133228427619)
                ·
                  refine ⟨4379602019691199842641429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919734679794133228427619 4379602019691199842641429)
                  ·
                    refine ⟨205293844673024992623817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4379602019691199842641429 205293844673024992623817)
                    ·
                      rfl

theorem cell23_1199425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1199425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199425 prefixEnd_1199425 := by exact prefixLift 1199425
  have htrace : WordTrace (prefixWord ++ tailWord_1199425) baseStart_1199425 baseEnd_1199425 := by
    simpa [prefixWord, tailWord_1199425, baseEnd_1199425] using wordTrace_append hprefix tailTrace_1199425
  have hstable : (prefixWord ++ tailWord_1199425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199425).length < 2 ^ (prefixWord ++ tailWord_1199425).sum := by decide
  have hdescent : baseEnd_1199425 < baseStart_1199425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199448 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_1199448 : Nat := 118140960795 + 1199448 * 2 ^ 59
def prefixEnd_1199448 : Nat := 4983230072969 + 3 ^ 40 * 1199448 * 2
def baseEnd_1199448 : Nat := 615893344074128387883845

theorem tailTrace_1199448 : CollatzResearch.WordTrace tailWord_1199448 prefixEnd_1199448 615893344074128387883845 := by
  unfold tailWord_1199448
  simp only [CollatzResearch.WordTrace]
  refine ⟨21873731279306110127307499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29164975039074813503076665 21873731279306110127307499)
  ·
    refine ⟨32810596918959165190961249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21873731279306110127307499 32810596918959165190961249)
    ·
      refine ⟨24607947689219373893220937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32810596918959165190961249 24607947689219373893220937)
      ·
        refine ⟨18455960766914530419915703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24607947689219373893220937 18455960766914530419915703)
        ·
          refine ⟨27683941150371795629873555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18455960766914530419915703 27683941150371795629873555)
          ·
            refine ⟨41525911725557693444810333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27683941150371795629873555 41525911725557693444810333)
            ·
              refine ⟨15572216897084135041803875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41525911725557693444810333 15572216897084135041803875)
              ·
                refine ⟨23358325345626202562705813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15572216897084135041803875 23358325345626202562705813)
                ·
                  refine ⟨1094921500576228245126835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23358325345626202562705813 1094921500576228245126835)
                  ·
                    refine ⟨1642382250864342367690253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1094921500576228245126835 1642382250864342367690253)
                    ·
                      refine ⟨615893344074128387883845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1642382250864342367690253 615893344074128387883845)
                      ·
                        rfl

theorem cell23_1199448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_1199448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199448 prefixEnd_1199448 := by exact prefixLift 1199448
  have htrace : WordTrace (prefixWord ++ tailWord_1199448) baseStart_1199448 baseEnd_1199448 := by
    simpa [prefixWord, tailWord_1199448, baseEnd_1199448] using wordTrace_append hprefix tailTrace_1199448
  have hstable : (prefixWord ++ tailWord_1199448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199448).length < 2 ^ (prefixWord ++ tailWord_1199448).sum := by decide
  have hdescent : baseEnd_1199448 < baseStart_1199448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199461 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_1199461 : Nat := 118140960795 + 1199461 * 2 ^ 59
def prefixEnd_1199461 : Nat := 4983230072969 + 3 ^ 40 * 1199461 * 2
def baseEnd_1199461 : Nat := 615900019322636837021285

theorem tailTrace_1199461 : CollatzResearch.WordTrace tailWord_1199461 prefixEnd_1199461 615900019322636837021285 := by
  unfold tailWord_1199461
  simp only [CollatzResearch.WordTrace]
  refine ⟨43747936707565123474838237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29165291138376748983225491 43747936707565123474838237)
  ·
    refine ⟨16405476265336921303064339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43747936707565123474838237 16405476265336921303064339)
    ·
      refine ⟨24608214398005381954596509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16405476265336921303064339 24608214398005381954596509)
      ·
        refine ⟨9228080399252018232973691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24608214398005381954596509 9228080399252018232973691)
        ·
          refine ⟨13842120598878027349460537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9228080399252018232973691 13842120598878027349460537)
          ·
            refine ⟨10381590449158520512095403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13842120598878027349460537 10381590449158520512095403)
            ·
              refine ⟨15572385673737780768143105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10381590449158520512095403 15572385673737780768143105)
              ·
                refine ⟨11679289255303335576107329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15572385673737780768143105 11679289255303335576107329)
                ·
                  refine ⟨8759466941477501682080497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11679289255303335576107329 8759466941477501682080497)
                  ·
                    refine ⟨6569600206108126261560373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8759466941477501682080497 6569600206108126261560373)
                    ·
                      refine ⟨615900019322636837021285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6569600206108126261560373 615900019322636837021285)
                      ·
                        rfl

theorem cell23_1199461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_1199461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199461 prefixEnd_1199461 := by exact prefixLift 1199461
  have htrace : WordTrace (prefixWord ++ tailWord_1199461) baseStart_1199461 baseEnd_1199461 := by
    simpa [prefixWord, tailWord_1199461, baseEnd_1199461] using wordTrace_append hprefix tailTrace_1199461
  have hstable : (prefixWord ++ tailWord_1199461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199461).length < 2 ^ (prefixWord ++ tailWord_1199461).sum := by decide
  have hdescent : baseEnd_1199461 < baseStart_1199461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199466 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1199466 : Nat := 118140960795 + 1199466 * 2 ^ 59
def prefixEnd_1199466 : Nat := 4983230072969 + 3 ^ 40 * 1199466 * 2
def baseEnd_1199466 : Nat := 615902586725909317458763

theorem tailTrace_1199466 : CollatzResearch.WordTrace tailWord_1199466 prefixEnd_1199466 615902586725909317458763 := by
  unfold tailWord_1199466
  simp only [CollatzResearch.WordTrace]
  refine ⟨10937029768136752332192563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29165412715031339552513501 10937029768136752332192563)
  ·
    refine ⟨16405544652205128498288845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10937029768136752332192563 16405544652205128498288845)
    ·
      refine ⟨6152079244576923186858317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16405544652205128498288845 6152079244576923186858317)
      ·
        refine ⟨2307029716716346195071869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6152079244576923186858317 2307029716716346195071869)
        ·
          refine ⟨865136143768629823151951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2307029716716346195071869 865136143768629823151951)
          ·
            refine ⟨1297704215652944734727927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865136143768629823151951 1297704215652944734727927)
            ·
              refine ⟨1946556323479417102091891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297704215652944734727927 1946556323479417102091891)
              ·
                refine ⟨2919834485219125653137837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946556323479417102091891 2919834485219125653137837)
                ·
                  refine ⟨1094937931957172119926689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2919834485219125653137837 1094937931957172119926689)
                  ·
                    refine ⟨821203448967879089945017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1094937931957172119926689 821203448967879089945017)
                    ·
                      refine ⟨615902586725909317458763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821203448967879089945017 615902586725909317458763)
                      ·
                        rfl

theorem cell23_1199466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1199466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199466 prefixEnd_1199466 := by exact prefixLift 1199466
  have htrace : WordTrace (prefixWord ++ tailWord_1199466) baseStart_1199466 baseEnd_1199466 := by
    simpa [prefixWord, tailWord_1199466, baseEnd_1199466] using wordTrace_append hprefix tailTrace_1199466
  have hstable : (prefixWord ++ tailWord_1199466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199466).length < 2 ^ (prefixWord ++ tailWord_1199466).sum := by decide
  have hdescent : baseEnd_1199466 < baseStart_1199466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199471 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_1199471 : Nat := 118140960795 + 1199471 * 2 ^ 59
def prefixEnd_1199471 : Nat := 4983230072969 + 3 ^ 40 * 1199471 * 2
def baseEnd_1199471 : Nat := 615905154129181797896239

theorem tailTrace_1199471 : CollatzResearch.WordTrace tailWord_1199471 prefixEnd_1199471 615905154129181797896239 := by
  unfold tailWord_1199471
  simp only [CollatzResearch.WordTrace]
  refine ⟨43748301437528895182702267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29165534291685930121801511 43748301437528895182702267)
  ·
    refine ⟨65622452156293342774053401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43748301437528895182702267 65622452156293342774053401)
    ·
      refine ⟨49216839117220007080540051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65622452156293342774053401 49216839117220007080540051)
      ·
        refine ⟨73825258675830010620810077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49216839117220007080540051 73825258675830010620810077)
        ·
          refine ⟨27684472003436253982803779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73825258675830010620810077 27684472003436253982803779)
          ·
            refine ⟨41526708005154380974205669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27684472003436253982803779 41526708005154380974205669)
            ·
              refine ⟨7786257750966446432663563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41526708005154380974205669 7786257750966446432663563)
              ·
                refine ⟨11679386626449669648995345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7786257750966446432663563 11679386626449669648995345)
                ·
                  refine ⟨8759539969837252236746509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11679386626449669648995345 8759539969837252236746509)
                  ·
                    refine ⟨3284827488688969588779941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8759539969837252236746509 3284827488688969588779941)
                    ·
                      refine ⟨615905154129181797896239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3284827488688969588779941 615905154129181797896239)
                      ·
                        rfl

theorem cell23_1199471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_1199471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199471 prefixEnd_1199471 := by exact prefixLift 1199471
  have htrace : WordTrace (prefixWord ++ tailWord_1199471) baseStart_1199471 baseEnd_1199471 := by
    simpa [prefixWord, tailWord_1199471, baseEnd_1199471] using wordTrace_append hprefix tailTrace_1199471
  have hstable : (prefixWord ++ tailWord_1199471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199471).length < 2 ^ (prefixWord ++ tailWord_1199471).sum := by decide
  have hdescent : baseEnd_1199471 < baseStart_1199471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199481 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 2, 6]
def baseStart_1199481 : Nat := 118140960795 + 1199481 * 2 ^ 59
def prefixEnd_1199481 : Nat := 4983230072969 + 3 ^ 40 * 1199481 * 2
def baseEnd_1199481 : Nat := 205303429645242252923731

theorem tailTrace_1199481 : CollatzResearch.WordTrace tailWord_1199481 prefixEnd_1199481 205303429645242252923731 := by
  unfold tailWord_1199481
  simp only [CollatzResearch.WordTrace]
  refine ⟨43748666167492666890566297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29165777444995111260377531 43748666167492666890566297)
  ·
    refine ⟨32811499625619500167924723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43748666167492666890566297 32811499625619500167924723)
    ·
      refine ⟨49217249438429250251887085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32811499625619500167924723 49217249438429250251887085)
      ·
        refine ⟨18456468539410968844457657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49217249438429250251887085 18456468539410968844457657)
        ·
          refine ⟨13842351404558226633343243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18456468539410968844457657 13842351404558226633343243)
          ·
            refine ⟨20763527106837339950014865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13842351404558226633343243 20763527106837339950014865)
            ·
              refine ⟨15572645330128004962511149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20763527106837339950014865 15572645330128004962511149)
              ·
                refine ⟨5839741998798001860941681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15572645330128004962511149 5839741998798001860941681)
                ·
                  refine ⟨4379806499098501395706261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5839741998798001860941681 4379806499098501395706261)
                  ·
                    refine ⟨205303429645242252923731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4379806499098501395706261 205303429645242252923731)
                    ·
                      rfl

theorem cell23_1199481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_1199481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199481 prefixEnd_1199481 := by exact prefixLift 1199481
  have htrace : WordTrace (prefixWord ++ tailWord_1199481) baseStart_1199481 baseEnd_1199481 := by
    simpa [prefixWord, tailWord_1199481, baseEnd_1199481] using wordTrace_append hprefix tailTrace_1199481
  have hstable : (prefixWord ++ tailWord_1199481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199481).length < 2 ^ (prefixWord ++ tailWord_1199481).sum := by decide
  have hdescent : baseEnd_1199481 < baseStart_1199481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199486 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1199486 : Nat := 118140960795 + 1199486 * 2 ^ 59
def prefixEnd_1199486 : Nat := 4983230072969 + 3 ^ 40 * 1199486 * 2
def baseEnd_1199486 : Nat := 615912856338999239208671

theorem tailTrace_1199486 : CollatzResearch.WordTrace tailWord_1199486 prefixEnd_1199486 615912856338999239208671 := by
  unfold tailWord_1199486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468606066559319093062289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29165899021649701829665541 5468606066559319093062289)
  ·
    refine ⟨4101454549919489319796717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5468606066559319093062289 4101454549919489319796717)
    ·
      refine ⟨1538045456219808494923769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4101454549919489319796717 1538045456219808494923769)
      ·
        refine ⟨1153534092164856371192827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1538045456219808494923769 1153534092164856371192827)
        ·
          refine ⟨1730301138247284556789241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153534092164856371192827 1730301138247284556789241)
          ·
            refine ⟨1297725853685463417591931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1730301138247284556789241 1297725853685463417591931)
            ·
              refine ⟨1946588780528195126387897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297725853685463417591931 1946588780528195126387897)
              ·
                refine ⟨1459941585396146344790923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1946588780528195126387897 1459941585396146344790923)
                ·
                  refine ⟨2189912378094219517186385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459941585396146344790923 2189912378094219517186385)
                  ·
                    refine ⟨1642434283570664637889789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2189912378094219517186385 1642434283570664637889789)
                    ·
                      refine ⟨615912856338999239208671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1642434283570664637889789 615912856338999239208671)
                      ·
                        rfl

theorem cell23_1199486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1199486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199486 prefixEnd_1199486 := by exact prefixLift 1199486
  have htrace : WordTrace (prefixWord ++ tailWord_1199486) baseStart_1199486 baseEnd_1199486 := by
    simpa [prefixWord, tailWord_1199486, baseEnd_1199486] using wordTrace_append hprefix tailTrace_1199486
  have hstable : (prefixWord ++ tailWord_1199486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199486).length < 2 ^ (prefixWord ++ tailWord_1199486).sum := by decide
  have hdescent : baseEnd_1199486 < baseStart_1199486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199488 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 5, 4, 2]
def baseStart_1199488 : Nat := 118140960795 + 1199488 * 2 ^ 59
def prefixEnd_1199488 : Nat := 4983230072969 + 3 ^ 40 * 1199488 * 2
def baseEnd_1199488 : Nat := 615913883300308231383661

theorem tailTrace_1199488 : CollatzResearch.WordTrace tailWord_1199488 prefixEnd_1199488 615913883300308231383661 := by
  unfold tailWord_1199488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21874460739233653543035559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29165947652311538057380745 21874460739233653543035559)
  ·
    refine ⟨32811691108850480314553339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21874460739233653543035559 32811691108850480314553339)
    ·
      refine ⟨49217536663275720471830009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32811691108850480314553339 49217536663275720471830009)
      ·
        refine ⟨36913152497456790353872507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49217536663275720471830009 36913152497456790353872507)
        ·
          refine ⟨55369728746185185530808761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36913152497456790353872507 55369728746185185530808761)
          ·
            refine ⟨41527296559638889148106571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55369728746185185530808761 41527296559638889148106571)
            ·
              refine ⟨62290944839458333722159857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41527296559638889148106571 62290944839458333722159857)
              ·
                refine ⟨46718208629593750291619893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62290944839458333722159857 46718208629593750291619893)
                ·
                  refine ⟨4379832059024414089839365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46718208629593750291619893 4379832059024414089839365)
                  ·
                    refine ⟨821218511067077641844881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4379832059024414089839365 821218511067077641844881)
                    ·
                      refine ⟨615913883300308231383661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821218511067077641844881 615913883300308231383661)
                      ·
                        rfl

theorem cell23_1199488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_1199488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199488 prefixEnd_1199488 := by exact prefixLift 1199488
  have htrace : WordTrace (prefixWord ++ tailWord_1199488) baseStart_1199488 baseEnd_1199488 := by
    simpa [prefixWord, tailWord_1199488, baseEnd_1199488] using wordTrace_append hprefix tailTrace_1199488
  have hstable : (prefixWord ++ tailWord_1199488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199488).length < 2 ^ (prefixWord ++ tailWord_1199488).sum := by decide
  have hdescent : baseEnd_1199488 < baseStart_1199488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199492 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_1199492 : Nat := 118140960795 + 1199492 * 2 ^ 59
def prefixEnd_1199492 : Nat := 4983230072969 + 3 ^ 40 * 1199492 * 2
def baseEnd_1199492 : Nat := 615915937222926215733643

theorem tailTrace_1199492 : CollatzResearch.WordTrace tailWord_1199492 prefixEnd_1199492 615915937222926215733643 := by
  unfold tailWord_1199492
  simp only [CollatzResearch.WordTrace]
  refine ⟨21874533685226407884608365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29166044913635210512811153 21874533685226407884608365)
  ·
    refine ⟨8202950131959902956728137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21874533685226407884608365 8202950131959902956728137)
    ·
      refine ⟨6152212598969927217546103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8202950131959902956728137 6152212598969927217546103)
      ·
        refine ⟨9228318898454890826319155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6152212598969927217546103 9228318898454890826319155)
        ·
          refine ⟨13842478347682336239478733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9228318898454890826319155 13842478347682336239478733)
          ·
            refine ⟨5190929380380876089804525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13842478347682336239478733 5190929380380876089804525)
            ·
              refine ⟨1946598517642828533676697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5190929380380876089804525 1946598517642828533676697)
              ·
                refine ⟨1459948888232121400257523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1946598517642828533676697 1459948888232121400257523)
                ·
                  refine ⟨2189923332348182100386285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459948888232121400257523 2189923332348182100386285)
                  ·
                    refine ⟨821221249630568287644857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189923332348182100386285 821221249630568287644857)
                    ·
                      refine ⟨615915937222926215733643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821221249630568287644857 615915937222926215733643)
                      ·
                        rfl

theorem cell23_1199492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_1199492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199492 prefixEnd_1199492 := by exact prefixLift 1199492
  have htrace : WordTrace (prefixWord ++ tailWord_1199492) baseStart_1199492 baseEnd_1199492 := by
    simpa [prefixWord, tailWord_1199492, baseEnd_1199492] using wordTrace_append hprefix tailTrace_1199492
  have hstable : (prefixWord ++ tailWord_1199492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199492).length < 2 ^ (prefixWord ++ tailWord_1199492).sum := by decide
  have hdescent : baseEnd_1199492 < baseStart_1199492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199551 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_1199551 : Nat := 118140960795 + 1199551 * 2 ^ 59
def prefixEnd_1199551 : Nat := 4983230072969 + 3 ^ 40 * 1199551 * 2
def baseEnd_1199551 : Nat := 615946232581541484895871

theorem tailTrace_1199551 : CollatzResearch.WordTrace tailWord_1199551 prefixEnd_1199551 615946232581541484895871 := by
  unfold tailWord_1199551
  simp only [CollatzResearch.WordTrace]
  refine ⟨43751219277239068845614507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29167479518159379230409671 43751219277239068845614507)
  ·
    refine ⟨65626828915858603268421761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43751219277239068845614507 65626828915858603268421761)
    ·
      refine ⟨49220121686893952451316321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65626828915858603268421761 49220121686893952451316321)
      ·
        refine ⟨36915091265170464338487241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49220121686893952451316321 36915091265170464338487241)
        ·
          refine ⟨27686318448877848253865431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36915091265170464338487241 27686318448877848253865431)
          ·
            refine ⟨41529477673316772380798147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27686318448877848253865431 41529477673316772380798147)
            ·
              refine ⟨62294216509975158571197221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41529477673316772380798147 62294216509975158571197221)
              ·
                refine ⟨11680165595620342232099479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62294216509975158571197221 11680165595620342232099479)
                ·
                  refine ⟨17520248393430513348149219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11680165595620342232099479 17520248393430513348149219)
                  ·
                    refine ⟨26280372590145770022223829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17520248393430513348149219 26280372590145770022223829)
                    ·
                      refine ⟨615946232581541484895871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26280372590145770022223829 615946232581541484895871)
                      ·
                        rfl

theorem cell23_1199551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_1199551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199551 prefixEnd_1199551 := by exact prefixLift 1199551
  have htrace : WordTrace (prefixWord ++ tailWord_1199551) baseStart_1199551 baseEnd_1199551 := by
    simpa [prefixWord, tailWord_1199551, baseEnd_1199551] using wordTrace_append hprefix tailTrace_1199551
  have hstable : (prefixWord ++ tailWord_1199551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199551).length < 2 ^ (prefixWord ++ tailWord_1199551).sum := by decide
  have hdescent : baseEnd_1199551 < baseStart_1199551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199672 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 2, 3, 2]
def baseStart_1199672 : Nat := 118140960795 + 1199672 * 2 ^ 59
def prefixEnd_1199672 : Nat := 4983230072969 + 3 ^ 40 * 1199672 * 2
def baseEnd_1199672 : Nat := 616008363740735511482815

theorem tailTrace_1199672 : CollatzResearch.WordTrace tailWord_1199672 prefixEnd_1199672 616008363740735511482815 := by
  unfold tailWord_1199672
  simp only [CollatzResearch.WordTrace]
  refine ⟨21877816254900353255384635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29170421673200471007179513 21877816254900353255384635)
  ·
    refine ⟨32816724382350529883076953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21877816254900353255384635 32816724382350529883076953)
    ·
      refine ⟨24612543286762897412307715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32816724382350529883076953 24612543286762897412307715)
      ·
        refine ⟨36918814930144346118461573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24612543286762897412307715 36918814930144346118461573)
        ·
          refine ⟨6922277799402064897211545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36918814930144346118461573 6922277799402064897211545)
          ·
            refine ⟨5191708349551548672908659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6922277799402064897211545 5191708349551548672908659)
            ·
              refine ⟨7787562524327323009362989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191708349551548672908659 7787562524327323009362989)
              ·
                refine ⟨2920335946622746128511121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7787562524327323009362989 2920335946622746128511121)
                ·
                  refine ⟨2190251959967059596383341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2920335946622746128511121 2190251959967059596383341)
                  ·
                    refine ⟨821344484987647348643753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190251959967059596383341 821344484987647348643753)
                    ·
                      refine ⟨616008363740735511482815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821344484987647348643753 616008363740735511482815)
                      ·
                        rfl

theorem cell23_1199672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_1199672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199672 prefixEnd_1199672 := by exact prefixLift 1199672
  have htrace : WordTrace (prefixWord ++ tailWord_1199672) baseStart_1199672 baseEnd_1199672 := by
    simpa [prefixWord, tailWord_1199672, baseEnd_1199672] using wordTrace_append hprefix tailTrace_1199672
  have hstable : (prefixWord ++ tailWord_1199672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199672).length < 2 ^ (prefixWord ++ tailWord_1199672).sum := by decide
  have hdescent : baseEnd_1199672 < baseStart_1199672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199715 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1199715 : Nat := 118140960795 + 1199715 * 2 ^ 59
def prefixEnd_1199715 : Nat := 4983230072969 + 3 ^ 40 * 1199715 * 2
def baseEnd_1199715 : Nat := 616030443408878843245117

theorem tailTrace_1199715 : CollatzResearch.WordTrace tailWord_1199715 prefixEnd_1199715 616030443408878843245117 := by
  unfold tailWord_1199715
  simp only [CollatzResearch.WordTrace]
  refine ⟨43757200848644924854584599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29171467232429949903056399 43757200848644924854584599)
  ·
    refine ⟨65635801272967387281876899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43757200848644924854584599 65635801272967387281876899)
    ·
      refine ⟨98453701909451080922815349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65635801272967387281876899 98453701909451080922815349)
      ·
        refine ⟨9230034554011038836513939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98453701909451080922815349 9230034554011038836513939)
        ·
          refine ⟨13845051831016558254770909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9230034554011038836513939 13845051831016558254770909)
          ·
            refine ⟨5191894436631209345539091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13845051831016558254770909 5191894436631209345539091)
            ·
              refine ⟨7787841654946814018308637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191894436631209345539091 7787841654946814018308637)
              ·
                refine ⟨2920440620605055256865739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7787841654946814018308637 2920440620605055256865739)
                ·
                  refine ⟨4380660930907582885298609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920440620605055256865739 4380660930907582885298609)
                  ·
                    refine ⟨3285495698180687163973957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4380660930907582885298609 3285495698180687163973957)
                    ·
                      refine ⟨616030443408878843245117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3285495698180687163973957 616030443408878843245117)
                      ·
                        rfl

theorem cell23_1199715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1199715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199715 prefixEnd_1199715 := by exact prefixLift 1199715
  have htrace : WordTrace (prefixWord ++ tailWord_1199715) baseStart_1199715 baseEnd_1199715 := by
    simpa [prefixWord, tailWord_1199715, baseEnd_1199715] using wordTrace_append hprefix tailTrace_1199715
  have hstable : (prefixWord ++ tailWord_1199715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199715).length < 2 ^ (prefixWord ++ tailWord_1199715).sum := by decide
  have hdescent : baseEnd_1199715 < baseStart_1199715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199722 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1199722 : Nat := 118140960795 + 1199722 * 2 ^ 59
def prefixEnd_1199722 : Nat := 4983230072969 + 3 ^ 40 * 1199722 * 2
def baseEnd_1199722 : Nat := 616034037773460315857585

theorem tailTrace_1199722 : CollatzResearch.WordTrace tailWord_1199722 prefixEnd_1199722 616034037773460315857585 := by
  unfold tailWord_1199722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939364039904891262522355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29171637439746376700059613 10939364039904891262522355)
  ·
    refine ⟨16409046059857336893783533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10939364039904891262522355 16409046059857336893783533)
    ·
      refine ⟨6153392272446501335168825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16409046059857336893783533 6153392272446501335168825)
      ·
        refine ⟨4615044204334876001376619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6153392272446501335168825 4615044204334876001376619)
        ·
          refine ⟨6922566306502314002064929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615044204334876001376619 6922566306502314002064929)
          ·
            refine ⟨5191924729876735501548697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6922566306502314002064929 5191924729876735501548697)
            ·
              refine ⟨3893943547407551626161523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5191924729876735501548697 3893943547407551626161523)
              ·
                refine ⟨5840915321111327439242285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893943547407551626161523 5840915321111327439242285)
                ·
                  refine ⟨2190343245416747789715857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5840915321111327439242285 2190343245416747789715857)
                  ·
                    refine ⟨1642757434062560842286893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2190343245416747789715857 1642757434062560842286893)
                    ·
                      refine ⟨616034037773460315857585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1642757434062560842286893 616034037773460315857585)
                      ·
                        rfl

theorem cell23_1199722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1199722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199722 prefixEnd_1199722 := by exact prefixLift 1199722
  have htrace : WordTrace (prefixWord ++ tailWord_1199722) baseStart_1199722 baseEnd_1199722 := by
    simpa [prefixWord, tailWord_1199722, baseEnd_1199722] using wordTrace_append hprefix tailTrace_1199722
  have hstable : (prefixWord ++ tailWord_1199722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199722).length < 2 ^ (prefixWord ++ tailWord_1199722).sum := by decide
  have hdescent : baseEnd_1199722 < baseStart_1199722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199738 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_1199738 : Nat := 118140960795 + 1199738 * 2 ^ 59
def prefixEnd_1199738 : Nat := 4983230072969 + 3 ^ 40 * 1199738 * 2
def baseEnd_1199738 : Nat := 205347417821310751085837

theorem tailTrace_1199738 : CollatzResearch.WordTrace tailWord_1199738 prefixEnd_1199738 205347417821310751085837 := by
  unfold tailWord_1199738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939509931890399945667967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29172026485041066521781245 10939509931890399945667967)
  ·
    refine ⟨16409264897835599918501951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10939509931890399945667967 16409264897835599918501951)
    ·
      refine ⟨24613897346753399877752927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16409264897835599918501951 24613897346753399877752927)
      ·
        refine ⟨36920846020130099816629391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24613897346753399877752927 36920846020130099816629391)
        ·
          refine ⟨55381269030195149724944087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36920846020130099816629391 55381269030195149724944087)
          ·
            refine ⟨83071903545292724587416131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55381269030195149724944087 83071903545292724587416131)
            ·
              refine ⟨124607855317939086881124197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83071903545292724587416131 124607855317939086881124197)
              ·
                refine ⟨23363972872113578790210787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124607855317939086881124197 23363972872113578790210787)
                ·
                  refine ⟨35045959308170368185316181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23363972872113578790210787 35045959308170368185316181)
                  ·
                    refine ⟨205347417821310751085837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 35045959308170368185316181 205347417821310751085837)
                    ·
                      rfl

theorem cell23_1199738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_1199738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199738 prefixEnd_1199738 := by exact prefixLift 1199738
  have htrace : WordTrace (prefixWord ++ tailWord_1199738) baseStart_1199738 baseEnd_1199738 := by
    simpa [prefixWord, tailWord_1199738, baseEnd_1199738] using wordTrace_append hprefix tailTrace_1199738
  have hstable : (prefixWord ++ tailWord_1199738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199738).length < 2 ^ (prefixWord ++ tailWord_1199738).sum := by decide
  have hdescent : baseEnd_1199738 < baseStart_1199738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199779 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 1, 3, 2]
def baseStart_1199779 : Nat := 118140960795 + 1199779 * 2 ^ 59
def prefixEnd_1199779 : Nat := 4983230072969 + 3 ^ 40 * 1199779 * 2
def baseEnd_1199779 : Nat := 616063306170766592844823

theorem tailTrace_1199779 : CollatzResearch.WordTrace tailWord_1199779 prefixEnd_1199779 616063306170766592844823 := by
  unfold tailWord_1199779
  simp only [CollatzResearch.WordTrace]
  refine ⟨43759535120413063784914391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29173023413608709189942927 43759535120413063784914391)
  ·
    refine ⟨65639302680619595677371587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43759535120413063784914391 65639302680619595677371587)
    ·
      refine ⟨98458954020929393516057381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65639302680619595677371587 98458954020929393516057381)
      ·
        refine ⟨18461053878924261284260759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98458954020929393516057381 18461053878924261284260759)
        ·
          refine ⟨27691580818386391926391139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18461053878924261284260759 27691580818386391926391139)
          ·
            refine ⟨41537371227579587889586709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27691580818386391926391139 41537371227579587889586709)
            ·
              refine ⟨1947064276292793182324377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41537371227579587889586709 1947064276292793182324377)
              ·
                refine ⟨1460298207219594886743283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947064276292793182324377 1460298207219594886743283)
                ·
                  refine ⟨2190447310829392330114925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460298207219594886743283 2190447310829392330114925)
                  ·
                    refine ⟨821417741561022123793097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190447310829392330114925 821417741561022123793097)
                    ·
                      refine ⟨616063306170766592844823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821417741561022123793097 616063306170766592844823)
                      ·
                        rfl

theorem cell23_1199779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_1199779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199779 prefixEnd_1199779 := by exact prefixLift 1199779
  have htrace : WordTrace (prefixWord ++ tailWord_1199779) baseStart_1199779 baseEnd_1199779 := by
    simpa [prefixWord, tailWord_1199779, baseEnd_1199779] using wordTrace_append hprefix tailTrace_1199779
  have hstable : (prefixWord ++ tailWord_1199779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199779).length < 2 ^ (prefixWord ++ tailWord_1199779).sum := by decide
  have hdescent : baseEnd_1199779 < baseStart_1199779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199792 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 1, 4, 2]
def baseStart_1199792 : Nat := 118140960795 + 1199792 * 2 ^ 59
def prefixEnd_1199792 : Nat := 4983230072969 + 3 ^ 40 * 1199792 * 2
def baseEnd_1199792 : Nat := 616069981419275041982263

theorem tailTrace_1199792 : CollatzResearch.WordTrace tailWord_1199792 prefixEnd_1199792 616069981419275041982263 := by
  unfold tailWord_1199792
  simp only [CollatzResearch.WordTrace]
  refine ⟨21880004634682983502568815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29173339512910644670091753 21880004634682983502568815)
  ·
    refine ⟨32820006952024475253853223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21880004634682983502568815 32820006952024475253853223)
    ·
      refine ⟨49230010428036712880779835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32820006952024475253853223 49230010428036712880779835)
      ·
        refine ⟨73845015642055069321169753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49230010428036712880779835 73845015642055069321169753)
        ·
          refine ⟨55383761731541301990877315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73845015642055069321169753 55383761731541301990877315)
          ·
            refine ⟨83075642597311952986315973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55383761731541301990877315 83075642597311952986315973)
            ·
              refine ⟨15576682986995991184934245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83075642597311952986315973 15576682986995991184934245)
              ·
                refine ⟨2920628060061748347175171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15576682986995991184934245 2920628060061748347175171)
                ·
                  refine ⟨4380942090092622520762757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2920628060061748347175171 4380942090092622520762757)
                  ·
                    refine ⟨821426641892366722643017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4380942090092622520762757 821426641892366722643017)
                    ·
                      refine ⟨616069981419275041982263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821426641892366722643017 616069981419275041982263)
                      ·
                        rfl

theorem cell23_1199792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 1, 4, 2].length) (baseStart_1199792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199792 prefixEnd_1199792 := by exact prefixLift 1199792
  have htrace : WordTrace (prefixWord ++ tailWord_1199792) baseStart_1199792 baseEnd_1199792 := by
    simpa [prefixWord, tailWord_1199792, baseEnd_1199792] using wordTrace_append hprefix tailTrace_1199792
  have hstable : (prefixWord ++ tailWord_1199792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199792).length < 2 ^ (prefixWord ++ tailWord_1199792).sum := by decide
  have hdescent : baseEnd_1199792 < baseStart_1199792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199795 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 5]
def baseStart_1199795 : Nat := 118140960795 + 1199795 * 2 ^ 59
def prefixEnd_1199795 : Nat := 4983230072969 + 3 ^ 40 * 1199795 * 2
def baseEnd_1199795 : Nat := 616071521861238530244749

theorem tailTrace_1199795 : CollatzResearch.WordTrace tailWord_1199795 prefixEnd_1199795 616071521861238530244749 := by
  unfold tailWord_1199795
  simp only [CollatzResearch.WordTrace]
  refine ⟨43760118688355098517496839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29173412458903399011664559 43760118688355098517496839)
  ·
    refine ⟨65640178032532647776245259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43760118688355098517496839 65640178032532647776245259)
    ·
      refine ⟨98460267048798971664367889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65640178032532647776245259 98460267048798971664367889)
      ·
        refine ⟨73845200286599228748275917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98460267048798971664367889 73845200286599228748275917)
        ·
          refine ⟨27691950107474710780603469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73845200286599228748275917 27691950107474710780603469)
          ·
            refine ⟨10384481290303016542726301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27691950107474710780603469 10384481290303016542726301)
            ·
              refine ⟨3894180483863631203522363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10384481290303016542726301 3894180483863631203522363)
              ·
                refine ⟨5841270725795446805283545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894180483863631203522363 5841270725795446805283545)
                ·
                  refine ⟨4380953044346585103962659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5841270725795446805283545 4380953044346585103962659)
                  ·
                    refine ⟨6571429566519877655943989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4380953044346585103962659 6571429566519877655943989)
                    ·
                      refine ⟨616071521861238530244749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6571429566519877655943989 616071521861238530244749)
                      ·
                        rfl

theorem cell23_1199795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_1199795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199795 prefixEnd_1199795 := by exact prefixLift 1199795
  have htrace : WordTrace (prefixWord ++ tailWord_1199795) baseStart_1199795 baseEnd_1199795 := by
    simpa [prefixWord, tailWord_1199795, baseEnd_1199795] using wordTrace_append hprefix tailTrace_1199795
  have hstable : (prefixWord ++ tailWord_1199795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199795).length < 2 ^ (prefixWord ++ tailWord_1199795).sum := by decide
  have hdescent : baseEnd_1199795 < baseStart_1199795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199812 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1199812 : Nat := 118140960795 + 1199812 * 2 ^ 59
def prefixEnd_1199812 : Nat := 4983230072969 + 3 ^ 40 * 1199812 * 2
def baseEnd_1199812 : Nat := 616080251032364963732171

theorem tailTrace_1199812 : CollatzResearch.WordTrace tailWord_1199812 prefixEnd_1199812 616080251032364963732171 := by
  unfold tailWord_1199812
  simp only [CollatzResearch.WordTrace]
  refine ⟨21880369364646755210432845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29173825819529006947243793 21880369364646755210432845)
  ·
    refine ⟨8205138511742533203912317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21880369364646755210432845 8205138511742533203912317)
    ·
      refine ⟨3076926941903449951467119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8205138511742533203912317 3076926941903449951467119)
      ·
        refine ⟨4615390412855174927200679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076926941903449951467119 4615390412855174927200679)
        ·
          refine ⟨6923085619282762390801019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615390412855174927200679 6923085619282762390801019)
          ·
            refine ⟨10384628428924143586201529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6923085619282762390801019 10384628428924143586201529)
            ·
              refine ⟨7788471321693107689651147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10384628428924143586201529 7788471321693107689651147)
              ·
                refine ⟨11682706982539661534476721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7788471321693107689651147 11682706982539661534476721)
                ·
                  refine ⟨8762030236904746150857541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11682706982539661534476721 8762030236904746150857541)
                  ·
                    refine ⟨1642880669419639903285789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8762030236904746150857541 1642880669419639903285789)
                    ·
                      refine ⟨616080251032364963732171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1642880669419639903285789 616080251032364963732171)
                      ·
                        rfl

theorem cell23_1199812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1199812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199812 prefixEnd_1199812 := by exact prefixLift 1199812
  have htrace : WordTrace (prefixWord ++ tailWord_1199812) baseStart_1199812 baseEnd_1199812 := by
    simpa [prefixWord, tailWord_1199812, baseEnd_1199812] using wordTrace_append hprefix tailTrace_1199812
  have hstable : (prefixWord ++ tailWord_1199812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199812).length < 2 ^ (prefixWord ++ tailWord_1199812).sum := by decide
  have hdescent : baseEnd_1199812 < baseStart_1199812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199820 : List Nat := [2, 2, 1, 5, 3, 1, 2, 1, 2, 1, 3]
def baseStart_1199820 : Nat := 118140960795 + 1199820 * 2 ^ 59
def prefixEnd_1199820 : Nat := 4983230072969 + 3 ^ 40 * 1199820 * 2
def baseEnd_1199820 : Nat := 616084358877600932432135

theorem tailTrace_1199820 : CollatzResearch.WordTrace tailWord_1199820 prefixEnd_1199820 616084358877600932432135 := by
  unfold tailWord_1199820
  simp only [CollatzResearch.WordTrace]
  refine ⟨21880515256632263893578457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29174020342176351858104609 21880515256632263893578457)
  ·
    refine ⟨16410386442474197920183843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21880515256632263893578457 16410386442474197920183843)
    ·
      refine ⟨24615579663711296880275765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16410386442474197920183843 24615579663711296880275765)
      ·
        refine ⟨2307710593472934082525853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24615579663711296880275765 2307710593472934082525853)
        ·
          refine ⟨865391472552350280947195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2307710593472934082525853 865391472552350280947195)
          ·
            refine ⟨1298087208828525421420793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865391472552350280947195 1298087208828525421420793)
            ·
              refine ⟨973565406621394066065595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298087208828525421420793 973565406621394066065595)
              ·
                refine ⟨1460348109932091099098393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973565406621394066065595 1460348109932091099098393)
                ·
                  refine ⟨1095261082449068324323795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460348109932091099098393 1095261082449068324323795)
                  ·
                    refine ⟨1642891623673602486485693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1095261082449068324323795 1642891623673602486485693)
                    ·
                      refine ⟨616084358877600932432135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1642891623673602486485693 616084358877600932432135)
                      ·
                        rfl

theorem cell23_1199820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_1199820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199820 prefixEnd_1199820 := by exact prefixLift 1199820
  have htrace : WordTrace (prefixWord ++ tailWord_1199820) baseStart_1199820 baseEnd_1199820 := by
    simpa [prefixWord, tailWord_1199820, baseEnd_1199820] using wordTrace_append hprefix tailTrace_1199820
  have hstable : (prefixWord ++ tailWord_1199820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199820).length < 2 ^ (prefixWord ++ tailWord_1199820).sum := by decide
  have hdescent : baseEnd_1199820 < baseStart_1199820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199855 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_1199855 : Nat := 118140960795 + 1199855 * 2 ^ 59
def prefixEnd_1199855 : Nat := 4983230072969 + 3 ^ 40 * 1199855 * 2
def baseEnd_1199855 : Nat := 616102330700508295494473

theorem tailTrace_1199855 : CollatzResearch.WordTrace tailWord_1199855 prefixEnd_1199855 616102330700508295494473 := by
  unfold tailWord_1199855
  simp only [CollatzResearch.WordTrace]
  refine ⟨43762307068137728764681019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29174871378758485843120679 43762307068137728764681019)
  ·
    refine ⟨65643460602206593147021529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43762307068137728764681019 65643460602206593147021529)
    ·
      refine ⟨49232595451654944860266147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65643460602206593147021529 49232595451654944860266147)
      ·
        refine ⟨73848893177482417290399221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49232595451654944860266147 73848893177482417290399221)
        ·
          refine ⟨6923333735388976620974927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73848893177482417290399221 6923333735388976620974927)
          ·
            refine ⟨10385000603083464931462391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6923333735388976620974927 10385000603083464931462391)
            ·
              refine ⟨15577500904625197397193587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10385000603083464931462391 15577500904625197397193587)
              ·
                refine ⟨23366251356937796095790381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15577500904625197397193587 23366251356937796095790381)
                ·
                  refine ⟨8762344258851673535921393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23366251356937796095790381 8762344258851673535921393)
                  ·
                    refine ⟨6571758194138755151941045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8762344258851673535921393 6571758194138755151941045)
                    ·
                      refine ⟨616102330700508295494473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6571758194138755151941045 616102330700508295494473)
                      ·
                        rfl

theorem cell23_1199855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_1199855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199855 prefixEnd_1199855 := by exact prefixLift 1199855
  have htrace : WordTrace (prefixWord ++ tailWord_1199855) baseStart_1199855 baseEnd_1199855 := by
    simpa [prefixWord, tailWord_1199855, baseEnd_1199855] using wordTrace_append hprefix tailTrace_1199855
  have hstable : (prefixWord ++ tailWord_1199855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199855).length < 2 ^ (prefixWord ++ tailWord_1199855).sum := by decide
  have hdescent : baseEnd_1199855 < baseStart_1199855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199860 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1199860 : Nat := 118140960795 + 1199860 * 2 ^ 59
def prefixEnd_1199860 : Nat := 4983230072969 + 3 ^ 40 * 1199860 * 2
def baseEnd_1199860 : Nat := 616104898103780775931951

theorem tailTrace_1199860 : CollatzResearch.WordTrace tailWord_1199860 prefixEnd_1199860 616104898103780775931951 := by
  unfold tailWord_1199860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21881244716559807309306517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29174992955413076412408689 21881244716559807309306517)
  ·
    refine ⟨1025683346088740967623743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21881244716559807309306517 1025683346088740967623743)
    ·
      refine ⟨1538525019133111451435615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1025683346088740967623743 1538525019133111451435615)
      ·
        refine ⟨2307787528699667177153423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1538525019133111451435615 2307787528699667177153423)
        ·
          refine ⟨3461681293049500765730135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307787528699667177153423 3461681293049500765730135)
          ·
            refine ⟨5192521939574251148595203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461681293049500765730135 5192521939574251148595203)
            ·
              refine ⟨7788782909361376722892805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5192521939574251148595203 7788782909361376722892805)
              ·
                refine ⟨1460396795505258135542401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7788782909361376722892805 1460396795505258135542401)
                ·
                  refine ⟨1095297596628943601656801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460396795505258135542401 1095297596628943601656801)
                  ·
                    refine ⟨821473197471707701242601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1095297596628943601656801 821473197471707701242601)
                    ·
                      refine ⟨616104898103780775931951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821473197471707701242601 616104898103780775931951)
                      ·
                        rfl

theorem cell23_1199860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1199860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199860 prefixEnd_1199860 := by exact prefixLift 1199860
  have htrace : WordTrace (prefixWord ++ tailWord_1199860) baseStart_1199860 baseEnd_1199860 := by
    simpa [prefixWord, tailWord_1199860, baseEnd_1199860] using wordTrace_append hprefix tailTrace_1199860
  have hstable : (prefixWord ++ tailWord_1199860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199860).length < 2 ^ (prefixWord ++ tailWord_1199860).sum := by decide
  have hdescent : baseEnd_1199860 < baseStart_1199860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199865 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1199865 : Nat := 118140960795 + 1199865 * 2 ^ 59
def prefixEnd_1199865 : Nat := 4983230072969 + 3 ^ 40 * 1199865 * 2
def baseEnd_1199865 : Nat := 616107465507053256369427

theorem tailTrace_1199865 : CollatzResearch.WordTrace tailWord_1199865 prefixEnd_1199865 616107465507053256369427 := by
  unfold tailWord_1199865
  simp only [CollatzResearch.WordTrace]
  refine ⟨43762671798101500472545049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29175114532067666981696699 43762671798101500472545049)
  ·
    refine ⟨32822003848576125354408787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43762671798101500472545049 32822003848576125354408787)
    ·
      refine ⟨49233005772864188031613181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32822003848576125354408787 49233005772864188031613181)
      ·
        refine ⟨18462377164824070511854943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49233005772864188031613181 18462377164824070511854943)
        ·
          refine ⟨27693565747236105767782415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18462377164824070511854943 27693565747236105767782415)
          ·
            refine ⟨41540348620854158651673623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27693565747236105767782415 41540348620854158651673623)
            ·
              refine ⟨62310522931281237977510435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41540348620854158651673623 62310522931281237977510435)
              ·
                refine ⟨93465784396921856966265653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62310522931281237977510435 93465784396921856966265653)
                ·
                  refine ⟨8762417287211424090587405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93465784396921856966265653 8762417287211424090587405)
                  ·
                    refine ⟨3285906482704284033970277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8762417287211424090587405 3285906482704284033970277)
                    ·
                      refine ⟨616107465507053256369427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3285906482704284033970277 616107465507053256369427)
                      ·
                        rfl

theorem cell23_1199865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1199865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199865 prefixEnd_1199865 := by exact prefixLift 1199865
  have htrace : WordTrace (prefixWord ++ tailWord_1199865) baseStart_1199865 baseEnd_1199865 := by
    simpa [prefixWord, tailWord_1199865, baseEnd_1199865] using wordTrace_append hprefix tailTrace_1199865
  have hstable : (prefixWord ++ tailWord_1199865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199865).length < 2 ^ (prefixWord ++ tailWord_1199865).sum := by decide
  have hdescent : baseEnd_1199865 < baseStart_1199865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199912 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1199912 : Nat := 118140960795 + 1199912 * 2 ^ 59
def prefixEnd_1199912 : Nat := 4983230072969 + 3 ^ 40 * 1199912 * 2
def baseEnd_1199912 : Nat := 616131599097814572481711

theorem tailTrace_1199912 : CollatzResearch.WordTrace tailWord_1199912 prefixEnd_1199912 616131599097814572481711 := by
  unfold tailWord_1199912
  simp only [CollatzResearch.WordTrace]
  refine ⟨21882193014465613749752995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29176257352620818333003993 21882193014465613749752995)
  ·
    refine ⟨32823289521698420624629493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21882193014465613749752995 32823289521698420624629493)
    ·
      refine ⟨3077183392659226933559015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32823289521698420624629493 3077183392659226933559015)
      ·
        refine ⟨4615775088988840400338523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077183392659226933559015 4615775088988840400338523)
        ·
          refine ⟨6923662633483260600507785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615775088988840400338523 6923662633483260600507785)
          ·
            refine ⟨5192746975112445450380839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6923662633483260600507785 5192746975112445450380839)
            ·
              refine ⟨7789120462668668175571259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5192746975112445450380839 7789120462668668175571259)
              ·
                refine ⟨11683680694003002263356889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7789120462668668175571259 11683680694003002263356889)
                ·
                  refine ⟨8762760520502251697517667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11683680694003002263356889 8762760520502251697517667)
                  ·
                    refine ⟨13144140780753377546276501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8762760520502251697517667 13144140780753377546276501)
                    ·
                      refine ⟨616131599097814572481711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13144140780753377546276501 616131599097814572481711)
                      ·
                        rfl

theorem cell23_1199912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1199912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199912 prefixEnd_1199912 := by exact prefixLift 1199912
  have htrace : WordTrace (prefixWord ++ tailWord_1199912) baseStart_1199912 baseEnd_1199912 := by
    simpa [prefixWord, tailWord_1199912, baseEnd_1199912] using wordTrace_append hprefix tailTrace_1199912
  have hstable : (prefixWord ++ tailWord_1199912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199912).length < 2 ^ (prefixWord ++ tailWord_1199912).sum := by decide
  have hdescent : baseEnd_1199912 < baseStart_1199912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199922 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 8]
def baseStart_1199922 : Nat := 118140960795 + 1199922 * 2 ^ 59
def prefixEnd_1199922 : Nat := 4983230072969 + 3 ^ 40 * 1199922 * 2
def baseEnd_1199922 : Nat := 68459637100484392595185

theorem tailTrace_1199922 : CollatzResearch.WordTrace tailWord_1199922 prefixEnd_1199922 68459637100484392595185 := by
  unfold tailWord_1199922
  simp only [CollatzResearch.WordTrace]
  refine ⟨10941187689723749801842505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29176500505929999471580013 10941187689723749801842505)
  ·
    refine ⟨8205890767292812351381879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10941187689723749801842505 8205890767292812351381879)
    ·
      refine ⟨12308836150939218527072819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8205890767292812351381879 12308836150939218527072819)
      ·
        refine ⟨18463254226408827790609229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12308836150939218527072819 18463254226408827790609229)
        ·
          refine ⟨6923720334903310421478461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18463254226408827790609229 6923720334903310421478461)
          ·
            refine ⟨2596395125588741408054423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6923720334903310421478461 2596395125588741408054423)
            ·
              refine ⟨3894592688383112112081635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596395125588741408054423 3894592688383112112081635)
              ·
                refine ⟨5841889032574668168122453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894592688383112112081635 5841889032574668168122453)
                ·
                  refine ⟨68459637100484392595185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5841889032574668168122453 68459637100484392595185)
                  ·
                    rfl

theorem cell23_1199922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_1199922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199922 prefixEnd_1199922 := by exact prefixLift 1199922
  have htrace : WordTrace (prefixWord ++ tailWord_1199922) baseStart_1199922 baseEnd_1199922 := by
    simpa [prefixWord, tailWord_1199922, baseEnd_1199922] using wordTrace_append hprefix tailTrace_1199922
  have hstable : (prefixWord ++ tailWord_1199922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199922).length < 2 ^ (prefixWord ++ tailWord_1199922).sum := by decide
  have hdescent : baseEnd_1199922 < baseStart_1199922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199926 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1199926 : Nat := 118140960795 + 1199926 * 2 ^ 59
def prefixEnd_1199926 : Nat := 4983230072969 + 3 ^ 40 * 1199926 * 2
def baseEnd_1199926 : Nat := 205379595942325839235549

theorem tailTrace_1199926 : CollatzResearch.WordTrace tailWord_1199926 prefixEnd_1199926 205379595942325839235549 := by
  unfold tailWord_1199926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735306040680031743157227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29176597767253671927010421 2735306040680031743157227)
  ·
    refine ⟨4102959061020047614735841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2735306040680031743157227 4102959061020047614735841)
    ·
      refine ⟨3077219295765035711051881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4102959061020047614735841 3077219295765035711051881)
      ·
        refine ⟨2307914471823776783288911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3077219295765035711051881 2307914471823776783288911)
        ·
          refine ⟨3461871707735665174933367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307914471823776783288911 3461871707735665174933367)
          ·
            refine ⟨5192807561603497762400051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461871707735665174933367 5192807561603497762400051)
            ·
              refine ⟨7789211342405246643600077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5192807561603497762400051 7789211342405246643600077)
              ·
                refine ⟨2920954253401967491350029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7789211342405246643600077 2920954253401967491350029)
                ·
                  refine ⟨1095357845025737809256261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2920954253401967491350029 1095357845025737809256261)
                  ·
                    refine ⟨205379595942325839235549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1095357845025737809256261 205379595942325839235549)
                    ·
                      rfl

theorem cell23_1199926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1199926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199926 prefixEnd_1199926 := by exact prefixLift 1199926
  have htrace : WordTrace (prefixWord ++ tailWord_1199926) baseStart_1199926 baseEnd_1199926 := by
    simpa [prefixWord, tailWord_1199926, baseEnd_1199926] using wordTrace_append hprefix tailTrace_1199926
  have hstable : (prefixWord ++ tailWord_1199926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199926).length < 2 ^ (prefixWord ++ tailWord_1199926).sum := by decide
  have hdescent : baseEnd_1199926 < baseStart_1199926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199939 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 6]
def baseStart_1199939 : Nat := 118140960795 + 1199939 * 2 ^ 59
def prefixEnd_1199939 : Nat := 4983230072969 + 3 ^ 40 * 1199939 * 2
def baseEnd_1199939 : Nat := 68460607008387329649343

theorem tailTrace_1199939 : CollatzResearch.WordTrace tailWord_1199939 prefixEnd_1199939 68460607008387329649343 := by
  unfold tailWord_1199939
  simp only [CollatzResearch.WordTrace]
  refine ⟨43765370799833411110738871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29176913866555607407159247 43765370799833411110738871)
  ·
    refine ⟨65648056199750116666108307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43765370799833411110738871 65648056199750116666108307)
    ·
      refine ⟨98472084299625174999162461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65648056199750116666108307 98472084299625174999162461)
      ·
        refine ⟨36927031612359440624685923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98472084299625174999162461 36927031612359440624685923)
        ·
          refine ⟨55390547418539160937028885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36927031612359440624685923 55390547418539160937028885)
          ·
            refine ⟨2596431910244023168923229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55390547418539160937028885 2596431910244023168923229)
            ·
              refine ⟨973661966341508688346211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2596431910244023168923229 973661966341508688346211)
              ·
                refine ⟨1460492949512263032519317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973661966341508688346211 1460492949512263032519317)
                ·
                  refine ⟨68460607008387329649343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1460492949512263032519317 68460607008387329649343)
                  ·
                    rfl

theorem cell23_1199939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 6].length) (baseStart_1199939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199939 prefixEnd_1199939 := by exact prefixLift 1199939
  have htrace : WordTrace (prefixWord ++ tailWord_1199939) baseStart_1199939 baseEnd_1199939 := by
    simpa [prefixWord, tailWord_1199939, baseEnd_1199939] using wordTrace_append hprefix tailTrace_1199939
  have hstable : (prefixWord ++ tailWord_1199939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199939).length < 2 ^ (prefixWord ++ tailWord_1199939).sum := by decide
  have hdescent : baseEnd_1199939 < baseStart_1199939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199976 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_1199976 : Nat := 118140960795 + 1199976 * 2 ^ 59
def prefixEnd_1199976 : Nat := 4983230072969 + 3 ^ 40 * 1199976 * 2
def baseEnd_1199976 : Nat := 616164461859702322081417

theorem tailTrace_1199976 : CollatzResearch.WordTrace tailWord_1199976 prefixEnd_1199976 616164461859702322081417 := by
  unfold tailWord_1199976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21883360150349683214917891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29177813533799577619890521 21883360150349683214917891)
  ·
    refine ⟨32825040225524524822376837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21883360150349683214917891 32825040225524524822376837)
    ·
      refine ⟨6154695042285848404195657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32825040225524524822376837 6154695042285848404195657)
      ·
        refine ⟨4616021281714386303146743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6154695042285848404195657 4616021281714386303146743)
        ·
          refine ⟨6924031922571579454720115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4616021281714386303146743 6924031922571579454720115)
          ·
            refine ⟨10386047883857369182080173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6924031922571579454720115 10386047883857369182080173)
            ·
              refine ⟨3894767956446513443280065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10386047883857369182080173 3894767956446513443280065)
              ·
                refine ⟨2921075967334885082460049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3894767956446513443280065 2921075967334885082460049)
                ·
                  refine ⟨2190806975501163811845037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921075967334885082460049 2190806975501163811845037)
                  ·
                    refine ⟨821552615812936429441889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2190806975501163811845037 821552615812936429441889)
                    ·
                      refine ⟨616164461859702322081417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821552615812936429441889 616164461859702322081417)
                      ·
                        rfl

theorem cell23_1199976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_1199976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199976 prefixEnd_1199976 := by exact prefixLift 1199976
  have htrace : WordTrace (prefixWord ++ tailWord_1199976) baseStart_1199976 baseEnd_1199976 := by
    simpa [prefixWord, tailWord_1199976, baseEnd_1199976] using wordTrace_append hprefix tailTrace_1199976
  have hstable : (prefixWord ++ tailWord_1199976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199976).length < 2 ^ (prefixWord ++ tailWord_1199976).sum := by decide
  have hdescent : baseEnd_1199976 < baseStart_1199976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199989 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1199989 : Nat := 118140960795 + 1199989 * 2 ^ 59
def prefixEnd_1199989 : Nat := 4983230072969 + 3 ^ 40 * 1199989 * 2
def baseEnd_1199989 : Nat := 616171137108210771218857

theorem tailTrace_1199989 : CollatzResearch.WordTrace tailWord_1199989 prefixEnd_1199989 616171137108210771218857 := by
  unfold tailWord_1199989
  simp only [CollatzResearch.WordTrace]
  refine ⟨43767194449652269650059021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29178129633101513100039347 43767194449652269650059021)
  ·
    refine ⟨16412697918619601118772133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43767194449652269650059021 16412697918619601118772133)
    ·
      refine ⟨3077380859741175209769775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16412697918619601118772133 3077380859741175209769775)
      ·
        refine ⟨4616071289611762814654663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077380859741175209769775 4616071289611762814654663)
        ·
          refine ⟨6924106934417644221981995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4616071289611762814654663 6924106934417644221981995)
          ·
            refine ⟨10386160401626466332972993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6924106934417644221981995 10386160401626466332972993)
            ·
              refine ⟨7789620301219849749729745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10386160401626466332972993 7789620301219849749729745)
              ·
                refine ⟨5842215225914887312297309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7789620301219849749729745 5842215225914887312297309)
                ·
                  refine ⟨2190830709718082742111491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5842215225914887312297309 2190830709718082742111491)
                  ·
                    refine ⟨3286246064577124113167237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2190830709718082742111491 3286246064577124113167237)
                    ·
                      refine ⟨616171137108210771218857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3286246064577124113167237 616171137108210771218857)
                      ·
                        rfl

theorem cell23_1199989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1199989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199989 prefixEnd_1199989 := by exact prefixLift 1199989
  have htrace : WordTrace (prefixWord ++ tailWord_1199989) baseStart_1199989 baseEnd_1199989 := by
    simpa [prefixWord, tailWord_1199989, baseEnd_1199989] using wordTrace_append hprefix tailTrace_1199989
  have hstable : (prefixWord ++ tailWord_1199989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199989).length < 2 ^ (prefixWord ++ tailWord_1199989).sum := by decide
  have hdescent : baseEnd_1199989 < baseStart_1199989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199990 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 6]
def baseStart_1199990 : Nat := 118140960795 + 1199990 * 2 ^ 59
def prefixEnd_1199990 : Nat := 4983230072969 + 3 ^ 40 * 1199990 * 2
def baseEnd_1199990 : Nat := 68463516732096140811817

theorem tailTrace_1199990 : CollatzResearch.WordTrace tailWord_1199990 prefixEnd_1199990 68463516732096140811817 := by
  unfold tailWord_1199990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735451932665540426302839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29178153948432431213896949 2735451932665540426302839)
  ·
    refine ⟨4103177898998310639454259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2735451932665540426302839 4103177898998310639454259)
    ·
      refine ⟨6154766848497465959181389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4103177898998310639454259 6154766848497465959181389)
      ·
        refine ⟨2308037568186549734693021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6154766848497465959181389 2308037568186549734693021)
        ·
          refine ⟨865514088069956150509883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2308037568186549734693021 865514088069956150509883)
          ·
            refine ⟨1298271132104934225764825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865514088069956150509883 1298271132104934225764825)
            ·
              refine ⟨973703349078700669323619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298271132104934225764825 973703349078700669323619)
              ·
                refine ⟨1460555023618051003985429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973703349078700669323619 1460555023618051003985429)
                ·
                  refine ⟨68463516732096140811817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1460555023618051003985429 68463516732096140811817)
                  ·
                    rfl

theorem cell23_1199990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_1199990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1199990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1199990 prefixEnd_1199990 := by exact prefixLift 1199990
  have htrace : WordTrace (prefixWord ++ tailWord_1199990) baseStart_1199990 baseEnd_1199990 := by
    simpa [prefixWord, tailWord_1199990, baseEnd_1199990] using wordTrace_append hprefix tailTrace_1199990
  have hstable : (prefixWord ++ tailWord_1199990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199990).length < 2 ^ (prefixWord ++ tailWord_1199990).sum := by decide
  have hdescent : baseEnd_1199990 < baseStart_1199990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200009 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 3]
def baseStart_1200009 : Nat := 118140960795 + 1200009 * 2 ^ 59
def prefixEnd_1200009 : Nat := 4983230072969 + 3 ^ 40 * 1200009 * 2
def baseEnd_1200009 : Nat := 616181406721300692968765

theorem tailTrace_1200009 : CollatzResearch.WordTrace tailWord_1200009 prefixEnd_1200009 616181406721300692968765 := by
  unfold tailWord_1200009
  simp only [CollatzResearch.WordTrace]
  refine ⟨43767923909579813065787081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29178615939719875377191387 43767923909579813065787081)
  ·
    refine ⟨32825942932184859799340311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43767923909579813065787081 32825942932184859799340311)
    ·
      refine ⟨49238914398277289699010467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32825942932184859799340311 49238914398277289699010467)
      ·
        refine ⟨73858371597415934548515701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49238914398277289699010467 73858371597415934548515701)
        ·
          refine ⟨6924222337257743863923347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73858371597415934548515701 6924222337257743863923347)
          ·
            refine ⟨10386333505886615795885021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6924222337257743863923347 10386333505886615795885021)
            ·
              refine ⟨3894875064707480923456883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10386333505886615795885021 3894875064707480923456883)
              ·
                refine ⟨5842312597061221385185325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894875064707480923456883 5842312597061221385185325)
                ·
                  refine ⟨2190867223897958019444497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5842312597061221385185325 2190867223897958019444497)
                  ·
                    refine ⟨1643150417923468514583373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2190867223897958019444497 1643150417923468514583373)
                    ·
                      refine ⟨616181406721300692968765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1643150417923468514583373 616181406721300692968765)
                      ·
                        rfl

theorem cell23_1200009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_1200009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200009 prefixEnd_1200009 := by exact prefixLift 1200009
  have htrace : WordTrace (prefixWord ++ tailWord_1200009) baseStart_1200009 baseEnd_1200009 := by
    simpa [prefixWord, tailWord_1200009, baseEnd_1200009] using wordTrace_append hprefix tailTrace_1200009
  have hstable : (prefixWord ++ tailWord_1200009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200009).length < 2 ^ (prefixWord ++ tailWord_1200009).sum := by decide
  have hdescent : baseEnd_1200009 < baseStart_1200009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200026 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1200026 : Nat := 118140960795 + 1200026 * 2 ^ 59
def prefixEnd_1200026 : Nat := 4983230072969 + 3 ^ 40 * 1200026 * 2
def baseEnd_1200026 : Nat := 616190135892427126456187

theorem tailTrace_1200026 : CollatzResearch.WordTrace tailWord_1200026 prefixEnd_1200026 616190135892427126456187 := by
  unfold tailWord_1200026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10942135987629556242288983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29179029300345483312770621 10942135987629556242288983)
  ·
    refine ⟨16413203981444334363433475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10942135987629556242288983 16413203981444334363433475)
    ·
      refine ⟨24619805972166501545150213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16413203981444334363433475 24619805972166501545150213)
      ·
        refine ⟨4616213619781219039715665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24619805972166501545150213 4616213619781219039715665)
        ·
          refine ⟨3462160214835914279786749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4616213619781219039715665 3462160214835914279786749)
          ·
            refine ⟨1298310080563467854920031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3462160214835914279786749 1298310080563467854920031)
            ·
              refine ⟨1947465120845201782380047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298310080563467854920031 1947465120845201782380047)
              ·
                refine ⟨2921197681267802673570071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947465120845201782380047 2921197681267802673570071)
                ·
                  refine ⟨4381796521901704010355107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2921197681267802673570071 4381796521901704010355107)
                  ·
                    refine ⟨6572694782852556015532661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4381796521901704010355107 6572694782852556015532661)
                    ·
                      refine ⟨616190135892427126456187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6572694782852556015532661 616190135892427126456187)
                      ·
                        rfl

theorem cell23_1200026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1200026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200026 prefixEnd_1200026 := by exact prefixLift 1200026
  have htrace : WordTrace (prefixWord ++ tailWord_1200026) baseStart_1200026 baseEnd_1200026 := by
    simpa [prefixWord, tailWord_1200026, baseEnd_1200026] using wordTrace_append hprefix tailTrace_1200026
  have hstable : (prefixWord ++ tailWord_1200026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200026).length < 2 ^ (prefixWord ++ tailWord_1200026).sum := by decide
  have hdescent : baseEnd_1200026 < baseStart_1200026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200033 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 2, 4]
def baseStart_1200033 : Nat := 118140960795 + 1200033 * 2 ^ 59
def prefixEnd_1200033 : Nat := 4983230072969 + 3 ^ 40 * 1200033 * 2
def baseEnd_1200033 : Nat := 205397910085669533022885

theorem tailTrace_1200033 : CollatzResearch.WordTrace tailWord_1200033 prefixEnd_1200033 205397910085669533022885 := by
  unfold tailWord_1200033
  simp only [CollatzResearch.WordTrace]
  refine ⟨43768799261492865164660753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29179199507661910109773835 43768799261492865164660753)
  ·
    refine ⟨32826599446119648873495565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43768799261492865164660753 32826599446119648873495565)
    ·
      refine ⟨12309974792294868327560837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32826599446119648873495565 12309974792294868327560837)
      ·
        refine ⟨2308120273555287811417657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12309974792294868327560837 2308120273555287811417657)
        ·
          refine ⟨1731090205166465858563243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2308120273555287811417657 1731090205166465858563243)
          ·
            refine ⟨2596635307749698787844865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731090205166465858563243 2596635307749698787844865)
            ·
              refine ⟨1947476480812274090883649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2596635307749698787844865 1947476480812274090883649)
              ·
                refine ⟨1460607360609205568162737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947476480812274090883649 1460607360609205568162737)
                ·
                  refine ⟨1095455520456904176122053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460607360609205568162737 1095455520456904176122053)
                  ·
                    refine ⟨205397910085669533022885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1095455520456904176122053 205397910085669533022885)
                    ·
                      rfl

theorem cell23_1200033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_1200033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200033 prefixEnd_1200033 := by exact prefixLift 1200033
  have htrace : WordTrace (prefixWord ++ tailWord_1200033) baseStart_1200033 baseEnd_1200033 := by
    simpa [prefixWord, tailWord_1200033, baseEnd_1200033] using wordTrace_append hprefix tailTrace_1200033
  have hstable : (prefixWord ++ tailWord_1200033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200033).length < 2 ^ (prefixWord ++ tailWord_1200033).sum := by decide
  have hdescent : baseEnd_1200033 < baseStart_1200033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200034 : List Nat := [3, 3, 1, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_1200034 : Nat := 118140960795 + 1200034 * 2 ^ 59
def prefixEnd_1200034 : Nat := 4983230072969 + 3 ^ 40 * 1200034 * 2
def baseEnd_1200034 : Nat := 616194243737663095156151

theorem tailTrace_1200034 : CollatzResearch.WordTrace tailWord_1200034 prefixEnd_1200034 616194243737663095156151 := by
  unfold tailWord_1200034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10942208933622310583861789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29179223822992828223631437 10942208933622310583861789)
  ·
    refine ⟨4103328350108366468948171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10942208933622310583861789 4103328350108366468948171)
    ·
      refine ⟨6154992525162549703422257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4103328350108366468948171 6154992525162549703422257)
      ·
        refine ⟨4616244393871912277566693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6154992525162549703422257 4616244393871912277566693)
        ·
          refine ⟨865545823850983552043755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4616244393871912277566693 865545823850983552043755)
          ·
            refine ⟨1298318735776475328065633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865545823850983552043755 1298318735776475328065633)
            ·
              refine ⟨973739051832356496049225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298318735776475328065633 973739051832356496049225)
              ·
                refine ⟨730304288874267372036919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973739051832356496049225 730304288874267372036919)
                ·
                  refine ⟨1095456433311401058055379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730304288874267372036919 1095456433311401058055379)
                  ·
                    refine ⟨1643184649967101587083069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1095456433311401058055379 1643184649967101587083069)
                    ·
                      refine ⟨616194243737663095156151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1643184649967101587083069 616194243737663095156151)
                      ·
                        rfl

theorem cell23_1200034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_1200034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200034 prefixEnd_1200034 := by exact prefixLift 1200034
  have htrace : WordTrace (prefixWord ++ tailWord_1200034) baseStart_1200034 baseEnd_1200034 := by
    simpa [prefixWord, tailWord_1200034, baseEnd_1200034] using wordTrace_append hprefix tailTrace_1200034
  have hstable : (prefixWord ++ tailWord_1200034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200034).length < 2 ^ (prefixWord ++ tailWord_1200034).sum := by decide
  have hdescent : baseEnd_1200034 < baseStart_1200034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200056 : List Nat := [2, 1, 2, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_1200056 : Nat := 118140960795 + 1200056 * 2 ^ 59
def prefixEnd_1200056 : Nat := 4983230072969 + 3 ^ 40 * 1200056 * 2
def baseEnd_1200056 : Nat := 616205540312062009081049

theorem tailTrace_1200056 : CollatzResearch.WordTrace tailWord_1200056 prefixEnd_1200056 616205540312062009081049 := by
  unfold tailWord_1200056
  simp only [CollatzResearch.WordTrace]
  refine ⟨21884819070204770046374011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29179758760273026728498681 21884819070204770046374011)
  ·
    refine ⟨32827228605307155069561017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21884819070204770046374011 32827228605307155069561017)
    ·
      refine ⟨24620421453980366302170763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32827228605307155069561017 24620421453980366302170763)
      ·
        refine ⟨36930632180970549453256145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24620421453980366302170763 36930632180970549453256145)
        ·
          refine ⟨27697974135727912089942109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36930632180970549453256145 27697974135727912089942109)
          ·
            refine ⟨10386740300897967033728291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27697974135727912089942109 10386740300897967033728291)
            ·
              refine ⟨15580110451346950550592437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10386740300897967033728291 15580110451346950550592437)
              ·
                refine ⟨1460635354813776614118041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15580110451346950550592437 1460635354813776614118041)
                ·
                  refine ⟨1095476516110332460588531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460635354813776614118041 1095476516110332460588531)
                  ·
                    refine ⟨1643214774165498690882797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1095476516110332460588531 1643214774165498690882797)
                    ·
                      refine ⟨616205540312062009081049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1643214774165498690882797 616205540312062009081049)
                      ·
                        rfl

theorem cell23_1200056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_1200056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200056 prefixEnd_1200056 := by exact prefixLift 1200056
  have htrace : WordTrace (prefixWord ++ tailWord_1200056) baseStart_1200056 baseEnd_1200056 := by
    simpa [prefixWord, tailWord_1200056, baseEnd_1200056] using wordTrace_append hprefix tailTrace_1200056
  have hstable : (prefixWord ++ tailWord_1200056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200056).length < 2 ^ (prefixWord ++ tailWord_1200056).sum := by decide
  have hdescent : baseEnd_1200056 < baseStart_1200056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200090 : List Nat := [3, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_1200090 : Nat := 118140960795 + 1200090 * 2 ^ 59
def prefixEnd_1200090 : Nat := 4983230072969 + 3 ^ 40 * 1200090 * 2
def baseEnd_1200090 : Nat := 616222998654314876055893

theorem tailTrace_1200090 : CollatzResearch.WordTrace tailWord_1200090 prefixEnd_1200090 616222998654314876055893 := by
  unfold tailWord_1200090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10942719555571590974871431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29180585481524242599657149 10942719555571590974871431)
  ·
    refine ⟨16414079333357386462307147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10942719555571590974871431 16414079333357386462307147)
    ·
      refine ⟨24621119000036079693460721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16414079333357386462307147 24621119000036079693460721)
      ·
        refine ⟨18465839250027059770095541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24621119000036079693460721 18465839250027059770095541)
        ·
          refine ⟨1731172429690036853446457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18465839250027059770095541 1731172429690036853446457)
          ·
            refine ⟨1298379322267527640084843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1731172429690036853446457 1298379322267527640084843)
            ·
              refine ⟨1947568983401291460127265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298379322267527640084843 1947568983401291460127265)
              ·
                refine ⟨1460676737550968595095449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947568983401291460127265 1460676737550968595095449)
                ·
                  refine ⟨1095507553163226446321587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460676737550968595095449 1095507553163226446321587)
                  ·
                    refine ⟨1643261329744839669482381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1095507553163226446321587 1643261329744839669482381)
                    ·
                      refine ⟨616222998654314876055893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1643261329744839669482381 616222998654314876055893)
                      ·
                        rfl

theorem cell23_1200090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_1200090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200090 prefixEnd_1200090 := by exact prefixLift 1200090
  have htrace : WordTrace (prefixWord ++ tailWord_1200090) baseStart_1200090 baseEnd_1200090 := by
    simpa [prefixWord, tailWord_1200090, baseEnd_1200090] using wordTrace_append hprefix tailTrace_1200090
  have hstable : (prefixWord ++ tailWord_1200090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200090).length < 2 ^ (prefixWord ++ tailWord_1200090).sum := by decide
  have hdescent : baseEnd_1200090 < baseStart_1200090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200159 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_1200159 : Nat := 118140960795 + 1200159 * 2 ^ 59
def prefixEnd_1200159 : Nat := 4983230072969 + 3 ^ 40 * 1200159 * 2
def baseEnd_1200159 : Nat := 616258428819475106093075

theorem tailTrace_1200159 : CollatzResearch.WordTrace tailWord_1200159 prefixEnd_1200159 616258428819475106093075 := by
  unfold tailWord_1200159
  simp only [CollatzResearch.WordTrace]
  refine ⟨43773394859036388683747531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29182263239357592455831687 43773394859036388683747531)
  ·
    refine ⟨65660092288554583025621297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43773394859036388683747531 65660092288554583025621297)
    ·
      refine ⟨49245069216415937269215973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65660092288554583025621297 49245069216415937269215973)
      ·
        refine ⟨9233450478077988237977995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49245069216415937269215973 9233450478077988237977995)
        ·
          refine ⟨13850175717116982356966993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9233450478077988237977995 13850175717116982356966993)
          ·
            refine ⟨10387631787837736767725245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13850175717116982356966993 10387631787837736767725245)
            ·
              refine ⟨3895361920439151287896967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10387631787837736767725245 3895361920439151287896967)
              ·
                refine ⟨5843042880658726931845451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895361920439151287896967 5843042880658726931845451)
                ·
                  refine ⟨8764564320988090397768177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5843042880658726931845451 8764564320988090397768177)
                  ·
                    refine ⟨6573423240741067798326133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8764564320988090397768177 6573423240741067798326133)
                    ·
                      refine ⟨616258428819475106093075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6573423240741067798326133 616258428819475106093075)
                      ·
                        rfl

theorem cell23_1200159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_1200159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200159 prefixEnd_1200159 := by exact prefixLift 1200159
  have htrace : WordTrace (prefixWord ++ tailWord_1200159) baseStart_1200159 baseEnd_1200159 := by
    simpa [prefixWord, tailWord_1200159, baseEnd_1200159] using wordTrace_append hprefix tailTrace_1200159
  have hstable : (prefixWord ++ tailWord_1200159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200159).length < 2 ^ (prefixWord ++ tailWord_1200159).sum := by decide
  have hdescent : baseEnd_1200159 < baseStart_1200159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200164 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1200164 : Nat := 118140960795 + 1200164 * 2 ^ 59
def prefixEnd_1200164 : Nat := 4983230072969 + 3 ^ 40 * 1200164 * 2
def baseEnd_1200164 : Nat := 616260996222747586530553

theorem tailTrace_1200164 : CollatzResearch.WordTrace tailWord_1200164 prefixEnd_1200164 616260996222747586530553 := by
  unfold tailWord_1200164
  simp only [CollatzResearch.WordTrace]
  refine ⟨21886788612009137268839773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29182384816012183025119697 21886788612009137268839773)
  ·
    refine ⟨8207545729503426475814915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21886788612009137268839773 8207545729503426475814915)
    ·
      refine ⟨12311318594255139713722373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8207545729503426475814915 12311318594255139713722373)
      ·
        refine ⟨2308372236422838696322945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12311318594255139713722373 2308372236422838696322945)
        ·
          refine ⟨1731279177317129022242209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2308372236422838696322945 1731279177317129022242209)
          ·
            refine ⟨1298459382987846766681657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1731279177317129022242209 1298459382987846766681657)
            ·
              refine ⟨973844537240885075011243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298459382987846766681657 973844537240885075011243)
              ·
                refine ⟨1460766805861327612516865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973844537240885075011243 1460766805861327612516865)
                ·
                  refine ⟨1095575104395995709387649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460766805861327612516865 1095575104395995709387649)
                  ·
                    refine ⟨821681328296996782040737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1095575104395995709387649 821681328296996782040737)
                    ·
                      refine ⟨616260996222747586530553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821681328296996782040737 616260996222747586530553)
                      ·
                        rfl

theorem cell23_1200164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1200164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200164 prefixEnd_1200164 := by exact prefixLift 1200164
  have htrace : WordTrace (prefixWord ++ tailWord_1200164) baseStart_1200164 baseEnd_1200164 := by
    simpa [prefixWord, tailWord_1200164, baseEnd_1200164] using wordTrace_append hprefix tailTrace_1200164
  have hstable : (prefixWord ++ tailWord_1200164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200164).length < 2 ^ (prefixWord ++ tailWord_1200164).sum := by decide
  have hdescent : baseEnd_1200164 < baseStart_1200164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200186 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2]
def baseStart_1200186 : Nat := 118140960795 + 1200186 * 2 ^ 59
def prefixEnd_1200186 : Nat := 4983230072969 + 3 ^ 40 * 1200186 * 2
def baseEnd_1200186 : Nat := 616272292797146500455451

theorem tailTrace_1200186 : CollatzResearch.WordTrace tailWord_1200186 prefixEnd_1200186 616272292797146500455451 := by
  unfold tailWord_1200186
  simp only [CollatzResearch.WordTrace]
  refine ⟨10943594907484643073745103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29182919753292381529986941 10943594907484643073745103)
  ·
    refine ⟨16415392361226964610617655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10943594907484643073745103 16415392361226964610617655)
    ·
      refine ⟨24623088541840446915926483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16415392361226964610617655 24623088541840446915926483)
      ·
        refine ⟨36934632812760670373889725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24623088541840446915926483 36934632812760670373889725)
        ·
          refine ⟨13850487304785251390208647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36934632812760670373889725 13850487304785251390208647)
          ·
            refine ⟨20775730957177877085312971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13850487304785251390208647 20775730957177877085312971)
            ·
              refine ⟨31163596435766815627969457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20775730957177877085312971 31163596435766815627969457)
              ·
                refine ⟨23372697326825111720977093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31163596435766815627969457 23372697326825111720977093)
                ·
                  refine ⟨4382380748779708447683205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23372697326825111720977093 4382380748779708447683205)
                  ·
                    refine ⟨821696390396195333940601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4382380748779708447683205 821696390396195333940601)
                    ·
                      refine ⟨616272292797146500455451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821696390396195333940601 616272292797146500455451)
                      ·
                        rfl

theorem cell23_1200186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_1200186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200186 prefixEnd_1200186 := by exact prefixLift 1200186
  have htrace : WordTrace (prefixWord ++ tailWord_1200186) baseStart_1200186 baseEnd_1200186 := by
    simpa [prefixWord, tailWord_1200186, baseEnd_1200186] using wordTrace_append hprefix tailTrace_1200186
  have hstable : (prefixWord ++ tailWord_1200186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200186).length < 2 ^ (prefixWord ++ tailWord_1200186).sum := by decide
  have hdescent : baseEnd_1200186 < baseStart_1200186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200199 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1200199 : Nat := 118140960795 + 1200199 * 2 ^ 59
def prefixEnd_1200199 : Nat := 4983230072969 + 3 ^ 40 * 1200199 * 2
def baseEnd_1200199 : Nat := 616278968045654949592891

theorem tailTrace_1200199 : CollatzResearch.WordTrace tailWord_1200199 prefixEnd_1200199 616278968045654949592891 := by
  unfold tailWord_1200199
  simp only [CollatzResearch.WordTrace]
  refine ⟨43774853778891475515203651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29183235852594317010135767 43774853778891475515203651)
  ·
    refine ⟨65662280668337213272805477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43774853778891475515203651 65662280668337213272805477)
    ·
      refine ⟨12311677625313227488651027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65662280668337213272805477 12311677625313227488651027)
      ·
        refine ⟨18467516437969841232976541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12311677625313227488651027 18467516437969841232976541)
        ·
          refine ⟨6925318664238690462366203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18467516437969841232976541 6925318664238690462366203)
          ·
            refine ⟨10387977996358035693549305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925318664238690462366203 10387977996358035693549305)
            ·
              refine ⟨7790983497268526770161979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10387977996358035693549305 7790983497268526770161979)
              ·
                refine ⟨11686475245902790155242969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7790983497268526770161979 11686475245902790155242969)
                ·
                  refine ⟨8764856434427092616432227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11686475245902790155242969 8764856434427092616432227)
                  ·
                    refine ⟨13147284651640638924648341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8764856434427092616432227 13147284651640638924648341)
                    ·
                      refine ⟨616278968045654949592891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13147284651640638924648341 616278968045654949592891)
                      ·
                        rfl

theorem cell23_1200199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1200199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200199 prefixEnd_1200199 := by exact prefixLift 1200199
  have htrace : WordTrace (prefixWord ++ tailWord_1200199) baseStart_1200199 baseEnd_1200199 := by
    simpa [prefixWord, tailWord_1200199, baseEnd_1200199] using wordTrace_append hprefix tailTrace_1200199
  have hstable : (prefixWord ++ tailWord_1200199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200199).length < 2 ^ (prefixWord ++ tailWord_1200199).sum := by decide
  have hdescent : baseEnd_1200199 < baseStart_1200199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200263 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_1200263 : Nat := 118140960795 + 1200263 * 2 ^ 59
def prefixEnd_1200263 : Nat := 4983230072969 + 3 ^ 40 * 1200263 * 2
def baseEnd_1200263 : Nat := 616311830807542699192597

theorem tailTrace_1200263 : CollatzResearch.WordTrace tailWord_1200263 prefixEnd_1200263 616311830807542699192597 := by
  unfold tailWord_1200263
  simp only [CollatzResearch.WordTrace]
  refine ⟨43777188050659614445533443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29184792033773076297022295 43777188050659614445533443)
  ·
    refine ⟨65665782075989421668300165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43777188050659614445533443 65665782075989421668300165)
    ·
      refine ⟨12312334139248016562806281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65665782075989421668300165 12312334139248016562806281)
      ·
        refine ⟨9234250604436012422104711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12312334139248016562806281 9234250604436012422104711)
        ·
          refine ⟨13851375906654018633157067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9234250604436012422104711 13851375906654018633157067)
          ·
            refine ⟨20777063859981027949735601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13851375906654018633157067 20777063859981027949735601)
            ·
              refine ⟨15582797894985770962301701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20777063859981027949735601 15582797894985770962301701)
              ·
                refine ⟨2921774605309832055431569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15582797894985770962301701 2921774605309832055431569)
                ·
                  refine ⟨2191330953982374041573677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2921774605309832055431569 2191330953982374041573677)
                  ·
                    refine ⟨821749107743390265590129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191330953982374041573677 821749107743390265590129)
                    ·
                      refine ⟨616311830807542699192597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821749107743390265590129 616311830807542699192597)
                      ·
                        rfl

theorem cell23_1200263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_1200263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200263 prefixEnd_1200263 := by exact prefixLift 1200263
  have htrace : WordTrace (prefixWord ++ tailWord_1200263) baseStart_1200263 baseEnd_1200263 := by
    simpa [prefixWord, tailWord_1200263, baseEnd_1200263] using wordTrace_append hprefix tailTrace_1200263
  have hstable : (prefixWord ++ tailWord_1200263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200263).length < 2 ^ (prefixWord ++ tailWord_1200263).sum := by decide
  have hdescent : baseEnd_1200263 < baseStart_1200263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200290 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1200290 : Nat := 118140960795 + 1200290 * 2 ^ 59
def prefixEnd_1200290 : Nat := 4983230072969 + 3 ^ 40 * 1200290 * 2
def baseEnd_1200290 : Nat := 205441898261738031184991

theorem tailTrace_1200290 : CollatzResearch.WordTrace tailWord_1200290 prefixEnd_1200290 205441898261738031184991 := by
  unfold tailWord_1200290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944543205390449514191581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29185448547707865371177549 10944543205390449514191581)
  ·
    refine ⟨4104203702021418567821843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10944543205390449514191581 4104203702021418567821843)
    ·
      refine ⟨6156305553032127851732765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4104203702021418567821843 6156305553032127851732765)
      ·
        refine ⟨2308614582387047944399787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6156305553032127851732765 2308614582387047944399787)
        ·
          refine ⟨3462921873580571916599681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308614582387047944399787 3462921873580571916599681)
          ·
            refine ⟨2597191405185428937449761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3462921873580571916599681 2597191405185428937449761)
            ·
              refine ⟨1947893553889071703087321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2597191405185428937449761 1947893553889071703087321)
              ·
                refine ⟨1460920165416803777315491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947893553889071703087321 1460920165416803777315491)
                ·
                  refine ⟨2191380248125205665973237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460920165416803777315491 2191380248125205665973237)
                  ·
                    refine ⟨205441898261738031184991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2191380248125205665973237 205441898261738031184991)
                    ·
                      rfl

theorem cell23_1200290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1200290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200290 prefixEnd_1200290 := by exact prefixLift 1200290
  have htrace : WordTrace (prefixWord ++ tailWord_1200290) baseStart_1200290 baseEnd_1200290 := by
    simpa [prefixWord, tailWord_1200290, baseEnd_1200290] using wordTrace_append hprefix tailTrace_1200290
  have hstable : (prefixWord ++ tailWord_1200290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200290).length < 2 ^ (prefixWord ++ tailWord_1200290).sum := by decide
  have hdescent : baseEnd_1200290 < baseStart_1200290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200293 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_1200293 : Nat := 118140960795 + 1200293 * 2 ^ 59
def prefixEnd_1200293 : Nat := 4983230072969 + 3 ^ 40 * 1200293 * 2
def baseEnd_1200293 : Nat := 616327235227177581817459

theorem tailTrace_1200293 : CollatzResearch.WordTrace tailWord_1200293 prefixEnd_1200293 616327235227177581817459 := by
  unfold tailWord_1200293
  simp only [CollatzResearch.WordTrace]
  refine ⟨43778282240550929569125533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29185521493700619712750355 43778282240550929569125533)
  ·
    refine ⟨16416855840206598588422075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43778282240550929569125533 16416855840206598588422075)
    ·
      refine ⟨24625283760309897882633113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16416855840206598588422075 24625283760309897882633113)
      ·
        refine ⟨18468962820232423411974835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24625283760309897882633113 18468962820232423411974835)
        ·
          refine ⟨27703444230348635117962253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18468962820232423411974835 27703444230348635117962253)
          ·
            refine ⟨10388791586380738169235845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27703444230348635117962253 10388791586380738169235845)
            ·
              refine ⟨1947898422446388406731721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10388791586380738169235845 1947898422446388406731721)
              ·
                refine ⟨1460923816834791305048791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947898422446388406731721 1460923816834791305048791)
                ·
                  refine ⟨2191385725252186957573187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460923816834791305048791 2191385725252186957573187)
                  ·
                    refine ⟨3287078587878280436359781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2191385725252186957573187 3287078587878280436359781)
                    ·
                      refine ⟨616327235227177581817459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3287078587878280436359781 616327235227177581817459)
                      ·
                        rfl

theorem cell23_1200293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_1200293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200293 prefixEnd_1200293 := by exact prefixLift 1200293
  have htrace : WordTrace (prefixWord ++ tailWord_1200293) baseStart_1200293 baseEnd_1200293 := by
    simpa [prefixWord, tailWord_1200293, baseEnd_1200293] using wordTrace_append hprefix tailTrace_1200293
  have hstable : (prefixWord ++ tailWord_1200293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200293).length < 2 ^ (prefixWord ++ tailWord_1200293).sum := by decide
  have hdescent : baseEnd_1200293 < baseStart_1200293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200306 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1200306 : Nat := 118140960795 + 1200306 * 2 ^ 59
def prefixEnd_1200306 : Nat := 4983230072969 + 3 ^ 40 * 1200306 * 2
def baseEnd_1200306 : Nat := 616333910475686030954899

theorem tailTrace_1200306 : CollatzResearch.WordTrace tailWord_1200306 prefixEnd_1200306 616333910475686030954899 := by
  unfold tailWord_1200306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944689097375958197337193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29185837593002555192899181 10944689097375958197337193)
  ·
    refine ⟨8208516823031968648002895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10944689097375958197337193 8208516823031968648002895)
    ·
      refine ⟨12312775234547952972004343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8208516823031968648002895 12312775234547952972004343)
      ·
        refine ⟨18469162851821929458006515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12312775234547952972004343 18469162851821929458006515)
        ·
          refine ⟨27703744277732894187009773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18469162851821929458006515 27703744277732894187009773)
          ·
            refine ⟨10388904104149835320128665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27703744277732894187009773 10388904104149835320128665)
            ·
              refine ⟨7791678078112376490096499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10388904104149835320128665 7791678078112376490096499)
              ·
                refine ⟨11687517117168564735144749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7791678078112376490096499 11687517117168564735144749)
                ·
                  refine ⟨4382818918938211775679281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11687517117168564735144749 4382818918938211775679281)
                  ·
                    refine ⟨3287114189203658831759461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4382818918938211775679281 3287114189203658831759461)
                    ·
                      refine ⟨616333910475686030954899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3287114189203658831759461 616333910475686030954899)
                      ·
                        rfl

theorem cell23_1200306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1200306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200306 prefixEnd_1200306 := by exact prefixLift 1200306
  have htrace : WordTrace (prefixWord ++ tailWord_1200306) baseStart_1200306 baseEnd_1200306 := by
    simpa [prefixWord, tailWord_1200306, baseEnd_1200306] using wordTrace_append hprefix tailTrace_1200306
  have hstable : (prefixWord ++ tailWord_1200306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200306).length < 2 ^ (prefixWord ++ tailWord_1200306).sum := by decide
  have hdescent : baseEnd_1200306 < baseStart_1200306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200313 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 3]
def baseStart_1200313 : Nat := 118140960795 + 1200313 * 2 ^ 59
def prefixEnd_1200313 : Nat := 4983230072969 + 3 ^ 40 * 1200313 * 2
def baseEnd_1200313 : Nat := 616337504840267503567367

theorem tailTrace_1200313 : CollatzResearch.WordTrace tailWord_1200313 prefixEnd_1200313 616337504840267503567367 := by
  unfold tailWord_1200313
  simp only [CollatzResearch.WordTrace]
  refine ⟨43779011700478472984853593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29186007800318981989902395 43779011700478472984853593)
  ·
    refine ⟨32834258775358854738640195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43779011700478472984853593 32834258775358854738640195)
    ·
      refine ⟨49251388163038282107960293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32834258775358854738640195 49251388163038282107960293)
      ·
        refine ⟨9234635280569677895242555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49251388163038282107960293 9234635280569677895242555)
        ·
          refine ⟨13851952920854516842863833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9234635280569677895242555 13851952920854516842863833)
          ·
            refine ⟨10388964690640887632147875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13851952920854516842863833 10388964690640887632147875)
            ·
              refine ⟨15583447035961331448221813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10388964690640887632147875 15583447035961331448221813)
              ·
                refine ⟨1460948159621374823270795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15583447035961331448221813 1460948159621374823270795)
                ·
                  refine ⟨2191422239432062234906193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460948159621374823270795 2191422239432062234906193)
                  ·
                    refine ⟨1643566679574046676179645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2191422239432062234906193 1643566679574046676179645)
                    ·
                      refine ⟨616337504840267503567367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1643566679574046676179645 616337504840267503567367)
                      ·
                        rfl

theorem cell23_1200313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_1200313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200313 prefixEnd_1200313 := by exact prefixLift 1200313
  have htrace : WordTrace (prefixWord ++ tailWord_1200313) baseStart_1200313 baseEnd_1200313 := by
    simpa [prefixWord, tailWord_1200313, baseEnd_1200313] using wordTrace_append hprefix tailTrace_1200313
  have hstable : (prefixWord ++ tailWord_1200313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200313).length < 2 ^ (prefixWord ++ tailWord_1200313).sum := by decide
  have hdescent : baseEnd_1200313 < baseStart_1200313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200321 : List Nat := [1, 2, 6, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1200321 : Nat := 118140960795 + 1200321 * 2 ^ 59
def prefixEnd_1200321 : Nat := 4983230072969 + 3 ^ 40 * 1200321 * 2
def baseEnd_1200321 : Nat := 616341612685503472267331

theorem tailTrace_1200321 : CollatzResearch.WordTrace tailWord_1200321 prefixEnd_1200321 616341612685503472267331 := by
  unfold tailWord_1200321
  simp only [CollatzResearch.WordTrace]
  refine ⟨43779303484449490351144817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29186202322966326900763211 43779303484449490351144817)
  ·
    refine ⟨32834477613337117763358613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43779303484449490351144817 32834477613337117763358613)
    ·
      refine ⟨1539116138125177395157435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32834477613337117763358613 1539116138125177395157435)
      ·
        refine ⟨2308674207187766092736153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1539116138125177395157435 2308674207187766092736153)
        ·
          refine ⟨1731505655390824569552115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2308674207187766092736153 1731505655390824569552115)
          ·
            refine ⟨2597258483086236854328173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731505655390824569552115 2597258483086236854328173)
            ·
              refine ⟨973971931157338820373065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2597258483086236854328173 973971931157338820373065)
              ·
                refine ⟨730478948368004115279799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973971931157338820373065 730478948368004115279799)
                ·
                  refine ⟨1095718422552006172919699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730478948368004115279799 1095718422552006172919699)
                  ·
                    refine ⟨1643577633828009259379549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1095718422552006172919699 1643577633828009259379549)
                    ·
                      refine ⟨616341612685503472267331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1643577633828009259379549 616341612685503472267331)
                      ·
                        rfl

theorem cell23_1200321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1200321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200321 prefixEnd_1200321 := by exact prefixLift 1200321
  have htrace : WordTrace (prefixWord ++ tailWord_1200321) baseStart_1200321 baseEnd_1200321 := by
    simpa [prefixWord, tailWord_1200321, baseEnd_1200321] using wordTrace_append hprefix tailTrace_1200321
  have hstable : (prefixWord ++ tailWord_1200321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200321).length < 2 ^ (prefixWord ++ tailWord_1200321).sum := by decide
  have hdescent : baseEnd_1200321 < baseStart_1200321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200383 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 3, 4, 2]
def baseStart_1200383 : Nat := 118140960795 + 1200383 * 2 ^ 59
def prefixEnd_1200383 : Nat := 4983230072969 + 3 ^ 40 * 1200383 * 2
def baseEnd_1200383 : Nat := 616373448486082229692045

theorem tailTrace_1200383 : CollatzResearch.WordTrace tailWord_1200383 prefixEnd_1200383 616373448486082229692045 := by
  unfold tailWord_1200383
  simp only [CollatzResearch.WordTrace]
  refine ⟨43781564810224874939901803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29187709873483249959934535 43781564810224874939901803)
  ·
    refine ⟨65672347215337312409852705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43781564810224874939901803 65672347215337312409852705)
    ·
      refine ⟨49254260411502984307389529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65672347215337312409852705 49254260411502984307389529)
      ·
        refine ⟨36940695308627238230542147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49254260411502984307389529 36940695308627238230542147)
        ·
          refine ⟨55411042962940857345813221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36940695308627238230542147 55411042962940857345813221)
          ·
            refine ⟨10389570555551410752339979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55411042962940857345813221 10389570555551410752339979)
            ·
              refine ⟨15584355833327116128509969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10389570555551410752339979 15584355833327116128509969)
              ·
                refine ⟨11688266874995337096382477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15584355833327116128509969 11688266874995337096382477)
                ·
                  refine ⟨4383100078123251411143429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11688266874995337096382477 4383100078123251411143429)
                  ·
                    refine ⟨821831264648109639589393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4383100078123251411143429 821831264648109639589393)
                    ·
                      refine ⟨616373448486082229692045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821831264648109639589393 616373448486082229692045)
                      ·
                        rfl

theorem cell23_1200383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_1200383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200383 prefixEnd_1200383 := by exact prefixLift 1200383
  have htrace : WordTrace (prefixWord ++ tailWord_1200383) baseStart_1200383 baseEnd_1200383 := by
    simpa [prefixWord, tailWord_1200383, baseEnd_1200383] using wordTrace_append hprefix tailTrace_1200383
  have hstable : (prefixWord ++ tailWord_1200383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200383).length < 2 ^ (prefixWord ++ tailWord_1200383).sum := by decide
  have hdescent : baseEnd_1200383 < baseStart_1200383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200421 : List Nat := [1, 3, 1, 2, 6, 1, 2, 1, 1, 3, 2]
def baseStart_1200421 : Nat := 118140960795 + 1200421 * 2 ^ 59
def prefixEnd_1200421 : Nat := 4983230072969 + 3 ^ 40 * 1200421 * 2
def baseEnd_1200421 : Nat := 616392960750953081016871

theorem tailTrace_1200421 : CollatzResearch.WordTrace tailWord_1200421 prefixEnd_1200421 616392960750953081016871 := by
  unfold tailWord_1200421
  simp only [CollatzResearch.WordTrace]
  refine ⟨43782950784087207429785117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29188633856058138286523411 43782950784087207429785117)
  ·
    refine ⟨16418606544032702786169419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43782950784087207429785117 16418606544032702786169419)
    ·
      refine ⟨24627909816049054179254129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16418606544032702786169419 24627909816049054179254129)
      ·
        refine ⟨18470932362036790634440597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24627909816049054179254129 18470932362036790634440597)
        ·
          refine ⟨865824954470474560989403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18470932362036790634440597 865824954470474560989403)
          ·
            refine ⟨1298737431705711841484105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865824954470474560989403 1298737431705711841484105)
            ·
              refine ⟨974053073779283881113079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298737431705711841484105 974053073779283881113079)
              ·
                refine ⟨1461079610668925821669619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 974053073779283881113079 1461079610668925821669619)
                ·
                  refine ⟨2191619416003388732504429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461079610668925821669619 2191619416003388732504429)
                  ·
                    refine ⟨821857281001270774689161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191619416003388732504429 821857281001270774689161)
                    ·
                      refine ⟨616392960750953081016871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821857281001270774689161 616392960750953081016871)
                      ·
                        rfl

theorem cell23_1200421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_1200421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200421 prefixEnd_1200421 := by exact prefixLift 1200421
  have htrace : WordTrace (prefixWord ++ tailWord_1200421) baseStart_1200421 baseEnd_1200421 := by
    simpa [prefixWord, tailWord_1200421, baseEnd_1200421] using wordTrace_append hprefix tailTrace_1200421
  have hstable : (prefixWord ++ tailWord_1200421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200421).length < 2 ^ (prefixWord ++ tailWord_1200421).sum := by decide
  have hdescent : baseEnd_1200421 < baseStart_1200421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200473 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_1200473 : Nat := 118140960795 + 1200473 * 2 ^ 59
def prefixEnd_1200473 : Nat := 4983230072969 + 3 ^ 40 * 1200473 * 2
def baseEnd_1200473 : Nat := 616419661744986877566631

theorem tailTrace_1200473 : CollatzResearch.WordTrace tailWord_1200473 prefixEnd_1200473 616419661744986877566631 := by
  unfold tailWord_1200473
  simp only [CollatzResearch.WordTrace]
  refine ⟨43784847379898820310678073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29189898253265880207118715 43784847379898820310678073)
  ·
    refine ⟨32838635534924115233008555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43784847379898820310678073 32838635534924115233008555)
    ·
      refine ⟨49257953302386172849512833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32838635534924115233008555 49257953302386172849512833)
      ·
        refine ⟨36943464976789629637134625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49257953302386172849512833 36943464976789629637134625)
        ·
          refine ⟨27707598732592222227850969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36943464976789629637134625 27707598732592222227850969)
          ·
            refine ⟨20780699049444166670888227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27707598732592222227850969 20780699049444166670888227)
            ·
              refine ⟨31171048574166250006332341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20780699049444166670888227 31171048574166250006332341)
              ·
                refine ⟨2922285803828085938093657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31171048574166250006332341 2922285803828085938093657)
                ·
                  refine ⟨2191714352871064453570243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2922285803828085938093657 2191714352871064453570243)
                  ·
                    refine ⟨3287571529306596680355365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2191714352871064453570243 3287571529306596680355365)
                    ·
                      refine ⟨616419661744986877566631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3287571529306596680355365 616419661744986877566631)
                      ·
                        rfl

theorem cell23_1200473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_1200473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200473 prefixEnd_1200473 := by exact prefixLift 1200473
  have htrace : WordTrace (prefixWord ++ tailWord_1200473) baseStart_1200473 baseEnd_1200473 := by
    simpa [prefixWord, tailWord_1200473, baseEnd_1200473] using wordTrace_append hprefix tailTrace_1200473
  have hstable : (prefixWord ++ tailWord_1200473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200473).length < 2 ^ (prefixWord ++ tailWord_1200473).sum := by decide
  have hdescent : baseEnd_1200473 < baseStart_1200473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200490 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1200490 : Nat := 118140960795 + 1200490 * 2 ^ 59
def prefixEnd_1200490 : Nat := 4983230072969 + 3 ^ 40 * 1200490 * 2
def baseEnd_1200490 : Nat := 616428390916113311054053

theorem tailTrace_1200490 : CollatzResearch.WordTrace tailWord_1200490 prefixEnd_1200490 616428390916113311054053 := by
  unfold tailWord_1200490
  simp only [CollatzResearch.WordTrace]
  refine ⟨10946366855209308053511731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29190311613891488142697949 10946366855209308053511731)
  ·
    refine ⟨16419550282813962080267597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10946366855209308053511731 16419550282813962080267597)
    ·
      refine ⟨6157331356055235780100349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16419550282813962080267597 6157331356055235780100349)
      ·
        refine ⟨2308999258520713417537631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6157331356055235780100349 2308999258520713417537631)
        ·
          refine ⟨3463498887781070126306447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308999258520713417537631 3463498887781070126306447)
          ·
            refine ⟨5195248331671605189459671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3463498887781070126306447 5195248331671605189459671)
            ·
              refine ⟨7792872497507407784189507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5195248331671605189459671 7792872497507407784189507)
              ·
                refine ⟨11689308746261111676284261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7792872497507407784189507 11689308746261111676284261)
                ·
                  refine ⟨2191745389923958439303299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11689308746261111676284261 2191745389923958439303299)
                  ·
                    refine ⟨3287618084885937658954949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2191745389923958439303299 3287618084885937658954949)
                    ·
                      refine ⟨616428390916113311054053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3287618084885937658954949 616428390916113311054053)
                      ·
                        rfl

theorem cell23_1200490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1200490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200490 prefixEnd_1200490 := by exact prefixLift 1200490
  have htrace : WordTrace (prefixWord ++ tailWord_1200490) baseStart_1200490 baseEnd_1200490 := by
    simpa [prefixWord, tailWord_1200490, baseEnd_1200490] using wordTrace_append hprefix tailTrace_1200490
  have hstable : (prefixWord ++ tailWord_1200490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200490).length < 2 ^ (prefixWord ++ tailWord_1200490).sum := by decide
  have hdescent : baseEnd_1200490 < baseStart_1200490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200551 : List Nat := [1, 1, 6, 1, 1, 4, 2, 2, 1, 4]
def baseStart_1200551 : Nat := 118140960795 + 1200551 * 2 ^ 59
def prefixEnd_1200551 : Nat := 4983230072969 + 3 ^ 40 * 1200551 * 2
def baseEnd_1200551 : Nat := 205486571078679190797091

theorem tailTrace_1200551 : CollatzResearch.WordTrace tailWord_1200551 prefixEnd_1200551 205486571078679190797091 := by
  unfold tailWord_1200551
  simp only [CollatzResearch.WordTrace]
  refine ⟨43787692273616239632017507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29191794849077493088011671 43787692273616239632017507)
  ·
    refine ⟨65681538410424359448026261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43787692273616239632017507 65681538410424359448026261)
    ·
      refine ⟨3078822112988641849126231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65681538410424359448026261 3078822112988641849126231)
      ·
        refine ⟨4618233169482962773689347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3078822112988641849126231 4618233169482962773689347)
        ·
          refine ⟨6927349754224444160534021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618233169482962773689347 6927349754224444160534021)
          ·
            refine ⟨1298878078917083280100129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6927349754224444160534021 1298878078917083280100129)
            ·
              refine ⟨974158559187812460075097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298878078917083280100129 974158559187812460075097)
              ·
                refine ⟨730618919390859345056323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974158559187812460075097 730618919390859345056323)
                ·
                  refine ⟨1095928379086289017584485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730618919390859345056323 1095928379086289017584485)
                  ·
                    refine ⟨205486571078679190797091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1095928379086289017584485 205486571078679190797091)
                    ·
                      rfl

theorem cell23_1200551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_1200551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200551 prefixEnd_1200551 := by exact prefixLift 1200551
  have htrace : WordTrace (prefixWord ++ tailWord_1200551) baseStart_1200551 baseEnd_1200551 := by
    simpa [prefixWord, tailWord_1200551, baseEnd_1200551] using wordTrace_append hprefix tailTrace_1200551
  have hstable : (prefixWord ++ tailWord_1200551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200551).length < 2 ^ (prefixWord ++ tailWord_1200551).sum := by decide
  have hdescent : baseEnd_1200551 < baseStart_1200551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200584 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_1200584 : Nat := 118140960795 + 1200584 * 2 ^ 59
def prefixEnd_1200584 : Nat := 4983230072969 + 3 ^ 40 * 1200584 * 2
def baseEnd_1200584 : Nat := 616476658097635943278621

theorem tailTrace_1200584 : CollatzResearch.WordTrace tailWord_1200584 prefixEnd_1200584 616476658097635943278621 := by
  unfold tailWord_1200584
  simp only [CollatzResearch.WordTrace]
  refine ⟨21894447941248343133984403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29192597254997790845312537 21894447941248343133984403)
  ·
    refine ⟨32841671911872514700976605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21894447941248343133984403 32841671911872514700976605)
    ·
      refine ⟨12315626966952193012866227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32841671911872514700976605 12315626966952193012866227)
      ·
        refine ⟨18473440450428289519299341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12315626966952193012866227 18473440450428289519299341)
        ·
          refine ⟨6927540168910608569737253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18473440450428289519299341 6927540168910608569737253)
          ·
            refine ⟨1298913781670739106825735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6927540168910608569737253 1298913781670739106825735)
            ·
              refine ⟨1948370672506108660238603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298913781670739106825735 1948370672506108660238603)
              ·
                refine ⟨2922556008759162990357905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948370672506108660238603 2922556008759162990357905)
                ·
                  refine ⟨2191917006569372242768429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2922556008759162990357905 2191917006569372242768429)
                  ·
                    refine ⟨821968877463514591038161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2191917006569372242768429 821968877463514591038161)
                    ·
                      refine ⟨616476658097635943278621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 821968877463514591038161 616476658097635943278621)
                      ·
                        rfl

theorem cell23_1200584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_1200584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200584 prefixEnd_1200584 := by exact prefixLift 1200584
  have htrace : WordTrace (prefixWord ++ tailWord_1200584) baseStart_1200584 baseEnd_1200584 := by
    simpa [prefixWord, tailWord_1200584, baseEnd_1200584] using wordTrace_append hprefix tailTrace_1200584
  have hstable : (prefixWord ++ tailWord_1200584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200584).length < 2 ^ (prefixWord ++ tailWord_1200584).sum := by decide
  have hdescent : baseEnd_1200584 < baseStart_1200584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200590 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_1200590 : Nat := 118140960795 + 1200590 * 2 ^ 59
def prefixEnd_1200590 : Nat := 4983230072969 + 3 ^ 40 * 1200590 * 2
def baseEnd_1200590 : Nat := 205493246327187639934531

theorem tailTrace_1200590 : CollatzResearch.WordTrace tailWord_1200590 prefixEnd_1200590 205493246327187639934531 := by
  unfold tailWord_1200590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473639340059368661585903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29192743146983299528458149 5473639340059368661585903)
  ·
    refine ⟨8210459010089052992378855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5473639340059368661585903 8210459010089052992378855)
    ·
      refine ⟨12315688515133579488568283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8210459010089052992378855 12315688515133579488568283)
      ·
        refine ⟨18473532772700369232852425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12315688515133579488568283 18473532772700369232852425)
        ·
          refine ⟨13855149579525276924639319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18473532772700369232852425 13855149579525276924639319)
          ·
            refine ⟨20782724369287915386958979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13855149579525276924639319 20782724369287915386958979)
            ·
              refine ⟨31174086553931873080438469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20782724369287915386958979 31174086553931873080438469)
              ·
                refine ⟨5845141228862226202582213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31174086553931873080438469 5845141228862226202582213)
                ·
                  refine ⟨1095963980411667412984165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5845141228862226202582213 1095963980411667412984165)
                  ·
                    refine ⟨205493246327187639934531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1095963980411667412984165 205493246327187639934531)
                    ·
                      rfl

theorem cell23_1200590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_1200590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200590 prefixEnd_1200590 := by exact prefixLift 1200590
  have htrace : WordTrace (prefixWord ++ tailWord_1200590) baseStart_1200590 baseEnd_1200590 := by
    simpa [prefixWord, tailWord_1200590, baseEnd_1200590] using wordTrace_append hprefix tailTrace_1200590
  have hstable : (prefixWord ++ tailWord_1200590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200590).length < 2 ^ (prefixWord ++ tailWord_1200590).sum := by decide
  have hdescent : baseEnd_1200590 < baseStart_1200590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200594 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_1200594 : Nat := 118140960795 + 1200594 * 2 ^ 59
def prefixEnd_1200594 : Nat := 4983230072969 + 3 ^ 40 * 1200594 * 2
def baseEnd_1200594 : Nat := 205493930968060301384525

theorem tailTrace_1200594 : CollatzResearch.WordTrace tailWord_1200594 prefixEnd_1200594 205493930968060301384525 := by
  unfold tailWord_1200594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10947315153115114493958209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29192840408306971983888557 10947315153115114493958209)
  ·
    refine ⟨8210486364836335870468657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10947315153115114493958209 8210486364836335870468657)
    ·
      refine ⟨6157864773627251902851493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8210486364836335870468657 6157864773627251902851493)
      ·
        refine ⟨1154599645055109731784655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6157864773627251902851493 1154599645055109731784655)
        ·
          refine ⟨1731899467582664597676983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154599645055109731784655 1731899467582664597676983)
          ·
            refine ⟨2597849201373996896515475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731899467582664597676983 2597849201373996896515475)
            ·
              refine ⟨3896773802060995344773213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597849201373996896515475 3896773802060995344773213)
              ·
                refine ⟨1461290175772873254289955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3896773802060995344773213 1461290175772873254289955)
                ·
                  refine ⟨2191935263659309881434933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461290175772873254289955 2191935263659309881434933)
                  ·
                    refine ⟨205493930968060301384525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2191935263659309881434933 205493930968060301384525)
                    ·
                      rfl

theorem cell23_1200594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_1200594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200594 prefixEnd_1200594 := by exact prefixLift 1200594
  have htrace : WordTrace (prefixWord ++ tailWord_1200594) baseStart_1200594 baseEnd_1200594 := by
    simpa [prefixWord, tailWord_1200594, baseEnd_1200594] using wordTrace_append hprefix tailTrace_1200594
  have hstable : (prefixWord ++ tailWord_1200594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200594).length < 2 ^ (prefixWord ++ tailWord_1200594).sum := by decide
  have hdescent : baseEnd_1200594 < baseStart_1200594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200597 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1200597 : Nat := 118140960795 + 1200597 * 2 ^ 59
def prefixEnd_1200597 : Nat := 4983230072969 + 3 ^ 40 * 1200597 * 2
def baseEnd_1200597 : Nat := 616483333346144392416061

theorem tailTrace_1200597 : CollatzResearch.WordTrace tailWord_1200597 prefixEnd_1200597 616483333346144392416061 := by
  unfold tailWord_1200597
  simp only [CollatzResearch.WordTrace]
  refine ⟨43789370031449589488192045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29192913354299726325461363 43789370031449589488192045)
  ·
    refine ⟨16421013761793596058072017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43789370031449589488192045 16421013761793596058072017)
    ·
      refine ⟨12315760321345197043554013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16421013761793596058072017 12315760321345197043554013)
      ·
        refine ⟨4618410120504448891332755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12315760321345197043554013 4618410120504448891332755)
        ·
          refine ⟨6927615180756673336999133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618410120504448891332755 6927615180756673336999133)
          ·
            refine ⟨2597855692783752501374675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6927615180756673336999133 2597855692783752501374675)
            ·
              refine ⟨3896783539175628752062013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597855692783752501374675 3896783539175628752062013)
              ·
                refine ⟨1461293827190860782023255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3896783539175628752062013 1461293827190860782023255)
                ·
                  refine ⟨2191940740786291173034883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461293827190860782023255 2191940740786291173034883)
                  ·
                    refine ⟨3287911111179436759552325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2191940740786291173034883 3287911111179436759552325)
                    ·
                      refine ⟨616483333346144392416061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3287911111179436759552325 616483333346144392416061)
                      ·
                        rfl

theorem cell23_1200597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1200597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200597 prefixEnd_1200597 := by exact prefixLift 1200597
  have htrace : WordTrace (prefixWord ++ tailWord_1200597) baseStart_1200597 baseEnd_1200597 := by
    simpa [prefixWord, tailWord_1200597, baseEnd_1200597] using wordTrace_append hprefix tailTrace_1200597
  have hstable : (prefixWord ++ tailWord_1200597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200597).length < 2 ^ (prefixWord ++ tailWord_1200597).sum := by decide
  have hdescent : baseEnd_1200597 < baseStart_1200597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200607 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 2, 4]
def baseStart_1200607 : Nat := 118140960795 + 1200607 * 2 ^ 59
def prefixEnd_1200607 : Nat := 4983230072969 + 3 ^ 40 * 1200607 * 2
def baseEnd_1200607 : Nat := 205496156050896451097005

theorem tailTrace_1200607 : CollatzResearch.WordTrace tailWord_1200607 prefixEnd_1200607 205496156050896451097005 := by
  unfold tailWord_1200607
  simp only [CollatzResearch.WordTrace]
  refine ⟨43789734761413361196056075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29193156507608907464037383 43789734761413361196056075)
  ·
    refine ⟨65684602142120041794084113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43789734761413361196056075 65684602142120041794084113)
    ·
      refine ⟨49263451606590031345563085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65684602142120041794084113 49263451606590031345563085)
      ·
        refine ⟨18473794352471261754586157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49263451606590031345563085 18473794352471261754586157)
        ·
          refine ⟨6927672882176723157969809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18473794352471261754586157 6927672882176723157969809)
          ·
            refine ⟨5195754661632542368477357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6927672882176723157969809 5195754661632542368477357)
            ·
              refine ⟨1948407998112203388179009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5195754661632542368477357 1948407998112203388179009)
              ·
                refine ⟨1461305998584152541134257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948407998112203388179009 1461305998584152541134257)
                ·
                  refine ⟨1095979498938114405850693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1461305998584152541134257 1095979498938114405850693)
                  ·
                    refine ⟨205496156050896451097005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1095979498938114405850693 205496156050896451097005)
                    ·
                      rfl

theorem cell23_1200607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 4].length) (baseStart_1200607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200607 prefixEnd_1200607 := by exact prefixLift 1200607
  have htrace : WordTrace (prefixWord ++ tailWord_1200607) baseStart_1200607 baseEnd_1200607 := by
    simpa [prefixWord, tailWord_1200607, baseEnd_1200607] using wordTrace_append hprefix tailTrace_1200607
  have hstable : (prefixWord ++ tailWord_1200607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200607).length < 2 ^ (prefixWord ++ tailWord_1200607).sum := by decide
  have hdescent : baseEnd_1200607 < baseStart_1200607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200633 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 2, 7]
def baseStart_1200633 : Nat := 118140960795 + 1200633 * 2 ^ 59
def prefixEnd_1200633 : Nat := 4983230072969 + 3 ^ 40 * 1200633 * 2
def baseEnd_1200633 : Nat := 205500606216568750521965

theorem tailTrace_1200633 : CollatzResearch.WordTrace tailWord_1200633 prefixEnd_1200633 205500606216568750521965 := by
  unfold tailWord_1200633
  simp only [CollatzResearch.WordTrace]
  refine ⟨43790683059319167636502553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29193788706212778424335035 43790683059319167636502553)
  ·
    refine ⟨32843012294489375727376915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43790683059319167636502553 32843012294489375727376915)
    ·
      refine ⟨49264518441734063591065373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32843012294489375727376915 49264518441734063591065373)
      ·
        refine ⟨18474194415650273846649515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49264518441734063591065373 18474194415650273846649515)
        ·
          refine ⟨27711291623475410769974273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18474194415650273846649515 27711291623475410769974273)
          ·
            refine ⟨20783468717606558077480705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27711291623475410769974273 20783468717606558077480705)
            ·
              refine ⟨15587601538204918558110529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20783468717606558077480705 15587601538204918558110529)
              ·
                refine ⟨11690701153653688918582897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15587601538204918558110529 11690701153653688918582897)
                ·
                  refine ⟨8768025865240266688937173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11690701153653688918582897 8768025865240266688937173)
                  ·
                    refine ⟨205500606216568750521965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8768025865240266688937173 205500606216568750521965)
                    ·
                      rfl

theorem cell23_1200633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_1200633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200633 prefixEnd_1200633 := by exact prefixLift 1200633
  have htrace : WordTrace (prefixWord ++ tailWord_1200633) baseStart_1200633 baseEnd_1200633 := by
    simpa [prefixWord, tailWord_1200633, baseEnd_1200633] using wordTrace_append hprefix tailTrace_1200633
  have hstable : (prefixWord ++ tailWord_1200633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200633).length < 2 ^ (prefixWord ++ tailWord_1200633).sum := by decide
  have hdescent : baseEnd_1200633 < baseStart_1200633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200640 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 4, 7, 2]
def baseStart_1200640 : Nat := 118140960795 + 1200640 * 2 ^ 59
def prefixEnd_1200640 : Nat := 4983230072969 + 3 ^ 40 * 1200640 * 2
def baseEnd_1200640 : Nat := 616505413014287724178363

theorem tailTrace_1200640 : CollatzResearch.WordTrace tailWord_1200640 prefixEnd_1200640 616505413014287724178363 := by
  unfold tailWord_1200640
  simp only [CollatzResearch.WordTrace]
  refine ⟨21895469185146903916003687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29193958913529205221338249 21895469185146903916003687)
  ·
    refine ⟨32843203777720355874005531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21895469185146903916003687 32843203777720355874005531)
    ·
      refine ⟨49264805666580533811008297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32843203777720355874005531 49264805666580533811008297)
      ·
        refine ⟨36948604249935400358256223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49264805666580533811008297 36948604249935400358256223)
        ·
          refine ⟨55422906374903100537384335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36948604249935400358256223 55422906374903100537384335)
          ·
            refine ⟨83134359562354650806076503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55422906374903100537384335 83134359562354650806076503)
            ·
              refine ⟨124701539343531976209114755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83134359562354650806076503 124701539343531976209114755)
              ·
                refine ⟨187052309015297964313672133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124701539343531976209114755 187052309015297964313672133)
                ·
                  refine ⟨35072307940368368308813525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187052309015297964313672133 35072307940368368308813525)
                  ·
                    refine ⟨822007217352383632237817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35072307940368368308813525 822007217352383632237817)
                    ·
                      refine ⟨616505413014287724178363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822007217352383632237817 616505413014287724178363)
                      ·
                        rfl

theorem cell23_1200640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_1200640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200640 prefixEnd_1200640 := by exact prefixLift 1200640
  have htrace : WordTrace (prefixWord ++ tailWord_1200640) baseStart_1200640 baseEnd_1200640 := by
    simpa [prefixWord, tailWord_1200640, baseEnd_1200640] using wordTrace_append hprefix tailTrace_1200640
  have hstable : (prefixWord ++ tailWord_1200640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200640).length < 2 ^ (prefixWord ++ tailWord_1200640).sum := by decide
  have hdescent : baseEnd_1200640 < baseStart_1200640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200643 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 5]
def baseStart_1200643 : Nat := 118140960795 + 1200643 * 2 ^ 59
def prefixEnd_1200643 : Nat := 4983230072969 + 3 ^ 40 * 1200643 * 2
def baseEnd_1200643 : Nat := 616506953456251212440849

theorem tailTrace_1200643 : CollatzResearch.WordTrace tailWord_1200643 prefixEnd_1200643 616506953456251212440849 := by
  unfold tailWord_1200643
  simp only [CollatzResearch.WordTrace]
  refine ⟨43791047789282939344366583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29194031859521959562911055 43791047789282939344366583)
  ·
    refine ⟨65686571683924409016549875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43791047789282939344366583 65686571683924409016549875)
    ·
      refine ⟨98529857525886613524824813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65686571683924409016549875 98529857525886613524824813)
      ·
        refine ⟨36948696572207480071809305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98529857525886613524824813 36948696572207480071809305)
        ·
          refine ⟨27711522429155610053856979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36948696572207480071809305 27711522429155610053856979)
          ·
            refine ⟨41567283643733415080785469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27711522429155610053856979 41567283643733415080785469)
            ·
              refine ⟨15587731366400030655294551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41567283643733415080785469 15587731366400030655294551)
              ·
                refine ⟨23381597049600045982941827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15587731366400030655294551 23381597049600045982941827)
                ·
                  refine ⟨35072395574400068974412741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23381597049600045982941827 35072395574400068974412741)
                  ·
                    refine ⟨6576074170200012932702389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35072395574400068974412741 6576074170200012932702389)
                    ·
                      refine ⟨616506953456251212440849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6576074170200012932702389 616506953456251212440849)
                      ·
                        rfl

theorem cell23_1200643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_1200643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200643 prefixEnd_1200643 := by exact prefixLift 1200643
  have htrace : WordTrace (prefixWord ++ tailWord_1200643) baseStart_1200643 baseEnd_1200643 := by
    simpa [prefixWord, tailWord_1200643, baseEnd_1200643] using wordTrace_append hprefix tailTrace_1200643
  have hstable : (prefixWord ++ tailWord_1200643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200643).length < 2 ^ (prefixWord ++ tailWord_1200643).sum := by decide
  have hdescent : baseEnd_1200643 < baseStart_1200643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200683 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 6]
def baseStart_1200683 : Nat := 118140960795 + 1200683 * 2 ^ 59
def prefixEnd_1200683 : Nat := 4983230072969 + 3 ^ 40 * 1200683 * 2
def baseEnd_1200683 : Nat := 616527492682431055940665

theorem tailTrace_1200683 : CollatzResearch.WordTrace tailWord_1200683 prefixEnd_1200683 616527492682431055940665 := by
  unfold tailWord_1200683
  simp only [CollatzResearch.WordTrace]
  refine ⟨43792506709138026175822703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29195004472758684117215135 43792506709138026175822703)
  ·
    refine ⟨65688760063707039263734055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43792506709138026175822703 65688760063707039263734055)
    ·
      refine ⟨98533140095560558895601083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65688760063707039263734055 98533140095560558895601083)
      ·
        refine ⟨147799710143340838343401625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98533140095560558895601083 147799710143340838343401625)
        ·
          refine ⟨110849782607505628757551219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147799710143340838343401625 110849782607505628757551219)
          ·
            refine ⟨166274673911258443136326829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110849782607505628757551219 166274673911258443136326829)
            ·
              refine ⟨62353002716721916176122561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166274673911258443136326829 62353002716721916176122561)
              ·
                refine ⟨46764752037541437132091921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62353002716721916176122561 46764752037541437132091921)
                ·
                  refine ⟨35073564028156077849068941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46764752037541437132091921 35073564028156077849068941)
                  ·
                    refine ⟨13152586510558529193400853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35073564028156077849068941 13152586510558529193400853)
                    ·
                      refine ⟨616527492682431055940665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13152586510558529193400853 616527492682431055940665)
                      ·
                        rfl

theorem cell23_1200683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_1200683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200683 prefixEnd_1200683 := by exact prefixLift 1200683
  have htrace : WordTrace (prefixWord ++ tailWord_1200683) baseStart_1200683 baseEnd_1200683 := by
    simpa [prefixWord, tailWord_1200683, baseEnd_1200683] using wordTrace_append hprefix tailTrace_1200683
  have hstable : (prefixWord ++ tailWord_1200683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200683).length < 2 ^ (prefixWord ++ tailWord_1200683).sum := by decide
  have hdescent : baseEnd_1200683 < baseStart_1200683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200685 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1200685 : Nat := 118140960795 + 1200685 * 2 ^ 59
def prefixEnd_1200685 : Nat := 4983230072969 + 3 ^ 40 * 1200685 * 2
def baseEnd_1200685 : Nat := 616528519643740048115657

theorem tailTrace_1200685 : CollatzResearch.WordTrace tailWord_1200685 prefixEnd_1200685 616528519643740048115657 := by
  unfold tailWord_1200685
  simp only [CollatzResearch.WordTrace]
  refine ⟨43792579655130780517395509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29195053103420520344930339 43792579655130780517395509)
  ·
    refine ⟨4105554342668510673505829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43792579655130780517395509 4105554342668510673505829)
    ·
      refine ⟨769791439250345751282343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4105554342668510673505829 769791439250345751282343)
      ·
        refine ⟨1154687158875518626923515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769791439250345751282343 1154687158875518626923515)
        ·
          refine ⟨1732030738313277940385273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154687158875518626923515 1732030738313277940385273)
          ·
            refine ⟨1299023053734958455288955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1732030738313277940385273 1299023053734958455288955)
            ·
              refine ⟨1948534580602437682933433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299023053734958455288955 1948534580602437682933433)
              ·
                refine ⟨1461400935451828262200075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948534580602437682933433 1461400935451828262200075)
                ·
                  refine ⟨2192101403177742393300113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461400935451828262200075 2192101403177742393300113)
                  ·
                    refine ⟨1644076052383306794975085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2192101403177742393300113 1644076052383306794975085)
                    ·
                      refine ⟨616528519643740048115657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1644076052383306794975085 616528519643740048115657)
                      ·
                        rfl

theorem cell23_1200685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1200685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200685 prefixEnd_1200685 := by exact prefixLift 1200685
  have htrace : WordTrace (prefixWord ++ tailWord_1200685) baseStart_1200685 baseEnd_1200685 := by
    simpa [prefixWord, tailWord_1200685, baseEnd_1200685] using wordTrace_append hprefix tailTrace_1200685
  have hstable : (prefixWord ++ tailWord_1200685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200685).length < 2 ^ (prefixWord ++ tailWord_1200685).sum := by decide
  have hdescent : baseEnd_1200685 < baseStart_1200685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200690 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1200690 : Nat := 118140960795 + 1200690 * 2 ^ 59
def prefixEnd_1200690 : Nat := 4983230072969 + 3 ^ 40 * 1200690 * 2
def baseEnd_1200690 : Nat := 616531087047012528553133

theorem tailTrace_1200690 : CollatzResearch.WordTrace tailWord_1200690 prefixEnd_1200690 616531087047012528553133 := by
  unfold tailWord_1200690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10948190505028166592831881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29195174680075110914218349 10948190505028166592831881)
  ·
    refine ⟨8211142878771124944623911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10948190505028166592831881 8211142878771124944623911)
    ·
      refine ⟨12316714318156687416935867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8211142878771124944623911 12316714318156687416935867)
      ·
        refine ⟨18475071477235031125403801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12316714318156687416935867 18475071477235031125403801)
        ·
          refine ⟨13856303607926273344052851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18475071477235031125403801 13856303607926273344052851)
          ·
            refine ⟨20784455411889410016079277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13856303607926273344052851 20784455411889410016079277)
            ·
              refine ⟨7794170779458528756029729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20784455411889410016079277 7794170779458528756029729)
              ·
                refine ⟨5845628084593896567022297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7794170779458528756029729 5845628084593896567022297)
                ·
                  refine ⟨4384221063445422425266723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5845628084593896567022297 4384221063445422425266723)
                  ·
                    refine ⟨6576331595168133637900085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4384221063445422425266723 6576331595168133637900085)
                    ·
                      refine ⟨616531087047012528553133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6576331595168133637900085 616531087047012528553133)
                      ·
                        rfl

theorem cell23_1200690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1200690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200690 prefixEnd_1200690 := by exact prefixLift 1200690
  have htrace : WordTrace (prefixWord ++ tailWord_1200690) baseStart_1200690 baseEnd_1200690 := by
    simpa [prefixWord, tailWord_1200690, baseEnd_1200690] using wordTrace_append hprefix tailTrace_1200690
  have hstable : (prefixWord ++ tailWord_1200690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200690).length < 2 ^ (prefixWord ++ tailWord_1200690).sum := by decide
  have hdescent : baseEnd_1200690 < baseStart_1200690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200721 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 2, 2, 2]
def baseStart_1200721 : Nat := 118140960795 + 1200721 * 2 ^ 59
def prefixEnd_1200721 : Nat := 4983230072969 + 3 ^ 40 * 1200721 * 2
def baseEnd_1200721 : Nat := 616547004947301907265491

theorem tailTrace_1200721 : CollatzResearch.WordTrace tailWord_1200721 prefixEnd_1200721 616547004947301907265491 := by
  unfold tailWord_1200721
  simp only [CollatzResearch.WordTrace]
  refine ⟨43793892683000358665706017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29195928455333572443804011 43793892683000358665706017)
  ·
    refine ⟨32845419512250268999279513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43793892683000358665706017 32845419512250268999279513)
    ·
      refine ⟨24634064634187701749459635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32845419512250268999279513 24634064634187701749459635)
      ·
        refine ⟨36951096951281552624189453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24634064634187701749459635 36951096951281552624189453)
        ·
          refine ⟨13856661356730582234071045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36951096951281552624189453 13856661356730582234071045)
          ·
            refine ⟨2598124004386984168888321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13856661356730582234071045 2598124004386984168888321)
            ·
              refine ⟨1948593003290238126666241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2598124004386984168888321 1948593003290238126666241)
              ·
                refine ⟨1461444752467678594999681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948593003290238126666241 1461444752467678594999681)
                ·
                  refine ⟨1096083564350758946249761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1461444752467678594999681 1096083564350758946249761)
                  ·
                    refine ⟨822062673263069209687321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1096083564350758946249761 822062673263069209687321)
                    ·
                      refine ⟨616547004947301907265491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822062673263069209687321 616547004947301907265491)
                      ·
                        rfl

theorem cell23_1200721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_1200721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200721 prefixEnd_1200721 := by exact prefixLift 1200721
  have htrace : WordTrace (prefixWord ++ tailWord_1200721) baseStart_1200721 baseEnd_1200721 := by
    simpa [prefixWord, tailWord_1200721, baseEnd_1200721] using wordTrace_append hprefix tailTrace_1200721
  have hstable : (prefixWord ++ tailWord_1200721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200721).length < 2 ^ (prefixWord ++ tailWord_1200721).sum := by decide
  have hdescent : baseEnd_1200721 < baseStart_1200721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200727 : List Nat := [1, 1, 3, 2, 2, 2, 3, 4, 5]
def baseStart_1200727 : Nat := 118140960795 + 1200727 * 2 ^ 59
def prefixEnd_1200727 : Nat := 4983230072969 + 3 ^ 40 * 1200727 * 2
def baseEnd_1200727 : Nat := 68505565092358764865607

theorem tailTrace_1200727 : CollatzResearch.WordTrace tailWord_1200727 prefixEnd_1200727 68505565092358764865607 := by
  unfold tailWord_1200727
  simp only [CollatzResearch.WordTrace]
  refine ⟨43794111520978621690424435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29196074347319081126949623 43794111520978621690424435)
  ·
    refine ⟨65691167281467932535636653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43794111520978621690424435 65691167281467932535636653)
    ·
      refine ⟨24634187730550474700863745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65691167281467932535636653 24634187730550474700863745)
      ·
        refine ⟨18475640797912856025647809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24634187730550474700863745 18475640797912856025647809)
        ·
          refine ⟨13856730598434642019235857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18475640797912856025647809 13856730598434642019235857)
          ·
            refine ⟨10392547948825981514426893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13856730598434642019235857 10392547948825981514426893)
            ·
              refine ⟨3897205480809743067910085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10392547948825981514426893 3897205480809743067910085)
              ·
                refine ⟨730726027651826825233141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3897205480809743067910085 730726027651826825233141)
                ·
                  refine ⟨68505565092358764865607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 730726027651826825233141 68505565092358764865607)
                  ·
                    rfl

theorem cell23_1200727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 5].length) (baseStart_1200727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200727 prefixEnd_1200727 := by exact prefixLift 1200727
  have htrace : WordTrace (prefixWord ++ tailWord_1200727) baseStart_1200727 baseEnd_1200727 := by
    simpa [prefixWord, tailWord_1200727, baseEnd_1200727] using wordTrace_append hprefix tailTrace_1200727
  have hstable : (prefixWord ++ tailWord_1200727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200727).length < 2 ^ (prefixWord ++ tailWord_1200727).sum := by decide
  have hdescent : baseEnd_1200727 < baseStart_1200727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200737 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_1200737 : Nat := 118140960795 + 1200737 * 2 ^ 59
def prefixEnd_1200737 : Nat := 4983230072969 + 3 ^ 40 * 1200737 * 2
def baseEnd_1200737 : Nat := 616555220637773844665417

theorem tailTrace_1200737 : CollatzResearch.WordTrace tailWord_1200737 prefixEnd_1200737 616555220637773844665417 := by
  unfold tailWord_1200737
  simp only [CollatzResearch.WordTrace]
  refine ⟨43794476250942393398288465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29196317500628262265525643 43794476250942393398288465)
  ·
    refine ⟨32845857188206795048716349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43794476250942393398288465 32845857188206795048716349)
    ·
      refine ⟨12317196445577548143268631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32845857188206795048716349 12317196445577548143268631)
      ·
        refine ⟨18475794668366322214902947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12317196445577548143268631 18475794668366322214902947)
        ·
          refine ⟨27713692002549483322354421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18475794668366322214902947 27713692002549483322354421)
          ·
            refine ⟨2598158625239014061470727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27713692002549483322354421 2598158625239014061470727)
            ·
              refine ⟨3897237937858521092206091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598158625239014061470727 3897237937858521092206091)
              ·
                refine ⟨5845856906787781638309137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897237937858521092206091 5845856906787781638309137)
                ·
                  refine ⟨4384392680090836228731853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5845856906787781638309137 4384392680090836228731853)
                  ·
                    refine ⟨1644147255034063585774445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4384392680090836228731853 1644147255034063585774445)
                    ·
                      refine ⟨616555220637773844665417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1644147255034063585774445 616555220637773844665417)
                      ·
                        rfl

theorem cell23_1200737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_1200737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200737 prefixEnd_1200737 := by exact prefixLift 1200737
  have htrace : WordTrace (prefixWord ++ tailWord_1200737) baseStart_1200737 baseEnd_1200737 := by
    simpa [prefixWord, tailWord_1200737, baseEnd_1200737] using wordTrace_append hprefix tailTrace_1200737
  have hstable : (prefixWord ++ tailWord_1200737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200737).length < 2 ^ (prefixWord ++ tailWord_1200737).sum := by decide
  have hdescent : baseEnd_1200737 < baseStart_1200737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200738 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1200738 : Nat := 118140960795 + 1200738 * 2 ^ 59
def prefixEnd_1200738 : Nat := 4983230072969 + 3 ^ 40 * 1200738 * 2
def baseEnd_1200738 : Nat := 616555734118428340752913

theorem tailTrace_1200738 : CollatzResearch.WordTrace tailWord_1200738 prefixEnd_1200738 616555734118428340752913 := by
  unfold tailWord_1200738
  simp only [CollatzResearch.WordTrace]
  refine ⟨10948628180984692642268717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29196341815959180379383245 10948628180984692642268717)
  ·
    refine ⟨4105735567869259740850769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10948628180984692642268717 4105735567869259740850769)
    ·
      refine ⟨3079301675901944805638077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4105735567869259740850769 3079301675901944805638077)
      ·
        refine ⟨1154738128463229302114279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3079301675901944805638077 1154738128463229302114279)
        ·
          refine ⟨1732107192694843953171419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154738128463229302114279 1732107192694843953171419)
          ·
            refine ⟨2598160789042265929757129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732107192694843953171419 2598160789042265929757129)
            ·
              refine ⟨1948620591781699447317847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2598160789042265929757129 1948620591781699447317847)
              ·
                refine ⟨2922930887672549170976771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948620591781699447317847 2922930887672549170976771)
                ·
                  refine ⟨4384396331508823756465157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922930887672549170976771 4384396331508823756465157)
                  ·
                    refine ⟨822074312157904454337217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4384396331508823756465157 822074312157904454337217)
                    ·
                      refine ⟨616555734118428340752913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822074312157904454337217 616555734118428340752913)
                      ·
                        rfl

theorem cell23_1200738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1200738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200738 prefixEnd_1200738 := by exact prefixLift 1200738
  have htrace : WordTrace (prefixWord ++ tailWord_1200738) baseStart_1200738 baseEnd_1200738 := by
    simpa [prefixWord, tailWord_1200738, baseEnd_1200738] using wordTrace_append hprefix tailTrace_1200738
  have hstable : (prefixWord ++ tailWord_1200738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200738).length < 2 ^ (prefixWord ++ tailWord_1200738).sum := by decide
  have hdescent : baseEnd_1200738 < baseStart_1200738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200740 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_1200740 : Nat := 118140960795 + 1200740 * 2 ^ 59
def prefixEnd_1200740 : Nat := 4983230072969 + 3 ^ 40 * 1200740 * 2
def baseEnd_1200740 : Nat := 205518920359912444309301

theorem tailTrace_1200740 : CollatzResearch.WordTrace tailWord_1200740 prefixEnd_1200740 205518920359912444309301 := by
  unfold tailWord_1200740
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897292834965762455323837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29196390446621016607098449 21897292834965762455323837)
  ·
    refine ⟨8211484813112160920746439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21897292834965762455323837 8211484813112160920746439)
    ·
      refine ⟨12317227219668241381119659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8211484813112160920746439 12317227219668241381119659)
      ·
        refine ⟨18475840829502362071679489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12317227219668241381119659 18475840829502362071679489)
        ·
          refine ⟨13856880622126771553759617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18475840829502362071679489 13856880622126771553759617)
          ·
            refine ⟨10392660466595078665319713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13856880622126771553759617 10392660466595078665319713)
            ·
              refine ⟨7794495349946308998989785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10392660466595078665319713 7794495349946308998989785)
              ·
                refine ⟨5845871512459731749242339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7794495349946308998989785 5845871512459731749242339)
                ·
                  refine ⟨8768807268689597623863509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845871512459731749242339 8768807268689597623863509)
                  ·
                    refine ⟨205518920359912444309301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8768807268689597623863509 205518920359912444309301)
                    ·
                      rfl

theorem cell23_1200740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_1200740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200740 prefixEnd_1200740 := by exact prefixLift 1200740
  have htrace : WordTrace (prefixWord ++ tailWord_1200740) baseStart_1200740 baseEnd_1200740 := by
    simpa [prefixWord, tailWord_1200740, baseEnd_1200740] using wordTrace_append hprefix tailTrace_1200740
  have hstable : (prefixWord ++ tailWord_1200740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200740).length < 2 ^ (prefixWord ++ tailWord_1200740).sum := by decide
  have hdescent : baseEnd_1200740 < baseStart_1200740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200760 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_1200760 : Nat := 118140960795 + 1200760 * 2 ^ 59
def prefixEnd_1200760 : Nat := 4983230072969 + 3 ^ 40 * 1200760 * 2
def baseEnd_1200760 : Nat := 616567030692827254677811

theorem tailTrace_1200760 : CollatzResearch.WordTrace tailWord_1200760 prefixEnd_1200760 616567030692827254677811 := by
  unfold tailWord_1200760
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897657564929534163187867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29196876753239378884250489 21897657564929534163187867)
  ·
    refine ⟨32846486347394301244781801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21897657564929534163187867 32846486347394301244781801)
    ·
      refine ⟨24634864760545725933586351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32846486347394301244781801 24634864760545725933586351)
      ·
        refine ⟨36952297140818588900379527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24634864760545725933586351 36952297140818588900379527)
        ·
          refine ⟨55428445711227883350569291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36952297140818588900379527 55428445711227883350569291)
          ·
            refine ⟨83142668566841825025853937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55428445711227883350569291 83142668566841825025853937)
            ·
              refine ⟨62357001425131368769390453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83142668566841825025853937 62357001425131368769390453)
              ·
                refine ⟨5845968883606065822130355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62357001425131368769390453 5845968883606065822130355)
                ·
                  refine ⟨8768953325409098733195533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5845968883606065822130355 8768953325409098733195533)
                  ·
                    refine ⟨3288357497028412024948325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8768953325409098733195533 3288357497028412024948325)
                    ·
                      refine ⟨616567030692827254677811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3288357497028412024948325 616567030692827254677811)
                      ·
                        rfl

theorem cell23_1200760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_1200760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200760 prefixEnd_1200760 := by exact prefixLift 1200760
  have htrace : WordTrace (prefixWord ++ tailWord_1200760) baseStart_1200760 baseEnd_1200760 := by
    simpa [prefixWord, tailWord_1200760, baseEnd_1200760] using wordTrace_append hprefix tailTrace_1200760
  have hstable : (prefixWord ++ tailWord_1200760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200760).length < 2 ^ (prefixWord ++ tailWord_1200760).sum := by decide
  have hdescent : baseEnd_1200760 < baseStart_1200760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200797 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1200797 : Nat := 118140960795 + 1200797 * 2 ^ 59
def prefixEnd_1200797 : Nat := 4983230072969 + 3 ^ 40 * 1200797 * 2
def baseEnd_1200797 : Nat := 616586029477043609915141

theorem tailTrace_1200797 : CollatzResearch.WordTrace tailWord_1200797 prefixEnd_1200797 616586029477043609915141 := by
  unfold tailWord_1200797
  simp only [CollatzResearch.WordTrace]
  refine ⟨43796664630725023645472645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29197776420483349096981763 43796664630725023645472645)
  ·
    refine ⟨8211874618260941933526121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43796664630725023645472645 8211874618260941933526121)
    ·
      refine ⟨6158905963695706450144591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8211874618260941933526121 6158905963695706450144591)
      ·
        refine ⟨9238358945543559675216887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6158905963695706450144591 9238358945543559675216887)
        ·
          refine ⟨13857538418315339512825331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9238358945543559675216887 13857538418315339512825331)
          ·
            refine ⟨20786307627473009269237997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13857538418315339512825331 20786307627473009269237997)
            ·
              refine ⟨7794865360302378475964249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20786307627473009269237997 7794865360302378475964249)
              ·
                refine ⟨5846149020226783856973187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7794865360302378475964249 5846149020226783856973187)
                ·
                  refine ⟨8769223530340175785459781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5846149020226783856973187 8769223530340175785459781)
                  ·
                    refine ⟨1644229411938782959773709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8769223530340175785459781 1644229411938782959773709)
                    ·
                      refine ⟨616586029477043609915141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1644229411938782959773709 616586029477043609915141)
                      ·
                        rfl

theorem cell23_1200797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1200797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200797 prefixEnd_1200797 := by exact prefixLift 1200797
  have htrace : WordTrace (prefixWord ++ tailWord_1200797) baseStart_1200797 baseEnd_1200797 := by
    simpa [prefixWord, tailWord_1200797, baseEnd_1200797] using wordTrace_append hprefix tailTrace_1200797
  have hstable : (prefixWord ++ tailWord_1200797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200797).length < 2 ^ (prefixWord ++ tailWord_1200797).sum := by decide
  have hdescent : baseEnd_1200797 < baseStart_1200797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200897 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1200897 : Nat := 118140960795 + 1200897 * 2 ^ 59
def prefixEnd_1200897 : Nat := 4983230072969 + 3 ^ 40 * 1200897 * 2
def baseEnd_1200897 : Nat := 616637377542493218664681

theorem tailTrace_1200897 : CollatzResearch.WordTrace tailWord_1200897 prefixEnd_1200897 616637377542493218664681 := by
  unfold tailWord_1200897
  simp only [CollatzResearch.WordTrace]
  refine ⟨43800311930362740724112945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29200207953575160482741963 43800311930362740724112945)
  ·
    refine ⟨32850233947772055543084709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43800311930362740724112945 32850233947772055543084709)
    ·
      refine ⟨6159418865207260414328383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32850233947772055543084709 6159418865207260414328383)
      ·
        refine ⟨9239128297810890621492575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6159418865207260414328383 9239128297810890621492575)
        ·
          refine ⟨13858692446716335932238863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9239128297810890621492575 13858692446716335932238863)
          ·
            refine ⟨20788038670074503898358295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13858692446716335932238863 20788038670074503898358295)
            ·
              refine ⟨31182058005111755847537443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20788038670074503898358295 31182058005111755847537443)
              ·
                refine ⟨46773087007667633771306165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31182058005111755847537443 46773087007667633771306165)
                ·
                  refine ⟨4384976906968840666059953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46773087007667633771306165 4384976906968840666059953)
                  ·
                    refine ⟨3288732680226630499544965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4384976906968840666059953 3288732680226630499544965)
                    ·
                      refine ⟨616637377542493218664681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3288732680226630499544965 616637377542493218664681)
                      ·
                        rfl

theorem cell23_1200897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1200897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200897 prefixEnd_1200897 := by exact prefixLift 1200897
  have htrace : WordTrace (prefixWord ++ tailWord_1200897) baseStart_1200897 baseEnd_1200897 := by
    simpa [prefixWord, tailWord_1200897, baseEnd_1200897] using wordTrace_append hprefix tailTrace_1200897
  have hstable : (prefixWord ++ tailWord_1200897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200897).length < 2 ^ (prefixWord ++ tailWord_1200897).sum := by decide
  have hdescent : baseEnd_1200897 < baseStart_1200897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200904 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_1200904 : Nat := 118140960795 + 1200904 * 2 ^ 59
def prefixEnd_1200904 : Nat := 4983230072969 + 3 ^ 40 * 1200904 * 2
def baseEnd_1200904 : Nat := 616640971907074691277149

theorem tailTrace_1200904 : CollatzResearch.WordTrace tailWord_1200904 prefixEnd_1200904 616640971907074691277149 := by
  unfold tailWord_1200904
  simp only [CollatzResearch.WordTrace]
  refine ⟨21900283620668690459808883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29200378160891587279745177 21900283620668690459808883)
  ·
    refine ⟨32850425431003035689713325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21900283620668690459808883 32850425431003035689713325)
    ·
      refine ⟨12318909536626138383642497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32850425431003035689713325 12318909536626138383642497)
      ·
        refine ⟨9239182152469603787731873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12318909536626138383642497 9239182152469603787731873)
        ·
          refine ⟨6929386614352202840798905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9239182152469603787731873 6929386614352202840798905)
          ·
            refine ⟨5197039960764152130599179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6929386614352202840798905 5197039960764152130599179)
            ·
              refine ⟨7795559941146228195898769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197039960764152130599179 7795559941146228195898769)
              ·
                refine ⟨5846669955859671146924077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7795559941146228195898769 5846669955859671146924077)
                ·
                  refine ⟨2192501233447376680096529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5846669955859671146924077 2192501233447376680096529)
                  ·
                    refine ⟨1644375925085532510072397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2192501233447376680096529 1644375925085532510072397)
                    ·
                      refine ⟨616640971907074691277149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1644375925085532510072397 616640971907074691277149)
                      ·
                        rfl

theorem cell23_1200904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_1200904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200904 prefixEnd_1200904 := by exact prefixLift 1200904
  have htrace : WordTrace (prefixWord ++ tailWord_1200904) baseStart_1200904 baseEnd_1200904 := by
    simpa [prefixWord, tailWord_1200904, baseEnd_1200904] using wordTrace_append hprefix tailTrace_1200904
  have hstable : (prefixWord ++ tailWord_1200904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200904).length < 2 ^ (prefixWord ++ tailWord_1200904).sum := by decide
  have hdescent : baseEnd_1200904 < baseStart_1200904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200924 : List Nat := [2, 2, 3, 1, 1, 4, 3, 7]
def baseStart_1200924 : Nat := 118140960795 + 1200924 * 2 ^ 59
def prefixEnd_1200924 : Nat := 4983230072969 + 3 ^ 40 * 1200924 * 2
def baseEnd_1200924 : Nat := 22838934871117207889891

theorem tailTrace_1200924 : CollatzResearch.WordTrace tailWord_1200924 prefixEnd_1200924 22838934871117207889891 := by
  unfold tailWord_1200924
  simp only [CollatzResearch.WordTrace]
  refine ⟨21900648350632462167672913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29200864467509949556897217 21900648350632462167672913)
  ·
    refine ⟨16425486262974346625754685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21900648350632462167672913 16425486262974346625754685)
    ·
      refine ⟨6159557348615379984658007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16425486262974346625754685 6159557348615379984658007)
      ·
        refine ⟨9239336022923069976987011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6159557348615379984658007 9239336022923069976987011)
        ·
          refine ⟨13859004034384604965480517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9239336022923069976987011 13859004034384604965480517)
          ·
            refine ⟨2598563256447113431027597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13859004034384604965480517 2598563256447113431027597)
            ·
              refine ⟨974461221167667536635349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2598563256447113431027597 974461221167667536635349)
              ·
                refine ⟨22838934871117207889891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 974461221167667536635349 22838934871117207889891)
                ·
                  rfl

theorem cell23_1200924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 7].length) (baseStart_1200924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200924 prefixEnd_1200924 := by exact prefixLift 1200924
  have htrace : WordTrace (prefixWord ++ tailWord_1200924) baseStart_1200924 baseEnd_1200924 := by
    simpa [prefixWord, tailWord_1200924, baseEnd_1200924] using wordTrace_append hprefix tailTrace_1200924
  have hstable : (prefixWord ++ tailWord_1200924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200924).length < 2 ^ (prefixWord ++ tailWord_1200924).sum := by decide
  have hdescent : baseEnd_1200924 < baseStart_1200924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200941 : List Nat := [1, 5, 3, 2, 1, 1, 10]
def baseStart_1200941 : Nat := 118140960795 + 1200941 * 2 ^ 59
def prefixEnd_1200941 : Nat := 4983230072969 + 3 ^ 40 * 1200941 * 2
def baseEnd_1200941 : Nat := 7613086057917173413759

theorem tailTrace_1200941 : CollatzResearch.WordTrace tailWord_1200941 prefixEnd_1200941 7613086057917173413759 := by
  unfold tailWord_1200941
  simp only [CollatzResearch.WordTrace]
  refine ⟨43801916742203336238714677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29201277828135557492476451 43801916742203336238714677)
  ·
    refine ⟨4106429694581562772379501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43801916742203336238714677 4106429694581562772379501)
    ·
      refine ⟨1539911135468086039642313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4106429694581562772379501 1539911135468086039642313)
      ·
        refine ⟨1154933351601064529731735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1539911135468086039642313 1154933351601064529731735)
        ·
          refine ⟨1732400027401596794597603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154933351601064529731735 1732400027401596794597603)
          ·
            refine ⟨2598600041102395191896405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732400027401596794597603 2598600041102395191896405)
            ·
              refine ⟨7613086057917173413759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2598600041102395191896405 7613086057917173413759)
              ·
                rfl

theorem cell23_1200941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 10].length) (baseStart_1200941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200941 prefixEnd_1200941 := by exact prefixLift 1200941
  have htrace : WordTrace (prefixWord ++ tailWord_1200941) baseStart_1200941 baseEnd_1200941 := by
    simpa [prefixWord, tailWord_1200941, baseEnd_1200941] using wordTrace_append hprefix tailTrace_1200941
  have hstable : (prefixWord ++ tailWord_1200941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200941).length < 2 ^ (prefixWord ++ tailWord_1200941).sum := by decide
  have hdescent : baseEnd_1200941 < baseStart_1200941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200968 : List Nat := [2, 1, 3, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_1200968 : Nat := 118140960795 + 1200968 * 2 ^ 59
def prefixEnd_1200968 : Nat := 4983230072969 + 3 ^ 40 * 1200968 * 2
def baseEnd_1200968 : Nat := 616673834668962440876855

theorem tailTrace_1200968 : CollatzResearch.WordTrace tailWord_1200968 prefixEnd_1200968 616673834668962440876855 := by
  unfold tailWord_1200968
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901450756552759924973779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29201934342070346566631705 21901450756552759924973779)
  ·
    refine ⟨32852176134829139887460669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21901450756552759924973779 32852176134829139887460669)
    ·
      refine ⟨12319566050560927457797751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32852176134829139887460669 12319566050560927457797751)
      ·
        refine ⟨18479349075841391186696627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12319566050560927457797751 18479349075841391186696627)
        ·
          refine ⟨27719023613762086780044941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18479349075841391186696627 27719023613762086780044941)
          ·
            refine ⟨10394633855160782542516853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27719023613762086780044941 10394633855160782542516853)
            ·
              refine ⟨974496923921323363360955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10394633855160782542516853 974496923921323363360955)
              ·
                refine ⟨1461745385881985045041433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 974496923921323363360955 1461745385881985045041433)
                ·
                  refine ⟨1096309039411488783781075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1461745385881985045041433 1096309039411488783781075)
                  ·
                    refine ⟨1644463559117233175671613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1096309039411488783781075 1644463559117233175671613)
                    ·
                      refine ⟨616673834668962440876855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1644463559117233175671613 616673834668962440876855)
                      ·
                        rfl

theorem cell23_1200968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_1200968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200968 prefixEnd_1200968 := by exact prefixLift 1200968
  have htrace : WordTrace (prefixWord ++ tailWord_1200968) baseStart_1200968 baseEnd_1200968 := by
    simpa [prefixWord, tailWord_1200968, baseEnd_1200968] using wordTrace_append hprefix tailTrace_1200968
  have hstable : (prefixWord ++ tailWord_1200968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200968).length < 2 ^ (prefixWord ++ tailWord_1200968).sum := by decide
  have hdescent : baseEnd_1200968 < baseStart_1200968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200978 : List Nat := [3, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_1200978 : Nat := 118140960795 + 1200978 * 2 ^ 59
def prefixEnd_1200978 : Nat := 4983230072969 + 3 ^ 40 * 1200978 * 2
def baseEnd_1200978 : Nat := 616678969475507401751809

theorem tailTrace_1200978 : CollatzResearch.WordTrace tailWord_1200978 prefixEnd_1200978 616678969475507401751809 := by
  unfold tailWord_1200978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10950816560767322889452897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29202177495379527705207725 10950816560767322889452897)
  ·
    refine ⟨8213112420575492167089673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10950816560767322889452897 8213112420575492167089673)
    ·
      refine ⟨6159834315431619125317255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8213112420575492167089673 6159834315431619125317255)
      ·
        refine ⟨9239751473147428687975883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6159834315431619125317255 9239751473147428687975883)
        ·
          refine ⟨13859627209721143031963825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9239751473147428687975883 13859627209721143031963825)
          ·
            refine ⟨10394720407290857273972869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13859627209721143031963825 10394720407290857273972869)
            ·
              refine ⟨1949010076367035738869913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10394720407290857273972869 1949010076367035738869913)
              ·
                refine ⟨1461757557275276804152435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1949010076367035738869913 1461757557275276804152435)
                ·
                  refine ⟨2192636335912915206228653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461757557275276804152435 2192636335912915206228653)
                  ·
                    refine ⟨822238625967343202335745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2192636335912915206228653 822238625967343202335745)
                    ·
                      refine ⟨616678969475507401751809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822238625967343202335745 616678969475507401751809)
                      ·
                        rfl

theorem cell23_1200978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_1200978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200978 prefixEnd_1200978 := by exact prefixLift 1200978
  have htrace : WordTrace (prefixWord ++ tailWord_1200978) baseStart_1200978 baseEnd_1200978 := by
    simpa [prefixWord, tailWord_1200978, baseEnd_1200978] using wordTrace_append hprefix tailTrace_1200978
  have hstable : (prefixWord ++ tailWord_1200978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200978).length < 2 ^ (prefixWord ++ tailWord_1200978).sum := by decide
  have hdescent : baseEnd_1200978 < baseStart_1200978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200991 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 6, 2, 2]
def baseStart_1200991 : Nat := 118140960795 + 1200991 * 2 ^ 59
def prefixEnd_1200991 : Nat := 4983230072969 + 3 ^ 40 * 1200991 * 2
def baseEnd_1200991 : Nat := 616685644724015850889249

theorem tailTrace_1200991 : CollatzResearch.WordTrace tailWord_1200991 prefixEnd_1200991 616685644724015850889249 := by
  unfold tailWord_1200991
  simp only [CollatzResearch.WordTrace]
  refine ⟨43803740392022194778034827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29202493594681463185356551 43803740392022194778034827)
  ·
    refine ⟨65705610588033292167052241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43803740392022194778034827 65705610588033292167052241)
    ·
      refine ⟨49279207941024969125289181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65705610588033292167052241 49279207941024969125289181)
      ·
        refine ⟨18479702977884363421983443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49279207941024969125289181 18479702977884363421983443)
        ·
          refine ⟨27719554466826545132975165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18479702977884363421983443 27719554466826545132975165)
          ·
            refine ⟨10394832925059954424865687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27719554466826545132975165 10394832925059954424865687)
            ·
              refine ⟨15592249387589931637298531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10394832925059954424865687 15592249387589931637298531)
              ·
                refine ⟨23388374081384897455947797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15592249387589931637298531 23388374081384897455947797)
                ·
                  refine ⟨1096330035064917068247553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23388374081384897455947797 1096330035064917068247553)
                  ·
                    refine ⟨822247526298687801185665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1096330035064917068247553 822247526298687801185665)
                    ·
                      refine ⟨616685644724015850889249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822247526298687801185665 616685644724015850889249)
                      ·
                        rfl

theorem cell23_1200991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_1200991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200991 prefixEnd_1200991 := by exact prefixLift 1200991
  have htrace : WordTrace (prefixWord ++ tailWord_1200991) baseStart_1200991 baseEnd_1200991 := by
    simpa [prefixWord, tailWord_1200991, baseEnd_1200991] using wordTrace_append hprefix tailTrace_1200991
  have hstable : (prefixWord ++ tailWord_1200991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200991).length < 2 ^ (prefixWord ++ tailWord_1200991).sum := by decide
  have hdescent : baseEnd_1200991 < baseStart_1200991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200997 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 9]
def baseStart_1200997 : Nat := 118140960795 + 1200997 * 2 ^ 59
def prefixEnd_1200997 : Nat := 4983230072969 + 3 ^ 40 * 1200997 * 2
def baseEnd_1200997 : Nat := 68520969511993647490469

theorem tailTrace_1200997 : CollatzResearch.WordTrace tailWord_1200997 prefixEnd_1200997 68520969511993647490469 := by
  unfold tailWord_1200997
  simp only [CollatzResearch.WordTrace]
  refine ⟨43803959230000457802753245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29202639486666971868502163 43803959230000457802753245)
  ·
    refine ⟨16426484711250171676032467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43803959230000457802753245 16426484711250171676032467)
    ·
      refine ⟨24639727066875257514048701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16426484711250171676032467 24639727066875257514048701)
      ·
        refine ⟨9239897650078221567768263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24639727066875257514048701 9239897650078221567768263)
        ·
          refine ⟨13859846475117332351652395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9239897650078221567768263 13859846475117332351652395)
          ·
            refine ⟨20789769712675998527478593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13859846475117332351652395 20789769712675998527478593)
            ·
              refine ⟨15592327284506998895608945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20789769712675998527478593 15592327284506998895608945)
              ·
                refine ⟨11694245463380249171706709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15592327284506998895608945 11694245463380249171706709)
                ·
                  refine ⟨68520969511993647490469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11694245463380249171706709 68520969511993647490469)
                  ·
                    rfl

theorem cell23_1200997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 9].length) (baseStart_1200997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1200997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1200997 prefixEnd_1200997 := by exact prefixLift 1200997
  have htrace : WordTrace (prefixWord ++ tailWord_1200997) baseStart_1200997 baseEnd_1200997 := by
    simpa [prefixWord, tailWord_1200997, baseEnd_1200997] using wordTrace_append hprefix tailTrace_1200997
  have hstable : (prefixWord ++ tailWord_1200997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200997).length < 2 ^ (prefixWord ++ tailWord_1200997).sum := by decide
  have hdescent : baseEnd_1200997 < baseStart_1200997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201081 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 1, 6, 2]
def baseStart_1201081 : Nat := 118140960795 + 1201081 * 2 ^ 59
def prefixEnd_1201081 : Nat := 4983230072969 + 3 ^ 40 * 1201081 * 2
def baseEnd_1201081 : Nat := 616731857982920498763835

theorem tailTrace_1201081 : CollatzResearch.WordTrace tailWord_1201081 prefixEnd_1201081 616731857982920498763835 := by
  unfold tailWord_1201081
  simp only [CollatzResearch.WordTrace]
  refine ⟨43807022961696140148811097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29204681974464093432540731 43807022961696140148811097)
  ·
    refine ⟨32855267221272105111608323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43807022961696140148811097 32855267221272105111608323)
    ·
      refine ⟨49282900831908157667412485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32855267221272105111608323 49282900831908157667412485)
      ·
        refine ⟨9240543905982779562639841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49282900831908157667412485 9240543905982779562639841)
        ·
          refine ⟨6930407929487084671979881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9240543905982779562639841 6930407929487084671979881)
          ·
            refine ⟨5197805947115313503984911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6930407929487084671979881 5197805947115313503984911)
            ·
              refine ⟨7796708920672970255977367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5197805947115313503984911 7796708920672970255977367)
              ·
                refine ⟨11695063381009455383966051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7796708920672970255977367 11695063381009455383966051)
                ·
                  refine ⟨17542595071514183075949077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11695063381009455383966051 17542595071514183075949077)
                  ·
                    refine ⟨822309143977227331685113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17542595071514183075949077 822309143977227331685113)
                    ·
                      refine ⟨616731857982920498763835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822309143977227331685113 616731857982920498763835)
                      ·
                        rfl

theorem cell23_1201081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_1201081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201081 prefixEnd_1201081 := by exact prefixLift 1201081
  have htrace : WordTrace (prefixWord ++ tailWord_1201081) baseStart_1201081 baseEnd_1201081 := by
    simpa [prefixWord, tailWord_1201081, baseEnd_1201081] using wordTrace_append hprefix tailTrace_1201081
  have hstable : (prefixWord ++ tailWord_1201081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201081).length < 2 ^ (prefixWord ++ tailWord_1201081).sum := by decide
  have hdescent : baseEnd_1201081 < baseStart_1201081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201125 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_1201125 : Nat := 118140960795 + 1201125 * 2 ^ 59
def prefixEnd_1201125 : Nat := 4983230072969 + 3 ^ 40 * 1201125 * 2
def baseEnd_1201125 : Nat := 205584817043906108871211

theorem tailTrace_1201125 : CollatzResearch.WordTrace tailWord_1201125 prefixEnd_1201125 205584817043906108871211 := by
  unfold tailWord_1201125
  simp only [CollatzResearch.WordTrace]
  refine ⟨43808627773536735663412829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29205751849024490442275219 43808627773536735663412829)
  ·
    refine ⟨16428235415076275873779811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43808627773536735663412829 16428235415076275873779811)
    ·
      refine ⟨24642353122614413810669717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16428235415076275873779811 24642353122614413810669717)
      ·
        refine ⟨1155110302622550647375143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24642353122614413810669717 1155110302622550647375143)
        ·
          refine ⟨1732665453933825971062715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155110302622550647375143 1732665453933825971062715)
          ·
            refine ⟨2598998180900738956594073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732665453933825971062715 2598998180900738956594073)
            ·
              refine ⟨1949248635675554217445555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2598998180900738956594073 1949248635675554217445555)
              ·
                refine ⟨2923872953513331326168333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949248635675554217445555 2923872953513331326168333)
                ·
                  refine ⟨1096452357567499247313125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2923872953513331326168333 1096452357567499247313125)
                  ·
                    refine ⟨205584817043906108871211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1096452357567499247313125 205584817043906108871211)
                    ·
                      rfl

theorem cell23_1201125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_1201125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201125 prefixEnd_1201125 := by exact prefixLift 1201125
  have htrace : WordTrace (prefixWord ++ tailWord_1201125) baseStart_1201125 baseEnd_1201125 := by
    simpa [prefixWord, tailWord_1201125, baseEnd_1201125] using wordTrace_append hprefix tailTrace_1201125
  have hstable : (prefixWord ++ tailWord_1201125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201125).length < 2 ^ (prefixWord ++ tailWord_1201125).sum := by decide
  have hdescent : baseEnd_1201125 < baseStart_1201125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201148 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_1201148 : Nat := 118140960795 + 1201148 * 2 ^ 59
def prefixEnd_1201148 : Nat := 4983230072969 + 3 ^ 40 * 1201148 * 2
def baseEnd_1201148 : Nat := 616766261186771736626027

theorem tailTrace_1201148 : CollatzResearch.WordTrace tailWord_1201148 prefixEnd_1201148 616766261186771736626027 := by
  unfold tailWord_1201148
  simp only [CollatzResearch.WordTrace]
  refine ⟨21904733326226705295750049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29206311101635607061000065 21904733326226705295750049)
  ·
    refine ⟨16428549994670028971812537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21904733326226705295750049 16428549994670028971812537)
    ·
      refine ⟨12321412496002521728859403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16428549994670028971812537 12321412496002521728859403)
      ·
        refine ⟨18482118744003782593289105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12321412496002521728859403 18482118744003782593289105)
        ·
          refine ⟨13861589058002836944966829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18482118744003782593289105 13861589058002836944966829)
          ·
            refine ⟨5198095896751063854362561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13861589058002836944966829 5198095896751063854362561)
            ·
              refine ⟨3898571922563297890771921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5198095896751063854362561 3898571922563297890771921)
              ·
                refine ⟨2923928941922473418078941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898571922563297890771921 2923928941922473418078941)
                ·
                  refine ⟨1096473353220927531779603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2923928941922473418078941 1096473353220927531779603)
                  ·
                    refine ⟨1644710029831391297669405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1096473353220927531779603 1644710029831391297669405)
                    ·
                      refine ⟨616766261186771736626027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1644710029831391297669405 616766261186771736626027)
                      ·
                        rfl

theorem cell23_1201148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_1201148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201148 prefixEnd_1201148 := by exact prefixLift 1201148
  have htrace : WordTrace (prefixWord ++ tailWord_1201148) baseStart_1201148 baseEnd_1201148 := by
    simpa [prefixWord, tailWord_1201148, baseEnd_1201148] using wordTrace_append hprefix tailTrace_1201148
  have hstable : (prefixWord ++ tailWord_1201148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201148).length < 2 ^ (prefixWord ++ tailWord_1201148).sum := by decide
  have hdescent : baseEnd_1201148 < baseStart_1201148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201175 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 2, 3, 2]
def baseStart_1201175 : Nat := 118140960795 + 1201175 * 2 ^ 59
def prefixEnd_1201175 : Nat := 4983230072969 + 3 ^ 40 * 1201175 * 2
def baseEnd_1201175 : Nat := 616780125164443130988403

theorem tailTrace_1201175 : CollatzResearch.WordTrace tailWord_1201175 prefixEnd_1201175 616780125164443130988403 := by
  unfold tailWord_1201175
  simp only [CollatzResearch.WordTrace]
  refine ⟨43810451423355594202732979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29206967615570396135155319 43810451423355594202732979)
  ·
    refine ⟨65715677135033391304099469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43810451423355594202732979 65715677135033391304099469)
    ·
      refine ⟨24643378925637521739037301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65715677135033391304099469 24643378925637521739037301)
      ·
        refine ⟨2310316774278517663034747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24643378925637521739037301 2310316774278517663034747)
        ·
          refine ⟨3465475161417776494552121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2310316774278517663034747 3465475161417776494552121)
          ·
            refine ⟨2599106371063332370914091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3465475161417776494552121 2599106371063332370914091)
            ·
              refine ⟨3898659556594998556371137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599106371063332370914091 3898659556594998556371137)
              ·
                refine ⟨2923994667446248917278353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898659556594998556371137 2923994667446248917278353)
                ·
                  refine ⟨2192996000584686687958765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2923994667446248917278353 2192996000584686687958765)
                  ·
                    refine ⟨822373500219257507984537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2192996000584686687958765 822373500219257507984537)
                    ·
                      refine ⟨616780125164443130988403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822373500219257507984537 616780125164443130988403)
                      ·
                        rfl

theorem cell23_1201175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_1201175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201175 prefixEnd_1201175 := by exact prefixLift 1201175
  have htrace : WordTrace (prefixWord ++ tailWord_1201175) baseStart_1201175 baseEnd_1201175 := by
    simpa [prefixWord, tailWord_1201175, baseEnd_1201175] using wordTrace_append hprefix tailTrace_1201175
  have hstable : (prefixWord ++ tailWord_1201175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201175).length < 2 ^ (prefixWord ++ tailWord_1201175).sum := by decide
  have hdescent : baseEnd_1201175 < baseStart_1201175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201201 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_1201201 : Nat := 118140960795 + 1201201 * 2 ^ 59
def prefixEnd_1201201 : Nat := 4983230072969 + 3 ^ 40 * 1201201 * 2
def baseEnd_1201201 : Nat := 616793475661460029263283

theorem tailTrace_1201201 : CollatzResearch.WordTrace tailWord_1201201 prefixEnd_1201201 616793475661460029263283 := by
  unfold tailWord_1201201
  simp only [CollatzResearch.WordTrace]
  refine ⟨43811399721261400643179457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29207599814174267095452971 43811399721261400643179457)
  ·
    refine ⟨32858549790946050482384593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43811399721261400643179457 32858549790946050482384593)
    ·
      refine ⟨24643912343209537861788445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32858549790946050482384593 24643912343209537861788445)
      ·
        refine ⟨9241467128703576698170667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24643912343209537861788445 9241467128703576698170667)
        ·
          refine ⟨13862200693055365047256001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9241467128703576698170667 13862200693055365047256001)
          ·
            refine ⟨10396650519791523785442001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13862200693055365047256001 10396650519791523785442001)
            ·
              refine ⟨7797487889843642839081501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10396650519791523785442001 7797487889843642839081501)
              ·
                refine ⟨2924057958691366064655563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7797487889843642839081501 2924057958691366064655563)
                ·
                  refine ⟨4386086938037049096983345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2924057958691366064655563 4386086938037049096983345)
                  ·
                    refine ⟨3289565203527786822737509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4386086938037049096983345 3289565203527786822737509)
                    ·
                      refine ⟨616793475661460029263283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3289565203527786822737509 616793475661460029263283)
                      ·
                        rfl

theorem cell23_1201201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_1201201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201201 prefixEnd_1201201 := by exact prefixLift 1201201
  have htrace : WordTrace (prefixWord ++ tailWord_1201201) baseStart_1201201 baseEnd_1201201 := by
    simpa [prefixWord, tailWord_1201201, baseEnd_1201201] using wordTrace_append hprefix tailTrace_1201201
  have hstable : (prefixWord ++ tailWord_1201201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201201).length < 2 ^ (prefixWord ++ tailWord_1201201).sum := by decide
  have hdescent : baseEnd_1201201 < baseStart_1201201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201208 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_1201208 : Nat := 118140960795 + 1201208 * 2 ^ 59
def prefixEnd_1201208 : Nat := 4983230072969 + 3 ^ 40 * 1201208 * 2
def baseEnd_1201208 : Nat := 616797070026041501875751

theorem tailTrace_1201208 : CollatzResearch.WordTrace tailWord_1201208 prefixEnd_1201208 616797070026041501875751 := by
  unfold tailWord_1201208
  simp only [CollatzResearch.WordTrace]
  refine ⟨21905827516118020419342139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29207770021490693892456185 21905827516118020419342139)
  ·
    refine ⟨32858741274177030629013209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21905827516118020419342139 32858741274177030629013209)
    ·
      refine ⟨24644055955632772971759907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32858741274177030629013209 24644055955632772971759907)
      ·
        refine ⟨36966083933449159457639861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24644055955632772971759907 36966083933449159457639861)
        ·
          refine ⟨3465570368760858699153737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36966083933449159457639861 3465570368760858699153737)
          ·
            refine ⟨2599177776570644024365303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3465570368760858699153737 2599177776570644024365303)
            ·
              refine ⟨3898766664855966036547955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599177776570644024365303 3898766664855966036547955)
              ·
                refine ⟨5848149997283949054821933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3898766664855966036547955 5848149997283949054821933)
                ·
                  refine ⟨2193056248981480895558225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5848149997283949054821933 2193056248981480895558225)
                  ·
                    refine ⟨1644792186736110671668669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2193056248981480895558225 1644792186736110671668669)
                    ·
                      refine ⟨616797070026041501875751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1644792186736110671668669 616797070026041501875751)
                      ·
                        rfl

theorem cell23_1201208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_1201208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201208 prefixEnd_1201208 := by exact prefixLift 1201208
  have htrace : WordTrace (prefixWord ++ tailWord_1201208) baseStart_1201208 baseEnd_1201208 := by
    simpa [prefixWord, tailWord_1201208, baseEnd_1201208] using wordTrace_append hprefix tailTrace_1201208
  have hstable : (prefixWord ++ tailWord_1201208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201208).length < 2 ^ (prefixWord ++ tailWord_1201208).sum := by decide
  have hdescent : baseEnd_1201208 < baseStart_1201208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201221 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_1201221 : Nat := 118140960795 + 1201221 * 2 ^ 59
def prefixEnd_1201221 : Nat := 4983230072969 + 3 ^ 40 * 1201221 * 2
def baseEnd_1201221 : Nat := 616803745274549951013191

theorem tailTrace_1201221 : CollatzResearch.WordTrace tailWord_1201221 prefixEnd_1201221 616803745274549951013191 := by
  unfold tailWord_1201221
  simp only [CollatzResearch.WordTrace]
  refine ⟨43812129181188944058907517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29208086120792629372605011 43812129181188944058907517)
  ·
    refine ⟨16429548442945854022090319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43812129181188944058907517 16429548442945854022090319)
    ·
      refine ⟨24644322664418781033135479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16429548442945854022090319 24644322664418781033135479)
      ·
        refine ⟨36966483996628171549703219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24644322664418781033135479 36966483996628171549703219)
        ·
          refine ⟨55449725994942257324554829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36966483996628171549703219 55449725994942257324554829)
          ·
            refine ⟨20793647248103346496708061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55449725994942257324554829 20793647248103346496708061)
            ·
              refine ⟨7797617718038754936265523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20793647248103346496708061 7797617718038754936265523)
              ·
                refine ⟨11696426577058132404398285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7797617718038754936265523 11696426577058132404398285)
                ·
                  refine ⟨4386159966396799651649357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11696426577058132404398285 4386159966396799651649357)
                  ·
                    refine ⟨1644809987398799869368509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4386159966396799651649357 1644809987398799869368509)
                    ·
                      refine ⟨616803745274549951013191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1644809987398799869368509 616803745274549951013191)
                      ·
                        rfl

theorem cell23_1201221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_1201221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201221 prefixEnd_1201221 := by exact prefixLift 1201221
  have htrace : WordTrace (prefixWord ++ tailWord_1201221) baseStart_1201221 baseEnd_1201221 := by
    simpa [prefixWord, tailWord_1201221, baseEnd_1201221] using wordTrace_append hprefix tailTrace_1201221
  have hstable : (prefixWord ++ tailWord_1201221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201221).length < 2 ^ (prefixWord ++ tailWord_1201221).sum := by decide
  have hdescent : baseEnd_1201221 < baseStart_1201221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201245 : List Nat := [1, 4, 4, 1, 2, 2, 1, 8]
def baseStart_1201245 : Nat := 118140960795 + 1201245 * 2 ^ 59
def prefixEnd_1201245 : Nat := 4983230072969 + 3 ^ 40 * 1201245 * 2
def baseEnd_1201245 : Nat := 22845039585565105819003

theorem tailTrace_1201245 : CollatzResearch.WordTrace tailWord_1201245 prefixEnd_1201245 22845039585565105819003 := by
  unfold tailWord_1201245
  simp only [CollatzResearch.WordTrace]
  refine ⟨43813004533101996157781189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29208669688734664105187459 43813004533101996157781189)
  ·
    refine ⟨8214938349956624279583973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43813004533101996157781189 8214938349956624279583973)
    ·
      refine ⟨1540300940616867052421995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8214938349956624279583973 1540300940616867052421995)
      ·
        refine ⟨2310451410925300578632993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540300940616867052421995 2310451410925300578632993)
        ·
          refine ⟨1732838558193975433974745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2310451410925300578632993 1732838558193975433974745)
          ·
            refine ⟨1299628918645481575481059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1732838558193975433974745 1299628918645481575481059)
            ·
              refine ⟨1949443377968222363221589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299628918645481575481059 1949443377968222363221589)
              ·
                refine ⟨22845039585565105819003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1949443377968222363221589 22845039585565105819003)
                ·
                  rfl

theorem cell23_1201245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 8].length) (baseStart_1201245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201245 prefixEnd_1201245 := by exact prefixLift 1201245
  have htrace : WordTrace (prefixWord ++ tailWord_1201245) baseStart_1201245 baseEnd_1201245 := by
    simpa [prefixWord, tailWord_1201245, baseEnd_1201245] using wordTrace_append hprefix tailTrace_1201245
  have hstable : (prefixWord ++ tailWord_1201245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201245).length < 2 ^ (prefixWord ++ tailWord_1201245).sum := by decide
  have hdescent : baseEnd_1201245 < baseStart_1201245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201248 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 5, 3, 2]
def baseStart_1201248 : Nat := 118140960795 + 1201248 * 2 ^ 59
def prefixEnd_1201248 : Nat := 4983230072969 + 3 ^ 40 * 1201248 * 2
def baseEnd_1201248 : Nat := 616817609252221345375567

theorem tailTrace_1201248 : CollatzResearch.WordTrace tailWord_1201248 prefixEnd_1201248 616817609252221345375567 := by
  unfold tailWord_1201248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21906556976045563835070199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29208742634727418446760265 21906556976045563835070199)
  ·
    refine ⟨32859835464068345752605299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21906556976045563835070199 32859835464068345752605299)
    ·
      refine ⟨49289753196102518628907949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32859835464068345752605299 49289753196102518628907949)
      ·
        refine ⟨18483657448538444485840481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49289753196102518628907949 18483657448538444485840481)
        ·
          refine ⟨13862743086403833364380361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18483657448538444485840481 13862743086403833364380361)
          ·
            refine ⟨10397057314802875023285271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13862743086403833364380361 10397057314802875023285271)
            ·
              refine ⟨15595585972204312534927907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10397057314802875023285271 15595585972204312534927907)
              ·
                refine ⟨23393378958306468802391861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15595585972204312534927907 23393378958306468802391861)
                ·
                  refine ⟨2193129277341231450224237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23393378958306468802391861 2193129277341231450224237)
                  ·
                    refine ⟨822423479002961793834089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2193129277341231450224237 822423479002961793834089)
                    ·
                      refine ⟨616817609252221345375567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822423479002961793834089 616817609252221345375567)
                      ·
                        rfl

theorem cell23_1201248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_1201248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201248 prefixEnd_1201248 := by exact prefixLift 1201248
  have htrace : WordTrace (prefixWord ++ tailWord_1201248) baseStart_1201248 baseEnd_1201248 := by
    simpa [prefixWord, tailWord_1201248, baseEnd_1201248] using wordTrace_append hprefix tailTrace_1201248
  have hstable : (prefixWord ++ tailWord_1201248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201248).length < 2 ^ (prefixWord ++ tailWord_1201248).sum := by decide
  have hdescent : baseEnd_1201248 < baseStart_1201248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201255 : List Nat := [1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_1201255 : Nat := 118140960795 + 1201255 * 2 ^ 59
def prefixEnd_1201255 : Nat := 4983230072969 + 3 ^ 40 * 1201255 * 2
def baseEnd_1201255 : Nat := 616821203616802817988035

theorem tailTrace_1201255 : CollatzResearch.WordTrace tailWord_1201255 prefixEnd_1201255 616821203616802817988035 := by
  unfold tailWord_1201255
  simp only [CollatzResearch.WordTrace]
  refine ⟨43813369263065767865645219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29208912842043845243763479 43813369263065767865645219)
  ·
    refine ⟨65720053894598651798467829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43813369263065767865645219 65720053894598651798467829)
    ·
      refine ⟨6161255052618623606106359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65720053894598651798467829 6161255052618623606106359)
      ·
        refine ⟨9241882578927935409159539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6161255052618623606106359 9241882578927935409159539)
        ·
          refine ⟨13862823868391903113739309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9241882578927935409159539 13862823868391903113739309)
          ·
            refine ⟨5198558950646963667652241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13862823868391903113739309 5198558950646963667652241)
            ·
              refine ⟨3898919212985222750739181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5198558950646963667652241 3898919212985222750739181)
              ·
                refine ⟨1462094704869458531527193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3898919212985222750739181 1462094704869458531527193)
                ·
                  refine ⟨1096571028652093898645395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1462094704869458531527193 1096571028652093898645395)
                  ·
                    refine ⟨1644856542978140847968093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1096571028652093898645395 1644856542978140847968093)
                    ·
                      refine ⟨616821203616802817988035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1644856542978140847968093 616821203616802817988035)
                      ·
                        rfl

theorem cell23_1201255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_1201255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201255 prefixEnd_1201255 := by exact prefixLift 1201255
  have htrace : WordTrace (prefixWord ++ tailWord_1201255) baseStart_1201255 baseEnd_1201255 := by
    simpa [prefixWord, tailWord_1201255, baseEnd_1201255] using wordTrace_append hprefix tailTrace_1201255
  have hstable : (prefixWord ++ tailWord_1201255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201255).length < 2 ^ (prefixWord ++ tailWord_1201255).sum := by decide
  have hdescent : baseEnd_1201255 < baseStart_1201255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201308 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1201308 : Nat := 118140960795 + 1201308 * 2 ^ 59
def prefixEnd_1201308 : Nat := 4983230072969 + 3 ^ 40 * 1201308 * 2
def baseEnd_1201308 : Nat := 616848418091491110625291

theorem tailTrace_1201308 : CollatzResearch.WordTrace tailWord_1201308 prefixEnd_1201308 616848418091491110625291 := by
  unfold tailWord_1201308
  simp only [CollatzResearch.WordTrace]
  refine ⟨21907651165936878958662289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29210201554582505278216385 21907651165936878958662289)
  ·
    refine ⟨16430738374452659218996717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21907651165936878958662289 16430738374452659218996717)
    ·
      refine ⟨6161526890419747207123769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16430738374452659218996717 6161526890419747207123769)
      ·
        refine ⟨4621145167814810405342827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6161526890419747207123769 4621145167814810405342827)
        ·
          refine ⟨6931717751722215608014241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4621145167814810405342827 6931717751722215608014241)
          ·
            refine ⟨5198788313791661706010681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6931717751722215608014241 5198788313791661706010681)
            ·
              refine ⟨3899091235343746279508011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5198788313791661706010681 3899091235343746279508011)
              ·
                refine ⟨5848636853015619419262017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3899091235343746279508011 5848636853015619419262017)
                ·
                  refine ⟨4386477639761714564446513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5848636853015619419262017 4386477639761714564446513)
                  ·
                    refine ⟨3289858229821285923334885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4386477639761714564446513 3289858229821285923334885)
                    ·
                      refine ⟨616848418091491110625291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3289858229821285923334885 616848418091491110625291)
                      ·
                        rfl

theorem cell23_1201308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1201308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201308 prefixEnd_1201308 := by exact prefixLift 1201308
  have htrace : WordTrace (prefixWord ++ tailWord_1201308) baseStart_1201308 baseEnd_1201308 := by
    simpa [prefixWord, tailWord_1201308, baseEnd_1201308] using wordTrace_append hprefix tailTrace_1201308
  have hstable : (prefixWord ++ tailWord_1201308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201308).length < 2 ^ (prefixWord ++ tailWord_1201308).sum := by decide
  have hdescent : baseEnd_1201308 < baseStart_1201308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201331 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 1, 7]
def baseStart_1201331 : Nat := 118140960795 + 1201331 * 2 ^ 59
def prefixEnd_1201331 : Nat := 4983230072969 + 3 ^ 40 * 1201331 * 2
def baseEnd_1201331 : Nat := 205620076048848173545895

theorem tailTrace_1201331 : CollatzResearch.WordTrace tailWord_1201331 prefixEnd_1201331 205620076048848173545895 := by
  unfold tailWord_1201331
  simp only [CollatzResearch.WordTrace]
  refine ⟨43816141210790432845411847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29210760807193621896941231 43816141210790432845411847)
  ·
    refine ⟨65724211816185649268117771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43816141210790432845411847 65724211816185649268117771)
    ·
      refine ⟨98586317724278473902176657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65724211816185649268117771 98586317724278473902176657)
      ·
        refine ⟨73939738293208855426632493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98586317724278473902176657 73939738293208855426632493)
        ·
          refine ⟨27727401859953320784987185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73939738293208855426632493 27727401859953320784987185)
          ·
            refine ⟨20795551394964990588740389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27727401859953320784987185 20795551394964990588740389)
            ·
              refine ⟨3899165886555935735388823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20795551394964990588740389 3899165886555935735388823)
              ·
                refine ⟨5848748829833903603083235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3899165886555935735388823 5848748829833903603083235)
                ·
                  refine ⟨8773123244750855404624853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5848748829833903603083235 8773123244750855404624853)
                  ·
                    refine ⟨205620076048848173545895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8773123244750855404624853 205620076048848173545895)
                    ·
                      rfl

theorem cell23_1201331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 7].length) (baseStart_1201331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201331 prefixEnd_1201331 := by exact prefixLift 1201331
  have htrace : WordTrace (prefixWord ++ tailWord_1201331) baseStart_1201331 baseEnd_1201331 := by
    simpa [prefixWord, tailWord_1201331, baseEnd_1201331] using wordTrace_append hprefix tailTrace_1201331
  have hstable : (prefixWord ++ tailWord_1201331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201331).length < 2 ^ (prefixWord ++ tailWord_1201331).sum := by decide
  have hdescent : baseEnd_1201331 < baseStart_1201331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201338 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2]
def baseStart_1201338 : Nat := 118140960795 + 1201338 * 2 ^ 59
def prefixEnd_1201338 : Nat := 4983230072969 + 3 ^ 40 * 1201338 * 2
def baseEnd_1201338 : Nat := 616863822511125993250153

theorem tailTrace_1201338 : CollatzResearch.WordTrace tailWord_1201338 prefixEnd_1201338 616863822511125993250153 := by
  unfold tailWord_1201338
  simp only [CollatzResearch.WordTrace]
  refine ⟨10954099130441268260229167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29210931014510048693944445 10954099130441268260229167)
  ·
    refine ⟨16431148695661902390343751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10954099130441268260229167 16431148695661902390343751)
    ·
      refine ⟨24646723043492853585515627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16431148695661902390343751 24646723043492853585515627)
      ·
        refine ⟨36970084565239280378273441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24646723043492853585515627 36970084565239280378273441)
        ·
          refine ⟨27727563423929460283705081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36970084565239280378273441 27727563423929460283705081)
          ·
            refine ⟨20795672567947095212778811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27727563423929460283705081 20795672567947095212778811)
            ·
              refine ⟨31193508851920642819168217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20795672567947095212778811 31193508851920642819168217)
              ·
                refine ⟨23395131638940482114376163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31193508851920642819168217 23395131638940482114376163)
                ·
                  refine ⟨35092697458410723171564245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23395131638940482114376163 35092697458410723171564245)
                  ·
                    refine ⟨822485096681501324333537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35092697458410723171564245 822485096681501324333537)
                    ·
                      refine ⟨616863822511125993250153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 822485096681501324333537 616863822511125993250153)
                      ·
                        rfl

theorem cell23_1201338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_1201338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201338 prefixEnd_1201338 := by exact prefixLift 1201338
  have htrace : WordTrace (prefixWord ++ tailWord_1201338) baseStart_1201338 baseEnd_1201338 := by
    simpa [prefixWord, tailWord_1201338, baseEnd_1201338] using wordTrace_append hprefix tailTrace_1201338
  have hstable : (prefixWord ++ tailWord_1201338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201338).length < 2 ^ (prefixWord ++ tailWord_1201338).sum := by decide
  have hdescent : baseEnd_1201338 < baseStart_1201338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201398 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1201398 : Nat := 118140960795 + 1201398 * 2 ^ 59
def prefixEnd_1201398 : Nat := 4983230072969 + 3 ^ 40 * 1201398 * 2
def baseEnd_1201398 : Nat := 616894631350395758499877

theorem tailTrace_1201398 : CollatzResearch.WordTrace tailWord_1201398 prefixEnd_1201398 616894631350395758499877 := by
  unfold tailWord_1201398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2738661556346731455506303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29212389934365135525400565 2738661556346731455506303)
  ·
    refine ⟨4107992334520097183259455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2738661556346731455506303 4107992334520097183259455)
    ·
      refine ⟨6161988501780145774889183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107992334520097183259455 6161988501780145774889183)
      ·
        refine ⟨9242982752670218662333775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6161988501780145774889183 9242982752670218662333775)
        ·
          refine ⟨13864474129005327993500663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9242982752670218662333775 13864474129005327993500663)
          ·
            refine ⟨20796711193507991990250995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13864474129005327993500663 20796711193507991990250995)
            ·
              refine ⟨31195066790261987985376493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20796711193507991990250995 31195066790261987985376493)
              ·
                refine ⟨11698150046348245494516185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31195066790261987985376493 11698150046348245494516185)
                ·
                  refine ⟨8773612534761184120887139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11698150046348245494516185 8773612534761184120887139)
                  ·
                    refine ⟨13160418802141776181330709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8773612534761184120887139 13160418802141776181330709)
                    ·
                      refine ⟨616894631350395758499877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13160418802141776181330709 616894631350395758499877)
                      ·
                        rfl

theorem cell23_1201398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1201398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201398 prefixEnd_1201398 := by exact prefixLift 1201398
  have htrace : WordTrace (prefixWord ++ tailWord_1201398) baseStart_1201398 baseEnd_1201398 := by
    simpa [prefixWord, tailWord_1201398, baseEnd_1201398] using wordTrace_append hprefix tailTrace_1201398
  have hstable : (prefixWord ++ tailWord_1201398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201398).length < 2 ^ (prefixWord ++ tailWord_1201398).sum := by decide
  have hdescent : baseEnd_1201398 < baseStart_1201398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201418 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1201418 : Nat := 118140960795 + 1201418 * 2 ^ 59
def prefixEnd_1201418 : Nat := 4983230072969 + 3 ^ 40 * 1201418 * 2
def baseEnd_1201418 : Nat := 616904900963485680249785

theorem tailTrace_1201418 : CollatzResearch.WordTrace tailWord_1201418 prefixEnd_1201418 616904900963485680249785 := by
  unfold tailWord_1201418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10954828590368811675957227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29212876240983497802552605 10954828590368811675957227)
  ·
    refine ⟨16432242885553217513935841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10954828590368811675957227 16432242885553217513935841)
    ·
      refine ⟨12324182164164913135451881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16432242885553217513935841 12324182164164913135451881)
      ·
        refine ⟨9243136623123684851588911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12324182164164913135451881 9243136623123684851588911)
        ·
          refine ⟨13864704934685527277383367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9243136623123684851588911 13864704934685527277383367)
          ·
            refine ⟨20797057402028290916075051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13864704934685527277383367 20797057402028290916075051)
            ·
              refine ⟨31195586103042436374112577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20797057402028290916075051 31195586103042436374112577)
              ·
                refine ⟨23396689577281827280584433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31195586103042436374112577 23396689577281827280584433)
                ·
                  refine ⟨17547517182961370460438325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23396689577281827280584433 17547517182961370460438325)
                  ·
                    refine ⟨1645079735902628480666093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17547517182961370460438325 1645079735902628480666093)
                    ·
                      refine ⟨616904900963485680249785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1645079735902628480666093 616904900963485680249785)
                      ·
                        rfl

theorem cell23_1201418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1201418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1201418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1201418 prefixEnd_1201418 := by exact prefixLift 1201418
  have htrace : WordTrace (prefixWord ++ tailWord_1201418) baseStart_1201418 baseEnd_1201418 := by
    simpa [prefixWord, tailWord_1201418, baseEnd_1201418] using wordTrace_append hprefix tailTrace_1201418
  have hstable : (prefixWord ++ tailWord_1201418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201418).length < 2 ^ (prefixWord ++ tailWord_1201418).sum := by decide
  have hdescent : baseEnd_1201418 < baseStart_1201418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
