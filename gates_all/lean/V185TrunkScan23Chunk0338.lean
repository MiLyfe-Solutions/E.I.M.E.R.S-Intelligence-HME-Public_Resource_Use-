import V185TrunkScan23Chunk0337

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1999009 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 3, 4]
def baseStart_1999009 : Nat := 118140960795 + 1999009 * 2 ^ 59
def prefixEnd_1999009 : Nat := 4983230072969 + 3 ^ 40 * 1999009 * 2
def baseEnd_1999009 : Nat := 342150816554558200598077

theorem tailTrace_1999009 : CollatzResearch.WordTrace tailWord_1999009 prefixEnd_1999009 342150816554558200598077 := by
  unfold tailWord_1999009
  simp only [CollatzResearch.WordTrace]
  refine ⟨72909848014939271401784081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48606565343292847601189387 72909848014939271401784081)
  ·
    refine ⟨54682386011204453551338061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72909848014939271401784081 54682386011204453551338061)
    ·
      refine ⟨20505894754201670081751773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54682386011204453551338061 20505894754201670081751773)
      ·
        refine ⟨7689710532825626280656915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20505894754201670081751773 7689710532825626280656915)
        ·
          refine ⟨11534565799238439420985373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7689710532825626280656915 11534565799238439420985373)
          ·
            refine ⟨4325462174714414782869515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11534565799238439420985373 4325462174714414782869515)
            ·
              refine ⟨6488193262071622174304273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4325462174714414782869515 6488193262071622174304273)
              ·
                refine ⟨4866144946553716630728205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6488193262071622174304273 4866144946553716630728205)
                ·
                  refine ⟨1824804354957643736523077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4866144946553716630728205 1824804354957643736523077)
                  ·
                    refine ⟨342150816554558200598077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1824804354957643736523077 342150816554558200598077)
                    ·
                      rfl

theorem cell23_1999009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_1999009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999009 prefixEnd_1999009 := by exact prefixLift 1999009
  have htrace : WordTrace (prefixWord ++ tailWord_1999009) baseStart_1999009 baseEnd_1999009 := by
    simpa [prefixWord, tailWord_1999009, baseEnd_1999009] using wordTrace_append hprefix tailTrace_1999009
  have hstable : (prefixWord ++ tailWord_1999009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999009).length < 2 ^ (prefixWord ++ tailWord_1999009).sum := by decide
  have hdescent : baseEnd_1999009 < baseStart_1999009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999026 : List Nat := [3, 2, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_1999026 : Nat := 118140960795 + 1999026 * 2 ^ 59
def prefixEnd_1999026 : Nat := 4983230072969 + 3 ^ 40 * 1999026 * 2
def baseEnd_1999026 : Nat := 342153726278267011760551

theorem tailTrace_1999026 : CollatzResearch.WordTrace tailWord_1999026 prefixEnd_1999026 342153726278267011760551 := by
  unfold tailWord_1999026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18227617013969420826288233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48606978703918455536768621 18227617013969420826288233)
  ·
    refine ⟨13670712760477065619716175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18227617013969420826288233 13670712760477065619716175)
    ·
      refine ⟨20506069140715598429574263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13670712760477065619716175 20506069140715598429574263)
      ·
        refine ⟨30759103711073397644361395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20506069140715598429574263 30759103711073397644361395)
        ·
          refine ⟨46138655566610096466542093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30759103711073397644361395 46138655566610096466542093)
          ·
            refine ⟨17301995837478786174953285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46138655566610096466542093 17301995837478786174953285)
            ·
              refine ⟨3244124219527272407803741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17301995837478786174953285 3244124219527272407803741)
              ·
                refine ⟨1216546582322727152926403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3244124219527272407803741 1216546582322727152926403)
                ·
                  refine ⟨1824819873484090729389605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216546582322727152926403 1824819873484090729389605)
                  ·
                    refine ⟨342153726278267011760551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1824819873484090729389605 342153726278267011760551)
                    ·
                      rfl

theorem cell23_1999026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_1999026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999026 prefixEnd_1999026 := by exact prefixLift 1999026
  have htrace : WordTrace (prefixWord ++ tailWord_1999026) baseStart_1999026 baseEnd_1999026 := by
    simpa [prefixWord, tailWord_1999026, baseEnd_1999026] using wordTrace_append hprefix tailTrace_1999026
  have hstable : (prefixWord ++ tailWord_1999026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999026).length < 2 ^ (prefixWord ++ tailWord_1999026).sum := by decide
  have hdescent : baseEnd_1999026 < baseStart_1999026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999082 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1999082 : Nat := 118140960795 + 1999082 * 2 ^ 59
def prefixEnd_1999082 : Nat := 4983230072969 + 3 ^ 40 * 1999082 * 2
def baseEnd_1999082 : Nat := 342163311250484272060465

theorem tailTrace_1999082 : CollatzResearch.WordTrace tailWord_1999082 prefixEnd_1999082 342163311250484272060465 := by
  unfold tailWord_1999082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18228127635918701217297875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48608340362449869912794333 18228127635918701217297875)
  ·
    refine ⟨27342191453878051825946813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18228127635918701217297875 27342191453878051825946813)
    ·
      refine ⟨10253321795204269434730055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27342191453878051825946813 10253321795204269434730055)
      ·
        refine ⟨15379982692806404152095083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253321795204269434730055 15379982692806404152095083)
        ·
          refine ⟨23069974039209606228142625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15379982692806404152095083 23069974039209606228142625)
          ·
            refine ⟨17302480529407204671106969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23069974039209606228142625 17302480529407204671106969)
            ·
              refine ⟨12976860397055403503330227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17302480529407204671106969 12976860397055403503330227)
              ·
                refine ⟨19465290595583105254995341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12976860397055403503330227 19465290595583105254995341)
                ·
                  refine ⟨7299483973343664470623253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19465290595583105254995341 7299483973343664470623253)
                  ·
                    refine ⟨342163311250484272060465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7299483973343664470623253 342163311250484272060465)
                    ·
                      rfl

theorem cell23_1999082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1999082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999082 prefixEnd_1999082 := by exact prefixLift 1999082
  have htrace : WordTrace (prefixWord ++ tailWord_1999082) baseStart_1999082 baseEnd_1999082 := by
    simpa [prefixWord, tailWord_1999082, baseEnd_1999082] using wordTrace_append hprefix tailTrace_1999082
  have hstable : (prefixWord ++ tailWord_1999082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999082).length < 2 ^ (prefixWord ++ tailWord_1999082).sum := by decide
  have hdescent : baseEnd_1999082 < baseStart_1999082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999089 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_1999089 : Nat := 118140960795 + 1999089 * 2 ^ 59
def prefixEnd_1999089 : Nat := 4983230072969 + 3 ^ 40 * 1999089 * 2
def baseEnd_1999089 : Nat := 1026493528116034288793863

theorem tailTrace_1999089 : CollatzResearch.WordTrace tailWord_1999089 prefixEnd_1999089 1026493528116034288793863 := by
  unfold tailWord_1999089
  simp only [CollatzResearch.WordTrace]
  refine ⟨72912765854649445064696321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48608510569766296709797547 72912765854649445064696321)
  ·
    refine ⟨54684574390987083798522241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72912765854649445064696321 54684574390987083798522241)
    ·
      refine ⟨41013430793240312848891681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54684574390987083798522241 41013430793240312848891681)
      ·
        refine ⟨30760073094930234636668761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41013430793240312848891681 30760073094930234636668761)
        ·
          refine ⟨23070054821197675977501571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30760073094930234636668761 23070054821197675977501571)
          ·
            refine ⟨34605082231796513966252357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23070054821197675977501571 34605082231796513966252357)
            ·
              refine ⟨6488452918461846368672317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34605082231796513966252357 6488452918461846368672317)
              ·
                refine ⟨2433169844423192388252119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6488452918461846368672317 2433169844423192388252119)
                ·
                  refine ⟨3649754766634788582378179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433169844423192388252119 3649754766634788582378179)
                  ·
                    refine ⟨5474632149952182873567269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3649754766634788582378179 5474632149952182873567269)
                    ·
                      refine ⟨1026493528116034288793863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5474632149952182873567269 1026493528116034288793863)
                      ·
                        rfl

theorem cell23_1999089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_1999089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999089 prefixEnd_1999089 := by exact prefixLift 1999089
  have htrace : WordTrace (prefixWord ++ tailWord_1999089) baseStart_1999089 baseEnd_1999089 := by
    simpa [prefixWord, tailWord_1999089, baseEnd_1999089] using wordTrace_append hprefix tailTrace_1999089
  have hstable : (prefixWord ++ tailWord_1999089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999089).length < 2 ^ (prefixWord ++ tailWord_1999089).sum := by decide
  have hdescent : baseEnd_1999089 < baseStart_1999089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999100 : List Nat := [2, 2, 2, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_1999100 : Nat := 118140960795 + 1999100 * 2 ^ 59
def prefixEnd_1999100 : Nat := 4983230072969 + 3 ^ 40 * 1999100 * 2
def baseEnd_1999100 : Nat := 1026499176403233745756313

theorem tailTrace_1999100 : CollatzResearch.WordTrace tailWord_1999100 prefixEnd_1999100 1026499176403233745756313 := by
  unfold tailWord_1999100
  simp only [CollatzResearch.WordTrace]
  refine ⟨36456583528804796971673377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48608778038406395962231169 36456583528804796971673377)
  ·
    refine ⟨27342437646603597728755033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36456583528804796971673377 27342437646603597728755033)
    ·
      refine ⟨20506828234952698296566275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27342437646603597728755033 20506828234952698296566275)
      ·
        refine ⟨30760242352429047444849413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20506828234952698296566275 30760242352429047444849413)
        ·
          refine ⟨5767545441080446395909265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30760242352429047444849413 5767545441080446395909265)
          ·
            refine ⟨4325659080810334796931949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5767545441080446395909265 4325659080810334796931949)
            ·
              refine ⟨1622122155303875548849481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4325659080810334796931949 1622122155303875548849481)
              ·
                refine ⟨1216591616477906661637111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622122155303875548849481 1216591616477906661637111)
                ·
                  refine ⟨1824887424716859992455667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216591616477906661637111 1824887424716859992455667)
                  ·
                    refine ⟨2737331137075289988683501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1824887424716859992455667 2737331137075289988683501)
                    ·
                      refine ⟨1026499176403233745756313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2737331137075289988683501 1026499176403233745756313)
                      ·
                        rfl

theorem cell23_1999100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_1999100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999100 prefixEnd_1999100 := by exact prefixLift 1999100
  have htrace : WordTrace (prefixWord ++ tailWord_1999100) baseStart_1999100 baseEnd_1999100 := by
    simpa [prefixWord, tailWord_1999100, baseEnd_1999100] using wordTrace_append hprefix tailTrace_1999100
  have hstable : (prefixWord ++ tailWord_1999100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999100).length < 2 ^ (prefixWord ++ tailWord_1999100).sum := by decide
  have hdescent : baseEnd_1999100 < baseStart_1999100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999112 : List Nat := [2, 1, 3, 2, 3, 1, 1, 10]
def baseStart_1999112 : Nat := 118140960795 + 1999112 * 2 ^ 59
def prefixEnd_1999112 : Nat := 4983230072969 + 3 ^ 40 * 1999112 * 2
def baseEnd_1999112 : Nat := 38018716228558803659491

theorem tailTrace_1999112 : CollatzResearch.WordTrace tailWord_1999112 prefixEnd_1999112 38018716228558803659491 := by
  unfold tailWord_1999112
  simp only [CollatzResearch.WordTrace]
  refine ⟨36456802366783059996391795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48609069822377413328522393 36456802366783059996391795)
  ·
    refine ⟨54685203550174589994587693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36456802366783059996391795 54685203550174589994587693)
    ·
      refine ⟨20506951331315471247970385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54685203550174589994587693 20506951331315471247970385)
      ·
        refine ⟨15380213498486603435977789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20506951331315471247970385 15380213498486603435977789)
        ·
          refine ⟨5767580061932476288491671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15380213498486603435977789 5767580061932476288491671)
          ·
            refine ⟨8651370092898714432737507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5767580061932476288491671 8651370092898714432737507)
            ·
              refine ⟨12977055139348071649106261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8651370092898714432737507 12977055139348071649106261)
              ·
                refine ⟨38018716228558803659491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12977055139348071649106261 38018716228558803659491)
                ·
                  rfl

theorem cell23_1999112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 10].length) (baseStart_1999112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999112 prefixEnd_1999112 := by exact prefixLift 1999112
  have htrace : WordTrace (prefixWord ++ tailWord_1999112) baseStart_1999112 baseEnd_1999112 := by
    simpa [prefixWord, tailWord_1999112, baseEnd_1999112] using wordTrace_append hprefix tailTrace_1999112
  have hstable : (prefixWord ++ tailWord_1999112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999112).length < 2 ^ (prefixWord ++ tailWord_1999112).sum := by decide
  have hdescent : baseEnd_1999112 < baseStart_1999112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999139 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 3]
def baseStart_1999139 : Nat := 118140960795 + 1999139 * 2 ^ 59
def prefixEnd_1999139 : Nat := 4983230072969 + 3 ^ 40 * 1999139 * 2
def baseEnd_1999139 : Nat := 1026519202148759093168633

theorem tailTrace_1999139 : CollatzResearch.WordTrace tailWord_1999139 prefixEnd_1999139 1026519202148759093168633 := by
  unfold tailWord_1999139
  simp only [CollatzResearch.WordTrace]
  refine ⟨72914589504468303604016471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48609726336312202402677647 72914589504468303604016471)
  ·
    refine ⟨109371884256702455406024707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72914589504468303604016471 109371884256702455406024707)
    ·
      refine ⟨164057826385053683109037061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109371884256702455406024707 164057826385053683109037061)
      ·
        refine ⟨30760842447197565582944449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164057826385053683109037061 30760842447197565582944449)
        ·
          refine ⟨23070631835398174187208337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30760842447197565582944449 23070631835398174187208337)
          ·
            refine ⟨17302973876548630640406253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23070631835398174187208337 17302973876548630640406253)
            ·
              refine ⟨6488615203705736490152345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17302973876548630640406253 6488615203705736490152345)
              ·
                refine ⟨4866461402779302367614259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6488615203705736490152345 4866461402779302367614259)
                ·
                  refine ⟨7299692104168953551421389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4866461402779302367614259 7299692104168953551421389)
                  ·
                    refine ⟨2737384539063357581783021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7299692104168953551421389 2737384539063357581783021)
                    ·
                      refine ⟨1026519202148759093168633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2737384539063357581783021 1026519202148759093168633)
                      ·
                        rfl

theorem cell23_1999139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_1999139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999139 prefixEnd_1999139 := by exact prefixLift 1999139
  have htrace : WordTrace (prefixWord ++ tailWord_1999139) baseStart_1999139 baseEnd_1999139 := by
    simpa [prefixWord, tailWord_1999139, baseEnd_1999139] using wordTrace_append hprefix tailTrace_1999139
  have hstable : (prefixWord ++ tailWord_1999139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999139).length < 2 ^ (prefixWord ++ tailWord_1999139).sum := by decide
  have hdescent : baseEnd_1999139 < baseStart_1999139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999150 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1999150 : Nat := 118140960795 + 1999150 * 2 ^ 59
def prefixEnd_1999150 : Nat := 4983230072969 + 3 ^ 40 * 1999150 * 2
def baseEnd_1999150 : Nat := 342174950145319516710361

theorem tailTrace_1999150 : CollatzResearch.WordTrace tailWord_1999150 prefixEnd_1999150 342174950145319516710361 := by
  unfold tailWord_1999150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9114373838428556560333363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48609993804952301655111269 9114373838428556560333363)
  ·
    refine ⟨13671560757642834840500045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9114373838428556560333363 13671560757642834840500045)
    ·
      refine ⟨5126835284116063065187517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13671560757642834840500045 5126835284116063065187517)
      ·
        refine ⟨1922563231543523649445319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5126835284116063065187517 1922563231543523649445319)
        ·
          refine ⟨2883844847315285474167979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922563231543523649445319 2883844847315285474167979)
          ·
            refine ⟨4325767270972928211251969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883844847315285474167979 4325767270972928211251969)
            ·
              refine ⟨3244325453229696158438977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325767270972928211251969 3244325453229696158438977)
              ·
                refine ⟨2433244089922272118829233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244325453229696158438977 2433244089922272118829233)
                ·
                  refine ⟨1824933067441704089121925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2433244089922272118829233 1824933067441704089121925)
                  ·
                    refine ⟨342174950145319516710361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1824933067441704089121925 342174950145319516710361)
                    ·
                      rfl

theorem cell23_1999150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1999150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999150 prefixEnd_1999150 := by exact prefixLift 1999150
  have htrace : WordTrace (prefixWord ++ tailWord_1999150) baseStart_1999150 baseEnd_1999150 := by
    simpa [prefixWord, tailWord_1999150, baseEnd_1999150] using wordTrace_append hprefix tailTrace_1999150
  have hstable : (prefixWord ++ tailWord_1999150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999150).length < 2 ^ (prefixWord ++ tailWord_1999150).sum := by decide
  have hdescent : baseEnd_1999150 < baseStart_1999150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999213 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_1999213 : Nat := 118140960795 + 1999213 * 2 ^ 59
def prefixEnd_1999213 : Nat := 4983230072969 + 3 ^ 40 * 1999213 * 2
def baseEnd_1999213 : Nat := 1026557199717191803643293

theorem tailTrace_1999213 : CollatzResearch.WordTrace tailWord_1999213 prefixEnd_1999213 1026557199717191803643293 := by
  unfold tailWord_1999213
  simp only [CollatzResearch.WordTrace]
  refine ⟨72917288506200214242210293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48611525670800142828140195 72917288506200214242210293)
  ·
    refine ⟨6835995797456270085207215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72917288506200214242210293 6835995797456270085207215)
    ·
      refine ⟨10253993696184405127810823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6835995797456270085207215 10253993696184405127810823)
      ·
        refine ⟨15380990544276607691716235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10253993696184405127810823 15380990544276607691716235)
        ·
          refine ⟨23071485816414911537574353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15380990544276607691716235 23071485816414911537574353)
          ·
            refine ⟨17303614362311183653180765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23071485816414911537574353 17303614362311183653180765)
            ·
              refine ⟨6488855385866693869942787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17303614362311183653180765 6488855385866693869942787)
              ·
                refine ⟨9733283078800040804914181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6488855385866693869942787 9733283078800040804914181)
                ·
                  refine ⟨1824990577275007650921409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9733283078800040804914181 1824990577275007650921409)
                  ·
                    refine ⟨1368742932956255738191057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1824990577275007650921409 1368742932956255738191057)
                    ·
                      refine ⟨1026557199717191803643293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368742932956255738191057 1026557199717191803643293)
                      ·
                        rfl

theorem cell23_1999213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_1999213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999213 prefixEnd_1999213 := by exact prefixLift 1999213
  have htrace : WordTrace (prefixWord ++ tailWord_1999213) baseStart_1999213 baseEnd_1999213 := by
    simpa [prefixWord, tailWord_1999213, baseEnd_1999213] using wordTrace_append hprefix tailTrace_1999213
  have hstable : (prefixWord ++ tailWord_1999213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999213).length < 2 ^ (prefixWord ++ tailWord_1999213).sum := by decide
  have hdescent : baseEnd_1999213 < baseStart_1999213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999266 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1999266 : Nat := 118140960795 + 1999266 * 2 ^ 59
def prefixEnd_1999266 : Nat := 4983230072969 + 3 ^ 40 * 1999266 * 2
def baseEnd_1999266 : Nat := 342194804730626698760183

theorem tailTrace_1999266 : CollatzResearch.WordTrace tailWord_1999266 prefixEnd_1999266 342194804730626698760183 := by
  unfold tailWord_1999266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18229805393752051073472413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48612814383338802862593101 18229805393752051073472413)
  ·
    refine ⟨6836177022657019152552155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18229805393752051073472413 6836177022657019152552155)
    ·
      refine ⟨10254265533985528728828233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6836177022657019152552155 10254265533985528728828233)
      ·
        refine ⟨7690699150489146546621175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10254265533985528728828233 7690699150489146546621175)
        ·
          refine ⟨11536048725733719819931763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7690699150489146546621175 11536048725733719819931763)
          ·
            refine ⟨17304073088600579729897645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11536048725733719819931763 17304073088600579729897645)
            ·
              refine ⟨6489027408225217398711617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17304073088600579729897645 6489027408225217398711617)
              ·
                refine ⟨4866770556168913049033713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6489027408225217398711617 4866770556168913049033713)
                ·
                  refine ⟨3650077917126684786775285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4866770556168913049033713 3650077917126684786775285)
                  ·
                    refine ⟨342194804730626698760183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3650077917126684786775285 342194804730626698760183)
                    ·
                      rfl

theorem cell23_1999266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1999266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999266 prefixEnd_1999266 := by exact prefixLift 1999266
  have htrace : WordTrace (prefixWord ++ tailWord_1999266) baseStart_1999266 baseEnd_1999266 := by
    simpa [prefixWord, tailWord_1999266, baseEnd_1999266] using wordTrace_append hprefix tailTrace_1999266
  have hstable : (prefixWord ++ tailWord_1999266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999266).length < 2 ^ (prefixWord ++ tailWord_1999266).sum := by decide
  have hdescent : baseEnd_1999266 < baseStart_1999266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999329 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_1999329 : Nat := 118140960795 + 1999329 * 2 ^ 59
def prefixEnd_1999329 : Nat := 4983230072969 + 3 ^ 40 * 1999329 * 2
def baseEnd_1999329 : Nat := 1026616763473113349792759

theorem tailTrace_1999329 : CollatzResearch.WordTrace tailWord_1999329 prefixEnd_1999329 1026616763473113349792759 := by
  unfold tailWord_1999329
  simp only [CollatzResearch.WordTrace]
  refine ⟨72921519373779966053433041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48614346249186644035622027 72921519373779966053433041)
  ·
    refine ⟨54691139530334974540074781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72921519373779966053433041 54691139530334974540074781)
    ·
      refine ⟨20509177323875615452528043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54691139530334974540074781 20509177323875615452528043)
      ·
        refine ⟨30763765985813423178792065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20509177323875615452528043 30763765985813423178792065)
        ·
          refine ⟨23072824489360067384094049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30763765985813423178792065 23072824489360067384094049)
          ·
            refine ⟨17304618367020050538070537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23072824489360067384094049 17304618367020050538070537)
            ·
              refine ⟨12978463775265037903552903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17304618367020050538070537 12978463775265037903552903)
              ·
                refine ⟨19467695662897556855329355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12978463775265037903552903 19467695662897556855329355)
                ·
                  refine ⟨29201543494346335282994033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19467695662897556855329355 29201543494346335282994033)
                  ·
                    refine ⟨21901157620759751462245525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29201543494346335282994033 21901157620759751462245525)
                    ·
                      refine ⟨1026616763473113349792759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21901157620759751462245525 1026616763473113349792759)
                      ·
                        rfl

theorem cell23_1999329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_1999329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999329 prefixEnd_1999329 := by exact prefixLift 1999329
  have htrace : WordTrace (prefixWord ++ tailWord_1999329) baseStart_1999329 baseEnd_1999329 := by
    simpa [prefixWord, tailWord_1999329, baseEnd_1999329] using wordTrace_append hprefix tailTrace_1999329
  have hstable : (prefixWord ++ tailWord_1999329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999329).length < 2 ^ (prefixWord ++ tailWord_1999329).sum := by decide
  have hdescent : baseEnd_1999329 < baseStart_1999329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999339 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 5, 5]
def baseStart_1999339 : Nat := 118140960795 + 1999339 * 2 ^ 59
def prefixEnd_1999339 : Nat := 4983230072969 + 3 ^ 40 * 1999339 * 2
def baseEnd_1999339 : Nat := 342207299426552770222571

theorem tailTrace_1999339 : CollatzResearch.WordTrace tailWord_1999339 prefixEnd_1999339 342207299426552770222571 := by
  unfold tailWord_1999339
  simp only [CollatzResearch.WordTrace]
  refine ⟨72921884103743737761297071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48614589402495825174198047 72921884103743737761297071)
  ·
    refine ⟨109382826155615606641945607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72921884103743737761297071 109382826155615606641945607)
    ·
      refine ⟨164074239233423409962918411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109382826155615606641945607 164074239233423409962918411)
      ·
        refine ⟨246111358850135114944377617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164074239233423409962918411 246111358850135114944377617)
        ·
          refine ⟨184583519137601336208283213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246111358850135114944377617 184583519137601336208283213)
          ·
            refine ⟨69218819676600501078106205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184583519137601336208283213 69218819676600501078106205)
            ·
              refine ⟨25957057378725187904289827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69218819676600501078106205 25957057378725187904289827)
              ·
                refine ⟨38935586068087781856434741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25957057378725187904289827 38935586068087781856434741)
                ·
                  refine ⟨3650211193883229549040757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38935586068087781856434741 3650211193883229549040757)
                  ·
                    refine ⟨342207299426552770222571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3650211193883229549040757 342207299426552770222571)
                    ·
                      rfl

theorem cell23_1999339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 5].length) (baseStart_1999339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999339 prefixEnd_1999339 := by exact prefixLift 1999339
  have htrace : WordTrace (prefixWord ++ tailWord_1999339) baseStart_1999339 baseEnd_1999339 := by
    simpa [prefixWord, tailWord_1999339, baseEnd_1999339] using wordTrace_append hprefix tailTrace_1999339
  have hstable : (prefixWord ++ tailWord_1999339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999339).length < 2 ^ (prefixWord ++ tailWord_1999339).sum := by decide
  have hdescent : baseEnd_1999339 < baseStart_1999339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999356 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_1999356 : Nat := 118140960795 + 1999356 * 2 ^ 59
def prefixEnd_1999356 : Nat := 4983230072969 + 3 ^ 40 * 1999356 * 2
def baseEnd_1999356 : Nat := 342210209150261581385045

theorem tailTrace_1999356 : CollatzResearch.WordTrace tailWord_1999356 prefixEnd_1999356 342210209150261581385045 := by
  unfold tailWord_1999356
  simp only [CollatzResearch.WordTrace]
  refine ⟨36461252072341074832332961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48615002763121433109777281 36461252072341074832332961)
  ·
    refine ⟨27345939054255806124249721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36461252072341074832332961 27345939054255806124249721)
    ·
      refine ⟨20509454290691854593187291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27345939054255806124249721 20509454290691854593187291)
      ·
        refine ⟨30764181436037781889780937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20509454290691854593187291 30764181436037781889780937)
        ·
          refine ⟨23073136077028336417335703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30764181436037781889780937 23073136077028336417335703)
          ·
            refine ⟨34609704115542504626003555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23073136077028336417335703 34609704115542504626003555)
            ·
              refine ⟨51914556173313756939005333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34609704115542504626003555 51914556173313756939005333)
              ·
                refine ⟨2433494820624082356515875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51914556173313756939005333 2433494820624082356515875)
                ·
                  refine ⟨3650242230936123534773813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433494820624082356515875 3650242230936123534773813)
                  ·
                    refine ⟨342210209150261581385045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3650242230936123534773813 342210209150261581385045)
                    ·
                      rfl

theorem cell23_1999356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_1999356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999356 prefixEnd_1999356 := by exact prefixLift 1999356
  have htrace : WordTrace (prefixWord ++ tailWord_1999356) baseStart_1999356 baseEnd_1999356 := by
    simpa [prefixWord, tailWord_1999356, baseEnd_1999356] using wordTrace_append hprefix tailTrace_1999356
  have hstable : (prefixWord ++ tailWord_1999356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999356).length < 2 ^ (prefixWord ++ tailWord_1999356).sum := by decide
  have hdescent : baseEnd_1999356 < baseStart_1999356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999369 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 3, 6]
def baseStart_1999369 : Nat := 118140960795 + 1999369 * 2 ^ 59
def prefixEnd_1999369 : Nat := 4983230072969 + 3 ^ 40 * 1999369 * 2
def baseEnd_1999369 : Nat := 342212434233097731097525

theorem tailTrace_1999369 : CollatzResearch.WordTrace tailWord_1999369 prefixEnd_1999369 342212434233097731097525 := by
  unfold tailWord_1999369
  simp only [CollatzResearch.WordTrace]
  refine ⟨72922978293635052884889161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48615318862423368589926107 72922978293635052884889161)
  ·
    refine ⟨54692233720226289663666871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72922978293635052884889161 54692233720226289663666871)
    ·
      refine ⟨82038350580339434495500307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54692233720226289663666871 82038350580339434495500307)
      ·
        refine ⟨123057525870509151743250461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82038350580339434495500307 123057525870509151743250461)
        ·
          refine ⟨46146572201440931903718923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123057525870509151743250461 46146572201440931903718923)
          ·
            refine ⟨69219858302161397855578385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46146572201440931903718923 69219858302161397855578385)
            ·
              refine ⟨51914893726621048391683789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69219858302161397855578385 51914893726621048391683789)
              ·
                refine ⟨19468085147482893146881421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51914893726621048391683789 19468085147482893146881421)
                ·
                  refine ⟨7300531930306084930080533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19468085147482893146881421 7300531930306084930080533)
                  ·
                    refine ⟨342212434233097731097525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7300531930306084930080533 342212434233097731097525)
                    ·
                      rfl

theorem cell23_1999369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_1999369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999369 prefixEnd_1999369 := by exact prefixLift 1999369
  have htrace : WordTrace (prefixWord ++ tailWord_1999369) baseStart_1999369 baseEnd_1999369 := by
    simpa [prefixWord, tailWord_1999369, baseEnd_1999369] using wordTrace_append hprefix tailTrace_1999369
  have hstable : (prefixWord ++ tailWord_1999369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999369).length < 2 ^ (prefixWord ++ tailWord_1999369).sum := by decide
  have hdescent : baseEnd_1999369 < baseStart_1999369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999410 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_1999410 : Nat := 118140960795 + 1999410 * 2 ^ 59
def prefixEnd_1999410 : Nat := 4983230072969 + 3 ^ 40 * 1999410 * 2
def baseEnd_1999410 : Nat := 1026658355406127532879887

theorem tailTrace_1999410 : CollatzResearch.WordTrace tailWord_1999410 prefixEnd_1999410 1026658355406127532879887 := by
  unfold tailWord_1999410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18231118421621629221782921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48616315790991011258087789 18231118421621629221782921)
  ·
    refine ⟨13673338816216221916337191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18231118421621629221782921 13673338816216221916337191)
    ·
      refine ⟨20510008224324332874505787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13673338816216221916337191 20510008224324332874505787)
      ·
        refine ⟨30765012336486499311758681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20510008224324332874505787 30765012336486499311758681)
        ·
          refine ⟨23073759252364874483819011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30765012336486499311758681 23073759252364874483819011)
          ·
            refine ⟨34610638878547311725728517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23073759252364874483819011 34610638878547311725728517)
            ·
              refine ⟨6489494789727620948574097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34610638878547311725728517 6489494789727620948574097)
              ·
                refine ⟨4867121092295715711430573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6489494789727620948574097 4867121092295715711430573)
                ·
                  refine ⟨1825170409610893391786465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4867121092295715711430573 1825170409610893391786465)
                  ·
                    refine ⟨1368877807208170043839849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1825170409610893391786465 1368877807208170043839849)
                    ·
                      refine ⟨1026658355406127532879887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368877807208170043839849 1026658355406127532879887)
                      ·
                        rfl

theorem cell23_1999410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_1999410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999410 prefixEnd_1999410 := by exact prefixLift 1999410
  have htrace : WordTrace (prefixWord ++ tailWord_1999410) baseStart_1999410 baseEnd_1999410 := by
    simpa [prefixWord, tailWord_1999410, baseEnd_1999410] using wordTrace_append hprefix tailTrace_1999410
  have hstable : (prefixWord ++ tailWord_1999410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999410).length < 2 ^ (prefixWord ++ tailWord_1999410).sum := by decide
  have hdescent : baseEnd_1999410 < baseStart_1999410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999430 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1999430 : Nat := 118140960795 + 1999430 * 2 ^ 59
def prefixEnd_1999430 : Nat := 4983230072969 + 3 ^ 40 * 1999430 * 2
def baseEnd_1999430 : Nat := 1026668625019217454629795

theorem tailTrace_1999430 : CollatzResearch.WordTrace tailWord_1999430 prefixEnd_1999430 1026668625019217454629795 := by
  unfold tailWord_1999430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278912598325439384464367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48616802097609373535239829 2278912598325439384464367)
  ·
    refine ⟨3418368897488159076696551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2278912598325439384464367 3418368897488159076696551)
    ·
      refine ⟨5127553346232238615044827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3418368897488159076696551 5127553346232238615044827)
      ·
        refine ⟨7691330019348357922567241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5127553346232238615044827 7691330019348357922567241)
        ·
          refine ⟨5768497514511268441925431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7691330019348357922567241 5768497514511268441925431)
          ·
            refine ⟨8652746271766902662888147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5768497514511268441925431 8652746271766902662888147)
            ·
              refine ⟨12979119407650353994332221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8652746271766902662888147 12979119407650353994332221)
              ·
                refine ⟨4867169777868882747874583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12979119407650353994332221 4867169777868882747874583)
                ·
                  refine ⟨7300754666803324121811875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4867169777868882747874583 7300754666803324121811875)
                  ·
                    refine ⟨10951132000204986182717813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7300754666803324121811875 10951132000204986182717813)
                    ·
                      refine ⟨1026668625019217454629795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10951132000204986182717813 1026668625019217454629795)
                      ·
                        rfl

theorem cell23_1999430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1999430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999430 prefixEnd_1999430 := by exact prefixLift 1999430
  have htrace : WordTrace (prefixWord ++ tailWord_1999430) baseStart_1999430 baseEnd_1999430 := by
    simpa [prefixWord, tailWord_1999430, baseEnd_1999430] using wordTrace_append hprefix tailTrace_1999430
  have hstable : (prefixWord ++ tailWord_1999430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999430).length < 2 ^ (prefixWord ++ tailWord_1999430).sum := by decide
  have hdescent : baseEnd_1999430 < baseStart_1999430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999460 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_1999460 : Nat := 118140960795 + 1999460 * 2 ^ 59
def prefixEnd_1999460 : Nat := 4983230072969 + 3 ^ 40 * 1999460 * 2
def baseEnd_1999460 : Nat := 1026684029438852337254657

theorem tailTrace_1999460 : CollatzResearch.WordTrace tailWord_1999460 prefixEnd_1999460 1026684029438852337254657 := by
  unfold tailWord_1999460
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463148668152687713225917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48617531557536916950967889 36463148668152687713225917)
  ·
    refine ⟨13673680750557257892459719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36463148668152687713225917 13673680750557257892459719)
    ·
      refine ⟨20510521125835886838689579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13673680750557257892459719 20510521125835886838689579)
      ·
        refine ⟨30765781688753830258034369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20510521125835886838689579 30765781688753830258034369)
        ·
          refine ⟨23074336266565372693525777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30765781688753830258034369 23074336266565372693525777)
          ·
            refine ⟨17305752199924029520144333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23074336266565372693525777 17305752199924029520144333)
            ·
              refine ⟨6489657074971511070054125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17305752199924029520144333 6489657074971511070054125)
              ·
                refine ⟨2433621403114316651270297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6489657074971511070054125 2433621403114316651270297)
                ·
                  refine ⟨1825216052335737488452723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2433621403114316651270297 1825216052335737488452723)
                  ·
                    refine ⟨2737824078503606232679085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1825216052335737488452723 2737824078503606232679085)
                    ·
                      refine ⟨1026684029438852337254657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2737824078503606232679085 1026684029438852337254657)
                      ·
                        rfl

theorem cell23_1999460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_1999460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999460 prefixEnd_1999460 := by exact prefixLift 1999460
  have htrace : WordTrace (prefixWord ++ tailWord_1999460) baseStart_1999460 baseEnd_1999460 := by
    simpa [prefixWord, tailWord_1999460, baseEnd_1999460] using wordTrace_append hprefix tailTrace_1999460
  have hstable : (prefixWord ++ tailWord_1999460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999460).length < 2 ^ (prefixWord ++ tailWord_1999460).sum := by decide
  have hdescent : baseEnd_1999460 < baseStart_1999460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999464 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1999464 : Nat := 118140960795 + 1999464 * 2 ^ 59
def prefixEnd_1999464 : Nat := 4983230072969 + 3 ^ 40 * 1999464 * 2
def baseEnd_1999464 : Nat := 1026686083361470321604639

theorem tailTrace_1999464 : CollatzResearch.WordTrace tailWord_1999464 prefixEnd_1999464 1026686083361470321604639 := by
  unfold tailWord_1999464
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463221614145442054798723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48617628818860589406398297 36463221614145442054798723)
  ·
    refine ⟨54694832421218163082198085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36463221614145442054798723 54694832421218163082198085)
    ·
      refine ⟨10255281078978405577912141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54694832421218163082198085 10255281078978405577912141)
      ·
        refine ⟨3845730404616902091717053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10255281078978405577912141 3845730404616902091717053)
        ·
          refine ⟨1442148901731338284393895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3845730404616902091717053 1442148901731338284393895)
          ·
            refine ⟨2163223352597007426590843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442148901731338284393895 2163223352597007426590843)
            ·
              refine ⟨3244835028895511139886265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163223352597007426590843 3244835028895511139886265)
              ·
                refine ⟨2433626271671633354914699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3244835028895511139886265 2433626271671633354914699)
                ·
                  refine ⟨3650439407507450032372049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433626271671633354914699 3650439407507450032372049)
                  ·
                    refine ⟨2737829555630587524279037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3650439407507450032372049 2737829555630587524279037)
                    ·
                      refine ⟨1026686083361470321604639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2737829555630587524279037 1026686083361470321604639)
                      ·
                        rfl

theorem cell23_1999464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1999464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999464 prefixEnd_1999464 := by exact prefixLift 1999464
  have htrace : WordTrace (prefixWord ++ tailWord_1999464) baseStart_1999464 baseEnd_1999464 := by
    simpa [prefixWord, tailWord_1999464, baseEnd_1999464] using wordTrace_append hprefix tailTrace_1999464
  have hstable : (prefixWord ++ tailWord_1999464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999464).length < 2 ^ (prefixWord ++ tailWord_1999464).sum := by decide
  have hdescent : baseEnd_1999464 < baseStart_1999464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999517 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 2, 2, 2]
def baseStart_1999517 : Nat := 118140960795 + 1999517 * 2 ^ 59
def prefixEnd_1999517 : Nat := 4983230072969 + 3 ^ 40 * 1999517 * 2
def baseEnd_1999517 : Nat := 1026713297836158614241895

theorem tailTrace_1999517 : CollatzResearch.WordTrace tailWord_1999517 prefixEnd_1999517 1026713297836158614241895 := by
  unfold tailWord_1999517
  simp only [CollatzResearch.WordTrace]
  refine ⟨72928376297098874161276805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48618917531399249440851203 72928376297098874161276805)
  ·
    refine ⟨13674070555706038905239401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72928376297098874161276805 13674070555706038905239401)
    ·
      refine ⟨10255552916779529178929551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13674070555706038905239401 10255552916779529178929551)
      ·
        refine ⟨15383329375169293768394327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10255552916779529178929551 15383329375169293768394327)
        ·
          refine ⟨23074994062753940652591491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15383329375169293768394327 23074994062753940652591491)
          ·
            refine ⟨34612491094130910978887237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23074994062753940652591491 34612491094130910978887237)
            ·
              refine ⟨6489842080149545808541357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34612491094130910978887237 6489842080149545808541357)
              ·
                refine ⟨2433690780056079678203009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6489842080149545808541357 2433690780056079678203009)
                ·
                  refine ⟨1825268085042059758652257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2433690780056079678203009 1825268085042059758652257)
                  ·
                    refine ⟨1368951063781544818989193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1825268085042059758652257 1368951063781544818989193)
                    ·
                      refine ⟨1026713297836158614241895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1368951063781544818989193 1026713297836158614241895)
                      ·
                        rfl

theorem cell23_1999517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_1999517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999517 prefixEnd_1999517 := by exact prefixLift 1999517
  have htrace : WordTrace (prefixWord ++ tailWord_1999517) baseStart_1999517 baseEnd_1999517 := by
    simpa [prefixWord, tailWord_1999517, baseEnd_1999517] using wordTrace_append hprefix tailTrace_1999517
  have hstable : (prefixWord ++ tailWord_1999517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999517).length < 2 ^ (prefixWord ++ tailWord_1999517).sum := by decide
  have hdescent : baseEnd_1999517 < baseStart_1999517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999593 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 3]
def baseStart_1999593 : Nat := 118140960795 + 1999593 * 2 ^ 59
def prefixEnd_1999593 : Nat := 4983230072969 + 3 ^ 40 * 1999593 * 2
def baseEnd_1999593 : Nat := 1026752322365900316891545

theorem tailTrace_1999593 : CollatzResearch.WordTrace tailWord_1999593 prefixEnd_1999593 1026752322365900316891545 := by
  unfold tailWord_1999593
  simp only [CollatzResearch.WordTrace]
  refine ⟨72931148244823539141043433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48620765496549026094028955 72931148244823539141043433)
  ·
    refine ⟨54698361183617654355782575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72931148244823539141043433 54698361183617654355782575)
    ·
      refine ⟨82047541775426481533673863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54698361183617654355782575 82047541775426481533673863)
      ·
        refine ⟨123071312663139722300510795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82047541775426481533673863 123071312663139722300510795)
        ·
          refine ⟨184606968994709583450766193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123071312663139722300510795 184606968994709583450766193)
          ·
            refine ⟨138455226746032187588074645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184606968994709583450766193 138455226746032187588074645)
            ·
              refine ⟨6490088753720258793190999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 138455226746032187588074645 6490088753720258793190999)
              ·
                refine ⟨9735133130580388189786499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490088753720258793190999 9735133130580388189786499)
                ·
                  refine ⟨14602699695870582284679749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9735133130580388189786499 14602699695870582284679749)
                  ·
                    refine ⟨2738006192975734178377453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14602699695870582284679749 2738006192975734178377453)
                    ·
                      refine ⟨1026752322365900316891545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2738006192975734178377453 1026752322365900316891545)
                      ·
                        rfl

theorem cell23_1999593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_1999593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999593 prefixEnd_1999593 := by exact prefixLift 1999593
  have htrace : WordTrace (prefixWord ++ tailWord_1999593) baseStart_1999593 baseEnd_1999593 := by
    simpa [prefixWord, tailWord_1999593, baseEnd_1999593] using wordTrace_append hprefix tailTrace_1999593
  have hstable : (prefixWord ++ tailWord_1999593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999593).length < 2 ^ (prefixWord ++ tailWord_1999593).sum := by decide
  have hdescent : baseEnd_1999593 < baseStart_1999593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999604 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1999604 : Nat := 118140960795 + 1999604 * 2 ^ 59
def prefixEnd_1999604 : Nat := 4983230072969 + 3 ^ 40 * 1999604 * 2
def baseEnd_1999604 : Nat := 342252656884366591284665

theorem tailTrace_1999604 : CollatzResearch.WordTrace tailWord_1999604 prefixEnd_1999604 342252656884366591284665 := by
  unfold tailWord_1999604
  simp only [CollatzResearch.WordTrace]
  refine ⟨36465774723891844009846933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48621032965189125346462577 36465774723891844009846933)
  ·
    refine ⟨1709333190182430187961575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36465774723891844009846933 1709333190182430187961575)
    ·
      refine ⟨2563999785273645281942363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1709333190182430187961575 2563999785273645281942363)
      ·
        refine ⟨3845999677910467922913545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2563999785273645281942363 3845999677910467922913545)
        ·
          refine ⟨2884499758432850942185159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3845999677910467922913545 2884499758432850942185159)
          ·
            refine ⟨4326749637649276413277739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884499758432850942185159 4326749637649276413277739)
            ·
              refine ⟨6490124456473914619916609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326749637649276413277739 6490124456473914619916609)
              ·
                refine ⟨4867593342355435964937457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6490124456473914619916609 4867593342355435964937457)
                ·
                  refine ⟨3650695006766576973703093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4867593342355435964937457 3650695006766576973703093)
                  ·
                    refine ⟨342252656884366591284665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3650695006766576973703093 342252656884366591284665)
                    ·
                      rfl

theorem cell23_1999604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1999604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999604 prefixEnd_1999604 := by exact prefixLift 1999604
  have htrace : WordTrace (prefixWord ++ tailWord_1999604) baseStart_1999604 baseEnd_1999604 := by
    simpa [prefixWord, tailWord_1999604, baseEnd_1999604] using wordTrace_append hprefix tailTrace_1999604
  have hstable : (prefixWord ++ tailWord_1999604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999604).length < 2 ^ (prefixWord ++ tailWord_1999604).sum := by decide
  have hdescent : baseEnd_1999604 < baseStart_1999604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999613 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 6]
def baseStart_1999613 : Nat := 118140960795 + 1999613 * 2 ^ 59
def prefixEnd_1999613 : Nat := 4983230072969 + 3 ^ 40 * 1999613 * 2
def baseEnd_1999613 : Nat := 114084732442110026515717

theorem tailTrace_1999613 : CollatzResearch.WordTrace tailWord_1999613 prefixEnd_1999613 114084732442110026515717 := by
  unfold tailWord_1999613
  simp only [CollatzResearch.WordTrace]
  refine ⟨72931877704751082556771493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48621251803167388371180995 72931877704751082556771493)
  ·
    refine ⟨13674727069640827979394655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72931877704751082556771493 13674727069640827979394655)
    ·
      refine ⟨20512090604461241969091983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13674727069640827979394655 20512090604461241969091983)
      ·
        refine ⟨30768135906691862953637975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20512090604461241969091983 30768135906691862953637975)
        ·
          refine ⟨46152203860037794430456963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30768135906691862953637975 46152203860037794430456963)
          ·
            refine ⟨69228305790056691645685445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46152203860037794430456963 69228305790056691645685445)
            ·
              refine ⟨12980307335635629683566021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69228305790056691645685445 12980307335635629683566021)
              ·
                refine ⟨2433807625431680565668629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12980307335635629683566021 2433807625431680565668629)
                ·
                  refine ⟨114084732442110026515717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2433807625431680565668629 114084732442110026515717)
                  ·
                    rfl

theorem cell23_1999613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_1999613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999613 prefixEnd_1999613 := by exact prefixLift 1999613
  have htrace : WordTrace (prefixWord ++ tailWord_1999613) baseStart_1999613 baseEnd_1999613 := by
    simpa [prefixWord, tailWord_1999613, baseEnd_1999613] using wordTrace_append hprefix tailTrace_1999613
  have hstable : (prefixWord ++ tailWord_1999613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999613).length < 2 ^ (prefixWord ++ tailWord_1999613).sum := by decide
  have hdescent : baseEnd_1999613 < baseStart_1999613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999640 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1999640 : Nat := 118140960795 + 1999640 * 2 ^ 59
def prefixEnd_1999640 : Nat := 4983230072969 + 3 ^ 40 * 1999640 * 2
def baseEnd_1999640 : Nat := 1026776455956661633003829

theorem tailTrace_1999640 : CollatzResearch.WordTrace tailWord_1999640 prefixEnd_1999640 1026776455956661633003829 := by
  unfold tailWord_1999640
  simp only [CollatzResearch.WordTrace]
  refine ⟨36466431237826633084002187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48621908317102177445336249 36466431237826633084002187)
  ·
    refine ⟨54699646856739949626003281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36466431237826633084002187 54699646856739949626003281)
    ·
      refine ⟨41024735142554962219502461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54699646856739949626003281 41024735142554962219502461)
      ·
        refine ⟨15384275678458110832313423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41024735142554962219502461 15384275678458110832313423)
        ·
          refine ⟨23076413517687166248470135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384275678458110832313423 23076413517687166248470135)
          ·
            refine ⟨34614620276530749372705203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23076413517687166248470135 34614620276530749372705203)
            ·
              refine ⟨51921930414796124059057805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34614620276530749372705203 51921930414796124059057805)
              ·
                refine ⟨19470723905548546522146677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51921930414796124059057805 19470723905548546522146677)
                ·
                  refine ⟨1825380366145176236451251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19470723905548546522146677 1825380366145176236451251)
                  ·
                    refine ⟨2738070549217764354676877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1825380366145176236451251 2738070549217764354676877)
                    ·
                      refine ⟨1026776455956661633003829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2738070549217764354676877 1026776455956661633003829)
                      ·
                        rfl

theorem cell23_1999640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1999640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999640 prefixEnd_1999640 := by exact prefixLift 1999640
  have htrace : WordTrace (prefixWord ++ tailWord_1999640) baseStart_1999640 baseEnd_1999640 := by
    simpa [prefixWord, tailWord_1999640, baseEnd_1999640] using wordTrace_append hprefix tailTrace_1999640
  have hstable : (prefixWord ++ tailWord_1999640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999640).length < 2 ^ (prefixWord ++ tailWord_1999640).sum := by decide
  have hdescent : baseEnd_1999640 < baseStart_1999640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999663 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_1999663 : Nat := 118140960795 + 1999663 * 2 ^ 59
def prefixEnd_1999663 : Nat := 4983230072969 + 3 ^ 40 * 1999663 * 2
def baseEnd_1999663 : Nat := 1026788266011715043016223

theorem tailTrace_1999663 : CollatzResearch.WordTrace tailWord_1999663 prefixEnd_1999663 1026788266011715043016223 := by
  unfold tailWord_1999663
  simp only [CollatzResearch.WordTrace]
  refine ⟨72933701354569941096091643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48622467569713294064061095 72933701354569941096091643)
  ·
    refine ⟨109400552031854911644137465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72933701354569941096091643 109400552031854911644137465)
    ·
      refine ⟨82050414023891183733103099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109400552031854911644137465 82050414023891183733103099)
      ·
        refine ⟨123075621035836775599654649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82050414023891183733103099 123075621035836775599654649)
        ·
          refine ⟨92306715776877581699740987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123075621035836775599654649 92306715776877581699740987)
          ·
            refine ⟨138460073665316372549611481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92306715776877581699740987 138460073665316372549611481)
            ·
              refine ⟨103845055248987279412208611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138460073665316372549611481 103845055248987279412208611)
              ·
                refine ⟨155767582873480919118312917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103845055248987279412208611 155767582873480919118312917)
                ·
                  refine ⟨3650802723597209041835459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 155767582873480919118312917 3650802723597209041835459)
                  ·
                    refine ⟨5476204085395813562753189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3650802723597209041835459 5476204085395813562753189)
                    ·
                      refine ⟨1026788266011715043016223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5476204085395813562753189 1026788266011715043016223)
                      ·
                        rfl

theorem cell23_1999663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_1999663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999663 prefixEnd_1999663 := by exact prefixLift 1999663
  have htrace : WordTrace (prefixWord ++ tailWord_1999663) baseStart_1999663 baseEnd_1999663 := by
    simpa [prefixWord, tailWord_1999663, baseEnd_1999663] using wordTrace_append hprefix tailTrace_1999663
  have hstable : (prefixWord ++ tailWord_1999663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999663).length < 2 ^ (prefixWord ++ tailWord_1999663).sum := by decide
  have hdescent : baseEnd_1999663 < baseStart_1999663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999667 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 2, 3, 2]
def baseStart_1999667 : Nat := 118140960795 + 1999667 * 2 ^ 59
def prefixEnd_1999667 : Nat := 4983230072969 + 3 ^ 40 * 1999667 * 2
def baseEnd_1999667 : Nat := 1026790319934333027366205

theorem tailTrace_1999667 : CollatzResearch.WordTrace tailWord_1999667 prefixEnd_1999667 1026790319934333027366205 := by
  unfold tailWord_1999667
  simp only [CollatzResearch.WordTrace]
  refine ⟨72933847246555449779237255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48622564831036966519491503 72933847246555449779237255)
  ·
    refine ⟨109400770869833174668855883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72933847246555449779237255 109400770869833174668855883)
    ·
      refine ⟨164101156304749762003283825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109400770869833174668855883 164101156304749762003283825)
      ·
        refine ⟨123075867228562321502462869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164101156304749762003283825 123075867228562321502462869)
        ·
          refine ⟨5769181276338858820427947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123075867228562321502462869 5769181276338858820427947)
          ·
            refine ⟨8653771914508288230641921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769181276338858820427947 8653771914508288230641921)
            ·
              refine ⟨6490328935881216172981441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8653771914508288230641921 6490328935881216172981441)
              ·
                refine ⟨4867746701910912129736081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6490328935881216172981441 4867746701910912129736081)
                ·
                  refine ⟨3650810026433184097302061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4867746701910912129736081 3650810026433184097302061)
                  ·
                    refine ⟨1369053759912444036488273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3650810026433184097302061 1369053759912444036488273)
                    ·
                      refine ⟨1026790319934333027366205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369053759912444036488273 1026790319934333027366205)
                      ·
                        rfl

theorem cell23_1999667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 3, 2].length) (baseStart_1999667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999667 prefixEnd_1999667 := by exact prefixLift 1999667
  have htrace : WordTrace (prefixWord ++ tailWord_1999667) baseStart_1999667 baseEnd_1999667 := by
    simpa [prefixWord, tailWord_1999667, baseEnd_1999667] using wordTrace_append hprefix tailTrace_1999667
  have hstable : (prefixWord ++ tailWord_1999667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999667).length < 2 ^ (prefixWord ++ tailWord_1999667).sum := by decide
  have hdescent : baseEnd_1999667 < baseStart_1999667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999668 : List Nat := [2, 5, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_1999668 : Nat := 118140960795 + 1999668 * 2 ^ 59
def prefixEnd_1999668 : Nat := 4983230072969 + 3 ^ 40 * 1999668 * 2
def baseEnd_1999668 : Nat := 342263611138329174484567

theorem tailTrace_1999668 : CollatzResearch.WordTrace tailWord_1999668 prefixEnd_1999668 342263611138329174484567 := by
  unfold tailWord_1999668
  simp only [CollatzResearch.WordTrace]
  refine ⟨36466941859775913475011829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48622589146367884633349105 36466941859775913475011829)
  ·
    refine ⟨3418775799353991888282359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36466941859775913475011829 3418775799353991888282359)
    ·
      refine ⟨5128163699030987832423539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3418775799353991888282359 5128163699030987832423539)
      ·
        refine ⟨7692245548546481748635309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128163699030987832423539 7692245548546481748635309)
        ·
          refine ⟨2884592080704930655738241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7692245548546481748635309 2884592080704930655738241)
          ·
            refine ⟨2163444060528697991803681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2884592080704930655738241 2163444060528697991803681)
            ·
              refine ⟨1622583045396523493852761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163444060528697991803681 1622583045396523493852761)
              ·
                refine ⟨1216937284047392620389571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622583045396523493852761 1216937284047392620389571)
                ·
                  refine ⟨1825405926071088930584357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216937284047392620389571 1825405926071088930584357)
                  ·
                    refine ⟨342263611138329174484567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1825405926071088930584357 342263611138329174484567)
                    ·
                      rfl

theorem cell23_1999668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_1999668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999668 prefixEnd_1999668 := by exact prefixLift 1999668
  have htrace : WordTrace (prefixWord ++ tailWord_1999668) baseStart_1999668 baseEnd_1999668 := by
    simpa [prefixWord, tailWord_1999668, baseEnd_1999668] using wordTrace_append hprefix tailTrace_1999668
  have hstable : (prefixWord ++ tailWord_1999668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999668).length < 2 ^ (prefixWord ++ tailWord_1999668).sum := by decide
  have hdescent : baseEnd_1999668 < baseStart_1999668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999683 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 5]
def baseStart_1999683 : Nat := 118140960795 + 1999683 * 2 ^ 59
def prefixEnd_1999683 : Nat := 4983230072969 + 3 ^ 40 * 1999683 * 2
def baseEnd_1999683 : Nat := 1026798535624804964766131

theorem tailTrace_1999683 : CollatzResearch.WordTrace tailWord_1999683 prefixEnd_1999683 1026798535624804964766131 := by
  unfold tailWord_1999683
  simp only [CollatzResearch.WordTrace]
  refine ⟨72934430814497484511819703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48622953876331656341213135 72934430814497484511819703)
  ·
    refine ⟨109401646221746226767729555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72934430814497484511819703 109401646221746226767729555)
    ·
      refine ⟨164102469332619340151594333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109401646221746226767729555 164102469332619340151594333)
      ·
        refine ⟨61538425999732252556847875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164102469332619340151594333 61538425999732252556847875)
        ·
          refine ⟨92307638999598378835271813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61538425999732252556847875 92307638999598378835271813)
          ·
            refine ⟨17307682312424696031613465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92307638999598378835271813 17307682312424696031613465)
            ·
              refine ⟨12980761734318522023710099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17307682312424696031613465 12980761734318522023710099)
              ·
                refine ⟨19471142601477783035565149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12980761734318522023710099 19471142601477783035565149)
                ·
                  refine ⟨7301678475554168638336931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19471142601477783035565149 7301678475554168638336931)
                  ·
                    refine ⟨10952517713331252957505397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7301678475554168638336931 10952517713331252957505397)
                    ·
                      refine ⟨1026798535624804964766131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10952517713331252957505397 1026798535624804964766131)
                      ·
                        rfl

theorem cell23_1999683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_1999683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999683 prefixEnd_1999683 := by exact prefixLift 1999683
  have htrace : WordTrace (prefixWord ++ tailWord_1999683) baseStart_1999683 baseEnd_1999683 := by
    simpa [prefixWord, tailWord_1999683, baseEnd_1999683] using wordTrace_append hprefix tailTrace_1999683
  have hstable : (prefixWord ++ tailWord_1999683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999683).length < 2 ^ (prefixWord ++ tailWord_1999683).sum := by decide
  have hdescent : baseEnd_1999683 < baseStart_1999683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999714 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1999714 : Nat := 118140960795 + 1999714 * 2 ^ 59
def prefixEnd_1999714 : Nat := 4983230072969 + 3 ^ 40 * 1999714 * 2
def baseEnd_1999714 : Nat := 1026814453525094343478489

theorem tailTrace_1999714 : CollatzResearch.WordTrace tailWord_1999714 prefixEnd_1999714 1026814453525094343478489 := by
  unfold tailWord_1999714
  simp only [CollatzResearch.WordTrace]
  refine ⟨18233890369346294201549549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48623707651590117870798797 18233890369346294201549549)
  ·
    refine ⟨6837708888504860325581081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18233890369346294201549549 6837708888504860325581081)
    ·
      refine ⟨5128281666378645244185811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6837708888504860325581081 5128281666378645244185811)
      ·
        refine ⟨7692422499567967866278717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5128281666378645244185811 7692422499567967866278717)
        ·
          refine ⟨2884658437337987949854519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7692422499567967866278717 2884658437337987949854519)
          ·
            refine ⟨4326987656006981924781779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884658437337987949854519 4326987656006981924781779)
            ·
              refine ⟨6490481484010472887172669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326987656006981924781779 6490481484010472887172669)
              ·
                refine ⟨2433930556503927332689751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6490481484010472887172669 2433930556503927332689751)
                ·
                  refine ⟨3650895834755890999034627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2433930556503927332689751 3650895834755890999034627)
                  ·
                    refine ⟨5476343752133836498551941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3650895834755890999034627 5476343752133836498551941)
                    ·
                      refine ⟨1026814453525094343478489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5476343752133836498551941 1026814453525094343478489)
                      ·
                        rfl

theorem cell23_1999714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1999714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999714 prefixEnd_1999714 := by exact prefixLift 1999714
  have htrace : WordTrace (prefixWord ++ tailWord_1999714) baseStart_1999714 baseEnd_1999714 := by
    simpa [prefixWord, tailWord_1999714, baseEnd_1999714] using wordTrace_append hprefix tailTrace_1999714
  have hstable : (prefixWord ++ tailWord_1999714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999714).length < 2 ^ (prefixWord ++ tailWord_1999714).sum := by decide
  have hdescent : baseEnd_1999714 < baseStart_1999714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999730 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 3, 3, 3]
def baseStart_1999730 : Nat := 118140960795 + 1999730 * 2 ^ 59
def prefixEnd_1999730 : Nat := 4983230072969 + 3 ^ 40 * 1999730 * 2
def baseEnd_1999730 : Nat := 1026822669215566280878415

theorem tailTrace_1999730 : CollatzResearch.WordTrace tailWord_1999730 prefixEnd_1999730 1026822669215566280878415 := by
  unfold tailWord_1999730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18234036261331802884695161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48624096696884807692520429 18234036261331802884695161)
  ·
    refine ⟨13675527195998852163521371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18234036261331802884695161 13675527195998852163521371)
    ·
      refine ⟨20513290793998278245282057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13675527195998852163521371 20513290793998278245282057)
      ·
        refine ⟨15384968095498708683961543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20513290793998278245282057 15384968095498708683961543)
        ·
          refine ⟨23077452143248063025942315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15384968095498708683961543 23077452143248063025942315)
          ·
            refine ⟨34616178214872094538913473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23077452143248063025942315 34616178214872094538913473)
            ·
              refine ⟨25962133661154070904185105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34616178214872094538913473 25962133661154070904185105)
              ·
                refine ⟨19471600245865553178138829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25962133661154070904185105 19471600245865553178138829)
                ·
                  refine ⟨7301850092199582441802061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19471600245865553178138829 7301850092199582441802061)
                  ·
                    refine ⟨2738193784574843415675773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7301850092199582441802061 2738193784574843415675773)
                    ·
                      refine ⟨1026822669215566280878415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2738193784574843415675773 1026822669215566280878415)
                      ·
                        rfl

theorem cell23_1999730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_1999730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999730 prefixEnd_1999730 := by exact prefixLift 1999730
  have htrace : WordTrace (prefixWord ++ tailWord_1999730) baseStart_1999730 baseEnd_1999730 := by
    simpa [prefixWord, tailWord_1999730, baseEnd_1999730] using wordTrace_append hprefix tailTrace_1999730
  have hstable : (prefixWord ++ tailWord_1999730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999730).length < 2 ^ (prefixWord ++ tailWord_1999730).sum := by decide
  have hdescent : baseEnd_1999730 < baseStart_1999730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999763 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 4, 6]
def baseStart_1999763 : Nat := 118140960795 + 1999763 * 2 ^ 59
def prefixEnd_1999763 : Nat := 4983230072969 + 3 ^ 40 * 1999763 * 2
def baseEnd_1999763 : Nat := 342279871359054883921921

theorem tailTrace_1999763 : CollatzResearch.WordTrace tailWord_1999763 prefixEnd_1999763 342279871359054883921921 := by
  unfold tailWord_1999763
  simp only [CollatzResearch.WordTrace]
  refine ⟨72937348654207658174731943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48624899102805105449821295 72937348654207658174731943)
  ·
    refine ⟨109406022981311487262097915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72937348654207658174731943 109406022981311487262097915)
    ·
      refine ⟨164109034471967230893146873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109406022981311487262097915 164109034471967230893146873)
      ·
        refine ⟨123081775853975423169860155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164109034471967230893146873 123081775853975423169860155)
        ·
          refine ⟨184622663780963134754790233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123081775853975423169860155 184622663780963134754790233)
          ·
            refine ⟨138466997835722351066092675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184622663780963134754790233 138466997835722351066092675)
            ·
              refine ⟨207700496753583526599139013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138466997835722351066092675 207700496753583526599139013)
              ·
                refine ⟨38943843141296911237338565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 207700496753583526599139013 38943843141296911237338565)
                ·
                  refine ⟨7301970588993170857000981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38943843141296911237338565 7301970588993170857000981)
                  ·
                    refine ⟨342279871359054883921921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7301970588993170857000981 342279871359054883921921)
                    ·
                      rfl

theorem cell23_1999763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 6].length) (baseStart_1999763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999763 prefixEnd_1999763 := by exact prefixLift 1999763
  have htrace : WordTrace (prefixWord ++ tailWord_1999763) baseStart_1999763 baseEnd_1999763 := by
    simpa [prefixWord, tailWord_1999763, baseEnd_1999763] using wordTrace_append hprefix tailTrace_1999763
  have hstable : (prefixWord ++ tailWord_1999763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999763).length < 2 ^ (prefixWord ++ tailWord_1999763).sum := by decide
  have hdescent : baseEnd_1999763 < baseStart_1999763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999803 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 7]
def baseStart_1999803 : Nat := 118140960795 + 1999803 * 2 ^ 59
def prefixEnd_1999803 : Nat := 4983230072969 + 3 ^ 40 * 1999803 * 2
def baseEnd_1999803 : Nat := 1026860153303344495265579

theorem tailTrace_1999803 : CollatzResearch.WordTrace tailWord_1999803 prefixEnd_1999803 1026860153303344495265579 := by
  unfold tailWord_1999803
  simp only [CollatzResearch.WordTrace]
  refine ⟨72938807574062745006188063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48625871716041830004125375 72938807574062745006188063)
  ·
    refine ⟨109408211361094117509282095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72938807574062745006188063 109408211361094117509282095)
    ·
      refine ⟨164112317041641176263923143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109408211361094117509282095 164112317041641176263923143)
      ·
        refine ⟨246168475562461764395884715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164112317041641176263923143 246168475562461764395884715)
        ·
          refine ⟨369252713343692646593827073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246168475562461764395884715 369252713343692646593827073)
          ·
            refine ⟨276939535007769484945370305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369252713343692646593827073 276939535007769484945370305)
            ·
              refine ⟨207704651255827113709027729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 276939535007769484945370305 207704651255827113709027729)
              ·
                refine ⟨155778488441870335281770797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207704651255827113709027729 155778488441870335281770797)
                ·
                  refine ⟨58416933165701375730664049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155778488441870335281770797 58416933165701375730664049)
                  ·
                    refine ⟨43812699874276031797998037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58416933165701375730664049 43812699874276031797998037)
                    ·
                      refine ⟨1026860153303344495265579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43812699874276031797998037 1026860153303344495265579)
                      ·
                        rfl

theorem cell23_1999803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_1999803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999803 prefixEnd_1999803 := by exact prefixLift 1999803
  have htrace : WordTrace (prefixWord ++ tailWord_1999803) baseStart_1999803 baseEnd_1999803 := by
    simpa [prefixWord, tailWord_1999803, baseEnd_1999803] using wordTrace_append hprefix tailTrace_1999803
  have hstable : (prefixWord ++ tailWord_1999803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999803).length < 2 ^ (prefixWord ++ tailWord_1999803).sum := by decide
  have hdescent : baseEnd_1999803 < baseStart_1999803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999854 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3]
def baseStart_1999854 : Nat := 118140960795 + 1999854 * 2 ^ 59
def prefixEnd_1999854 : Nat := 4983230072969 + 3 ^ 40 * 1999854 * 2
def baseEnd_1999854 : Nat := 1026886340816723795727845

theorem tailTrace_1999854 : CollatzResearch.WordTrace tailWord_1999854 prefixEnd_1999854 1026886340816723795727845 := by
  unfold tailWord_1999854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9117583462109747589536827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48627111797918653810863077 9117583462109747589536827)
  ·
    refine ⟨13676375193164621384305241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9117583462109747589536827 13676375193164621384305241)
    ·
      refine ⟨10257281394873466038228931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13676375193164621384305241 10257281394873466038228931)
      ·
        refine ⟨15385922092310199057343397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10257281394873466038228931 15385922092310199057343397)
        ·
          refine ⟨2884860392308162323251887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15385922092310199057343397 2884860392308162323251887)
          ·
            refine ⟨4327290588462243484877831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884860392308162323251887 4327290588462243484877831)
            ·
              refine ⟨6490935882693365227316747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327290588462243484877831 6490935882693365227316747)
              ·
                refine ⟨9736403824040047840975121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6490935882693365227316747 9736403824040047840975121)
                ·
                  refine ⟨7302302868030035880731341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736403824040047840975121 7302302868030035880731341)
                  ·
                    refine ⟨2738363575511263455274253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7302302868030035880731341 2738363575511263455274253)
                    ·
                      refine ⟨1026886340816723795727845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2738363575511263455274253 1026886340816723795727845)
                      ·
                        rfl

theorem cell23_1999854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_1999854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999854 prefixEnd_1999854 := by exact prefixLift 1999854
  have htrace : WordTrace (prefixWord ++ tailWord_1999854) baseStart_1999854 baseEnd_1999854 := by
    simpa [prefixWord, tailWord_1999854, baseEnd_1999854] using wordTrace_append hprefix tailTrace_1999854
  have hstable : (prefixWord ++ tailWord_1999854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999854).length < 2 ^ (prefixWord ++ tailWord_1999854).sum := by decide
  have hdescent : baseEnd_1999854 < baseStart_1999854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999877 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 1, 6, 2]
def baseStart_1999877 : Nat := 118140960795 + 1999877 * 2 ^ 59
def prefixEnd_1999877 : Nat := 4983230072969 + 3 ^ 40 * 1999877 * 2
def baseEnd_1999877 : Nat := 1026898150871777205740239

theorem tailTrace_1999877 : CollatzResearch.WordTrace tailWord_1999877 prefixEnd_1999877 1026898150871777205740239 := by
  unfold tailWord_1999877
  simp only [CollatzResearch.WordTrace]
  refine ⟨72941506575794655644381885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48627671050529770429587923 72941506575794655644381885)
  ·
    refine ⟨27353064965922995866643207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72941506575794655644381885 27353064965922995866643207)
    ·
      refine ⟨41029597448884493799964811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27353064965922995866643207 41029597448884493799964811)
      ·
        refine ⟨61544396173326740699947217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41029597448884493799964811 61544396173326740699947217)
        ·
          refine ⟨46158297129995055524960413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61544396173326740699947217 46158297129995055524960413)
          ·
            refine ⟨17309361423748145821860155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46158297129995055524960413 17309361423748145821860155)
            ·
              refine ⟨25964042135622218732790233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17309361423748145821860155 25964042135622218732790233)
              ·
                refine ⟨19473031601716664049592675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25964042135622218732790233 19473031601716664049592675)
                ·
                  refine ⟨29209547402574996074389013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19473031601716664049592675 29209547402574996074389013)
                  ·
                    refine ⟨1369197534495702940986985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29209547402574996074389013 1369197534495702940986985)
                    ·
                      refine ⟨1026898150871777205740239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369197534495702940986985 1026898150871777205740239)
                      ·
                        rfl

theorem cell23_1999877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_1999877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999877 prefixEnd_1999877 := by exact prefixLift 1999877
  have htrace : WordTrace (prefixWord ++ tailWord_1999877) baseStart_1999877 baseEnd_1999877 := by
    simpa [prefixWord, tailWord_1999877, baseEnd_1999877] using wordTrace_append hprefix tailTrace_1999877
  have hstable : (prefixWord ++ tailWord_1999877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999877).length < 2 ^ (prefixWord ++ tailWord_1999877).sum := by decide
  have hdescent : baseEnd_1999877 < baseStart_1999877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999897 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 3]
def baseStart_1999897 : Nat := 118140960795 + 1999897 * 2 ^ 59
def prefixEnd_1999897 : Nat := 4983230072969 + 3 ^ 40 * 1999897 * 2
def baseEnd_1999897 : Nat := 1026908420484867127490147

theorem tailTrace_1999897 : CollatzResearch.WordTrace tailWord_1999897 prefixEnd_1999897 1026908420484867127490147 := by
  unfold tailWord_1999897
  simp only [CollatzResearch.WordTrace]
  refine ⟨72942236035722199060109945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48628157357148132706739963 72942236035722199060109945)
  ·
    refine ⟨54706677026791649295082459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72942236035722199060109945 54706677026791649295082459)
    ·
      refine ⟨82060015540187473942623689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54706677026791649295082459 82060015540187473942623689)
      ·
        refine ⟨61545011655140605456967767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82060015540187473942623689 61545011655140605456967767)
        ·
          refine ⟨92317517482710908185451651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61545011655140605456967767 92317517482710908185451651)
          ·
            refine ⟨138476276224066362278177477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92317517482710908185451651 138476276224066362278177477)
            ·
              refine ⟨25964301792012442927158277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138476276224066362278177477 25964301792012442927158277)
              ·
                refine ⟨4868306586002333048842177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25964301792012442927158277 4868306586002333048842177)
                ·
                  refine ⟨3651229939501749786631633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4868306586002333048842177 3651229939501749786631633)
                  ·
                    refine ⟨2738422454626312339973725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3651229939501749786631633 2738422454626312339973725)
                    ·
                      refine ⟨1026908420484867127490147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2738422454626312339973725 1026908420484867127490147)
                      ·
                        rfl

theorem cell23_1999897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_1999897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999897 prefixEnd_1999897 := by exact prefixLift 1999897
  have htrace : WordTrace (prefixWord ++ tailWord_1999897) baseStart_1999897 baseEnd_1999897 := by
    simpa [prefixWord, tailWord_1999897, baseEnd_1999897] using wordTrace_append hprefix tailTrace_1999897
  have hstable : (prefixWord ++ tailWord_1999897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999897).length < 2 ^ (prefixWord ++ tailWord_1999897).sum := by decide
  have hdescent : baseEnd_1999897 < baseStart_1999897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999911 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_1999911 : Nat := 118140960795 + 1999911 * 2 ^ 59
def prefixEnd_1999911 : Nat := 4983230072969 + 3 ^ 40 * 1999911 * 2
def baseEnd_1999911 : Nat := 1026915609214030072715083

theorem tailTrace_1999911 : CollatzResearch.WordTrace tailWord_1999911 prefixEnd_1999911 1026915609214030072715083 := by
  unfold tailWord_1999911
  simp only [CollatzResearch.WordTrace]
  refine ⟨72942746657671479451119587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48628497771780986300746391 72942746657671479451119587)
  ·
    refine ⟨109414119986507219176679381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72942746657671479451119587 109414119986507219176679381)
    ·
      refine ⟨2564393437183762949453423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 109414119986507219176679381 2564393437183762949453423)
      ·
        refine ⟨3846590155775644424180135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564393437183762949453423 3846590155775644424180135)
        ·
          refine ⟨5769885233663466636270203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846590155775644424180135 5769885233663466636270203)
          ·
            refine ⟨8654827850495199954405305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5769885233663466636270203 8654827850495199954405305)
            ·
              refine ⟨6491120887871399965803979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8654827850495199954405305 6491120887871399965803979)
              ·
                refine ⟨9736681331807099948705969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491120887871399965803979 9736681331807099948705969)
                ·
                  refine ⟨7302510998855324961529477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9736681331807099948705969 7302510998855324961529477)
                  ·
                    refine ⟨1369220812285373430286777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7302510998855324961529477 1369220812285373430286777)
                    ·
                      refine ⟨1026915609214030072715083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369220812285373430286777 1026915609214030072715083)
                      ·
                        rfl

theorem cell23_1999911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_1999911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999911 prefixEnd_1999911 := by exact prefixLift 1999911
  have htrace : WordTrace (prefixWord ++ tailWord_1999911) baseStart_1999911 baseEnd_1999911 := by
    simpa [prefixWord, tailWord_1999911, baseEnd_1999911] using wordTrace_append hprefix tailTrace_1999911
  have hstable : (prefixWord ++ tailWord_1999911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999911).length < 2 ^ (prefixWord ++ tailWord_1999911).sum := by decide
  have hdescent : baseEnd_1999911 < baseStart_1999911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999920 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_1999920 : Nat := 118140960795 + 1999920 * 2 ^ 59
def prefixEnd_1999920 : Nat := 4983230072969 + 3 ^ 40 * 1999920 * 2
def baseEnd_1999920 : Nat := 1026920230539920537502541

theorem tailTrace_1999920 : CollatzResearch.WordTrace tailWord_1999920 prefixEnd_1999920 1026920230539920537502541 := by
  unfold tailWord_1999920
  simp only [CollatzResearch.WordTrace]
  refine ⟨36471537457319436994098607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48628716609759249325464809 36471537457319436994098607)
  ·
    refine ⟨54707306185979155491147911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36471537457319436994098607 54707306185979155491147911)
    ·
      refine ⟨82060959278968733236721867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54707306185979155491147911 82060959278968733236721867)
      ·
        refine ⟨123091438918453099855082801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82060959278968733236721867 123091438918453099855082801)
        ·
          refine ⟨92318579188839824891312101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123091438918453099855082801 92318579188839824891312101)
          ·
            refine ⟨17309733597907467167121019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92318579188839824891312101 17309733597907467167121019)
            ·
              refine ⟨25964600396861200750681529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17309733597907467167121019 25964600396861200750681529)
              ·
                refine ⟨19473450297645900563011147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25964600396861200750681529 19473450297645900563011147)
                ·
                  refine ⟨29210175446468850844516721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19473450297645900563011147 29210175446468850844516721)
                  ·
                    refine ⟨21907631584851638133387541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29210175446468850844516721 21907631584851638133387541)
                    ·
                      refine ⟨1026920230539920537502541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21907631584851638133387541 1026920230539920537502541)
                      ·
                        rfl

theorem cell23_1999920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_1999920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999920 prefixEnd_1999920 := by exact prefixLift 1999920
  have htrace : WordTrace (prefixWord ++ tailWord_1999920) baseStart_1999920 baseEnd_1999920 := by
    simpa [prefixWord, tailWord_1999920, baseEnd_1999920] using wordTrace_append hprefix tailTrace_1999920
  have hstable : (prefixWord ++ tailWord_1999920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999920).length < 2 ^ (prefixWord ++ tailWord_1999920).sum := by decide
  have hdescent : baseEnd_1999920 < baseStart_1999920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999967 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_1999967 : Nat := 118140960795 + 1999967 * 2 ^ 59
def prefixEnd_1999967 : Nat := 4983230072969 + 3 ^ 40 * 1999967 * 2
def baseEnd_1999967 : Nat := 1026944364130681853614825

theorem tailTrace_1999967 : CollatzResearch.WordTrace tailWord_1999967 prefixEnd_1999967 1026944364130681853614825 := by
  unfold tailWord_1999967
  simp only [CollatzResearch.WordTrace]
  refine ⟨72944789145468601015158155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48629859430312400676772103 72944789145468601015158155)
  ·
    refine ⟨109417183718202901522737233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72944789145468601015158155 109417183718202901522737233)
    ·
      refine ⟨82062887788652176142052925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109417183718202901522737233 82062887788652176142052925)
      ·
        refine ⟨30773582920744566053269847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82062887788652176142052925 30773582920744566053269847)
        ·
          refine ⟨46160374381116849079904771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30773582920744566053269847 46160374381116849079904771)
          ·
            refine ⟨69240561571675273619857157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46160374381116849079904771 69240561571675273619857157)
            ·
              refine ⟨12982605294689113803723217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69240561571675273619857157 12982605294689113803723217)
              ·
                refine ⟨9736953971016835352792413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12982605294689113803723217 9736953971016835352792413)
                ·
                  refine ⟨3651357739131313257297155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9736953971016835352792413 3651357739131313257297155)
                  ·
                    refine ⟨5477036608696969885945733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3651357739131313257297155 5477036608696969885945733)
                    ·
                      refine ⟨1026944364130681853614825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5477036608696969885945733 1026944364130681853614825)
                      ·
                        rfl

theorem cell23_1999967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_1999967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999967 prefixEnd_1999967 := by exact prefixLift 1999967
  have htrace : WordTrace (prefixWord ++ tailWord_1999967) baseStart_1999967 baseEnd_1999967 := by
    simpa [prefixWord, tailWord_1999967, baseEnd_1999967] using wordTrace_append hprefix tailTrace_1999967
  have hstable : (prefixWord ++ tailWord_1999967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999967).length < 2 ^ (prefixWord ++ tailWord_1999967).sum := by decide
  have hdescent : baseEnd_1999967 < baseStart_1999967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1999981 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1999981 : Nat := 118140960795 + 1999981 * 2 ^ 59
def prefixEnd_1999981 : Nat := 4983230072969 + 3 ^ 40 * 1999981 * 2
def baseEnd_1999981 : Nat := 342317184286614932946587

theorem tailTrace_1999981 : CollatzResearch.WordTrace tailWord_1999981 prefixEnd_1999981 342317184286614932946587 := by
  unfold tailWord_1999981
  simp only [CollatzResearch.WordTrace]
  refine ⟨72945299767417881406167797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48630199844945254270778531 72945299767417881406167797)
  ·
    refine ⟨6838621853195426381828231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72945299767417881406167797 6838621853195426381828231)
    ·
      refine ⟨10257932779793139572742347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6838621853195426381828231 10257932779793139572742347)
      ·
        refine ⟨15386899169689709359113521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10257932779793139572742347 15386899169689709359113521)
        ·
          refine ⟨11540174377267282019335141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15386899169689709359113521 11540174377267282019335141)
          ·
            refine ⟨2163782695737615378625339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11540174377267282019335141 2163782695737615378625339)
            ·
              refine ⟨3245674043606423067938009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163782695737615378625339 3245674043606423067938009)
              ·
                refine ⟨2434255532704817300953507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3245674043606423067938009 2434255532704817300953507)
                ·
                  refine ⟨3651383299057225951430261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434255532704817300953507 3651383299057225951430261)
                  ·
                    refine ⟨342317184286614932946587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3651383299057225951430261 342317184286614932946587)
                    ·
                      rfl

theorem cell23_1999981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1999981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1999981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1999981 prefixEnd_1999981 := by exact prefixLift 1999981
  have htrace : WordTrace (prefixWord ++ tailWord_1999981) baseStart_1999981 baseEnd_1999981 := by
    simpa [prefixWord, tailWord_1999981, baseEnd_1999981] using wordTrace_append hprefix tailTrace_1999981
  have hstable : (prefixWord ++ tailWord_1999981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1999981).length < 2 ^ (prefixWord ++ tailWord_1999981).sum := by decide
  have hdescent : baseEnd_1999981 < baseStart_1999981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1999981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000004 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_2000004 : Nat := 118140960795 + 2000004 * 2 ^ 59
def prefixEnd_2000004 : Nat := 4983230072969 + 3 ^ 40 * 2000004 * 2
def baseEnd_2000004 : Nat := 1026963362914898208852155

theorem tailTrace_2000004 : CollatzResearch.WordTrace tailWord_2000004 prefixEnd_2000004 1026963362914898208852155 := by
  unfold tailWord_2000004
  simp only [CollatzResearch.WordTrace]
  refine ⟨36473069323167278167127533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48630759097556370889503377 36473069323167278167127533)
  ·
    refine ⟨13677400996187729312672825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36473069323167278167127533 13677400996187729312672825)
    ·
      refine ⟨10258050747140796984504619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13677400996187729312672825 10258050747140796984504619)
      ·
        refine ⟨15387076120711195476756929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10258050747140796984504619 15387076120711195476756929)
        ·
          refine ⟨11540307090533396607567697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15387076120711195476756929 11540307090533396607567697)
          ·
            refine ⟨8655230317900047455675773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11540307090533396607567697 8655230317900047455675773)
            ·
              refine ⟨3245711369212517795878415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8655230317900047455675773 3245711369212517795878415)
              ·
                refine ⟨4868567053818776693817623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245711369212517795878415 4868567053818776693817623)
                ·
                  refine ⟨7302850580728165040726435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868567053818776693817623 7302850580728165040726435)
                  ·
                    refine ⟨10954275871092247561089653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7302850580728165040726435 10954275871092247561089653)
                    ·
                      refine ⟨1026963362914898208852155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10954275871092247561089653 1026963362914898208852155)
                      ·
                        rfl

theorem cell23_2000004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_2000004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000004 prefixEnd_2000004 := by exact prefixLift 2000004
  have htrace : WordTrace (prefixWord ++ tailWord_2000004) baseStart_2000004 baseEnd_2000004 := by
    simpa [prefixWord, tailWord_2000004, baseEnd_2000004] using wordTrace_append hprefix tailTrace_2000004
  have hstable : (prefixWord ++ tailWord_2000004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000004).length < 2 ^ (prefixWord ++ tailWord_2000004).sum := by decide
  have hdescent : baseEnd_2000004 < baseStart_2000004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000024 : List Nat := [2, 1, 2, 4, 2, 3, 1, 8]
def baseStart_2000024 : Nat := 118140960795 + 2000024 * 2 ^ 59
def prefixEnd_2000024 : Nat := 4983230072969 + 3 ^ 40 * 2000024 * 2
def baseEnd_2000024 : Nat := 38036060463999560392669

theorem tailTrace_2000024 : CollatzResearch.WordTrace tailWord_2000024 prefixEnd_2000024 38036060463999560392669 := by
  unfold tailWord_2000024
  simp only [CollatzResearch.WordTrace]
  refine ⟨36473434053131049874991563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48631245404174733166655417 36473434053131049874991563)
  ·
    refine ⟨54710151079696574812487345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36473434053131049874991563 54710151079696574812487345)
    ·
      refine ⟨41032613309772431109365509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54710151079696574812487345 41032613309772431109365509)
      ·
        refine ⟨7693614995582330833006033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41032613309772431109365509 7693614995582330833006033)
        ·
          refine ⟨5770211246686748124754525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7693614995582330833006033 5770211246686748124754525)
          ·
            refine ⟨2163829217507530546782947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5770211246686748124754525 2163829217507530546782947)
            ·
              refine ⟨3245743826261295820174421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163829217507530546782947 3245743826261295820174421)
              ·
                refine ⟨38036060463999560392669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3245743826261295820174421 38036060463999560392669)
                ·
                  rfl

theorem cell23_2000024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 8].length) (baseStart_2000024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000024 prefixEnd_2000024 := by exact prefixLift 2000024
  have htrace : WordTrace (prefixWord ++ tailWord_2000024) baseStart_2000024 baseEnd_2000024 := by
    simpa [prefixWord, tailWord_2000024, baseEnd_2000024] using wordTrace_append hprefix tailTrace_2000024
  have hstable : (prefixWord ++ tailWord_2000024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000024).length < 2 ^ (prefixWord ++ tailWord_2000024).sum := by decide
  have hdescent : baseEnd_2000024 < baseStart_2000024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000031 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 4]
def baseStart_2000031 : Nat := 118140960795 + 2000031 * 2 ^ 59
def prefixEnd_2000031 : Nat := 4983230072969 + 3 ^ 40 * 2000031 * 2
def baseEnd_2000031 : Nat := 1026977226892569603214531

theorem tailTrace_2000031 : CollatzResearch.WordTrace tailWord_2000031 prefixEnd_2000031 1026977226892569603214531 := by
  unfold tailWord_2000031
  simp only [CollatzResearch.WordTrace]
  refine ⟨72947123417236739945487947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48631415611491159963658631 72947123417236739945487947)
  ·
    refine ⟨109420685125855109918231921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72947123417236739945487947 109420685125855109918231921)
    ·
      refine ⟨82065513844391332438673941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109420685125855109918231921 82065513844391332438673941)
      ·
        refine ⟨3846820961455843708062841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82065513844391332438673941 3846820961455843708062841)
        ·
          refine ⟨2885115721091882781047131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3846820961455843708062841 2885115721091882781047131)
          ·
            refine ⟨4327673581637824171570697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885115721091882781047131 4327673581637824171570697)
            ·
              refine ⟨3245755186228368128678023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4327673581637824171570697 3245755186228368128678023)
              ·
                refine ⟨4868632779342552193017035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245755186228368128678023 4868632779342552193017035)
                ·
                  refine ⟨7302949169013828289525553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4868632779342552193017035 7302949169013828289525553)
                  ·
                    refine ⟨5477211876760371217144165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7302949169013828289525553 5477211876760371217144165)
                    ·
                      refine ⟨1026977226892569603214531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5477211876760371217144165 1026977226892569603214531)
                      ·
                        rfl

theorem cell23_2000031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_2000031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000031 prefixEnd_2000031 := by exact prefixLift 2000031
  have htrace : WordTrace (prefixWord ++ tailWord_2000031) baseStart_2000031 baseEnd_2000031 := by
    simpa [prefixWord, tailWord_2000031, baseEnd_2000031] using wordTrace_append hprefix tailTrace_2000031
  have hstable : (prefixWord ++ tailWord_2000031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000031).length < 2 ^ (prefixWord ++ tailWord_2000031).sum := by decide
  have hdescent : baseEnd_2000031 < baseStart_2000031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000068 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2000068 : Nat := 118140960795 + 2000068 * 2 ^ 59
def prefixEnd_2000068 : Nat := 4983230072969 + 3 ^ 40 * 2000068 * 2
def baseEnd_2000068 : Nat := 1026996225676785958451861

theorem tailTrace_2000068 : CollatzResearch.WordTrace tailWord_2000068 prefixEnd_2000068 1026996225676785958451861 := by
  unfold tailWord_2000068
  simp only [CollatzResearch.WordTrace]
  refine ⟨36474236459051347632292429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48632315278735130176389905 36474236459051347632292429)
  ·
    refine ⟨13677838672144255362109661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36474236459051347632292429 13677838672144255362109661)
    ·
      refine ⟨5129189502054095760791123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13677838672144255362109661 5129189502054095760791123)
      ·
        refine ⟨7693784253081143641186685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129189502054095760791123 7693784253081143641186685)
        ·
          refine ⟨2885169094905428865445007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7693784253081143641186685 2885169094905428865445007)
          ·
            refine ⟨4327753642358143298167511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885169094905428865445007 4327753642358143298167511)
            ·
              refine ⟨6491630463537214947251267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327753642358143298167511 6491630463537214947251267)
              ·
                refine ⟨9737445695305822420876901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491630463537214947251267 9737445695305822420876901)
                ·
                  refine ⟨1825771067869841703914419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9737445695305822420876901 1825771067869841703914419)
                  ·
                    refine ⟨2738656601804762555871629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1825771067869841703914419 2738656601804762555871629)
                    ·
                      refine ⟨1026996225676785958451861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2738656601804762555871629 1026996225676785958451861)
                      ·
                        rfl

theorem cell23_2000068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2000068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000068 prefixEnd_2000068 := by exact prefixLift 2000068
  have htrace : WordTrace (prefixWord ++ tailWord_2000068) baseStart_2000068 baseEnd_2000068 := by
    simpa [prefixWord, tailWord_2000068, baseEnd_2000068] using wordTrace_append hprefix tailTrace_2000068
  have hstable : (prefixWord ++ tailWord_2000068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000068).length < 2 ^ (prefixWord ++ tailWord_2000068).sum := by decide
  have hdescent : baseEnd_2000068 < baseStart_2000068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000085 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2000085 : Nat := 118140960795 + 2000085 * 2 ^ 59
def prefixEnd_2000085 : Nat := 4983230072969 + 3 ^ 40 * 2000085 * 2
def baseEnd_2000085 : Nat := 1027004954847912391939283

theorem tailTrace_2000085 : CollatzResearch.WordTrace tailWord_2000085 prefixEnd_2000085 1027004954847912391939283 := by
  unfold tailWord_2000085
  simp only [CollatzResearch.WordTrace]
  refine ⟨72949092959041107167953709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48632728639360738111969139 72949092959041107167953709)
  ·
    refine ⟨27355909859640415187982641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72949092959041107167953709 27355909859640415187982641)
    ·
      refine ⟨20516932394730311390986981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27355909859640415187982641 20516932394730311390986981)
      ·
        refine ⟨3846924824011933385810059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20516932394730311390986981 3846924824011933385810059)
        ·
          refine ⟨5770387236017900078715089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846924824011933385810059 5770387236017900078715089)
          ·
            refine ⟨4327790427013425059036317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5770387236017900078715089 4327790427013425059036317)
            ·
              refine ⟨1622921410130034397138619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4327790427013425059036317 1622921410130034397138619)
              ·
                refine ⟨2434382115195051595707929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622921410130034397138619 2434382115195051595707929)
                ·
                  refine ⟨1825786586396288696780947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2434382115195051595707929 1825786586396288696780947)
                  ·
                    refine ⟨2738679879594433045171421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1825786586396288696780947 2738679879594433045171421)
                    ·
                      refine ⟨1027004954847912391939283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2738679879594433045171421 1027004954847912391939283)
                      ·
                        rfl

theorem cell23_2000085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2000085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000085 prefixEnd_2000085 := by exact prefixLift 2000085
  have htrace : WordTrace (prefixWord ++ tailWord_2000085) baseStart_2000085 baseEnd_2000085 := by
    simpa [prefixWord, tailWord_2000085, baseEnd_2000085] using wordTrace_append hprefix tailTrace_2000085
  have hstable : (prefixWord ++ tailWord_2000085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000085).length < 2 ^ (prefixWord ++ tailWord_2000085).sum := by decide
  have hdescent : baseEnd_2000085 < baseStart_2000085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000142 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2]
def baseStart_2000142 : Nat := 118140960795 + 2000142 * 2 ^ 59
def prefixEnd_2000142 : Nat := 4983230072969 + 3 ^ 40 * 2000142 * 2
def baseEnd_2000142 : Nat := 1027034223245218668926521

theorem tailTrace_2000142 : CollatzResearch.WordTrace tailWord_2000142 prefixEnd_2000142 1027034223245218668926521 := by
  unfold tailWord_2000142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9118896489979325737847335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48634114613223070601852453 9118896489979325737847335)
  ·
    refine ⟨13678344734968988606771003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9118896489979325737847335 13678344734968988606771003)
    ·
      refine ⟨20517517102453482910156505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13678344734968988606771003 20517517102453482910156505)
      ·
        refine ⟨15388137826840112182617379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20517517102453482910156505 15388137826840112182617379)
        ·
          refine ⟨23082206740260168273926069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15388137826840112182617379 23082206740260168273926069)
          ·
            refine ⟨2163956881899390775680569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23082206740260168273926069 2163956881899390775680569)
            ·
              refine ⟨1622967661424543081760427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163956881899390775680569 1622967661424543081760427)
              ·
                refine ⟨2434451492136814622640641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1622967661424543081760427 2434451492136814622640641)
                ·
                  refine ⟨1825838619102610966980481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2434451492136814622640641 1825838619102610966980481)
                  ·
                    refine ⟨1369378964326958225235361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1825838619102610966980481 1369378964326958225235361)
                    ·
                      refine ⟨1027034223245218668926521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369378964326958225235361 1027034223245218668926521)
                      ·
                        rfl

theorem cell23_2000142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_2000142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000142 prefixEnd_2000142 := by exact prefixLift 2000142
  have htrace : WordTrace (prefixWord ++ tailWord_2000142) baseStart_2000142 baseEnd_2000142 := by
    simpa [prefixWord, tailWord_2000142, baseEnd_2000142] using wordTrace_append hprefix tailTrace_2000142
  have hstable : (prefixWord ++ tailWord_2000142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000142).length < 2 ^ (prefixWord ++ tailWord_2000142).sum := by decide
  have hdescent : baseEnd_2000142 < baseStart_2000142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000181 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_2000181 : Nat := 118140960795 + 2000181 * 2 ^ 59
def prefixEnd_2000181 : Nat := 4983230072969 + 3 ^ 40 * 2000181 * 2
def baseEnd_2000181 : Nat := 1027054248990744016338841

theorem tailTrace_2000181 : CollatzResearch.WordTrace tailWord_2000181 prefixEnd_2000181 1027054248990744016338841 := by
  unfold tailWord_2000181
  simp only [CollatzResearch.WordTrace]
  refine ⟨72952594366693315563448397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48635062911128877042298931 72952594366693315563448397)
  ·
    refine ⟨27357222887509993336293149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72952594366693315563448397 27357222887509993336293149)
    ·
      refine ⟨10258958582816247501109931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27357222887509993336293149 10258958582816247501109931)
      ·
        refine ⟨15388437874224371251664897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10258958582816247501109931 15388437874224371251664897)
        ·
          refine ⟨11541328405668278438748673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15388437874224371251664897 11541328405668278438748673)
          ·
            refine ⟨8655996304251208829061505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11541328405668278438748673 8655996304251208829061505)
            ·
              refine ⟨6491997228188406621796129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8655996304251208829061505 6491997228188406621796129)
              ·
                refine ⟨4868997921141304966347097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6491997228188406621796129 4868997921141304966347097)
                ·
                  refine ⟨3651748440855978724760323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4868997921141304966347097 3651748440855978724760323)
                  ·
                    refine ⟨5477622661283968087140485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3651748440855978724760323 5477622661283968087140485)
                    ·
                      refine ⟨1027054248990744016338841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5477622661283968087140485 1027054248990744016338841)
                      ·
                        rfl

theorem cell23_2000181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_2000181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000181 prefixEnd_2000181 := by exact prefixLift 2000181
  have htrace : WordTrace (prefixWord ++ tailWord_2000181) baseStart_2000181 baseEnd_2000181 := by
    simpa [prefixWord, tailWord_2000181, baseEnd_2000181] using wordTrace_append hprefix tailTrace_2000181
  have hstable : (prefixWord ++ tailWord_2000181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000181).length < 2 ^ (prefixWord ++ tailWord_2000181).sum := by decide
  have hdescent : baseEnd_2000181 < baseStart_2000181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000184 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_2000184 : Nat := 118140960795 + 2000184 * 2 ^ 59
def prefixEnd_2000184 : Nat := 4983230072969 + 3 ^ 40 * 2000184 * 2
def baseEnd_2000184 : Nat := 1027055789432707504601327

theorem tailTrace_2000184 : CollatzResearch.WordTrace tailWord_2000184 prefixEnd_2000184 1027055789432707504601327 := by
  unfold tailWord_2000184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36476351892841223537903803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48635135857121631383871737 36476351892841223537903803)
  ·
    refine ⟨54714527839261835306855705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36476351892841223537903803 54714527839261835306855705)
    ·
      refine ⟨41035895879446376480141779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54714527839261835306855705 41035895879446376480141779)
      ·
        refine ⟨61553843819169564720212669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41035895879446376480141779 61553843819169564720212669)
        ·
          refine ⟨23082691432188586770079751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61553843819169564720212669 23082691432188586770079751)
          ·
            refine ⟨34624037148282880155119627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23082691432188586770079751 34624037148282880155119627)
            ·
              refine ⟨51936055722424320232679441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34624037148282880155119627 51936055722424320232679441)
              ·
                refine ⟨38952041791818240174509581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51936055722424320232679441 38952041791818240174509581)
                ·
                  refine ⟨14607015671931840065441093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38952041791818240174509581 14607015671931840065441093)
                  ·
                    refine ⟨2738815438487220012270205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14607015671931840065441093 2738815438487220012270205)
                    ·
                      refine ⟨1027055789432707504601327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2738815438487220012270205 1027055789432707504601327)
                      ·
                        rfl

theorem cell23_2000184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_2000184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000184 prefixEnd_2000184 := by exact prefixLift 2000184
  have htrace : WordTrace (prefixWord ++ tailWord_2000184) baseStart_2000184 baseEnd_2000184 := by
    simpa [prefixWord, tailWord_2000184, baseEnd_2000184] using wordTrace_append hprefix tailTrace_2000184
  have hstable : (prefixWord ++ tailWord_2000184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000184).length < 2 ^ (prefixWord ++ tailWord_2000184).sum := by decide
  have hdescent : baseEnd_2000184 < baseStart_2000184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000187 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 14]
def baseStart_2000187 : Nat := 118140960795 + 2000187 * 2 ^ 59
def prefixEnd_2000187 : Nat := 4983230072969 + 3 ^ 40 * 2000187 * 2
def baseEnd_2000187 : Nat := 114117481097185665873757

theorem tailTrace_2000187 : CollatzResearch.WordTrace tailWord_2000187 prefixEnd_2000187 114117481097185665873757 := by
  unfold tailWord_2000187
  simp only [CollatzResearch.WordTrace]
  refine ⟨72952813204671578588166815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48635208803114385725444543 72952813204671578588166815)
  ·
    refine ⟨109429219807007367882250223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72952813204671578588166815 109429219807007367882250223)
    ·
      refine ⟨164143829710511051823375335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109429219807007367882250223 164143829710511051823375335)
      ·
        refine ⟨246215744565766577735063003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164143829710511051823375335 246215744565766577735063003)
        ·
          refine ⟨369323616848649866602594505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246215744565766577735063003 369323616848649866602594505)
          ·
            refine ⟨276992712636487399951945879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369323616848649866602594505 276992712636487399951945879)
            ·
              refine ⟨415489068954731099927918819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276992712636487399951945879 415489068954731099927918819)
              ·
                refine ⟨623233603432096649891878229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415489068954731099927918819 623233603432096649891878229)
                ·
                  refine ⟨114117481097185665873757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 14 623233603432096649891878229 114117481097185665873757)
                  ·
                    rfl

theorem cell23_2000187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 14].length) (baseStart_2000187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000187 prefixEnd_2000187 := by exact prefixLift 2000187
  have htrace : WordTrace (prefixWord ++ tailWord_2000187) baseStart_2000187 baseEnd_2000187 := by
    simpa [prefixWord, tailWord_2000187, baseEnd_2000187] using wordTrace_append hprefix tailTrace_2000187
  have hstable : (prefixWord ++ tailWord_2000187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000187).length < 2 ^ (prefixWord ++ tailWord_2000187).sum := by decide
  have hdescent : baseEnd_2000187 < baseStart_2000187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000238 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_2000238 : Nat := 118140960795 + 2000238 * 2 ^ 59
def prefixEnd_2000238 : Nat := 4983230072969 + 3 ^ 40 * 2000238 * 2
def baseEnd_2000238 : Nat := 114120390820894477036231

theorem tailTrace_2000238 : CollatzResearch.WordTrace tailWord_2000238 prefixEnd_2000238 114120390820894477036231 := by
  unfold tailWord_2000238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119334165935851787284171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48636448884991209532182245 9119334165935851787284171)
  ·
    refine ⟨13679001248903777680926257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9119334165935851787284171 13679001248903777680926257)
    ·
      refine ⟨10259250936677833260694693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13679001248903777680926257 10259250936677833260694693)
      ·
        refine ⟨1923609550627093736380255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10259250936677833260694693 1923609550627093736380255)
        ·
          refine ⟨2885414325940640604570383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923609550627093736380255 2885414325940640604570383)
          ·
            refine ⟨4328121488910960906855575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885414325940640604570383 4328121488910960906855575)
            ·
              refine ⟨6492182233366441360283363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328121488910960906855575 6492182233366441360283363)
              ·
                refine ⟨9738273350049662040425045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492182233366441360283363 9738273350049662040425045)
                ·
                  refine ⟨114120390820894477036231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9738273350049662040425045 114120390820894477036231)
                  ·
                    rfl

theorem cell23_2000238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_2000238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000238 prefixEnd_2000238 := by exact prefixLift 2000238
  have htrace : WordTrace (prefixWord ++ tailWord_2000238) baseStart_2000238 baseEnd_2000238 := by
    simpa [prefixWord, tailWord_2000238, baseEnd_2000238] using wordTrace_append hprefix tailTrace_2000238
  have hstable : (prefixWord ++ tailWord_2000238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000238).length < 2 ^ (prefixWord ++ tailWord_2000238).sum := by decide
  have hdescent : baseEnd_2000238 < baseStart_2000238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000281 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 4, 4]
def baseStart_2000281 : Nat := 118140960795 + 2000281 * 2 ^ 59
def prefixEnd_2000281 : Nat := 4983230072969 + 3 ^ 40 * 2000281 * 2
def baseEnd_2000281 : Nat := 342368532352064541696127

theorem tailTrace_2000281 : CollatzResearch.WordTrace tailWord_2000281 prefixEnd_2000281 342368532352064541696127 := by
  unfold tailWord_2000281
  simp only [CollatzResearch.WordTrace]
  refine ⟨72956241666331032642088697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48637494444220688428059131 72956241666331032642088697)
  ·
    refine ⟨54717181249748274481566523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72956241666331032642088697 54717181249748274481566523)
    ·
      refine ⟨82075771874622411722349785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54717181249748274481566523 82075771874622411722349785)
      ·
        refine ⟨61556828905966808791762339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82075771874622411722349785 61556828905966808791762339)
        ·
          refine ⟨92335243358950213187643509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61556828905966808791762339 92335243358950213187643509)
          ·
            refine ⟨8656429064901582486341579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92335243358950213187643509 8656429064901582486341579)
            ·
              refine ⟨12984643597352373729512369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656429064901582486341579 12984643597352373729512369)
              ·
                refine ⟨9738482698014280297134277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12984643597352373729512369 9738482698014280297134277)
                ·
                  refine ⟨1825965505877677555712677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9738482698014280297134277 1825965505877677555712677)
                  ·
                    refine ⟨342368532352064541696127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1825965505877677555712677 342368532352064541696127)
                    ·
                      rfl

theorem cell23_2000281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 4].length) (baseStart_2000281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000281 prefixEnd_2000281 := by exact prefixLift 2000281
  have htrace : WordTrace (prefixWord ++ tailWord_2000281) baseStart_2000281 baseEnd_2000281 := by
    simpa [prefixWord, tailWord_2000281, baseEnd_2000281] using wordTrace_append hprefix tailTrace_2000281
  have hstable : (prefixWord ++ tailWord_2000281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000281).length < 2 ^ (prefixWord ++ tailWord_2000281).sum := by decide
  have hdescent : baseEnd_2000281 < baseStart_2000281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000291 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 5]
def baseStart_2000291 : Nat := 118140960795 + 2000291 * 2 ^ 59
def prefixEnd_2000291 : Nat := 4983230072969 + 3 ^ 40 * 2000291 * 2
def baseEnd_2000291 : Nat := 1027110731862738585963335

theorem tailTrace_2000291 : CollatzResearch.WordTrace tailWord_2000291 prefixEnd_2000291 1027110731862738585963335 := by
  unfold tailWord_2000291
  simp only [CollatzResearch.WordTrace]
  refine ⟨72956606396294804349952727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48637737597529869566635151 72956606396294804349952727)
  ·
    refine ⟨109434909594442206524929091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72956606396294804349952727 109434909594442206524929091)
    ·
      refine ⟨164152364391663309787393637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109434909594442206524929091 164152364391663309787393637)
      ·
        refine ⟨30778568323436870585136307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164152364391663309787393637 30778568323436870585136307)
        ·
          refine ⟨46167852485155305877704461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30778568323436870585136307 46167852485155305877704461)
          ·
            refine ⟨17312944681933239704139173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46167852485155305877704461 17312944681933239704139173)
            ·
              refine ⟨3246177127862482444526095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17312944681933239704139173 3246177127862482444526095)
              ·
                refine ⟨4869265691793723666789143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246177127862482444526095 4869265691793723666789143)
                ·
                  refine ⟨7303898537690585500183715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869265691793723666789143 7303898537690585500183715)
                  ·
                    refine ⟨10955847806535878250275573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7303898537690585500183715 10955847806535878250275573)
                    ·
                      refine ⟨1027110731862738585963335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10955847806535878250275573 1027110731862738585963335)
                      ·
                        rfl

theorem cell23_2000291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_2000291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000291 prefixEnd_2000291 := by exact prefixLift 2000291
  have htrace : WordTrace (prefixWord ++ tailWord_2000291) baseStart_2000291 baseEnd_2000291 := by
    simpa [prefixWord, tailWord_2000291, baseEnd_2000291] using wordTrace_append hprefix tailTrace_2000291
  have hstable : (prefixWord ++ tailWord_2000291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000291).length < 2 ^ (prefixWord ++ tailWord_2000291).sum := by decide
  have hdescent : baseEnd_2000291 < baseStart_2000291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000355 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2000355 : Nat := 118140960795 + 2000355 * 2 ^ 59
def prefixEnd_2000355 : Nat := 4983230072969 + 3 ^ 40 * 2000355 * 2
def baseEnd_2000355 : Nat := 1027143594624626335563041

theorem tailTrace_2000355 : CollatzResearch.WordTrace tailWord_2000355 prefixEnd_2000355 1027143594624626335563041 := by
  unfold tailWord_2000355
  simp only [CollatzResearch.WordTrace]
  refine ⟨72958940668062943280282519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48639293778708628853521679 72958940668062943280282519)
  ·
    refine ⟨109438411002094414920423779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72958940668062943280282519 109438411002094414920423779)
    ·
      refine ⟨164157616503141622380635669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109438411002094414920423779 164157616503141622380635669)
      ·
        refine ⟨7694888273584763549092297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164157616503141622380635669 7694888273584763549092297)
        ·
          refine ⟨5771166205188572661819223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7694888273584763549092297 5771166205188572661819223)
          ·
            refine ⟨8656749307782858992728835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771166205188572661819223 8656749307782858992728835)
            ·
              refine ⟨12985123961674288489093253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656749307782858992728835 12985123961674288489093253)
              ·
                refine ⟨2434710742813929091704985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12985123961674288489093253 2434710742813929091704985)
                ·
                  refine ⟨1826033057110446818778739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2434710742813929091704985 1826033057110446818778739)
                  ·
                    refine ⟨2739049585665670228168109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1826033057110446818778739 2739049585665670228168109)
                    ·
                      refine ⟨1027143594624626335563041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2739049585665670228168109 1027143594624626335563041)
                      ·
                        rfl

theorem cell23_2000355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2000355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000355 prefixEnd_2000355 := by exact prefixLift 2000355
  have htrace : WordTrace (prefixWord ++ tailWord_2000355) baseStart_2000355 baseEnd_2000355 := by
    simpa [prefixWord, tailWord_2000355, baseEnd_2000355] using wordTrace_append hprefix tailTrace_2000355
  have hstable : (prefixWord ++ tailWord_2000355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000355).length < 2 ^ (prefixWord ++ tailWord_2000355).sum := by decide
  have hdescent : baseEnd_2000355 < baseStart_2000355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000390 : List Nat := [6, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_2000390 : Nat := 118140960795 + 2000390 * 2 ^ 59
def prefixEnd_2000390 : Nat := 4983230072969 + 3 ^ 40 * 2000390 * 2
def baseEnd_2000390 : Nat := 1027161566447533698625381

theorem tailTrace_2000390 : CollatzResearch.WordTrace tailWord_2000390 prefixEnd_2000390 1027161566447533698625381 := by
  unfold tailWord_2000390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280006788216754508056457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48640144815290762838537749 2280006788216754508056457)
  ·
    refine ⟨1710005091162565881042343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2280006788216754508056457 1710005091162565881042343)
    ·
      refine ⟨2565007636743848821563515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710005091162565881042343 2565007636743848821563515)
      ·
        refine ⟨3847511455115773232345273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565007636743848821563515 3847511455115773232345273)
        ·
          refine ⟨2885633591336829924258955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3847511455115773232345273 2885633591336829924258955)
          ·
            refine ⟨4328450387005244886388433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885633591336829924258955 4328450387005244886388433)
            ·
              refine ⟨3246337790253933664791325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328450387005244886388433 3246337790253933664791325)
              ·
                refine ⟨1217376671345225124296747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3246337790253933664791325 1217376671345225124296747)
                ·
                  refine ⟨1826065007017837686445121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217376671345225124296747 1826065007017837686445121)
                  ·
                    refine ⟨1369548755263378264833841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1826065007017837686445121 1369548755263378264833841)
                    ·
                      refine ⟨1027161566447533698625381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369548755263378264833841 1027161566447533698625381)
                      ·
                        rfl

theorem cell23_2000390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_2000390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000390 prefixEnd_2000390 := by exact prefixLift 2000390
  have htrace : WordTrace (prefixWord ++ tailWord_2000390) baseStart_2000390 baseEnd_2000390 := by
    simpa [prefixWord, tailWord_2000390, baseEnd_2000390] using wordTrace_append hprefix tailTrace_2000390
  have hstable : (prefixWord ++ tailWord_2000390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000390).length < 2 ^ (prefixWord ++ tailWord_2000390).sum := by decide
  have hdescent : baseEnd_2000390 < baseStart_2000390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000502 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2000502 : Nat := 118140960795 + 2000502 * 2 ^ 59
def prefixEnd_2000502 : Nat := 4983230072969 + 3 ^ 40 * 2000502 * 2
def baseEnd_2000502 : Nat := 1027219076280837260424865

theorem tailTrace_2000502 : CollatzResearch.WordTrace tailWord_2000502 prefixEnd_2000502 1027219076280837260424865 := by
  unfold tailWord_2000502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560268887408149211617735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48642868132353591590589173 4560268887408149211617735)
  ·
    refine ⟨6840403331112223817426603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4560268887408149211617735 6840403331112223817426603)
    ·
      refine ⟨10260604996668335726139905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840403331112223817426603 10260604996668335726139905)
      ·
        refine ⟨7695453747501251794604929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10260604996668335726139905 7695453747501251794604929)
        ·
          refine ⟨5771590310625938845953697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7695453747501251794604929 5771590310625938845953697)
          ·
            refine ⟨4328692732969454134465273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5771590310625938845953697 4328692732969454134465273)
            ·
              refine ⟨3246519549727090600848955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328692732969454134465273 3246519549727090600848955)
              ·
                refine ⟨4869779324590635901273433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246519549727090600848955 4869779324590635901273433)
                ·
                  refine ⟨3652334493442976925955075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4869779324590635901273433 3652334493442976925955075)
                  ·
                    refine ⟨5478501740164465388932613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652334493442976925955075 5478501740164465388932613)
                    ·
                      refine ⟨1027219076280837260424865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5478501740164465388932613 1027219076280837260424865)
                      ·
                        rfl

theorem cell23_2000502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2000502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000502 prefixEnd_2000502 := by exact prefixLift 2000502
  have htrace : WordTrace (prefixWord ++ tailWord_2000502) baseStart_2000502 baseEnd_2000502 := by
    simpa [prefixWord, tailWord_2000502, baseEnd_2000502] using wordTrace_append hprefix tailTrace_2000502
  have hstable : (prefixWord ++ tailWord_2000502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000502).length < 2 ^ (prefixWord ++ tailWord_2000502).sum := by decide
  have hdescent : baseEnd_2000502 < baseStart_2000502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000505 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 3]
def baseStart_2000505 : Nat := 118140960795 + 2000505 * 2 ^ 59
def prefixEnd_2000505 : Nat := 4983230072969 + 3 ^ 40 * 2000505 * 2
def baseEnd_2000505 : Nat := 1027220616722800748687351

theorem tailTrace_2000505 : CollatzResearch.WordTrace tailWord_2000505 prefixEnd_2000505 1027220616722800748687351 := by
  unfold tailWord_2000505
  simp only [CollatzResearch.WordTrace]
  refine ⟨72964411617519518898242969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48642941078346345932161979 72964411617519518898242969)
  ·
    refine ⟨54723308713139639173682227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72964411617519518898242969 54723308713139639173682227)
    ·
      refine ⟨82084963069709458760523341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54723308713139639173682227 82084963069709458760523341)
      ·
        refine ⟨30781861151141047035196253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82084963069709458760523341 30781861151141047035196253)
        ·
          refine ⟨11543197931677892638198595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30781861151141047035196253 11543197931677892638198595)
          ·
            refine ⟨17314796897516838957297893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11543197931677892638198595 17314796897516838957297893)
            ·
              refine ⟨3246524418284407304493355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17314796897516838957297893 3246524418284407304493355)
              ·
                refine ⟨4869786627426610956740033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246524418284407304493355 4869786627426610956740033)
                ·
                  refine ⟨3652339970569958217555025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4869786627426610956740033 3652339970569958217555025)
                  ·
                    refine ⟨2739254977927468663166269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3652339970569958217555025 2739254977927468663166269)
                    ·
                      refine ⟨1027220616722800748687351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2739254977927468663166269 1027220616722800748687351)
                      ·
                        rfl

theorem cell23_2000505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_2000505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000505 prefixEnd_2000505 := by exact prefixLift 2000505
  have htrace : WordTrace (prefixWord ++ tailWord_2000505) baseStart_2000505 baseEnd_2000505 := by
    simpa [prefixWord, tailWord_2000505, baseEnd_2000505] using wordTrace_append hprefix tailTrace_2000505
  have hstable : (prefixWord ++ tailWord_2000505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000505).length < 2 ^ (prefixWord ++ tailWord_2000505).sum := by decide
  have hdescent : baseEnd_2000505 < baseStart_2000505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000531 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 7]
def baseStart_2000531 : Nat := 118140960795 + 2000531 * 2 ^ 59
def prefixEnd_2000531 : Nat := 4983230072969 + 3 ^ 40 * 2000531 * 2
def baseEnd_2000531 : Nat := 1027233967219817646962231

theorem tailTrace_2000531 : CollatzResearch.WordTrace tailWord_2000531 prefixEnd_2000531 1027233967219817646962231 := by
  unfold tailWord_2000531
  simp only [CollatzResearch.WordTrace]
  refine ⟨72965359915425325338689447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48643573276950216892459631 72965359915425325338689447)
  ·
    refine ⟨109448039873137988008034171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72965359915425325338689447 109448039873137988008034171)
    ·
      refine ⟨164172059809706982012051257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109448039873137988008034171 164172059809706982012051257)
      ·
        refine ⟨123129044857280236509038443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164172059809706982012051257 123129044857280236509038443)
        ·
          refine ⟨184693567285920354763557665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123129044857280236509038443 184693567285920354763557665)
          ·
            refine ⟨138520175464440266072668249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184693567285920354763557665 138520175464440266072668249)
            ·
              refine ⟨103890131598330199554501187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138520175464440266072668249 103890131598330199554501187)
              ·
                refine ⟨155835197397495299331751781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103890131598330199554501187 155835197397495299331751781)
                ·
                  refine ⟨29219099512030368624703459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155835197397495299331751781 29219099512030368624703459)
                  ·
                    refine ⟨43828649268045552937055189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29219099512030368624703459 43828649268045552937055189)
                    ·
                      refine ⟨1027233967219817646962231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43828649268045552937055189 1027233967219817646962231)
                      ·
                        rfl

theorem cell23_2000531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_2000531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000531 prefixEnd_2000531 := by exact prefixLift 2000531
  have htrace : WordTrace (prefixWord ++ tailWord_2000531) baseStart_2000531 baseEnd_2000531 := by
    simpa [prefixWord, tailWord_2000531, baseEnd_2000531] using wordTrace_append hprefix tailTrace_2000531
  have hstable : (prefixWord ++ tailWord_2000531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000531).length < 2 ^ (prefixWord ++ tailWord_2000531).sum := by decide
  have hdescent : baseEnd_2000531 < baseStart_2000531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000562 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2]
def baseStart_2000562 : Nat := 118140960795 + 2000562 * 2 ^ 59
def prefixEnd_2000562 : Nat := 4983230072969 + 3 ^ 40 * 2000562 * 2
def baseEnd_2000562 : Nat := 1027249885120107025674589

theorem tailTrace_2000562 : CollatzResearch.WordTrace tailWord_2000562 prefixEnd_2000562 1027249885120107025674589 := by
  unfold tailWord_2000562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18241622644578254408266985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48644327052208678422045293 18241622644578254408266985)
  ·
    refine ⟨13681216983433690806200239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18241622644578254408266985 13681216983433690806200239)
    ·
      refine ⟨20521825475150536209300359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13681216983433690806200239 20521825475150536209300359)
      ·
        refine ⟨30782738212725804313950539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20521825475150536209300359 30782738212725804313950539)
        ·
          refine ⟨46174107319088706470925809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30782738212725804313950539 46174107319088706470925809)
          ·
            refine ⟨34630580489316529853194357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46174107319088706470925809 34630580489316529853194357)
            ·
              refine ⟨3246616920873424673736971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34630580489316529853194357 3246616920873424673736971)
              ·
                refine ⟨4869925381310137010605457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3246616920873424673736971 4869925381310137010605457)
                ·
                  refine ⟨3652444035982602757954093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4869925381310137010605457 3652444035982602757954093)
                  ·
                    refine ⟨1369666513493476034232785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652444035982602757954093 1369666513493476034232785)
                    ·
                      refine ⟨1027249885120107025674589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369666513493476034232785 1027249885120107025674589)
                      ·
                        rfl

theorem cell23_2000562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_2000562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000562 prefixEnd_2000562 := by exact prefixLift 2000562
  have htrace : WordTrace (prefixWord ++ tailWord_2000562) baseStart_2000562 baseEnd_2000562 := by
    simpa [prefixWord, tailWord_2000562, baseEnd_2000562] using wordTrace_append hprefix tailTrace_2000562
  have hstable : (prefixWord ++ tailWord_2000562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000562).length < 2 ^ (prefixWord ++ tailWord_2000562).sum := by decide
  have hdescent : baseEnd_2000562 < baseStart_2000562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000572 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_2000572 : Nat := 118140960795 + 2000572 * 2 ^ 59
def prefixEnd_2000572 : Nat := 4983230072969 + 3 ^ 40 * 2000572 * 2
def baseEnd_2000572 : Nat := 342418339975550662183181

theorem tailTrace_2000572 : CollatzResearch.WordTrace tailWord_2000572 prefixEnd_2000572 342418339975550662183181 := by
  unfold tailWord_2000572
  simp only [CollatzResearch.WordTrace]
  refine ⟨36483427654138394670465985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48644570205517859560621313 36483427654138394670465985)
  ·
    refine ⟨27362570740603796002849489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36483427654138394670465985 27362570740603796002849489)
    ·
      refine ⟨20521928055452847002137117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27362570740603796002849489 20521928055452847002137117)
      ·
        refine ⟨7695723020794817625801419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20521928055452847002137117 7695723020794817625801419)
        ·
          refine ⟨11543584531192226438702129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695723020794817625801419 11543584531192226438702129)
          ·
            refine ⟨8657688398394169829026597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11543584531192226438702129 8657688398394169829026597)
            ·
              refine ⟨1623316574698906842942487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8657688398394169829026597 1623316574698906842942487)
              ·
                refine ⟨2434974862048360264413731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623316574698906842942487 2434974862048360264413731)
                ·
                  refine ⟨3652462293072540396620597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434974862048360264413731 3652462293072540396620597)
                  ·
                    refine ⟨342418339975550662183181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3652462293072540396620597 342418339975550662183181)
                    ·
                      rfl

theorem cell23_2000572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_2000572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000572 prefixEnd_2000572 := by exact prefixLift 2000572
  have htrace : WordTrace (prefixWord ++ tailWord_2000572) baseStart_2000572 baseEnd_2000572 := by
    simpa [prefixWord, tailWord_2000572, baseEnd_2000572] using wordTrace_append hprefix tailTrace_2000572
  have hstable : (prefixWord ++ tailWord_2000572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000572).length < 2 ^ (prefixWord ++ tailWord_2000572).sum := by decide
  have hdescent : baseEnd_2000572 < baseStart_2000572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000575 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 4]
def baseStart_2000575 : Nat := 118140960795 + 2000575 * 2 ^ 59
def prefixEnd_2000575 : Nat := 4983230072969 + 3 ^ 40 * 2000575 * 2
def baseEnd_2000575 : Nat := 1027256560368615474812029

theorem tailTrace_2000575 : CollatzResearch.WordTrace tailWord_2000575 prefixEnd_2000575 1027256560368615474812029 := by
  unfold tailWord_2000575
  simp only [CollatzResearch.WordTrace]
  refine ⟨72966964727265920853291179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48644643151510613902194119 72966964727265920853291179)
  ·
    refine ⟨109450447090898881279936769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72966964727265920853291179 109450447090898881279936769)
    ·
      refine ⟨82087835318174160959952577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109450447090898881279936769 82087835318174160959952577)
      ·
        refine ⟨61565876488630620719964433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82087835318174160959952577 61565876488630620719964433)
        ·
          refine ⟨46174407366472965539973325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61565876488630620719964433 46174407366472965539973325)
          ·
            refine ⟨17315402762427362077489997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46174407366472965539973325 17315402762427362077489997)
            ·
              refine ⟨6493276035910260779058749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17315402762427362077489997 6493276035910260779058749)
              ·
                refine ⟨2434978513466347792147031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6493276035910260779058749 2434978513466347792147031)
                ·
                  refine ⟨3652467770199521688220547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434978513466347792147031 3652467770199521688220547)
                  ·
                    refine ⟨5478701655299282532330821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652467770199521688220547 5478701655299282532330821)
                    ·
                      refine ⟨1027256560368615474812029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5478701655299282532330821 1027256560368615474812029)
                      ·
                        rfl

theorem cell23_2000575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_2000575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000575 prefixEnd_2000575 := by exact prefixLift 2000575
  have htrace : WordTrace (prefixWord ++ tailWord_2000575) baseStart_2000575 baseEnd_2000575 := by
    simpa [prefixWord, tailWord_2000575, baseEnd_2000575] using wordTrace_append hprefix tailTrace_2000575
  have hstable : (prefixWord ++ tailWord_2000575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000575).length < 2 ^ (prefixWord ++ tailWord_2000575).sum := by decide
  have hdescent : baseEnd_2000575 < baseStart_2000575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000612 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_2000612 : Nat := 118140960795 + 2000612 * 2 ^ 59
def prefixEnd_2000612 : Nat := 4983230072969 + 3 ^ 40 * 2000612 * 2
def baseEnd_2000612 : Nat := 1027275559152831830049359

theorem tailTrace_2000612 : CollatzResearch.WordTrace tailWord_2000612 prefixEnd_2000612 1027275559152831830049359 := by
  unfold tailWord_2000612
  simp only [CollatzResearch.WordTrace]
  refine ⟨36484157114065938086194045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48645542818754584114925393 36484157114065938086194045)
  ·
    refine ⟨13681558917774726782322767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36484157114065938086194045 13681558917774726782322767)
    ·
      refine ⟨20522338376662090173484151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13681558917774726782322767 20522338376662090173484151)
      ·
        refine ⟨30783507564993135260226227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20522338376662090173484151 30783507564993135260226227)
        ·
          refine ⟨46175261347489702890339341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30783507564993135260226227 46175261347489702890339341)
          ·
            refine ⟨17315723005308638583877253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46175261347489702890339341 17315723005308638583877253)
            ·
              refine ⟨3246698063495369734476985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17315723005308638583877253 3246698063495369734476985)
              ·
                refine ⟨2435023547621527300857739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246698063495369734476985 2435023547621527300857739)
                ·
                  refine ⟨3652535321432290951286609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435023547621527300857739 3652535321432290951286609)
                  ·
                    refine ⟨2739401491074218213464957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3652535321432290951286609 2739401491074218213464957)
                    ·
                      refine ⟨1027275559152831830049359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2739401491074218213464957 1027275559152831830049359)
                      ·
                        rfl

theorem cell23_2000612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_2000612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000612 prefixEnd_2000612 := by exact prefixLift 2000612
  have htrace : WordTrace (prefixWord ++ tailWord_2000612) baseStart_2000612 baseEnd_2000612 := by
    simpa [prefixWord, tailWord_2000612, baseEnd_2000612] using wordTrace_append hprefix tailTrace_2000612
  have hstable : (prefixWord ++ tailWord_2000612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000612).length < 2 ^ (prefixWord ++ tailWord_2000612).sum := by decide
  have hdescent : baseEnd_2000612 < baseStart_2000612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000660 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2000660 : Nat := 118140960795 + 2000660 * 2 ^ 59
def prefixEnd_2000660 : Nat := 4983230072969 + 3 ^ 40 * 2000660 * 2
def baseEnd_2000660 : Nat := 1027300206224247642249139

theorem tailTrace_2000660 : CollatzResearch.WordTrace tailWord_2000660 prefixEnd_2000660 1027300206224247642249139 := by
  unfold tailWord_2000660
  simp only [CollatzResearch.WordTrace]
  refine ⟨36485032465978990185067717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48646709954638653580090289 36485032465978990185067717)
  ·
    refine ⟨6840943587371060659700197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36485032465978990185067717 6840943587371060659700197)
    ·
      refine ⟨1282676922632073873693787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6840943587371060659700197 1282676922632073873693787)
      ·
        refine ⟨1924015383948110810540681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282676922632073873693787 1924015383948110810540681)
        ·
          refine ⟨1443011537961083107905511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1924015383948110810540681 1443011537961083107905511)
          ·
            refine ⟨2164517306941624661858267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443011537961083107905511 2164517306941624661858267)
            ·
              refine ⟨3246775960412436992787401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164517306941624661858267 3246775960412436992787401)
              ·
                refine ⟨2435081970309327744590551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246775960412436992787401 2435081970309327744590551)
                ·
                  refine ⟨3652622955463991616885827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435081970309327744590551 3652622955463991616885827)
                  ·
                    refine ⟨5478934433195987425328741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652622955463991616885827 5478934433195987425328741)
                    ·
                      refine ⟨1027300206224247642249139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5478934433195987425328741 1027300206224247642249139)
                      ·
                        rfl

theorem cell23_2000660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2000660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000660 prefixEnd_2000660 := by exact prefixLift 2000660
  have htrace : WordTrace (prefixWord ++ tailWord_2000660) baseStart_2000660 baseEnd_2000660 := by
    simpa [prefixWord, tailWord_2000660, baseEnd_2000660] using wordTrace_append hprefix tailTrace_2000660
  have hstable : (prefixWord ++ tailWord_2000660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000660).length < 2 ^ (prefixWord ++ tailWord_2000660).sum := by decide
  have hdescent : baseEnd_2000660 < baseStart_2000660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000702 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2000702 : Nat := 118140960795 + 2000702 * 2 ^ 59
def prefixEnd_2000702 : Nat := 4983230072969 + 3 ^ 40 * 2000702 * 2
def baseEnd_2000702 : Nat := 1027321772411736477923945

theorem tailTrace_2000702 : CollatzResearch.WordTrace tailWord_2000702 prefixEnd_2000702 1027321772411736477923945 := by
  unfold tailWord_2000702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121449599725727692895545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48647731198537214362109573 9121449599725727692895545)
  ·
    refine ⟨6841087199794295769671659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9121449599725727692895545 6841087199794295769671659)
    ·
      refine ⟨10261630799691443654507489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6841087199794295769671659 10261630799691443654507489)
      ·
        refine ⟨7696223099768582740880617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10261630799691443654507489 7696223099768582740880617)
        ·
          refine ⟨5772167324826437055660463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7696223099768582740880617 5772167324826437055660463)
          ·
            refine ⟨8658250987239655583490695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772167324826437055660463 8658250987239655583490695)
            ·
              refine ⟨12987376480859483375236043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8658250987239655583490695 12987376480859483375236043)
              ·
                refine ⟨19481064721289225062854065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12987376480859483375236043 19481064721289225062854065)
                ·
                  refine ⟨14610798540966918797140549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19481064721289225062854065 14610798540966918797140549)
                  ·
                    refine ⟨2739524726431297274463853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14610798540966918797140549 2739524726431297274463853)
                    ·
                      refine ⟨1027321772411736477923945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2739524726431297274463853 1027321772411736477923945)
                      ·
                        rfl

theorem cell23_2000702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2000702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000702 prefixEnd_2000702 := by exact prefixLift 2000702
  have htrace : WordTrace (prefixWord ++ tailWord_2000702) baseStart_2000702 baseEnd_2000702 := by
    simpa [prefixWord, tailWord_2000702, baseEnd_2000702] using wordTrace_append hprefix tailTrace_2000702
  have hstable : (prefixWord ++ tailWord_2000702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000702).length < 2 ^ (prefixWord ++ tailWord_2000702).sum := by decide
  have hdescent : baseEnd_2000702 < baseStart_2000702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000735 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 1, 7]
def baseStart_2000735 : Nat := 118140960795 + 2000735 * 2 ^ 59
def prefixEnd_2000735 : Nat := 4983230072969 + 3 ^ 40 * 2000735 * 2
def baseEnd_2000735 : Nat := 342446239091111616270431

theorem tailTrace_2000735 : CollatzResearch.WordTrace tailWord_2000735 prefixEnd_2000735 342446239091111616270431 := by
  unfold tailWord_2000735
  simp only [CollatzResearch.WordTrace]
  refine ⟨72972800406686268179115659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48648533604457512119410439 72972800406686268179115659)
  ·
    refine ⟨109459200610029402268673489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72972800406686268179115659 109459200610029402268673489)
    ·
      refine ⟨82094400457522051701505117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109459200610029402268673489 82094400457522051701505117)
      ·
        refine ⟨30785400171570769388064419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82094400457522051701505117 30785400171570769388064419)
        ·
          refine ⟨46178100257356154082096629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30785400171570769388064419 46178100257356154082096629)
          ·
            refine ⟨4329196899127139445196559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46178100257356154082096629 4329196899127139445196559)
            ·
              refine ⟨6493795348690709167794839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4329196899127139445196559 6493795348690709167794839)
              ·
                refine ⟨9740693023036063751692259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493795348690709167794839 9740693023036063751692259)
                ·
                  refine ⟨14611039534554095627538389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9740693023036063751692259 14611039534554095627538389)
                  ·
                    refine ⟨342446239091111616270431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14611039534554095627538389 342446239091111616270431)
                    ·
                      rfl

theorem cell23_2000735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_2000735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000735 prefixEnd_2000735 := by exact prefixLift 2000735
  have htrace : WordTrace (prefixWord ++ tailWord_2000735) baseStart_2000735 baseEnd_2000735 := by
    simpa [prefixWord, tailWord_2000735, baseEnd_2000735] using wordTrace_append hprefix tailTrace_2000735
  have hstable : (prefixWord ++ tailWord_2000735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000735).length < 2 ^ (prefixWord ++ tailWord_2000735).sum := by decide
  have hdescent : baseEnd_2000735 < baseStart_2000735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000739 : List Nat := [1, 1, 1, 5, 4, 1, 2, 3, 5]
def baseStart_2000739 : Nat := 118140960795 + 2000739 * 2 ^ 59
def prefixEnd_2000739 : Nat := 4983230072969 + 3 ^ 40 * 2000739 * 2
def baseEnd_2000739 : Nat := 114148974577328092573475

theorem tailTrace_2000739 : CollatzResearch.WordTrace tailWord_2000739 prefixEnd_2000739 114148974577328092573475 := by
  unfold tailWord_2000739
  simp only [CollatzResearch.WordTrace]
  refine ⟨72972946298671776862261271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48648630865781184574840847 72972946298671776862261271)
  ·
    refine ⟨109459419448007665293391907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72972946298671776862261271 109459419448007665293391907)
    ·
      refine ⟨164189129172011497940087861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109459419448007665293391907 164189129172011497940087861)
      ·
        refine ⟨15392730859876077931883237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164189129172011497940087861 15392730859876077931883237)
        ·
          refine ⟨2886137036226764612228107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15392730859876077931883237 2886137036226764612228107)
          ·
            refine ⟨4329205554340146918342161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886137036226764612228107 4329205554340146918342161)
            ·
              refine ⟨3246904165755110188756621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4329205554340146918342161 3246904165755110188756621)
              ·
                refine ⟨1217589062158166320783733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3246904165755110188756621 1217589062158166320783733)
                ·
                  refine ⟨114148974577328092573475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1217589062158166320783733 114148974577328092573475)
                  ·
                    rfl

theorem cell23_2000739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 5].length) (baseStart_2000739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000739 prefixEnd_2000739 := by exact prefixLift 2000739
  have htrace : WordTrace (prefixWord ++ tailWord_2000739) baseStart_2000739 baseEnd_2000739 := by
    simpa [prefixWord, tailWord_2000739, baseEnd_2000739] using wordTrace_append hprefix tailTrace_2000739
  have hstable : (prefixWord ++ tailWord_2000739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000739).length < 2 ^ (prefixWord ++ tailWord_2000739).sum := by decide
  have hdescent : baseEnd_2000739 < baseStart_2000739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000755 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 4]
def baseStart_2000755 : Nat := 118140960795 + 2000755 * 2 ^ 59
def prefixEnd_2000755 : Nat := 4983230072969 + 3 ^ 40 * 2000755 * 2
def baseEnd_2000755 : Nat := 1027348986886424770561201

theorem tailTrace_2000755 : CollatzResearch.WordTrace tailWord_2000755 prefixEnd_2000755 1027348986886424770561201 := by
  unfold tailWord_2000755
  simp only [CollatzResearch.WordTrace]
  refine ⟨72973529866613811594843719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48649019911075874396562479 72973529866613811594843719)
  ·
    refine ⟨109460294799920717392265579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72973529866613811594843719 109460294799920717392265579)
    ·
      refine ⟨164190442199881076088398369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109460294799920717392265579 164190442199881076088398369)
      ·
        refine ⟨123142831649910807066298777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164190442199881076088398369 123142831649910807066298777)
        ·
          refine ⟨92357123737433105299724083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123142831649910807066298777 92357123737433105299724083)
          ·
            refine ⟨138535685606149657949586125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92357123737433105299724083 138535685606149657949586125)
            ·
              refine ⟨51950882102306121731094797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138535685606149657949586125 51950882102306121731094797)
              ·
                refine ⟨19481580788364795649160549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51950882102306121731094797 19481580788364795649160549)
                ·
                  refine ⟨3652796397818399184217603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19481580788364795649160549 3652796397818399184217603)
                  ·
                    refine ⟨5479194596727598776326405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3652796397818399184217603 5479194596727598776326405)
                    ·
                      refine ⟨1027348986886424770561201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5479194596727598776326405 1027348986886424770561201)
                      ·
                        rfl

theorem cell23_2000755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_2000755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000755 prefixEnd_2000755 := by exact prefixLift 2000755
  have htrace : WordTrace (prefixWord ++ tailWord_2000755) baseStart_2000755 baseEnd_2000755 := by
    simpa [prefixWord, tailWord_2000755, baseEnd_2000755] using wordTrace_append hprefix tailTrace_2000755
  have hstable : (prefixWord ++ tailWord_2000755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000755).length < 2 ^ (prefixWord ++ tailWord_2000755).sum := by decide
  have hdescent : baseEnd_2000755 < baseStart_2000755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000790 : List Nat := [5, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2000790 : Nat := 118140960795 + 2000790 * 2 ^ 59
def prefixEnd_2000790 : Nat := 4983230072969 + 3 ^ 40 * 2000790 * 2
def baseEnd_2000790 : Nat := 114151884301036903735949

theorem tailTrace_2000790 : CollatzResearch.WordTrace tailWord_2000790 prefixEnd_2000790 114151884301036903735949 := by
  unfold tailWord_2000790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4560925401342938285772989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48649870947658008381578549 4560925401342938285772989)
  ·
    refine ⟨1710347025503601857164871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4560925401342938285772989 1710347025503601857164871)
    ·
      refine ⟨2565520538255402785747307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710347025503601857164871 2565520538255402785747307)
      ·
        refine ⟨3848280807383104178620961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565520538255402785747307 3848280807383104178620961)
        ·
          refine ⟨2886210605537328133965721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3848280807383104178620961 2886210605537328133965721)
          ·
            refine ⟨2164657954152996100474291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886210605537328133965721 2164657954152996100474291)
            ·
              refine ⟨3246986931229494150711437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164657954152996100474291 3246986931229494150711437)
              ·
                refine ⟨1217620099211060306516789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3246986931229494150711437 1217620099211060306516789)
                ·
                  refine ⟨114151884301036903735949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1217620099211060306516789 114151884301036903735949)
                  ·
                    rfl

theorem cell23_2000790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2000790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000790 prefixEnd_2000790 := by exact prefixLift 2000790
  have htrace : WordTrace (prefixWord ++ tailWord_2000790) baseStart_2000790 baseEnd_2000790 := by
    simpa [prefixWord, tailWord_2000790, baseEnd_2000790] using wordTrace_append hprefix tailTrace_2000790
  have hstable : (prefixWord ++ tailWord_2000790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000790).length < 2 ^ (prefixWord ++ tailWord_2000790).sum := by decide
  have hdescent : baseEnd_2000790 < baseStart_2000790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000829 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 6]
def baseStart_2000829 : Nat := 118140960795 + 2000829 * 2 ^ 59
def prefixEnd_2000829 : Nat := 4983230072969 + 3 ^ 40 * 2000829 * 2
def baseEnd_2000829 : Nat := 114154109383873053448429

theorem tailTrace_2000829 : CollatzResearch.WordTrace tailWord_2000829 prefixEnd_2000829 114154109383873053448429 := by
  unfold tailWord_2000829
  simp only [CollatzResearch.WordTrace]
  refine ⟨72976228868345722233037541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48650819245563814822025027 72976228868345722233037541)
  ·
    refine ⟨13683042912814822918694539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72976228868345722233037541 13683042912814822918694539)
    ·
      refine ⟨20524564369222234378041809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13683042912814822918694539 20524564369222234378041809)
      ·
        refine ⟨15393423276916675783531357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20524564369222234378041809 15393423276916675783531357)
        ·
          refine ⟨5772533728843753418824259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15393423276916675783531357 5772533728843753418824259)
          ·
            refine ⟨8658800593265630128236389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772533728843753418824259 8658800593265630128236389)
            ·
              refine ⟨1623525111237305649044323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8658800593265630128236389 1623525111237305649044323)
              ·
                refine ⟨2435287666855958473566485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623525111237305649044323 2435287666855958473566485)
                ·
                  refine ⟨114154109383873053448429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2435287666855958473566485 114154109383873053448429)
                  ·
                    rfl

theorem cell23_2000829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_2000829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000829 prefixEnd_2000829 := by exact prefixLift 2000829
  have htrace : WordTrace (prefixWord ++ tailWord_2000829) baseStart_2000829 baseEnd_2000829 := by
    simpa [prefixWord, tailWord_2000829, baseEnd_2000829] using wordTrace_append hprefix tailTrace_2000829
  have hstable : (prefixWord ++ tailWord_2000829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000829).length < 2 ^ (prefixWord ++ tailWord_2000829).sum := by decide
  have hdescent : baseEnd_2000829 < baseStart_2000829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000856 : List Nat := [2, 1, 2, 2, 2, 2, 2, 5, 1, 1, 3]
def baseStart_2000856 : Nat := 118140960795 + 2000856 * 2 ^ 59
def prefixEnd_2000856 : Nat := 4983230072969 + 3 ^ 40 * 2000856 * 2
def baseEnd_2000856 : Nat := 1027400848432528875398237

theorem tailTrace_2000856 : CollatzResearch.WordTrace tailWord_2000856 prefixEnd_2000856 1027400848432528875398237 := by
  unfold tailWord_2000856
  simp only [CollatzResearch.WordTrace]
  refine ⟨36488606819623952922135211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48651475759498603896180281 36488606819623952922135211)
  ·
    refine ⟨54732910229435929383202817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36488606819623952922135211 54732910229435929383202817)
    ·
      refine ⟨41049682672076947037402113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54732910229435929383202817 41049682672076947037402113)
      ·
        refine ⟨30787262004057710278051585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41049682672076947037402113 30787262004057710278051585)
        ·
          refine ⟨23090446503043282708538689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30787262004057710278051585 23090446503043282708538689)
          ·
            refine ⟨17317834877282462031404017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23090446503043282708538689 17317834877282462031404017)
            ·
              refine ⟨12988376157961846523553013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17317834877282462031404017 12988376157961846523553013)
              ·
                refine ⟨1217660264808923111583095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12988376157961846523553013 1217660264808923111583095)
                ·
                  refine ⟨1826490397213384667374643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217660264808923111583095 1826490397213384667374643)
                  ·
                    refine ⟨2739735595820077001061965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1826490397213384667374643 2739735595820077001061965)
                    ·
                      refine ⟨1027400848432528875398237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2739735595820077001061965 1027400848432528875398237)
                      ·
                        rfl

theorem cell23_2000856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_2000856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000856 prefixEnd_2000856 := by exact prefixLift 2000856
  have htrace : WordTrace (prefixWord ++ tailWord_2000856) baseStart_2000856 baseEnd_2000856 := by
    simpa [prefixWord, tailWord_2000856, baseEnd_2000856] using wordTrace_append hprefix tailTrace_2000856
  have hstable : (prefixWord ++ tailWord_2000856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000856).length < 2 ^ (prefixWord ++ tailWord_2000856).sum := by decide
  have hdescent : baseEnd_2000856 < baseStart_2000856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000875 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 6]
def baseStart_2000875 : Nat := 118140960795 + 2000875 * 2 ^ 59
def prefixEnd_2000875 : Nat := 4983230072969 + 3 ^ 40 * 2000875 * 2
def baseEnd_2000875 : Nat := 1027410604564964301060649

theorem tailTrace_2000875 : CollatzResearch.WordTrace tailWord_2000875 prefixEnd_2000875 1027410604564964301060649 := by
  unfold tailWord_2000875
  simp only [CollatzResearch.WordTrace]
  refine ⟨72977906626179072089212079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48651937750786048059474719 72977906626179072089212079)
  ·
    refine ⟨109466859939268608133818119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72977906626179072089212079 109466859939268608133818119)
    ·
      refine ⟨164200289908902912200727179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109466859939268608133818119 164200289908902912200727179)
      ·
        refine ⟨246300434863354368301090769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164200289908902912200727179 246300434863354368301090769)
        ·
          refine ⟨184725326147515776225818077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246300434863354368301090769 184725326147515776225818077)
          ·
            refine ⟨69271997305318416084681779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 184725326147515776225818077 69271997305318416084681779)
            ·
              refine ⟨103907995957977624127022669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69271997305318416084681779 103907995957977624127022669)
              ·
                refine ⟨38965498484241609047633501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103907995957977624127022669 38965498484241609047633501)
                ·
                  refine ⟨14612061931590603392862563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38965498484241609047633501 14612061931590603392862563)
                  ·
                    refine ⟨21918092897385905089293845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14612061931590603392862563 21918092897385905089293845)
                    ·
                      refine ⟨1027410604564964301060649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21918092897385905089293845 1027410604564964301060649)
                      ·
                        rfl

theorem cell23_2000875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_2000875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000875 prefixEnd_2000875 := by exact prefixLift 2000875
  have htrace : WordTrace (prefixWord ++ tailWord_2000875) baseStart_2000875 baseEnd_2000875 := by
    simpa [prefixWord, tailWord_2000875, baseEnd_2000875] using wordTrace_append hprefix tailTrace_2000875
  have hstable : (prefixWord ++ tailWord_2000875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000875).length < 2 ^ (prefixWord ++ tailWord_2000875).sum := by decide
  have hdescent : baseEnd_2000875 < baseStart_2000875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000889 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 2, 4]
def baseStart_2000889 : Nat := 118140960795 + 2000889 * 2 ^ 59
def prefixEnd_2000889 : Nat := 4983230072969 + 3 ^ 40 * 2000889 * 2
def baseEnd_2000889 : Nat := 342472597764709082095195

theorem tailTrace_2000889 : CollatzResearch.WordTrace tailWord_2000889 prefixEnd_2000889 342472597764709082095195 := by
  unfold tailWord_2000889
  simp only [CollatzResearch.WordTrace]
  refine ⟨72978417248128352480221721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48652278165418901653481147 72978417248128352480221721)
  ·
    refine ⟨54733812936096264360166291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72978417248128352480221721 54733812936096264360166291)
    ·
      refine ⟨82100719404144396540249437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54733812936096264360166291 82100719404144396540249437)
      ·
        refine ⟨30787769776554148702593539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82100719404144396540249437 30787769776554148702593539)
        ·
          refine ⟨46181654664831223053890309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30787769776554148702593539 46181654664831223053890309)
          ·
            refine ⟨8659060249655854322604433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46181654664831223053890309 8659060249655854322604433)
            ·
              refine ⟨6494295187241890741953325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8659060249655854322604433 6494295187241890741953325)
              ·
                refine ⟨2435360695215709028232497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6494295187241890741953325 2435360695215709028232497)
                ·
                  refine ⟨1826520521411781771174373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2435360695215709028232497 1826520521411781771174373)
                  ·
                    refine ⟨342472597764709082095195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1826520521411781771174373 342472597764709082095195)
                    ·
                      rfl

theorem cell23_2000889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4].length) (baseStart_2000889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000889 prefixEnd_2000889 := by exact prefixLift 2000889
  have htrace : WordTrace (prefixWord ++ tailWord_2000889) baseStart_2000889 baseEnd_2000889 := by
    simpa [prefixWord, tailWord_2000889, baseEnd_2000889] using wordTrace_append hprefix tailTrace_2000889
  have hstable : (prefixWord ++ tailWord_2000889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000889).length < 2 ^ (prefixWord ++ tailWord_2000889).sum := by decide
  have hdescent : baseEnd_2000889 < baseStart_2000889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000895 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_2000895 : Nat := 118140960795 + 2000895 * 2 ^ 59
def prefixEnd_2000895 : Nat := 4983230072969 + 3 ^ 40 * 2000895 * 2
def baseEnd_2000895 : Nat := 1027420874178054222810557

theorem tailTrace_2000895 : CollatzResearch.WordTrace tailWord_2000895 prefixEnd_2000895 1027420874178054222810557 := by
  unfold tailWord_2000895
  simp only [CollatzResearch.WordTrace]
  refine ⟨72978636086106615504940139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48652424057404410336626759 72978636086106615504940139)
  ·
    refine ⟨109467954129159923257410209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72978636086106615504940139 109467954129159923257410209)
    ·
      refine ⟨82100965596869942443057657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109467954129159923257410209 82100965596869942443057657)
      ·
        refine ⟨61575724197652456832293243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82100965596869942443057657 61575724197652456832293243)
        ·
          refine ⟨92363586296478685248439865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61575724197652456832293243 92363586296478685248439865)
          ·
            refine ⟨69272689722359013936329899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92363586296478685248439865 69272689722359013936329899)
            ·
              refine ⟨103909034583538520904494849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69272689722359013936329899 103909034583538520904494849)
              ·
                refine ⟨77931775937653890678371137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103909034583538520904494849 77931775937653890678371137)
                ·
                  refine ⟨58448831953240418008778353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77931775937653890678371137 58448831953240418008778353)
                  ·
                    refine ⟨43836623964930313506583765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58448831953240418008778353 43836623964930313506583765)
                    ·
                      refine ⟨1027420874178054222810557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43836623964930313506583765 1027420874178054222810557)
                      ·
                        rfl

theorem cell23_2000895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_2000895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000895 prefixEnd_2000895 := by exact prefixLift 2000895
  have htrace : WordTrace (prefixWord ++ tailWord_2000895) baseStart_2000895 baseEnd_2000895 := by
    simpa [prefixWord, tailWord_2000895, baseEnd_2000895] using wordTrace_append hprefix tailTrace_2000895
  have hstable : (prefixWord ++ tailWord_2000895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000895).length < 2 ^ (prefixWord ++ tailWord_2000895).sum := by decide
  have hdescent : baseEnd_2000895 < baseStart_2000895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000900 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2000900 : Nat := 118140960795 + 2000900 * 2 ^ 59
def prefixEnd_2000900 : Nat := 4983230072969 + 3 ^ 40 * 2000900 * 2
def baseEnd_2000900 : Nat := 1027423441581326703248035

theorem tailTrace_2000900 : CollatzResearch.WordTrace tailWord_2000900 prefixEnd_2000900 1027423441581326703248035 := by
  unfold tailWord_2000900
  simp only [CollatzResearch.WordTrace]
  refine ⟨36489409225544250679436077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48652545634059000905914769 36489409225544250679436077)
  ·
    refine ⟨13683528459579094004788529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36489409225544250679436077 13683528459579094004788529)
    ·
      refine ⟨10262646344684320503591397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13683528459579094004788529 10262646344684320503591397)
      ·
        refine ⟨1924246189628310094423387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10262646344684320503591397 1924246189628310094423387)
        ·
          refine ⟨2886369284442465141635081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924246189628310094423387 2886369284442465141635081)
          ·
            refine ⟨2164776963331848856226311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886369284442465141635081 2164776963331848856226311)
            ·
              refine ⟨3247165444997773284339467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164776963331848856226311 3247165444997773284339467)
              ·
                refine ⟨4870748167496659926509201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247165444997773284339467 4870748167496659926509201)
                ·
                  refine ⟨3653061125622494944881901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4870748167496659926509201 3653061125622494944881901)
                  ·
                    refine ⟨1369897922108435604330713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653061125622494944881901 1369897922108435604330713)
                    ·
                      refine ⟨1027423441581326703248035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369897922108435604330713 1027423441581326703248035)
                      ·
                        rfl

theorem cell23_2000900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2000900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000900 prefixEnd_2000900 := by exact prefixLift 2000900
  have htrace : WordTrace (prefixWord ++ tailWord_2000900) baseStart_2000900 baseEnd_2000900 := by
    simpa [prefixWord, tailWord_2000900, baseEnd_2000900] using wordTrace_append hprefix tailTrace_2000900
  have hstable : (prefixWord ++ tailWord_2000900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000900).length < 2 ^ (prefixWord ++ tailWord_2000900).sum := by decide
  have hdescent : baseEnd_2000900 < baseStart_2000900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000939 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 3, 3, 2]
def baseStart_2000939 : Nat := 118140960795 + 2000939 * 2 ^ 59
def prefixEnd_2000939 : Nat := 4983230072969 + 3 ^ 40 * 2000939 * 2
def baseEnd_2000939 : Nat := 1027443467326852050660355

theorem tailTrace_2000939 : CollatzResearch.WordTrace tailWord_2000939 prefixEnd_2000939 1027443467326852050660355 := by
  unfold tailWord_2000939
  simp only [CollatzResearch.WordTrace]
  refine ⟨72980240897947211019541871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48653493931964807346361247 72980240897947211019541871)
  ·
    refine ⟨109470361346920816529312807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72980240897947211019541871 109470361346920816529312807)
    ·
      refine ⟨164205542020381224793969211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109470361346920816529312807 164205542020381224793969211)
      ·
        refine ⟨246308313030571837190953817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164205542020381224793969211 246308313030571837190953817)
        ·
          refine ⟨184731234772928877893215363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246308313030571837190953817 184731234772928877893215363)
          ·
            refine ⟨277096852159393316839823045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184731234772928877893215363 277096852159393316839823045)
            ·
              refine ⟨51955659779886246907466821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277096852159393316839823045 51955659779886246907466821)
              ·
                refine ⟨9741686208728671295150029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51955659779886246907466821 9741686208728671295150029)
                ·
                  refine ⟨3653132328273251735681261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9741686208728671295150029 3653132328273251735681261)
                  ·
                    refine ⟨1369924623102469400880473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653132328273251735681261 1369924623102469400880473)
                    ·
                      refine ⟨1027443467326852050660355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369924623102469400880473 1027443467326852050660355)
                      ·
                        rfl

theorem cell23_2000939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 3, 2].length) (baseStart_2000939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000939 prefixEnd_2000939 := by exact prefixLift 2000939
  have htrace : WordTrace (prefixWord ++ tailWord_2000939) baseStart_2000939 baseEnd_2000939 := by
    simpa [prefixWord, tailWord_2000939, baseEnd_2000939] using wordTrace_append hprefix tailTrace_2000939
  have hstable : (prefixWord ++ tailWord_2000939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000939).length < 2 ^ (prefixWord ++ tailWord_2000939).sum := by decide
  have hdescent : baseEnd_2000939 < baseStart_2000939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000946 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2000946 : Nat := 118140960795 + 2000946 * 2 ^ 59
def prefixEnd_2000946 : Nat := 4983230072969 + 3 ^ 40 * 2000946 * 2
def baseEnd_2000946 : Nat := 1027447061691433523272823

theorem tailTrace_2000946 : CollatzResearch.WordTrace tailWord_2000946 prefixEnd_2000946 1027447061691433523272823 := by
  unfold tailWord_2000946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245124052230462803761673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48653664139281234143364461 18245124052230462803761673)
  ·
    refine ⟨13683843039172847102821255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18245124052230462803761673 13683843039172847102821255)
    ·
      refine ⟨20525764558759270654231883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13683843039172847102821255 20525764558759270654231883)
      ·
        refine ⟨30788646838138905981347825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20525764558759270654231883 30788646838138905981347825)
        ·
          refine ⟨23091485128604179486010869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30788646838138905981347825 23091485128604179486010869)
          ·
            refine ⟨2164826730806641826813519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23091485128604179486010869 2164826730806641826813519)
            ·
              refine ⟨3247240096209962740220279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164826730806641826813519 3247240096209962740220279)
              ·
                refine ⟨4870860144314944110330419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247240096209962740220279 4870860144314944110330419)
                ·
                  refine ⟨7306290216472416165495629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4870860144314944110330419 7306290216472416165495629)
                  ·
                    refine ⟨2739858831177156062060861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7306290216472416165495629 2739858831177156062060861)
                    ·
                      refine ⟨1027447061691433523272823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2739858831177156062060861 1027447061691433523272823)
                      ·
                        rfl

theorem cell23_2000946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2000946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000946 prefixEnd_2000946 := by exact prefixLift 2000946
  have htrace : WordTrace (prefixWord ++ tailWord_2000946) baseStart_2000946 baseEnd_2000946 := by
    simpa [prefixWord, tailWord_2000946, baseEnd_2000946] using wordTrace_append hprefix tailTrace_2000946
  have hstable : (prefixWord ++ tailWord_2000946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000946).length < 2 ^ (prefixWord ++ tailWord_2000946).sum := by decide
  have hdescent : baseEnd_2000946 < baseStart_2000946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000969 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 3, 4, 2]
def baseStart_2000969 : Nat := 118140960795 + 2000969 * 2 ^ 59
def prefixEnd_2000969 : Nat := 4983230072969 + 3 ^ 40 * 2000969 * 2
def baseEnd_2000969 : Nat := 1027458871746486933285217

theorem tailTrace_2000969 : CollatzResearch.WordTrace tailWord_2000969 prefixEnd_2000969 1027458871746486933285217 := by
  unfold tailWord_2000969
  simp only [CollatzResearch.WordTrace]
  refine ⟨72981335087838526143133961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48654223391892350762089307 72981335087838526143133961)
  ·
    refine ⟨54736001315878894607350471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72981335087838526143133961 54736001315878894607350471)
    ·
      refine ⟨82104001973818341911025707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54736001315878894607350471 82104001973818341911025707)
      ·
        refine ⟨123156002960727512866538561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82104001973818341911025707 123156002960727512866538561)
        ·
          refine ⟨92367002220545634649903921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123156002960727512866538561 92367002220545634649903921)
          ·
            refine ⟨69275251665409225987427941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92367002220545634649903921 69275251665409225987427941)
            ·
              refine ⟨12989109687264229872642739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69275251665409225987427941 12989109687264229872642739)
              ·
                refine ⟨19483664530896344808964109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12989109687264229872642739 19483664530896344808964109)
                ·
                  refine ⟨7306374199086129303361541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19483664530896344808964109 7306374199086129303361541)
                  ·
                    refine ⟨1369945162328649244380289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7306374199086129303361541 1369945162328649244380289)
                    ·
                      refine ⟨1027458871746486933285217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369945162328649244380289 1027458871746486933285217)
                      ·
                        rfl

theorem cell23_2000969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 4, 2].length) (baseStart_2000969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000969 prefixEnd_2000969 := by exact prefixLift 2000969
  have htrace : WordTrace (prefixWord ++ tailWord_2000969) baseStart_2000969 baseEnd_2000969 := by
    simpa [prefixWord, tailWord_2000969, baseEnd_2000969] using wordTrace_append hprefix tailTrace_2000969
  have hstable : (prefixWord ++ tailWord_2000969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000969).length < 2 ^ (prefixWord ++ tailWord_2000969).sum := by decide
  have hdescent : baseEnd_2000969 < baseStart_2000969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000972 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2000972 : Nat := 118140960795 + 2000972 * 2 ^ 59
def prefixEnd_2000972 : Nat := 4983230072969 + 3 ^ 40 * 2000972 * 2
def baseEnd_2000972 : Nat := 1027460412188450421547703

theorem tailTrace_2000972 : CollatzResearch.WordTrace tailWord_2000972 prefixEnd_2000972 1027460412188450421547703 := by
  unfold tailWord_2000972
  simp only [CollatzResearch.WordTrace]
  refine ⟨36490722253413828827746585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48654296337885105103662113 36490722253413828827746585)
  ·
    refine ⟨27368041690060371620809939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36490722253413828827746585 27368041690060371620809939)
    ·
      refine ⟨41052062535090557431214909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27368041690060371620809939 41052062535090557431214909)
      ·
        refine ⟨15394523450658959036705591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41052062535090557431214909 15394523450658959036705591)
        ·
          refine ⟨23091785175988438555058387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15394523450658959036705591 23091785175988438555058387)
          ·
            refine ⟨34637677763982657832587581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23091785175988438555058387 34637677763982657832587581)
            ·
              refine ⟨12989129161493496687220343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34637677763982657832587581 12989129161493496687220343)
              ·
                refine ⟨19483693742240245030830515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12989129161493496687220343 19483693742240245030830515)
                ·
                  refine ⟨29225540613360367546245773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19483693742240245030830515 29225540613360367546245773)
                  ·
                    refine ⟨10959577730010137829842165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29225540613360367546245773 10959577730010137829842165)
                    ·
                      refine ⟨1027460412188450421547703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10959577730010137829842165 1027460412188450421547703)
                      ·
                        rfl

theorem cell23_2000972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2000972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000972 prefixEnd_2000972 := by exact prefixLift 2000972
  have htrace : WordTrace (prefixWord ++ tailWord_2000972) baseStart_2000972 baseEnd_2000972 := by
    simpa [prefixWord, tailWord_2000972, baseEnd_2000972] using wordTrace_append hprefix tailTrace_2000972
  have hstable : (prefixWord ++ tailWord_2000972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000972).length < 2 ^ (prefixWord ++ tailWord_2000972).sum := by decide
  have hdescent : baseEnd_2000972 < baseStart_2000972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000973 : List Nat := [1, 6, 1, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_2000973 : Nat := 118140960795 + 2000973 * 2 ^ 59
def prefixEnd_2000973 : Nat := 4983230072969 + 3 ^ 40 * 2000973 * 2
def baseEnd_2000973 : Nat := 1027460925669104917635199

theorem tailTrace_2000973 : CollatzResearch.WordTrace tailWord_2000973 prefixEnd_2000973 1027460925669104917635199 := by
  unfold tailWord_2000973
  simp only [CollatzResearch.WordTrace]
  refine ⟨72981480979824034826279573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48654320653216023217519715 72981480979824034826279573)
  ·
    refine ⟨3421006920929251632481855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72981480979824034826279573 3421006920929251632481855)
    ·
      refine ⟨5131510381393877448722783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421006920929251632481855 5131510381393877448722783)
      ·
        refine ⟨7697265572090816173084175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131510381393877448722783 7697265572090816173084175)
        ·
          refine ⟨11545898358136224259626263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7697265572090816173084175 11545898358136224259626263)
          ·
            refine ⟨17318847537204336389439395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11545898358136224259626263 17318847537204336389439395)
            ·
              refine ⟨25978271305806504584159093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17318847537204336389439395 25978271305806504584159093)
              ·
                refine ⟨2435462934919359804764915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25978271305806504584159093 2435462934919359804764915)
                ·
                  refine ⟨3653194402379039707147373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435462934919359804764915 3653194402379039707147373)
                  ·
                    refine ⟨1369947900892139890180265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653194402379039707147373 1369947900892139890180265)
                    ·
                      refine ⟨1027460925669104917635199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369947900892139890180265 1027460925669104917635199)
                      ·
                        rfl

theorem cell23_2000973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_2000973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000973 prefixEnd_2000973 := by exact prefixLift 2000973
  have htrace : WordTrace (prefixWord ++ tailWord_2000973) baseStart_2000973 baseEnd_2000973 := by
    simpa [prefixWord, tailWord_2000973, baseEnd_2000973] using wordTrace_append hprefix tailTrace_2000973
  have hstable : (prefixWord ++ tailWord_2000973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000973).length < 2 ^ (prefixWord ++ tailWord_2000973).sum := by decide
  have hdescent : baseEnd_2000973 < baseStart_2000973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2000986 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2]
def baseStart_2000986 : Nat := 118140960795 + 2000986 * 2 ^ 59
def prefixEnd_2000986 : Nat := 4983230072969 + 3 ^ 40 * 2000986 * 2
def baseEnd_2000986 : Nat := 1027467600917613366772639

theorem tailTrace_2000986 : CollatzResearch.WordTrace tailWord_2000986 prefixEnd_2000986 1027467600917613366772639 := by
  unfold tailWord_2000986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245488782194234511625703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48654636752517958697668541 18245488782194234511625703)
  ·
    refine ⟨27368233173291351767438555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18245488782194234511625703 27368233173291351767438555)
    ·
      refine ⟨41052349759937027651157833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27368233173291351767438555 41052349759937027651157833)
      ·
        refine ⟨30789262319952770738368375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41052349759937027651157833 30789262319952770738368375)
        ·
          refine ⟨46183893479929156107552563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30789262319952770738368375 46183893479929156107552563)
          ·
            refine ⟨69275840219893734161328845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46183893479929156107552563 69275840219893734161328845)
            ·
              refine ⟨25978440082460150310498317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69275840219893734161328845 25978440082460150310498317)
              ·
                refine ⟨9741915030922556366436869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25978440082460150310498317 9741915030922556366436869)
                ·
                  refine ⟨1826609068297979318706913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9741915030922556366436869 1826609068297979318706913)
                  ·
                    refine ⟨1369956801223484489030185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1826609068297979318706913 1369956801223484489030185)
                    ·
                      refine ⟨1027467600917613366772639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1369956801223484489030185 1027467600917613366772639)
                      ·
                        rfl

theorem cell23_2000986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_2000986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2000986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2000986 prefixEnd_2000986 := by exact prefixLift 2000986
  have htrace : WordTrace (prefixWord ++ tailWord_2000986) baseStart_2000986 baseEnd_2000986 := by
    simpa [prefixWord, tailWord_2000986, baseEnd_2000986] using wordTrace_append hprefix tailTrace_2000986
  have hstable : (prefixWord ++ tailWord_2000986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2000986).length < 2 ^ (prefixWord ++ tailWord_2000986).sum := by decide
  have hdescent : baseEnd_2000986 < baseStart_2000986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2000986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001072 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_2001072 : Nat := 118140960795 + 2001072 * 2 ^ 59
def prefixEnd_2001072 : Nat := 4983230072969 + 3 ^ 40 * 2001072 * 2
def baseEnd_2001072 : Nat := 1027511760253900030297243

theorem tailTrace_2001072 : CollatzResearch.WordTrace tailWord_2001072 prefixEnd_2001072 1027511760253900030297243 := by
  unfold tailWord_2001072
  simp only [CollatzResearch.WordTrace]
  refine ⟨36492545903232687367066735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48656727870976916489422313 36492545903232687367066735)
  ·
    refine ⟨54738818854849031050600103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36492545903232687367066735 54738818854849031050600103)
    ·
      refine ⟨82108228282273546575900155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54738818854849031050600103 82108228282273546575900155)
      ·
        refine ⟨123162342423410319863850233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82108228282273546575900155 123162342423410319863850233)
        ·
          refine ⟨92371756817557739897887675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123162342423410319863850233 92371756817557739897887675)
          ·
            refine ⟨138557635226336609846831513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92371756817557739897887675 138557635226336609846831513)
            ·
              refine ⟨103918226419752457385123635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138557635226336609846831513 103918226419752457385123635)
              ·
                refine ⟨155877339629628686077685453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103918226419752457385123635 155877339629628686077685453)
                ·
                  refine ⟨58454002361110757279132045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155877339629628686077685453 58454002361110757279132045)
                  ·
                    refine ⟨21920250885416533979674517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58454002361110757279132045 21920250885416533979674517)
                    ·
                      refine ⟨1027511760253900030297243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21920250885416533979674517 1027511760253900030297243)
                      ·
                        rfl

theorem cell23_2001072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_2001072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001072 prefixEnd_2001072 := by exact prefixLift 2001072
  have htrace : WordTrace (prefixWord ++ tailWord_2001072) baseStart_2001072 baseEnd_2001072 := by
    simpa [prefixWord, tailWord_2001072, baseEnd_2001072] using wordTrace_append hprefix tailTrace_2001072
  have hstable : (prefixWord ++ tailWord_2001072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001072).length < 2 ^ (prefixWord ++ tailWord_2001072).sum := by decide
  have hdescent : baseEnd_2001072 < baseStart_2001072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001073 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 2, 5]
def baseStart_2001073 : Nat := 118140960795 + 2001073 * 2 ^ 59
def prefixEnd_2001073 : Nat := 4983230072969 + 3 ^ 40 * 2001073 * 2
def baseEnd_2001073 : Nat := 342504091244851508794913

theorem tailTrace_2001073 : CollatzResearch.WordTrace tailWord_2001073 prefixEnd_2001073 342504091244851508794913 := by
  unfold tailWord_2001073
  simp only [CollatzResearch.WordTrace]
  refine ⟨72985128279461751904919873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48656752186307834603279915 72985128279461751904919873)
  ·
    refine ⟨54738846209596313928689905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72985128279461751904919873 54738846209596313928689905)
    ·
      refine ⟨41054134657197235446517429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54738846209596313928689905 41054134657197235446517429)
      ·
        refine ⟨3848825124112240823111009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41054134657197235446517429 3848825124112240823111009)
        ·
          refine ⟨2886618843084180617333257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3848825124112240823111009 2886618843084180617333257)
          ·
            refine ⟨2164964132313135462999943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886618843084180617333257 2164964132313135462999943)
            ·
              refine ⟨3247446198469703194499915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164964132313135462999943 3247446198469703194499915)
              ·
                refine ⟨4871169297704554791749873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247446198469703194499915 4871169297704554791749873)
                ·
                  refine ⟨3653376973278416093812405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871169297704554791749873 3653376973278416093812405)
                  ·
                    refine ⟨342504091244851508794913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3653376973278416093812405 342504091244851508794913)
                    ·
                      rfl

theorem cell23_2001073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_2001073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001073 prefixEnd_2001073 := by exact prefixLift 2001073
  have htrace : WordTrace (prefixWord ++ tailWord_2001073) baseStart_2001073 baseEnd_2001073 := by
    simpa [prefixWord, tailWord_2001073, baseEnd_2001073] using wordTrace_append hprefix tailTrace_2001073
  have hstable : (prefixWord ++ tailWord_2001073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001073).length < 2 ^ (prefixWord ++ tailWord_2001073).sum := by decide
  have hdescent : baseEnd_2001073 < baseStart_2001073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001110 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_2001110 : Nat := 118140960795 + 2001110 * 2 ^ 59
def prefixEnd_2001110 : Nat := 4983230072969 + 3 ^ 40 * 2001110 * 2
def baseEnd_2001110 : Nat := 1027531272518770881622069

theorem tailTrace_2001110 : CollatzResearch.WordTrace tailWord_2001110 prefixEnd_2001110 1027531272518770881622069 := by
  unfold tailWord_2001110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561654861270481701501049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48657651853551804816011189 4561654861270481701501049)
  ·
    refine ⟨3421241145952861276125787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4561654861270481701501049 3421241145952861276125787)
    ·
      refine ⟨5131861718929291914188681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421241145952861276125787 5131861718929291914188681)
      ·
        refine ⟨3848896289196968935641511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5131861718929291914188681 3848896289196968935641511)
        ·
          refine ⟨5773344433795453403462267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848896289196968935641511 5773344433795453403462267)
          ·
            refine ⟨8660016650693180105193401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773344433795453403462267 8660016650693180105193401)
            ·
              refine ⟨6495012488019885078895051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8660016650693180105193401 6495012488019885078895051)
              ·
                refine ⟨9742518732029827618342577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495012488019885078895051 9742518732029827618342577)
                ·
                  refine ⟨7306889049022370713756933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9742518732029827618342577 7306889049022370713756933)
                  ·
                    refine ⟨1370041696691694508829425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7306889049022370713756933 1370041696691694508829425)
                    ·
                      refine ⟨1027531272518770881622069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370041696691694508829425 1027531272518770881622069)
                      ·
                        rfl

theorem cell23_2001110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_2001110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001110 prefixEnd_2001110 := by exact prefixLift 2001110
  have htrace : WordTrace (prefixWord ++ tailWord_2001110) baseStart_2001110 baseEnd_2001110 := by
    simpa [prefixWord, tailWord_2001110, baseEnd_2001110] using wordTrace_append hprefix tailTrace_2001110
  have hstable : (prefixWord ++ tailWord_2001110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001110).length < 2 ^ (prefixWord ++ tailWord_2001110).sum := by decide
  have hdescent : baseEnd_2001110 < baseStart_2001110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001136 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 6, 3, 2]
def baseStart_2001136 : Nat := 118140960795 + 2001136 * 2 ^ 59
def prefixEnd_2001136 : Nat := 4983230072969 + 3 ^ 40 * 2001136 * 2
def baseEnd_2001136 : Nat := 1027544623015787779896949

theorem tailTrace_2001136 : CollatzResearch.WordTrace tailWord_2001136 prefixEnd_2001136 1027544623015787779896949 := by
  unfold tailWord_2001136
  simp only [CollatzResearch.WordTrace]
  refine ⟨36493713039116756832231631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48658284052155675776308841 36493713039116756832231631)
  ·
    refine ⟨54740569558675135248347447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36493713039116756832231631 54740569558675135248347447)
    ·
      refine ⟨82110854338012702872521171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54740569558675135248347447 82110854338012702872521171)
      ·
        refine ⟨123166281507019054308781757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82110854338012702872521171 123166281507019054308781757)
        ·
          refine ⟨46187355565132145365793159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123166281507019054308781757 46187355565132145365793159)
          ·
            refine ⟨69281033347698218048689739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46187355565132145365793159 69281033347698218048689739)
            ·
              refine ⟨103921550021547327073034609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69281033347698218048689739 103921550021547327073034609)
              ·
                refine ⟨77941162516160495304775957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103921550021547327073034609 77941162516160495304775957)
                ·
                  refine ⟨3653491992945023217411373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77941162516160495304775957 3653491992945023217411373)
                  ·
                    refine ⟨1370059497354383706529265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653491992945023217411373 1370059497354383706529265)
                    ·
                      refine ⟨1027544623015787779896949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370059497354383706529265 1027544623015787779896949)
                      ·
                        rfl

theorem cell23_2001136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 6, 3, 2].length) (baseStart_2001136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001136 prefixEnd_2001136 := by exact prefixLift 2001136
  have htrace : WordTrace (prefixWord ++ tailWord_2001136) baseStart_2001136 baseEnd_2001136 := by
    simpa [prefixWord, tailWord_2001136, baseEnd_2001136] using wordTrace_append hprefix tailTrace_2001136
  have hstable : (prefixWord ++ tailWord_2001136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001136).length < 2 ^ (prefixWord ++ tailWord_2001136).sum := by decide
  have hdescent : baseEnd_2001136 < baseStart_2001136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001146 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 1, 5]
def baseStart_2001146 : Nat := 118140960795 + 2001146 * 2 ^ 59
def prefixEnd_2001146 : Nat := 4983230072969 + 3 ^ 40 * 2001146 * 2
def baseEnd_2001146 : Nat := 342516585940777580257301

theorem tailTrace_2001146 : CollatzResearch.WordTrace tailWord_2001146 prefixEnd_2001146 342516585940777580257301 := by
  unfold tailWord_2001146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18246947702049321343081823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48658527205464856914884861 18246947702049321343081823)
  ·
    refine ⟨27370421553073982014622735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18246947702049321343081823 27370421553073982014622735)
    ·
      refine ⟨41055632329610973021934103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27370421553073982014622735 41055632329610973021934103)
      ·
        refine ⟨61583448494416459532901155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41055632329610973021934103 61583448494416459532901155)
        ·
          refine ⟨92375172741624689299351733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61583448494416459532901155 92375172741624689299351733)
          ·
            refine ⟨8660172444527314621814225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92375172741624689299351733 8660172444527314621814225)
            ·
              refine ⟨6495129333395485966360669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8660172444527314621814225 6495129333395485966360669)
              ·
                refine ⟨2435673500023307237385251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6495129333395485966360669 2435673500023307237385251)
                ·
                  refine ⟨3653510250034960856077877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435673500023307237385251 3653510250034960856077877)
                  ·
                    refine ⟨342516585940777580257301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3653510250034960856077877 342516585940777580257301)
                    ·
                      rfl

theorem cell23_2001146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_2001146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001146 prefixEnd_2001146 := by exact prefixLift 2001146
  have htrace : WordTrace (prefixWord ++ tailWord_2001146) baseStart_2001146 baseEnd_2001146 := by
    simpa [prefixWord, tailWord_2001146, baseEnd_2001146] using wordTrace_append hprefix tailTrace_2001146
  have hstable : (prefixWord ++ tailWord_2001146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001146).length < 2 ^ (prefixWord ++ tailWord_2001146).sum := by decide
  have hdescent : baseEnd_2001146 < baseStart_2001146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001153 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_2001153 : Nat := 118140960795 + 2001153 * 2 ^ 59
def prefixEnd_2001153 : Nat := 4983230072969 + 3 ^ 40 * 2001153 * 2
def baseEnd_2001153 : Nat := 1027553352186914213384371

theorem tailTrace_2001153 : CollatzResearch.WordTrace tailWord_2001153 prefixEnd_2001153 1027553352186914213384371 := by
  unfold tailWord_2001153
  simp only [CollatzResearch.WordTrace]
  refine ⟨72988046119171925567832113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48658697412781283711888075 72988046119171925567832113)
  ·
    refine ⟨54741034589378944175874085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72988046119171925567832113 54741034589378944175874085)
    ·
      refine ⟨10263943985508552032976391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54741034589378944175874085 10263943985508552032976391)
      ·
        refine ⟨15395915978262828049464587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10263943985508552032976391 15395915978262828049464587)
        ·
          refine ⟨23093873967394242074196881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15395915978262828049464587 23093873967394242074196881)
          ·
            refine ⟨17320405475545681555647661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23093873967394242074196881 17320405475545681555647661)
            ·
              refine ⟨6495152053329630583367873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17320405475545681555647661 6495152053329630583367873)
              ·
                refine ⟨4871364039997222937525905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6495152053329630583367873 4871364039997222937525905)
                ·
                  refine ⟨3653523029997917203144429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871364039997222937525905 3653523029997917203144429)
                  ·
                    refine ⟨1370071136249218951179161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653523029997917203144429 1370071136249218951179161)
                    ·
                      refine ⟨1027553352186914213384371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370071136249218951179161 1027553352186914213384371)
                      ·
                        rfl

theorem cell23_2001153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_2001153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001153 prefixEnd_2001153 := by exact prefixLift 2001153
  have htrace : WordTrace (prefixWord ++ tailWord_2001153) baseStart_2001153 baseEnd_2001153 := by
    simpa [prefixWord, tailWord_2001153, baseEnd_2001153] using wordTrace_append hprefix tailTrace_2001153
  have hstable : (prefixWord ++ tailWord_2001153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001153).length < 2 ^ (prefixWord ++ tailWord_2001153).sum := by decide
  have hdescent : baseEnd_2001153 < baseStart_2001153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001160 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_2001160 : Nat := 118140960795 + 2001160 * 2 ^ 59
def prefixEnd_2001160 : Nat := 4983230072969 + 3 ^ 40 * 2001160 * 2
def baseEnd_2001160 : Nat := 1027556946551495685996839

theorem tailTrace_2001160 : CollatzResearch.WordTrace tailWord_2001160 prefixEnd_2001160 1027556946551495685996839 := by
  unfold tailWord_2001160
  simp only [CollatzResearch.WordTrace]
  refine ⟨36494150715073282881668467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48658867620097710508891289 36494150715073282881668467)
  ·
    refine ⟨54741226072609924322502701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36494150715073282881668467 54741226072609924322502701)
    ·
      refine ⟨20527959777228721620938513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54741226072609924322502701 20527959777228721620938513)
      ·
        refine ⟨15395969832921541215703885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20527959777228721620938513 15395969832921541215703885)
        ·
          refine ⟨5773488687345577955888957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15395969832921541215703885 5773488687345577955888957)
          ·
            refine ⟨2165058257754591733458359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5773488687345577955888957 2165058257754591733458359)
            ·
              refine ⟨3247587386631887600187539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165058257754591733458359 3247587386631887600187539)
              ·
                refine ⟨4871381079947831400281309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247587386631887600187539 4871381079947831400281309)
                ·
                  refine ⟨1826767904980436775105491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4871381079947831400281309 1826767904980436775105491)
                  ·
                    refine ⟨2740151857470655162658237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1826767904980436775105491 2740151857470655162658237)
                    ·
                      refine ⟨1027556946551495685996839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2740151857470655162658237 1027556946551495685996839)
                      ·
                        rfl

theorem cell23_2001160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_2001160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001160 prefixEnd_2001160 := by exact prefixLift 2001160
  have htrace : WordTrace (prefixWord ++ tailWord_2001160) baseStart_2001160 baseEnd_2001160 := by
    simpa [prefixWord, tailWord_2001160, baseEnd_2001160] using wordTrace_append hprefix tailTrace_2001160
  have hstable : (prefixWord ++ tailWord_2001160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001160).length < 2 ^ (prefixWord ++ tailWord_2001160).sum := by decide
  have hdescent : baseEnd_2001160 < baseStart_2001160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001166 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2001166 : Nat := 118140960795 + 2001166 * 2 ^ 59
def prefixEnd_2001166 : Nat := 4983230072969 + 3 ^ 40 * 2001166 * 2
def baseEnd_2001166 : Nat := 1027560027435422662521811

theorem tailTrace_2001166 : CollatzResearch.WordTrace tailWord_2001166 prefixEnd_2001166 1027560027435422662521811 := by
  unfold tailWord_2001166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9123565033515603598506919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48659013512083219192036901 9123565033515603598506919)
  ·
    refine ⟨13685347550273405397760379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9123565033515603598506919 13685347550273405397760379)
    ·
      refine ⟨20528021325410108096640569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13685347550273405397760379 20528021325410108096640569)
      ·
        refine ⟨15396015994057581072480427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20528021325410108096640569 15396015994057581072480427)
        ·
          refine ⟨23094023991086371608720641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15396015994057581072480427 23094023991086371608720641)
          ·
            refine ⟨17320517993314778706540481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23094023991086371608720641 17320517993314778706540481)
            ·
              refine ⟨12990388494986084029905361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17320517993314778706540481 12990388494986084029905361)
              ·
                refine ⟨9742791371239563022429021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12990388494986084029905361 9742791371239563022429021)
                ·
                  refine ⟨3653546764214836133410883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9742791371239563022429021 3653546764214836133410883)
                  ·
                    refine ⟨5480320146322254200116325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3653546764214836133410883 5480320146322254200116325)
                    ·
                      refine ⟨1027560027435422662521811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5480320146322254200116325 1027560027435422662521811)
                      ·
                        rfl

theorem cell23_2001166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2001166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001166 prefixEnd_2001166 := by exact prefixLift 2001166
  have htrace : WordTrace (prefixWord ++ tailWord_2001166) baseStart_2001166 baseEnd_2001166 := by
    simpa [prefixWord, tailWord_2001166, baseEnd_2001166] using wordTrace_append hprefix tailTrace_2001166
  have hstable : (prefixWord ++ tailWord_2001166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001166).length < 2 ^ (prefixWord ++ tailWord_2001166).sum := by decide
  have hdescent : baseEnd_2001166 < baseStart_2001166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001179 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 6]
def baseStart_2001179 : Nat := 118140960795 + 2001179 * 2 ^ 59
def prefixEnd_2001179 : Nat := 4983230072969 + 3 ^ 40 * 2001179 * 2
def baseEnd_2001179 : Nat := 1027566702683931111659251

theorem tailTrace_2001179 : CollatzResearch.WordTrace tailWord_2001179 prefixEnd_2001179 1027566702683931111659251 := by
  unfold tailWord_2001179
  simp only [CollatzResearch.WordTrace]
  refine ⟨72988994417077732008278591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48659329611385154672185727 72988994417077732008278591)
  ·
    refine ⟨109483491625616598012417887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72988994417077732008278591 109483491625616598012417887)
    ·
      refine ⟨164225237438424897018626831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109483491625616598012417887 164225237438424897018626831)
      ·
        refine ⟨246337856157637345527940247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164225237438424897018626831 246337856157637345527940247)
        ·
          refine ⟨369506784236456018291910371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246337856157637345527940247 369506784236456018291910371)
          ·
            refine ⟨554260176354684027437865557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369506784236456018291910371 554260176354684027437865557)
            ·
              refine ⟨6495236441656453446537487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 554260176354684027437865557 6495236441656453446537487)
              ·
                refine ⟨9742854662484680169806231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495236441656453446537487 9742854662484680169806231)
                ·
                  refine ⟨14614281993727020254709347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9742854662484680169806231 14614281993727020254709347)
                  ·
                    refine ⟨21921422990590530382064021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14614281993727020254709347 21921422990590530382064021)
                    ·
                      refine ⟨1027566702683931111659251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21921422990590530382064021 1027566702683931111659251)
                      ·
                        rfl

theorem cell23_2001179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_2001179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001179 prefixEnd_2001179 := by exact prefixLift 2001179
  have htrace : WordTrace (prefixWord ++ tailWord_2001179) baseStart_2001179 baseEnd_2001179 := by
    simpa [prefixWord, tailWord_2001179, baseEnd_2001179] using wordTrace_append hprefix tailTrace_2001179
  have hstable : (prefixWord ++ tailWord_2001179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001179).length < 2 ^ (prefixWord ++ tailWord_2001179).sum := by decide
  have hdescent : baseEnd_2001179 < baseStart_2001179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001183 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 4]
def baseStart_2001183 : Nat := 118140960795 + 2001183 * 2 ^ 59
def prefixEnd_2001183 : Nat := 4983230072969 + 3 ^ 40 * 2001183 * 2
def baseEnd_2001183 : Nat := 1027568756606549096009233

theorem tailTrace_2001183 : CollatzResearch.WordTrace tailWord_2001183 prefixEnd_2001183 1027568756606549096009233 := by
  unfold tailWord_2001183
  simp only [CollatzResearch.WordTrace]
  refine ⟨72989140309063240691424203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48659426872708827127616135 72989140309063240691424203)
  ·
    refine ⟨109483710463594861037136305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72989140309063240691424203 109483710463594861037136305)
    ·
      refine ⟨82112782847696145777852229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109483710463594861037136305 82112782847696145777852229)
      ·
        refine ⟨15396146783943027333347293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82112782847696145777852229 15396146783943027333347293)
        ·
          refine ⟨5773555043978635250005235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15396146783943027333347293 5773555043978635250005235)
          ·
            refine ⟨8660332565967952875007853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773555043978635250005235 8660332565967952875007853)
            ·
              refine ⟨3247624712237982328127945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8660332565967952875007853 3247624712237982328127945)
              ·
                refine ⟨2435718534178486746095959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3247624712237982328127945 2435718534178486746095959)
                ·
                  refine ⟨3653577801267730119143939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435718534178486746095959 3653577801267730119143939)
                  ·
                    refine ⟨5480366701901595178715909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3653577801267730119143939 5480366701901595178715909)
                    ·
                      refine ⟨1027568756606549096009233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5480366701901595178715909 1027568756606549096009233)
                      ·
                        rfl

theorem cell23_2001183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_2001183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001183 prefixEnd_2001183 := by exact prefixLift 2001183
  have htrace : WordTrace (prefixWord ++ tailWord_2001183) baseStart_2001183 baseEnd_2001183 := by
    simpa [prefixWord, tailWord_2001183, baseEnd_2001183] using wordTrace_append hprefix tailTrace_2001183
  have hstable : (prefixWord ++ tailWord_2001183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001183).length < 2 ^ (prefixWord ++ tailWord_2001183).sum := by decide
  have hdescent : baseEnd_2001183 < baseStart_2001183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001197 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2001197 : Nat := 118140960795 + 2001197 * 2 ^ 59
def prefixEnd_2001197 : Nat := 4983230072969 + 3 ^ 40 * 2001197 * 2
def baseEnd_2001197 : Nat := 342525315111904013744723

theorem tailTrace_2001197 : CollatzResearch.WordTrace tailWord_2001197 prefixEnd_2001197 342525315111904013744723 := by
  unfold tailWord_2001197
  simp only [CollatzResearch.WordTrace]
  refine ⟨72989650931012521082433845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48659767287341680721622563 72989650931012521082433845)
  ·
    refine ⟨6842779774782423851478173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72989650931012521082433845 6842779774782423851478173)
    ·
      refine ⟨2566042415543408944304315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6842779774782423851478173 2566042415543408944304315)
      ·
        refine ⟨3849063623315113416456473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566042415543408944304315 3849063623315113416456473)
        ·
          refine ⟨2886797717486335062342355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3849063623315113416456473 2886797717486335062342355)
          ·
            refine ⟨4330196576229502593513533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886797717486335062342355 4330196576229502593513533)
            ·
              refine ⟨1623823716086063472567575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4330196576229502593513533 1623823716086063472567575)
              ·
                refine ⟨2435735574129095208851363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623823716086063472567575 2435735574129095208851363)
                ·
                  refine ⟨3653603361193642813277045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435735574129095208851363 3653603361193642813277045)
                  ·
                    refine ⟨342525315111904013744723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3653603361193642813277045 342525315111904013744723)
                    ·
                      rfl

theorem cell23_2001197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2001197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001197 prefixEnd_2001197 := by exact prefixLift 2001197
  have htrace : WordTrace (prefixWord ++ tailWord_2001197) baseStart_2001197 baseEnd_2001197 := by
    simpa [prefixWord, tailWord_2001197, baseEnd_2001197] using wordTrace_append hprefix tailTrace_2001197
  have hstable : (prefixWord ++ tailWord_2001197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001197).length < 2 ^ (prefixWord ++ tailWord_2001197).sum := by decide
  have hdescent : baseEnd_2001197 < baseStart_2001197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001219 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 2, 7]
def baseStart_2001219 : Nat := 118140960795 + 2001219 * 2 ^ 59
def prefixEnd_2001219 : Nat := 4983230072969 + 3 ^ 40 * 2001219 * 2
def baseEnd_2001219 : Nat := 342529080636703651719689

theorem tailTrace_2001219 : CollatzResearch.WordTrace tailWord_2001219 prefixEnd_2001219 342529080636703651719689 := by
  unfold tailWord_2001219
  simp only [CollatzResearch.WordTrace]
  refine ⟨72990453336932818839734711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48660302224621879226489807 72990453336932818839734711)
  ·
    refine ⟨109485680005399228259602067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72990453336932818839734711 109485680005399228259602067)
    ·
      refine ⟨164228520008098842389403101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109485680005399228259602067 164228520008098842389403101)
      ·
        refine ⟨61585695003037065896026163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164228520008098842389403101 61585695003037065896026163)
        ·
          refine ⟨92378542504555598844039245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61585695003037065896026163 92378542504555598844039245)
          ·
            refine ⟨34641953439208349566514717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92378542504555598844039245 34641953439208349566514717)
            ·
              refine ⟨12990732539703131087443019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34641953439208349566514717 12990732539703131087443019)
              ·
                refine ⟨19486098809554696631164529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12990732539703131087443019 19486098809554696631164529)
                ·
                  refine ⟨14614574107166022473373397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19486098809554696631164529 14614574107166022473373397)
                  ·
                    refine ⟨342529080636703651719689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14614574107166022473373397 342529080636703651719689)
                    ·
                      rfl

theorem cell23_2001219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 7].length) (baseStart_2001219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001219 prefixEnd_2001219 := by exact prefixLift 2001219
  have htrace : WordTrace (prefixWord ++ tailWord_2001219) baseStart_2001219 baseEnd_2001219 := by
    simpa [prefixWord, tailWord_2001219, baseEnd_2001219] using wordTrace_append hprefix tailTrace_2001219
  have hstable : (prefixWord ++ tailWord_2001219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001219).length < 2 ^ (prefixWord ++ tailWord_2001219).sum := by decide
  have hdescent : baseEnd_2001219 < baseStart_2001219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001233 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_2001233 : Nat := 118140960795 + 2001233 * 2 ^ 59
def prefixEnd_2001233 : Nat := 4983230072969 + 3 ^ 40 * 2001233 * 2
def baseEnd_2001233 : Nat := 1027594430639273900384003

theorem tailTrace_2001233 : CollatzResearch.WordTrace tailWord_2001233 prefixEnd_2001233 1027594430639273900384003 := by
  unfold tailWord_2001233
  simp only [CollatzResearch.WordTrace]
  refine ⟨72990963958882099230744353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48660642639254732820496235 72990963958882099230744353)
  ·
    refine ⟨54743222969161574423058265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72990963958882099230744353 54743222969161574423058265)
    ·
      refine ⟨41057417226871180817293699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54743222969161574423058265 41057417226871180817293699)
      ·
        refine ⟨61586125840306771225940549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41057417226871180817293699 61586125840306771225940549)
        ·
          refine ⟨11547398595057519604863853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61586125840306771225940549 11547398595057519604863853)
          ·
            refine ⟨4330274473146569851823945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11547398595057519604863853 4330274473146569851823945)
            ·
              refine ⟨3247705854859927388867959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330274473146569851823945 3247705854859927388867959)
              ·
                refine ⟨4871558782289891083301939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3247705854859927388867959 4871558782289891083301939)
                ·
                  refine ⟨7307338173434836624952909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4871558782289891083301939 7307338173434836624952909)
                  ·
                    refine ⟨2740251815038063734357341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7307338173434836624952909 2740251815038063734357341)
                    ·
                      refine ⟨1027594430639273900384003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2740251815038063734357341 1027594430639273900384003)
                      ·
                        rfl

theorem cell23_2001233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_2001233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001233 prefixEnd_2001233 := by exact prefixLift 2001233
  have htrace : WordTrace (prefixWord ++ tailWord_2001233) baseStart_2001233 baseEnd_2001233 := by
    simpa [prefixWord, tailWord_2001233, baseEnd_2001233] using wordTrace_append hprefix tailTrace_2001233
  have hstable : (prefixWord ++ tailWord_2001233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001233).length < 2 ^ (prefixWord ++ tailWord_2001233).sum := by decide
  have hdescent : baseEnd_2001233 < baseStart_2001233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001266 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_2001266 : Nat := 118140960795 + 2001266 * 2 ^ 59
def prefixEnd_2001266 : Nat := 4983230072969 + 3 ^ 40 * 2001266 * 2
def baseEnd_2001266 : Nat := 342537125166957423757117

theorem tailTrace_2001266 : CollatzResearch.WordTrace tailWord_2001266 prefixEnd_2001266 342537125166957423757117 := by
  unfold tailWord_2001266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18248041891940636466673913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48661445045175030577797101 18248041891940636466673913)
  ·
    refine ⟨13686031418955477350005435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18248041891940636466673913 13686031418955477350005435)
    ·
      refine ⟨20529047128433216025008153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13686031418955477350005435 20529047128433216025008153)
      ·
        refine ⟨15396785346324912018756115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20529047128433216025008153 15396785346324912018756115)
        ·
          refine ⟨23095178019487368028134173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15396785346324912018756115 23095178019487368028134173)
          ·
            refine ⟨8660691757307763010550315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23095178019487368028134173 8660691757307763010550315)
            ·
              refine ⟨12991037635961644515825473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8660691757307763010550315 12991037635961644515825473)
              ·
                refine ⟨9743278226971233386869105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12991037635961644515825473 9743278226971233386869105)
                ·
                  refine ⟨7307458670228425040151829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9743278226971233386869105 7307458670228425040151829)
                  ·
                    refine ⟨342537125166957423757117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7307458670228425040151829 342537125166957423757117)
                    ·
                      rfl

theorem cell23_2001266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_2001266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001266 prefixEnd_2001266 := by exact prefixLift 2001266
  have htrace : WordTrace (prefixWord ++ tailWord_2001266) baseStart_2001266 baseEnd_2001266 := by
    simpa [prefixWord, tailWord_2001266, baseEnd_2001266] using wordTrace_append hprefix tailTrace_2001266
  have hstable : (prefixWord ++ tailWord_2001266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001266).length < 2 ^ (prefixWord ++ tailWord_2001266).sum := by decide
  have hdescent : baseEnd_2001266 < baseStart_2001266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001276 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_2001276 : Nat := 118140960795 + 2001276 * 2 ^ 59
def prefixEnd_2001276 : Nat := 4983230072969 + 3 ^ 40 * 2001276 * 2
def baseEnd_2001276 : Nat := 1027616510307417232146305

theorem tailTrace_2001276 : CollatzResearch.WordTrace tailWord_2001276 prefixEnd_2001276 1027616510307417232146305 := by
  unfold tailWord_2001276
  simp only [CollatzResearch.WordTrace]
  refine ⟨36496266148863158787279841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48661688198484211716373121 36496266148863158787279841)
  ·
    refine ⟨27372199611647369090459881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36496266148863158787279841 27372199611647369090459881)
    ·
      refine ⟨20529149708735526817844911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27372199611647369090459881 20529149708735526817844911)
      ·
        refine ⟨30793724563103290226767367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20529149708735526817844911 30793724563103290226767367)
        ·
          refine ⟨46190586844654935340151051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30793724563103290226767367 46190586844654935340151051)
          ·
            refine ⟨69285880266982403010226577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46190586844654935340151051 69285880266982403010226577)
            ·
              refine ⟨51964410200236802257669933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69285880266982403010226577 51964410200236802257669933)
              ·
                refine ⟨19486653825088800846626225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51964410200236802257669933 19486653825088800846626225)
                ·
                  refine ⟨14614990368816600634969669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19486653825088800846626225 14614990368816600634969669)
                  ·
                    refine ⟨2740310694153112619056813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14614990368816600634969669 2740310694153112619056813)
                    ·
                      refine ⟨1027616510307417232146305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2740310694153112619056813 1027616510307417232146305)
                      ·
                        rfl

theorem cell23_2001276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_2001276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001276 prefixEnd_2001276 := by exact prefixLift 2001276
  have htrace : WordTrace (prefixWord ++ tailWord_2001276) baseStart_2001276 baseEnd_2001276 := by
    simpa [prefixWord, tailWord_2001276, baseEnd_2001276] using wordTrace_append hprefix tailTrace_2001276
  have hstable : (prefixWord ++ tailWord_2001276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001276).length < 2 ^ (prefixWord ++ tailWord_2001276).sum := by decide
  have hdescent : baseEnd_2001276 < baseStart_2001276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001279 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 11]
def baseStart_2001279 : Nat := 118140960795 + 2001279 * 2 ^ 59
def prefixEnd_2001279 : Nat := 4983230072969 + 3 ^ 40 * 2001279 * 2
def baseEnd_2001279 : Nat := 114179783416597857823199

theorem tailTrace_2001279 : CollatzResearch.WordTrace tailWord_2001279 prefixEnd_2001279 114179783416597857823199 := by
  unfold tailWord_2001279
  simp only [CollatzResearch.WordTrace]
  refine ⟨72992641716715449086918891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48661761144476966057945927 72992641716715449086918891)
  ·
    refine ⟨109488962575073173630378337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72992641716715449086918891 109488962575073173630378337)
    ·
      refine ⟨82116721931304880222783753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109488962575073173630378337 82116721931304880222783753)
      ·
        refine ⟨61587541448478660167087815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82116721931304880222783753 61587541448478660167087815)
        ·
          refine ⟨92381312172717990250631723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61587541448478660167087815 92381312172717990250631723)
          ·
            refine ⟨138571968259076985375947585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92381312172717990250631723 138571968259076985375947585)
            ·
              refine ⟨103928976194307739031960689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138571968259076985375947585 103928976194307739031960689)
              ·
                refine ⟨77946732145730804273970517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103928976194307739031960689 77946732145730804273970517)
                ·
                  refine ⟨114179783416597857823199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 77946732145730804273970517 114179783416597857823199)
                  ·
                    rfl

theorem cell23_2001279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 11].length) (baseStart_2001279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001279 prefixEnd_2001279 := by exact prefixLift 2001279
  have htrace : WordTrace (prefixWord ++ tailWord_2001279) baseStart_2001279 baseEnd_2001279 := by
    simpa [prefixWord, tailWord_2001279, baseEnd_2001279] using wordTrace_append hprefix tailTrace_2001279
  have hstable : (prefixWord ++ tailWord_2001279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001279).length < 2 ^ (prefixWord ++ tailWord_2001279).sum := by decide
  have hdescent : baseEnd_2001279 < baseStart_2001279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001302 : List Nat := [5, 3, 1, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2001302 : Nat := 118140960795 + 2001302 * 2 ^ 59
def prefixEnd_2001302 : Nat := 4983230072969 + 3 ^ 40 * 2001302 * 2
def baseEnd_2001302 : Nat := 1027629860804434130421187

theorem tailTrace_2001302 : CollatzResearch.WordTrace tailWord_2001302 prefixEnd_2001302 1027629860804434130421187 := by
  unfold tailWord_2001302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562092537227007750937885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48662320397088082676670773 4562092537227007750937885)
  ·
    refine ⟨1710784701460127906601707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4562092537227007750937885 1710784701460127906601707)
    ·
      refine ⟨2566177052190191859902561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710784701460127906601707 2566177052190191859902561)
      ·
        refine ⟨1924632789142643894926921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2566177052190191859902561 1924632789142643894926921)
        ·
          refine ⟨1443474591856982921195191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1924632789142643894926921 1443474591856982921195191)
          ·
            refine ⟨2165211887785474381792787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443474591856982921195191 2165211887785474381792787)
            ·
              refine ⟨3247817831678211572689181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165211887785474381792787 3247817831678211572689181)
              ·
                refine ⟨1217931686879329339758443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3247817831678211572689181 1217931686879329339758443)
                ·
                  refine ⟨1826897530318994009637665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217931686879329339758443 1826897530318994009637665)
                  ·
                    refine ⟨1370173147739245507228249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1826897530318994009637665 1370173147739245507228249)
                    ·
                      refine ⟨1027629860804434130421187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370173147739245507228249 1027629860804434130421187)
                      ·
                        rfl

theorem cell23_2001302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2001302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001302 prefixEnd_2001302 := by exact prefixLift 2001302
  have htrace : WordTrace (prefixWord ++ tailWord_2001302) baseStart_2001302 baseEnd_2001302 := by
    simpa [prefixWord, tailWord_2001302, baseEnd_2001302] using wordTrace_append hprefix tailTrace_2001302
  have hstable : (prefixWord ++ tailWord_2001302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001302).length < 2 ^ (prefixWord ++ tailWord_2001302).sum := by decide
  have hdescent : baseEnd_2001302 < baseStart_2001302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001310 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2001310 : Nat := 118140960795 + 2001310 * 2 ^ 59
def prefixEnd_2001310 : Nat := 4983230072969 + 3 ^ 40 * 2001310 * 2
def baseEnd_2001310 : Nat := 1027633968649670099121149

theorem tailTrace_2001310 : CollatzResearch.WordTrace tailWord_2001310 prefixEnd_2001310 1027633968649670099121149 := by
  unfold tailWord_2001310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124221547450392672662173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48662514919735427587531589 9124221547450392672662173)
  ·
    refine ⟨3421583080293897252248315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9124221547450392672662173 3421583080293897252248315)
    ·
      refine ⟨5132374620440845878372473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421583080293897252248315 5132374620440845878372473)
      ·
        refine ⟨3849280965330634408779355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5132374620440845878372473 3849280965330634408779355)
        ·
          refine ⟨5773921447995951613169033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849280965330634408779355 5773921447995951613169033)
          ·
            refine ⟨4330441085996963709876775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5773921447995951613169033 4330441085996963709876775)
            ·
              refine ⟨6495661628995445564815163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330441085996963709876775 6495661628995445564815163)
              ·
                refine ⟨9743492443493168347222745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495661628995445564815163 9743492443493168347222745)
                ·
                  refine ⟨7307619332619876260417059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9743492443493168347222745 7307619332619876260417059)
                  ·
                    refine ⟨10961428998929814390625589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7307619332619876260417059 10961428998929814390625589)
                    ·
                      refine ⟨1027633968649670099121149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10961428998929814390625589 1027633968649670099121149)
                      ·
                        rfl

theorem cell23_2001310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2001310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001310 prefixEnd_2001310 := by exact prefixLift 2001310
  have htrace : WordTrace (prefixWord ++ tailWord_2001310) baseStart_2001310 baseEnd_2001310 := by
    simpa [prefixWord, tailWord_2001310, baseEnd_2001310] using wordTrace_append hprefix tailTrace_2001310
  have hstable : (prefixWord ++ tailWord_2001310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001310).length < 2 ^ (prefixWord ++ tailWord_2001310).sum := by decide
  have hdescent : baseEnd_2001310 < baseStart_2001310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001330 : List Nat := [3, 2, 1, 1, 1, 1, 7, 2, 5]
def baseStart_2001330 : Nat := 118140960795 + 2001330 * 2 ^ 59
def prefixEnd_2001330 : Nat := 4983230072969 + 3 ^ 40 * 2001330 * 2
def baseEnd_2001330 : Nat := 114182693140306668985673

theorem tailTrace_2001330 : CollatzResearch.WordTrace tailWord_2001330 prefixEnd_2001330 114182693140306668985673 := by
  unfold tailWord_2001330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18248625459882671199256361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48663001226353789864683629 18248625459882671199256361)
  ·
    refine ⟨13686469094912003399442271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18248625459882671199256361 13686469094912003399442271)
    ·
      refine ⟨20529703642368005099163407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13686469094912003399442271 20529703642368005099163407)
      ·
        refine ⟨30794555463552007648745111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20529703642368005099163407 30794555463552007648745111)
        ·
          refine ⟨46191833195328011473117667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30794555463552007648745111 46191833195328011473117667)
          ·
            refine ⟨69287749792992017209676501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46191833195328011473117667 69287749792992017209676501)
            ·
              refine ⟨1623931635773250403351793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69287749792992017209676501 1623931635773250403351793)
              ·
                refine ⟨1217948726829937802513845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623931635773250403351793 1217948726829937802513845)
                ·
                  refine ⟨114182693140306668985673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1217948726829937802513845 114182693140306668985673)
                  ·
                    rfl

theorem cell23_2001330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_2001330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001330 prefixEnd_2001330 := by exact prefixLift 2001330
  have htrace : WordTrace (prefixWord ++ tailWord_2001330) baseStart_2001330 baseEnd_2001330 := by
    simpa [prefixWord, tailWord_2001330, baseEnd_2001330] using wordTrace_append hprefix tailTrace_2001330
  have hstable : (prefixWord ++ tailWord_2001330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001330).length < 2 ^ (prefixWord ++ tailWord_2001330).sum := by decide
  have hdescent : baseEnd_2001330 < baseStart_2001330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001376 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2001376 : Nat := 118140960795 + 2001376 * 2 ^ 59
def prefixEnd_2001376 : Nat := 4983230072969 + 3 ^ 40 * 2001376 * 2
def baseEnd_2001376 : Nat := 1027667858372866840895845

theorem tailTrace_2001376 : CollatzResearch.WordTrace tailWord_2001376 prefixEnd_2001376 1027667858372866840895845 := by
  unfold tailWord_2001376
  simp only [CollatzResearch.WordTrace]
  refine ⟨36498089798682017326599991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48664119731576023102133321 36498089798682017326599991)
  ·
    refine ⟨54747134698023025989899987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36498089798682017326599991 54747134698023025989899987)
    ·
      refine ⟨82120702047034538984849981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54747134698023025989899987 82120702047034538984849981)
      ·
        refine ⟨30795263267637952119318743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82120702047034538984849981 30795263267637952119318743)
        ·
          refine ⟨46192894901456928178978115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30795263267637952119318743 46192894901456928178978115)
          ·
            refine ⟨69289342352185392268467173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46192894901456928178978115 69289342352185392268467173)
            ·
              refine ⟨12991751691034761050337595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69289342352185392268467173 12991751691034761050337595)
              ·
                refine ⟨19487627536552141575506393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12991751691034761050337595 19487627536552141575506393)
                ·
                  refine ⟨14615720652414106181629795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19487627536552141575506393 14615720652414106181629795)
                  ·
                    refine ⟨21923580978621159272444693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14615720652414106181629795 21923580978621159272444693)
                    ·
                      refine ⟨1027667858372866840895845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21923580978621159272444693 1027667858372866840895845)
                      ·
                        rfl

theorem cell23_2001376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2001376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001376 prefixEnd_2001376 := by exact prefixLift 2001376
  have htrace : WordTrace (prefixWord ++ tailWord_2001376) baseStart_2001376 baseEnd_2001376 := by
    simpa [prefixWord, tailWord_2001376, baseEnd_2001376] using wordTrace_append hprefix tailTrace_2001376
  have hstable : (prefixWord ++ tailWord_2001376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001376).length < 2 ^ (prefixWord ++ tailWord_2001376).sum := by decide
  have hdescent : baseEnd_2001376 < baseStart_2001376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001414 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2001414 : Nat := 118140960795 + 2001414 * 2 ^ 59
def prefixEnd_2001414 : Nat := 4983230072969 + 3 ^ 40 * 2001414 * 2
def baseEnd_2001414 : Nat := 1027687370637737692220671

theorem tailTrace_2001414 : CollatzResearch.WordTrace tailWord_2001414 prefixEnd_2001414 1027687370637737692220671 := by
  unfold tailWord_2001414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281173924100823973221353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48665043714150911428722197 2281173924100823973221353)
  ·
    refine ⟨1710880443075617979916015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2281173924100823973221353 1710880443075617979916015)
    ·
      refine ⟨2566320664613426969874023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710880443075617979916015 2566320664613426969874023)
      ·
        refine ⟨3849480996920140454811035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566320664613426969874023 3849480996920140454811035)
        ·
          refine ⟨5774221495380210682216553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849480996920140454811035 5774221495380210682216553)
          ·
            refine ⟨4330666121535158011662415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5774221495380210682216553 4330666121535158011662415)
            ·
              refine ⟨6495999182302737017493623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330666121535158011662415 6495999182302737017493623)
              ·
                refine ⟨9743998773454105526240435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495999182302737017493623 9743998773454105526240435)
                ·
                  refine ⟨14615998160181158289360653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9743998773454105526240435 14615998160181158289360653)
                  ·
                    refine ⟨5480999310067934358510245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14615998160181158289360653 5480999310067934358510245)
                    ·
                      refine ⟨1027687370637737692220671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5480999310067934358510245 1027687370637737692220671)
                      ·
                        rfl

theorem cell23_2001414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2001414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001414 prefixEnd_2001414 := by exact prefixLift 2001414
  have htrace : WordTrace (prefixWord ++ tailWord_2001414) baseStart_2001414 baseEnd_2001414 := by
    simpa [prefixWord, tailWord_2001414, baseEnd_2001414] using wordTrace_append hprefix tailTrace_2001414
  have hstable : (prefixWord ++ tailWord_2001414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001414).length < 2 ^ (prefixWord ++ tailWord_2001414).sum := by decide
  have hdescent : baseEnd_2001414 < baseStart_2001414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001433 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 1, 5]
def baseStart_2001433 : Nat := 118140960795 + 2001433 * 2 ^ 59
def prefixEnd_2001433 : Nat := 4983230072969 + 3 ^ 40 * 2001433 * 2
def baseEnd_2001433 : Nat := 342565708923391039294361

theorem tailTrace_2001433 : CollatzResearch.WordTrace tailWord_2001433 prefixEnd_2001433 342565708923391039294361 := by
  unfold tailWord_2001433
  simp only [CollatzResearch.WordTrace]
  refine ⟨72998258558157533388024953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48665505705438355592016635 72998258558157533388024953)
  ·
    refine ⟨54748693918618150041018715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72998258558157533388024953 54748693918618150041018715)
    ·
      refine ⟨82123040877927225061528073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54748693918618150041018715 82123040877927225061528073)
      ·
        refine ⟨61592280658445418796146055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82123040877927225061528073 61592280658445418796146055)
        ·
          refine ⟨92388420987668128194219083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61592280658445418796146055 92388420987668128194219083)
          ·
            refine ⟨138582631481502192291328625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92388420987668128194219083 138582631481502192291328625)
            ·
              refine ⟨103936973611126644218496469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138582631481502192291328625 103936973611126644218496469)
              ·
                refine ⟨2436022819010780723871011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103936973611126644218496469 2436022819010780723871011)
                ·
                  refine ⟨3654034228516171085806517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436022819010780723871011 3654034228516171085806517)
                  ·
                    refine ⟨342565708923391039294361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3654034228516171085806517 342565708923391039294361)
                    ·
                      rfl

theorem cell23_2001433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_2001433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001433 prefixEnd_2001433 := by exact prefixLift 2001433
  have htrace : WordTrace (prefixWord ++ tailWord_2001433) baseStart_2001433 baseEnd_2001433 := by
    simpa [prefixWord, tailWord_2001433, baseEnd_2001433] using wordTrace_append hprefix tailTrace_2001433
  have hstable : (prefixWord ++ tailWord_2001433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001433).length < 2 ^ (prefixWord ++ tailWord_2001433).sum := by decide
  have hdescent : baseEnd_2001433 < baseStart_2001433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001483 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 4]
def baseStart_2001483 : Nat := 118140960795 + 2001483 * 2 ^ 59
def prefixEnd_2001483 : Nat := 4983230072969 + 3 ^ 40 * 2001483 * 2
def baseEnd_2001483 : Nat := 1027722800802897922257853

theorem tailTrace_2001483 : CollatzResearch.WordTrace tailWord_2001483 prefixEnd_2001483 1027722800802897922257853 := by
  unfold tailWord_2001483
  simp only [CollatzResearch.WordTrace]
  refine ⟨73000082207976391927345103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48666721471984261284896735 73000082207976391927345103)
  ·
    refine ⟨109500123311964587891017655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73000082207976391927345103 109500123311964587891017655)
    ·
      refine ⟨164250184967946881836526483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109500123311964587891017655 164250184967946881836526483)
      ·
        refine ⟨246375277451920322754789725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164250184967946881836526483 246375277451920322754789725)
        ·
          refine ⟨92390729044470121033046147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246375277451920322754789725 92390729044470121033046147)
          ·
            refine ⟨138586093566705181549569221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92390729044470121033046147 138586093566705181549569221)
            ·
              refine ⟨25984892543757221540544229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138586093566705181549569221 25984892543757221540544229)
              ·
                refine ⟨4872167351954479038852043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25984892543757221540544229 4872167351954479038852043)
                ·
                  refine ⟨7308251027931718558278065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872167351954479038852043 7308251027931718558278065)
                  ·
                    refine ⟨5481188270948788918708549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7308251027931718558278065 5481188270948788918708549)
                    ·
                      refine ⟨1027722800802897922257853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5481188270948788918708549 1027722800802897922257853)
                      ·
                        rfl

theorem cell23_2001483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 4].length) (baseStart_2001483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001483 prefixEnd_2001483 := by exact prefixLift 2001483
  have htrace : WordTrace (prefixWord ++ tailWord_2001483) baseStart_2001483 baseEnd_2001483 := by
    simpa [prefixWord, tailWord_2001483, baseEnd_2001483] using wordTrace_append hprefix tailTrace_2001483
  have hstable : (prefixWord ++ tailWord_2001483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001483).length < 2 ^ (prefixWord ++ tailWord_2001483).sum := by decide
  have hdescent : baseEnd_2001483 < baseStart_2001483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001490 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_2001490 : Nat := 118140960795 + 2001490 * 2 ^ 59
def prefixEnd_2001490 : Nat := 4983230072969 + 3 ^ 40 * 2001490 * 2
def baseEnd_2001490 : Nat := 1027726395167479394870321

theorem tailTrace_2001490 : CollatzResearch.WordTrace tailWord_2001490 prefixEnd_2001490 1027726395167479394870321 := by
  unfold tailWord_2001490
  simp only [CollatzResearch.WordTrace]
  refine ⟨18250084379737758030712481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48666891679300688081899949 18250084379737758030712481)
  ·
    refine ⟨13687563284803318523034361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18250084379737758030712481 13687563284803318523034361)
    ·
      refine ⟨10265672463602488892275771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13687563284803318523034361 10265672463602488892275771)
      ·
        refine ⟨15398508695403733338413657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10265672463602488892275771 15398508695403733338413657)
        ·
          refine ⟨11548881521552800003810243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15398508695403733338413657 11548881521552800003810243)
          ·
            refine ⟨17323322282329200005715365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548881521552800003810243 17323322282329200005715365)
            ·
              refine ⟨3248122927936725001071631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17323322282329200005715365 3248122927936725001071631)
              ·
                refine ⟨4872184391905087501607447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248122927936725001071631 4872184391905087501607447)
                ·
                  refine ⟨7308276587857631252411171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872184391905087501607447 7308276587857631252411171)
                  ·
                    refine ⟨10962414881786446878616757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7308276587857631252411171 10962414881786446878616757)
                    ·
                      refine ⟨1027726395167479394870321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10962414881786446878616757 1027726395167479394870321)
                      ·
                        rfl

theorem cell23_2001490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_2001490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001490 prefixEnd_2001490 := by exact prefixLift 2001490
  have htrace : WordTrace (prefixWord ++ tailWord_2001490) baseStart_2001490 baseEnd_2001490 := by
    simpa [prefixWord, tailWord_2001490, baseEnd_2001490] using wordTrace_append hprefix tailTrace_2001490
  have hstable : (prefixWord ++ tailWord_2001490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001490).length < 2 ^ (prefixWord ++ tailWord_2001490).sum := by decide
  have hdescent : baseEnd_2001490 < baseStart_2001490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001504 : List Nat := [2, 1, 1, 3, 2, 1, 2, 6, 1, 2, 2]
def baseStart_2001504 : Nat := 118140960795 + 2001504 * 2 ^ 59
def prefixEnd_2001504 : Nat := 4983230072969 + 3 ^ 40 * 2001504 * 2
def baseEnd_2001504 : Nat := 1027733583896642340095257

theorem tailTrace_2001504 : CollatzResearch.WordTrace tailWord_2001504 prefixEnd_2001504 1027733583896642340095257 := by
  unfold tailWord_2001504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36500424070450156256929783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48667232093933541675906377 36500424070450156256929783)
  ·
    refine ⟨54750636105675234385394675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36500424070450156256929783 54750636105675234385394675)
    ·
      refine ⟨82125954158512851578092013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54750636105675234385394675 82125954158512851578092013)
      ·
        refine ⟨30797232809442319341784505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82125954158512851578092013 30797232809442319341784505)
        ·
          refine ⟨23097924607081739506338379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30797232809442319341784505 23097924607081739506338379)
          ·
            refine ⟨34646886910622609259507569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23097924607081739506338379 34646886910622609259507569)
            ·
              refine ⟨25985165182966956944630677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34646886910622609259507569 25985165182966956944630677)
              ·
                refine ⟨1218054617951576106779563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25985165182966956944630677 1218054617951576106779563)
                ·
                  refine ⟨1827081926927364160169345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218054617951576106779563 1827081926927364160169345)
                  ·
                    refine ⟨1370311445195523120127009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827081926927364160169345 1370311445195523120127009)
                    ·
                      refine ⟨1027733583896642340095257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370311445195523120127009 1027733583896642340095257)
                      ·
                        rfl

theorem cell23_2001504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_2001504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001504 prefixEnd_2001504 := by exact prefixLift 2001504
  have htrace : WordTrace (prefixWord ++ tailWord_2001504) baseStart_2001504 baseEnd_2001504 := by
    simpa [prefixWord, tailWord_2001504, baseEnd_2001504] using wordTrace_append hprefix tailTrace_2001504
  have hstable : (prefixWord ++ tailWord_2001504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001504).length < 2 ^ (prefixWord ++ tailWord_2001504).sum := by decide
  have hdescent : baseEnd_2001504 < baseStart_2001504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001554 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2001554 : Nat := 118140960795 + 2001554 * 2 ^ 59
def prefixEnd_2001554 : Nat := 4983230072969 + 3 ^ 40 * 2001554 * 2
def baseEnd_2001554 : Nat := 1027759257929367144470027

theorem tailTrace_2001554 : CollatzResearch.WordTrace tailWord_2001554 prefixEnd_2001554 1027759257929367144470027 := by
  unfold tailWord_2001554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18250667947679792763294929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48668447860479447368786477 18250667947679792763294929)
  ·
    refine ⟨13688000960759844572471197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18250667947679792763294929 13688000960759844572471197)
    ·
      refine ⟨5133000360284941714676699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13688000960759844572471197 5133000360284941714676699)
      ·
        refine ⟨7699500540427412572015049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133000360284941714676699 7699500540427412572015049)
        ·
          refine ⟨5774625405320559429011287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7699500540427412572015049 5774625405320559429011287)
          ·
            refine ⟨8661938107980839143516931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5774625405320559429011287 8661938107980839143516931)
            ·
              refine ⟨12992907161971258715275397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8661938107980839143516931 12992907161971258715275397)
              ·
                refine ⟨2436170092869611009114137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12992907161971258715275397 2436170092869611009114137)
                ·
                  refine ⟨1827127569652208256835603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2436170092869611009114137 1827127569652208256835603)
                  ·
                    refine ⟨2740691354478312385253405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1827127569652208256835603 2740691354478312385253405)
                    ·
                      refine ⟨1027759257929367144470027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2740691354478312385253405 1027759257929367144470027)
                      ·
                        rfl

theorem cell23_2001554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2001554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001554 prefixEnd_2001554 := by exact prefixLift 2001554
  have htrace : WordTrace (prefixWord ++ tailWord_2001554) baseStart_2001554 baseEnd_2001554 := by
    simpa [prefixWord, tailWord_2001554, baseEnd_2001554] using wordTrace_append hprefix tailTrace_2001554
  have hstable : (prefixWord ++ tailWord_2001554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001554).length < 2 ^ (prefixWord ++ tailWord_2001554).sum := by decide
  have hdescent : baseEnd_2001554 < baseStart_2001554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001583 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 9]
def baseStart_2001583 : Nat := 118140960795 + 2001583 * 2 ^ 59
def prefixEnd_2001583 : Nat := 4983230072969 + 3 ^ 40 * 2001583 * 2
def baseEnd_2001583 : Nat := 114197127652038614556377

theorem tailTrace_2001583 : CollatzResearch.WordTrace tailWord_2001583 prefixEnd_2001583 114197127652038614556377 := by
  unfold tailWord_2001583
  simp only [CollatzResearch.WordTrace]
  refine ⟨73003729507614109005985403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48669153005076072670656935 73003729507614109005985403)
  ·
    refine ⟨109505594261421163508978105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73003729507614109005985403 109505594261421163508978105)
    ·
      refine ⟨82129195696065872631733579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109505594261421163508978105 82129195696065872631733579)
      ·
        refine ⟨123193793544098808947600369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82129195696065872631733579 123193793544098808947600369)
        ·
          refine ⟨92395345158074106710700277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123193793544098808947600369 92395345158074106710700277)
          ·
            refine ⟨8662063608569447504128151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92395345158074106710700277 8662063608569447504128151)
            ·
              refine ⟨12993095412854171256192227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8662063608569447504128151 12993095412854171256192227)
              ·
                refine ⟨19489643119281256884288341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12993095412854171256192227 19489643119281256884288341)
                ·
                  refine ⟨114197127652038614556377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19489643119281256884288341 114197127652038614556377)
                  ·
                    rfl

theorem cell23_2001583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 9].length) (baseStart_2001583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001583 prefixEnd_2001583 := by exact prefixLift 2001583
  have htrace : WordTrace (prefixWord ++ tailWord_2001583) baseStart_2001583 baseEnd_2001583 := by
    simpa [prefixWord, tailWord_2001583, baseEnd_2001583] using wordTrace_append hprefix tailTrace_2001583
  have hstable : (prefixWord ++ tailWord_2001583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001583).length < 2 ^ (prefixWord ++ tailWord_2001583).sum := by decide
  have hdescent : baseEnd_2001583 < baseStart_2001583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001593 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2001593 : Nat := 118140960795 + 2001593 * 2 ^ 59
def prefixEnd_2001593 : Nat := 4983230072969 + 3 ^ 40 * 2001593 * 2
def baseEnd_2001593 : Nat := 1027779283674892491882347

theorem tailTrace_2001593 : CollatzResearch.WordTrace tailWord_2001593 prefixEnd_2001593 1027779283674892491882347 := by
  unfold tailWord_2001593
  simp only [CollatzResearch.WordTrace]
  refine ⟨73004094237577880713849433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48669396158385253809232955 73004094237577880713849433)
  ·
    refine ⟨54753070678183410535387075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73004094237577880713849433 54753070678183410535387075)
    ·
      refine ⟨82129606017275115803080613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54753070678183410535387075 82129606017275115803080613)
      ·
        refine ⟨15399301128239084213077615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82129606017275115803080613 15399301128239084213077615)
        ·
          refine ⟨23098951692358626319616423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15399301128239084213077615 23098951692358626319616423)
          ·
            refine ⟨34648427538537939479424635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23098951692358626319616423 34648427538537939479424635)
            ·
              refine ⟨51972641307806909219136953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34648427538537939479424635 51972641307806909219136953)
              ·
                refine ⟨38979480980855181914352715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51972641307806909219136953 38979480980855181914352715)
                ·
                  refine ⟨58469221471282772871529073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38979480980855181914352715 58469221471282772871529073)
                  ·
                    refine ⟨43851916103462079653646805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58469221471282772871529073 43851916103462079653646805)
                    ·
                      refine ⟨1027779283674892491882347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43851916103462079653646805 1027779283674892491882347)
                      ·
                        rfl

theorem cell23_2001593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2001593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001593 prefixEnd_2001593 := by exact prefixLift 2001593
  have htrace : WordTrace (prefixWord ++ tailWord_2001593) baseStart_2001593 baseEnd_2001593 := by
    simpa [prefixWord, tailWord_2001593, baseEnd_2001593] using wordTrace_append hprefix tailTrace_2001593
  have hstable : (prefixWord ++ tailWord_2001593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001593).length < 2 ^ (prefixWord ++ tailWord_2001593).sum := by decide
  have hdescent : baseEnd_2001593 < baseStart_2001593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001643 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 1, 10]
def baseStart_2001643 : Nat := 118140960795 + 2001643 * 2 ^ 59
def prefixEnd_2001643 : Nat := 4983230072969 + 3 ^ 40 * 2001643 * 2
def baseEnd_2001643 : Nat := 342601652569205765419039

theorem tailTrace_2001643 : CollatzResearch.WordTrace tailWord_2001643 prefixEnd_2001643 342601652569205765419039 := by
  unfold tailWord_2001643
  simp only [CollatzResearch.WordTrace]
  refine ⟨73005917887396739253169583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48670611924931159502113055 73005917887396739253169583)
  ·
    refine ⟨109508876831095108879754375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73005917887396739253169583 109508876831095108879754375)
    ·
      refine ⟨164263315246642663319631563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109508876831095108879754375 164263315246642663319631563)
      ·
        refine ⟨246394972869963994979447345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164263315246642663319631563 246394972869963994979447345)
        ·
          refine ⟨184796229652472996234585509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246394972869963994979447345 184796229652472996234585509)
          ·
            refine ⟨34649293059838686793984783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184796229652472996234585509 34649293059838686793984783)
            ·
              refine ⟨51973939589758030190977175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34649293059838686793984783 51973939589758030190977175)
              ·
                refine ⟨77960909384637045286465763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51973939589758030190977175 77960909384637045286465763)
                ·
                  refine ⟨116941364076955567929698645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77960909384637045286465763 116941364076955567929698645)
                  ·
                    refine ⟨342601652569205765419039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 116941364076955567929698645 342601652569205765419039)
                    ·
                      rfl

theorem cell23_2001643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 10].length) (baseStart_2001643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001643 prefixEnd_2001643 := by exact prefixLift 2001643
  have htrace : WordTrace (prefixWord ++ tailWord_2001643) baseStart_2001643 baseEnd_2001643 := by
    simpa [prefixWord, tailWord_2001643, baseEnd_2001643] using wordTrace_append hprefix tailTrace_2001643
  have hstable : (prefixWord ++ tailWord_2001643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001643).length < 2 ^ (prefixWord ++ tailWord_2001643).sum := by decide
  have hdescent : baseEnd_2001643 < baseStart_2001643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001704 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2001704 : Nat := 118140960795 + 2001704 * 2 ^ 59
def prefixEnd_2001704 : Nat := 4983230072969 + 3 ^ 40 * 2001704 * 2
def baseEnd_2001704 : Nat := 1027836280027541557594337

theorem tailTrace_2001704 : CollatzResearch.WordTrace tailWord_2001704 prefixEnd_2001704 1027836280027541557594337 := by
  unfold tailWord_2001704
  simp only [CollatzResearch.WordTrace]
  refine ⟨36504071370087873335570083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48672095160117164447426777 36504071370087873335570083)
  ·
    refine ⟨54756107055131810003355125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36504071370087873335570083 54756107055131810003355125)
    ·
      refine ⟨5133385036418607187814543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54756107055131810003355125 5133385036418607187814543)
      ·
        refine ⟨7700077554627910781721815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133385036418607187814543 7700077554627910781721815)
        ·
          refine ⟨11550116331941866172582723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700077554627910781721815 11550116331941866172582723)
          ·
            refine ⟨17325174497912799258874085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11550116331941866172582723 17325174497912799258874085)
            ·
              refine ⟨3248470218358649861038891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17325174497912799258874085 3248470218358649861038891)
              ·
                refine ⟨4872705327537974791558337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248470218358649861038891 4872705327537974791558337)
                ·
                  refine ⟨3654528995653481093668753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872705327537974791558337 3654528995653481093668753)
                  ·
                    refine ⟨2740896746740110820251565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3654528995653481093668753 2740896746740110820251565)
                    ·
                      refine ⟨1027836280027541557594337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2740896746740110820251565 1027836280027541557594337)
                      ·
                        rfl

theorem cell23_2001704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2001704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001704 prefixEnd_2001704 := by exact prefixLift 2001704
  have htrace : WordTrace (prefixWord ++ tailWord_2001704) baseStart_2001704 baseEnd_2001704 := by
    simpa [prefixWord, tailWord_2001704, baseEnd_2001704] using wordTrace_append hprefix tailTrace_2001704
  have hstable : (prefixWord ++ tailWord_2001704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001704).length < 2 ^ (prefixWord ++ tailWord_2001704).sum := by decide
  have hdescent : baseEnd_2001704 < baseStart_2001704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001767 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 1, 6]
def baseStart_2001767 : Nat := 118140960795 + 2001767 * 2 ^ 59
def prefixEnd_2001767 : Nat := 4983230072969 + 3 ^ 40 * 2001767 * 2
def baseEnd_2001767 : Nat := 342622876436258270368849

theorem tailTrace_2001767 : CollatzResearch.WordTrace tailWord_2001767 prefixEnd_2001767 342622876436258270368849 := by
  unfold tailWord_2001767
  simp only [CollatzResearch.WordTrace]
  refine ⟨73010440538947508430683555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48673627025965005620455703 73010440538947508430683555)
  ·
    refine ⟨109515660808421262646025333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73010440538947508430683555 109515660808421262646025333)
    ·
      refine ⟨10267093200789493373064875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109515660808421262646025333 10267093200789493373064875)
      ·
        refine ⟨15400639801184240059597313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10267093200789493373064875 15400639801184240059597313)
        ·
          refine ⟨11550479850888180044697985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15400639801184240059597313 11550479850888180044697985)
          ·
            refine ⟨8662859888166135033523489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11550479850888180044697985 8662859888166135033523489)
            ·
              refine ⟨6497144916124601275142617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8662859888166135033523489 6497144916124601275142617)
              ·
                refine ⟨4872858687093450956356963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497144916124601275142617 4872858687093450956356963)
                ·
                  refine ⟨7309288030640176434535445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4872858687093450956356963 7309288030640176434535445)
                  ·
                    refine ⟨342622876436258270368849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7309288030640176434535445 342622876436258270368849)
                    ·
                      rfl

theorem cell23_2001767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_2001767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001767 prefixEnd_2001767 := by exact prefixLift 2001767
  have htrace : WordTrace (prefixWord ++ tailWord_2001767) baseStart_2001767 baseEnd_2001767 := by
    simpa [prefixWord, tailWord_2001767, baseEnd_2001767] using wordTrace_append hprefix tailTrace_2001767
  have hstable : (prefixWord ++ tailWord_2001767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001767).length < 2 ^ (prefixWord ++ tailWord_2001767).sum := by decide
  have hdescent : baseEnd_2001767 < baseStart_2001767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001768 : List Nat := [2, 1, 4, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_2001768 : Nat := 118140960795 + 2001768 * 2 ^ 59
def prefixEnd_2001768 : Nat := 4983230072969 + 3 ^ 40 * 2001768 * 2
def baseEnd_2001768 : Nat := 1027869142789429307194043

theorem tailTrace_2001768 : CollatzResearch.WordTrace tailWord_2001768 prefixEnd_2001768 1027869142789429307194043 := by
  unfold tailWord_2001768
  simp only [CollatzResearch.WordTrace]
  refine ⟨36505238505971942800734979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48673651341295923734313305 36505238505971942800734979)
  ·
    refine ⟨54757857758957914201102469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36505238505971942800734979 54757857758957914201102469)
    ·
      refine ⟨10267098329804608912706713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54757857758957914201102469 10267098329804608912706713)
      ·
        refine ⟨7700323747353456684530035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10267098329804608912706713 7700323747353456684530035)
        ·
          refine ⟨11550485621030185026795053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7700323747353456684530035 11550485621030185026795053)
          ·
            refine ⟨4331432107886319385048145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11550485621030185026795053 4331432107886319385048145)
            ·
              refine ⟨3248574080914739538786109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4331432107886319385048145 3248574080914739538786109)
              ·
                refine ⟨1218215280343027327044791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3248574080914739538786109 1218215280343027327044791)
                ·
                  refine ⟨1827322920514540990567187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218215280343027327044791 1827322920514540990567187)
                  ·
                    refine ⟨2740984380771811485850781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1827322920514540990567187 2740984380771811485850781)
                    ·
                      refine ⟨1027869142789429307194043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2740984380771811485850781 1027869142789429307194043)
                      ·
                        rfl

theorem cell23_2001768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_2001768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001768 prefixEnd_2001768 := by exact prefixLift 2001768
  have htrace : WordTrace (prefixWord ++ tailWord_2001768) baseStart_2001768 baseEnd_2001768 := by
    simpa [prefixWord, tailWord_2001768, baseEnd_2001768] using wordTrace_append hprefix tailTrace_2001768
  have hstable : (prefixWord ++ tailWord_2001768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001768).length < 2 ^ (prefixWord ++ tailWord_2001768).sum := by decide
  have hdescent : baseEnd_2001768 < baseStart_2001768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001801 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 2, 4]
def baseStart_2001801 : Nat := 118140960795 + 2001801 * 2 ^ 59
def prefixEnd_2001801 : Nat := 4983230072969 + 3 ^ 40 * 2001801 * 2
def baseEnd_2001801 : Nat := 342628695883675892693797

theorem tailTrace_2001801 : CollatzResearch.WordTrace tailWord_2001801 prefixEnd_2001801 342628695883675892693797 := by
  unfold tailWord_2001801
  simp only [CollatzResearch.WordTrace]
  refine ⟨73011680620824332237421257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48674453747216221491614171 73011680620824332237421257)
  ·
    refine ⟨54758760465618249178065943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73011680620824332237421257 54758760465618249178065943)
    ·
      refine ⟨82138140698427373767098915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54758760465618249178065943 82138140698427373767098915)
      ·
        refine ⟨123207211047641060650648373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82138140698427373767098915 123207211047641060650648373)
        ·
          refine ⟨11550676035716349435998285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123207211047641060650648373 11550676035716349435998285)
          ·
            refine ⟨4331503513393631038499357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11550676035716349435998285 4331503513393631038499357)
            ·
              refine ⟨1624313817522611639437259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4331503513393631038499357 1624313817522611639437259)
              ·
                refine ⟨2436470726283917459155889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624313817522611639437259 2436470726283917459155889)
                ·
                  refine ⟨1827353044712938094366917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2436470726283917459155889 1827353044712938094366917)
                  ·
                    refine ⟨342628695883675892693797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1827353044712938094366917 342628695883675892693797)
                    ·
                      rfl

theorem cell23_2001801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 2, 4].length) (baseStart_2001801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001801 prefixEnd_2001801 := by exact prefixLift 2001801
  have htrace : WordTrace (prefixWord ++ tailWord_2001801) baseStart_2001801 baseEnd_2001801 := by
    simpa [prefixWord, tailWord_2001801, baseEnd_2001801] using wordTrace_append hprefix tailTrace_2001801
  have hstable : (prefixWord ++ tailWord_2001801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001801).length < 2 ^ (prefixWord ++ tailWord_2001801).sum := by decide
  have hdescent : baseEnd_2001801 < baseStart_2001801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001824 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2001824 : Nat := 118140960795 + 2001824 * 2 ^ 59
def prefixEnd_2001824 : Nat := 4983230072969 + 3 ^ 40 * 2001824 * 2
def baseEnd_2001824 : Nat := 1027897897706081088093785

theorem tailTrace_2001824 : CollatzResearch.WordTrace tailWord_2001824 prefixEnd_2001824 1027897897706081088093785 := by
  unfold tailWord_2001824
  simp only [CollatzResearch.WordTrace]
  refine ⟨36506259749870503582754263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48675012999827338110339017 36506259749870503582754263)
  ·
    refine ⟨54759389624805755374131395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36506259749870503582754263 54759389624805755374131395)
    ·
      refine ⟨82139084437208633061197093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54759389624805755374131395 82139084437208633061197093)
      ·
        refine ⟨15401078331976618698974455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82139084437208633061197093 15401078331976618698974455)
        ·
          refine ⟨23101617497964928048461683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15401078331976618698974455 23101617497964928048461683)
          ·
            refine ⟨34652426246947392072692525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23101617497964928048461683 34652426246947392072692525)
            ·
              refine ⟨12994659842605272027259697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34652426246947392072692525 12994659842605272027259697)
              ·
                refine ⟨9745994881953954020444773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12994659842605272027259697 9745994881953954020444773)
                ·
                  refine ⟨1827374040366366378833395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9745994881953954020444773 1827374040366366378833395)
                  ·
                    refine ⟨2741061060549549568250093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1827374040366366378833395 2741061060549549568250093)
                    ·
                      refine ⟨1027897897706081088093785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741061060549549568250093 1027897897706081088093785)
                      ·
                        rfl

theorem cell23_2001824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2001824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001824 prefixEnd_2001824 := by exact prefixLift 2001824
  have htrace : WordTrace (prefixWord ++ tailWord_2001824) baseStart_2001824 baseEnd_2001824 := by
    simpa [prefixWord, tailWord_2001824, baseEnd_2001824] using wordTrace_append hprefix tailTrace_2001824
  have hstable : (prefixWord ++ tailWord_2001824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001824).length < 2 ^ (prefixWord ++ tailWord_2001824).sum := by decide
  have hdescent : baseEnd_2001824 < baseStart_2001824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001825 : List Nat := [1, 2, 3, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2001825 : Nat := 118140960795 + 2001825 * 2 ^ 59
def prefixEnd_2001825 : Nat := 4983230072969 + 3 ^ 40 * 2001825 * 2
def baseEnd_2001825 : Nat := 1027898411186735584181281

theorem tailTrace_2001825 : CollatzResearch.WordTrace tailWord_2001825 prefixEnd_2001825 1027898411186735584181281 := by
  unfold tailWord_2001825
  simp only [CollatzResearch.WordTrace]
  refine ⟨73012555972737384336294929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48675037315158256224196619 73012555972737384336294929)
  ·
    refine ⟨54759416979553038252221197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73012555972737384336294929 54759416979553038252221197)
    ·
      refine ⟨20534781367332389344582949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54759416979553038252221197 20534781367332389344582949)
      ·
        refine ⟨3850271506374823002109303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20534781367332389344582949 3850271506374823002109303)
        ·
          refine ⟨5775407259562234503163955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850271506374823002109303 5775407259562234503163955)
          ·
            refine ⟨8663110889343351754745933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5775407259562234503163955 8663110889343351754745933)
            ·
              refine ⟨3248666583503756908029725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8663110889343351754745933 3248666583503756908029725)
              ·
                refine ⟨1218249968813908840511147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3248666583503756908029725 1218249968813908840511147)
                ·
                  refine ⟨1827374953220863260766721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218249968813908840511147 1827374953220863260766721)
                  ·
                    refine ⟨1370531214915647445575041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827374953220863260766721 1370531214915647445575041)
                    ·
                      refine ⟨1027898411186735584181281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370531214915647445575041 1027898411186735584181281)
                      ·
                        rfl

theorem cell23_2001825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2001825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001825 prefixEnd_2001825 := by exact prefixLift 2001825
  have htrace : WordTrace (prefixWord ++ tailWord_2001825) baseStart_2001825 baseEnd_2001825 := by
    simpa [prefixWord, tailWord_2001825, baseEnd_2001825] using wordTrace_append hprefix tailTrace_2001825
  have hstable : (prefixWord ++ tailWord_2001825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001825).length < 2 ^ (prefixWord ++ tailWord_2001825).sum := by decide
  have hdescent : baseEnd_2001825 < baseStart_2001825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001862 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2001862 : Nat := 118140960795 + 2001862 * 2 ^ 59
def prefixEnd_2001862 : Nat := 4983230072969 + 3 ^ 40 * 2001862 * 2
def baseEnd_2001862 : Nat := 1027917409970951939418611

theorem tailTrace_2001862 : CollatzResearch.WordTrace tailWord_2001862 prefixEnd_2001862 1027917409970951939418611 := by
  unfold tailWord_2001862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281684546050104364230995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48675936982402226436927893 2281684546050104364230995)
  ·
    refine ⟨3422526819075156546346493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281684546050104364230995 3422526819075156546346493)
    ·
      refine ⟨1283447557153183704879935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3422526819075156546346493 1283447557153183704879935)
      ·
        refine ⟨1925171335729775557319903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283447557153183704879935 1925171335729775557319903)
        ·
          refine ⟨2887757003594663335979855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925171335729775557319903 2887757003594663335979855)
          ·
            refine ⟨4331635505391995003969783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887757003594663335979855 4331635505391995003969783)
            ·
              refine ⟨6497453258087992505954675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331635505391995003969783 6497453258087992505954675)
              ·
                refine ⟨9746179887131988758932013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497453258087992505954675 9746179887131988758932013)
                ·
                  refine ⟨3654817457674495784599505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9746179887131988758932013 3654817457674495784599505)
                  ·
                    refine ⟨2741113093255871838449629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3654817457674495784599505 2741113093255871838449629)
                    ·
                      refine ⟨1027917409970951939418611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741113093255871838449629 1027917409970951939418611)
                      ·
                        rfl

theorem cell23_2001862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2001862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001862 prefixEnd_2001862 := by exact prefixLift 2001862
  have htrace : WordTrace (prefixWord ++ tailWord_2001862) baseStart_2001862 baseEnd_2001862 := by
    simpa [prefixWord, tailWord_2001862, baseEnd_2001862] using wordTrace_append hprefix tailTrace_2001862
  have hstable : (prefixWord ++ tailWord_2001862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001862).length < 2 ^ (prefixWord ++ tailWord_2001862).sum := by decide
  have hdescent : baseEnd_2001862 < baseStart_2001862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001867 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 5]
def baseStart_2001867 : Nat := 118140960795 + 2001867 * 2 ^ 59
def prefixEnd_2001867 : Nat := 4983230072969 + 3 ^ 40 * 2001867 * 2
def baseEnd_2001867 : Nat := 1027919977374224419856087

theorem tailTrace_2001867 : CollatzResearch.WordTrace tailWord_2001867 prefixEnd_2001867 1027919977374224419856087 := by
  unfold tailWord_2001867
  simp only [CollatzResearch.WordTrace]
  refine ⟨73014087838585225509323855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48676058559056817006215903 73014087838585225509323855)
  ·
    refine ⟨109521131757877838263985783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73014087838585225509323855 109521131757877838263985783)
    ·
      refine ⟨164281697636816757395978675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109521131757877838263985783 164281697636816757395978675)
      ·
        refine ⟨246422546455225136093968013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164281697636816757395978675 246422546455225136093968013)
        ·
          refine ⟨92408454920709426035238005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246422546455225136093968013 92408454920709426035238005)
          ·
            refine ⟨8663292648816508690803563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92408454920709426035238005 8663292648816508690803563)
            ·
              refine ⟨12994938973224763036205345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663292648816508690803563 12994938973224763036205345)
              ·
                refine ⟨9746204229918572277154009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12994938973224763036205345 9746204229918572277154009)
                ·
                  refine ⟨7309653172438929207865507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9746204229918572277154009 7309653172438929207865507)
                  ·
                    refine ⟨10964479758658393811798261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7309653172438929207865507 10964479758658393811798261)
                    ·
                      refine ⟨1027919977374224419856087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10964479758658393811798261 1027919977374224419856087)
                      ·
                        rfl

theorem cell23_2001867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_2001867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001867 prefixEnd_2001867 := by exact prefixLift 2001867
  have htrace : WordTrace (prefixWord ++ tailWord_2001867) baseStart_2001867 baseEnd_2001867 := by
    simpa [prefixWord, tailWord_2001867, baseEnd_2001867] using wordTrace_append hprefix tailTrace_2001867
  have hstable : (prefixWord ++ tailWord_2001867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001867).length < 2 ^ (prefixWord ++ tailWord_2001867).sum := by decide
  have hdescent : baseEnd_2001867 < baseStart_2001867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001881 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 1, 4, 2]
def baseStart_2001881 : Nat := 118140960795 + 2001881 * 2 ^ 59
def prefixEnd_2001881 : Nat := 4983230072969 + 3 ^ 40 * 2001881 * 2
def baseEnd_2001881 : Nat := 1027927166103387365081023

theorem tailTrace_2001881 : CollatzResearch.WordTrace tailWord_2001881 prefixEnd_2001881 1027927166103387365081023 := by
  unfold tailWord_2001881
  simp only [CollatzResearch.WordTrace]
  refine ⟨73014598460534505900333497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48676398973689670600222331 73014598460534505900333497)
  ·
    refine ⟨54760948845400879425250123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73014598460534505900333497 54760948845400879425250123)
    ·
      refine ⟨82141423268101319137875185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54760948845400879425250123 82141423268101319137875185)
      ·
        refine ⟨61606067451075989353406389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82141423268101319137875185 61606067451075989353406389)
        ·
          refine ⟨5775568823538374001881849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61606067451075989353406389 5775568823538374001881849)
          ·
            refine ⟨4331676617653780501411387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775568823538374001881849 4331676617653780501411387)
            ·
              refine ⟨6497514926480670752117081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331676617653780501411387 6497514926480670752117081)
              ·
                refine ⟨4873136194860503064087811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497514926480670752117081 4873136194860503064087811)
                ·
                  refine ⟨7309704292290754596131717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873136194860503064087811 7309704292290754596131717)
                  ·
                    refine ⟨1370569554804516486774697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7309704292290754596131717 1370569554804516486774697)
                    ·
                      refine ⟨1027927166103387365081023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370569554804516486774697 1027927166103387365081023)
                      ·
                        rfl

theorem cell23_2001881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_2001881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001881 prefixEnd_2001881 := by exact prefixLift 2001881
  have htrace : WordTrace (prefixWord ++ tailWord_2001881) baseStart_2001881 baseEnd_2001881 := by
    simpa [prefixWord, tailWord_2001881, baseEnd_2001881] using wordTrace_append hprefix tailTrace_2001881
  have hstable : (prefixWord ++ tailWord_2001881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001881).length < 2 ^ (prefixWord ++ tailWord_2001881).sum := by decide
  have hdescent : baseEnd_2001881 < baseStart_2001881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001885 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_2001885 : Nat := 118140960795 + 2001885 * 2 ^ 59
def prefixEnd_2001885 : Nat := 4983230072969 + 3 ^ 40 * 2001885 * 2
def baseEnd_2001885 : Nat := 1027929220026005349431005

theorem tailTrace_2001885 : CollatzResearch.WordTrace tailWord_2001885 prefixEnd_2001885 1027929220026005349431005 := by
  unfold tailWord_2001885
  simp only [CollatzResearch.WordTrace]
  refine ⟨73014744352520014583479109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48676496235013343055652739 73014744352520014583479109)
  ·
    refine ⟨13690264566097502734402333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73014744352520014583479109 13690264566097502734402333)
    ·
      refine ⟨5133849212286563525400875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13690264566097502734402333 5133849212286563525400875)
      ·
        refine ⟨7700773818429845288101313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133849212286563525400875 7700773818429845288101313)
        ·
          refine ⟨5775580363822383966075985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7700773818429845288101313 5775580363822383966075985)
          ·
            refine ⟨4331685272866787974556989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775580363822383966075985 4331685272866787974556989)
            ·
              refine ⟨1624381977325045490458871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4331685272866787974556989 1624381977325045490458871)
              ·
                refine ⟨2436572965987568235688307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624381977325045490458871 2436572965987568235688307)
                ·
                  refine ⟨3654859448981352353532461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436572965987568235688307 3654859448981352353532461)
                  ·
                    refine ⟨1370572293368007132574673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3654859448981352353532461 1370572293368007132574673)
                    ·
                      refine ⟨1027929220026005349431005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370572293368007132574673 1027929220026005349431005)
                      ·
                        rfl

theorem cell23_2001885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_2001885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001885 prefixEnd_2001885 := by exact prefixLift 2001885
  have htrace : WordTrace (prefixWord ++ tailWord_2001885) baseStart_2001885 baseEnd_2001885 := by
    simpa [prefixWord, tailWord_2001885, baseEnd_2001885] using wordTrace_append hprefix tailTrace_2001885
  have hstable : (prefixWord ++ tailWord_2001885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001885).length < 2 ^ (prefixWord ++ tailWord_2001885).sum := by decide
  have hdescent : baseEnd_2001885 < baseStart_2001885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001897 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 3]
def baseStart_2001897 : Nat := 118140960795 + 2001897 * 2 ^ 59
def prefixEnd_2001897 : Nat := 4983230072969 + 3 ^ 40 * 2001897 * 2
def baseEnd_2001897 : Nat := 1027935381793859302480949

theorem tailTrace_2001897 : CollatzResearch.WordTrace tailWord_2001897 prefixEnd_2001897 1027935381793859302480949 := by
  unfold tailWord_2001897
  simp only [CollatzResearch.WordTrace]
  refine ⟨73015182028476540632915945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48676788018984360421943963 73015182028476540632915945)
  ·
    refine ⟨54761386521357405474686959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73015182028476540632915945 54761386521357405474686959)
    ·
      refine ⟨82142079782036108212030439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54761386521357405474686959 82142079782036108212030439)
      ·
        refine ⟨123213119673054162318045659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82142079782036108212030439 123213119673054162318045659)
        ·
          refine ⟨184819679509581243477068489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123213119673054162318045659 184819679509581243477068489)
          ·
            refine ⟨138614759632185932607801367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184819679509581243477068489 138614759632185932607801367)
            ·
              refine ⟨207922139448278898911702051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138614759632185932607801367 207922139448278898911702051)
              ·
                refine ⟨311883209172418348367553077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207922139448278898911702051 311883209172418348367553077)
                ·
                  refine ⟨29239050859914220159458101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311883209172418348367553077 29239050859914220159458101)
                  ·
                    refine ⟨2741161018116958139949197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29239050859914220159458101 2741161018116958139949197)
                    ·
                      refine ⟨1027935381793859302480949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741161018116958139949197 1027935381793859302480949)
                      ·
                        rfl

theorem cell23_2001897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_2001897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001897 prefixEnd_2001897 := by exact prefixLift 2001897
  have htrace : WordTrace (prefixWord ++ tailWord_2001897) baseStart_2001897 baseEnd_2001897 := by
    simpa [prefixWord, tailWord_2001897, baseEnd_2001897] using wordTrace_append hprefix tailTrace_2001897
  have hstable : (prefixWord ++ tailWord_2001897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001897).length < 2 ^ (prefixWord ++ tailWord_2001897).sum := by decide
  have hdescent : baseEnd_2001897 < baseStart_2001897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001898 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_2001898 : Nat := 118140960795 + 2001898 * 2 ^ 59
def prefixEnd_2001898 : Nat := 4983230072969 + 3 ^ 40 * 2001898 * 2
def baseEnd_2001898 : Nat := 1027935895274513798568445

theorem tailTrace_2001898 : CollatzResearch.WordTrace tailWord_2001898 prefixEnd_2001898 1027935895274513798568445 := by
  unfold tailWord_2001898
  simp only [CollatzResearch.WordTrace]
  refine ⟨18253804625368229450925587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48676812334315278535801565 18253804625368229450925587)
  ·
    refine ⟨27380706938052344176388381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18253804625368229450925587 27380706938052344176388381)
    ·
      refine ⟨10267765101769629066145643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27380706938052344176388381 10267765101769629066145643)
      ·
        refine ⟨15401647652654443599218465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10267765101769629066145643 15401647652654443599218465)
        ·
          refine ⟨11551235739490832699413849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15401647652654443599218465 11551235739490832699413849)
          ·
            refine ⟨8663426804618124524560387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11551235739490832699413849 8663426804618124524560387)
            ·
              refine ⟨12995140206927186786840581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8663426804618124524560387 12995140206927186786840581)
              ·
                refine ⟨2436588788798847522532609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12995140206927186786840581 2436588788798847522532609)
                ·
                  refine ⟨1827441591599135641899457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2436588788798847522532609 1827441591599135641899457)
                  ·
                    refine ⟨1370581193699351731424593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827441591599135641899457 1370581193699351731424593)
                    ·
                      refine ⟨1027935895274513798568445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370581193699351731424593 1027935895274513798568445)
                      ·
                        rfl

theorem cell23_2001898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_2001898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001898 prefixEnd_2001898 := by exact prefixLift 2001898
  have htrace : WordTrace (prefixWord ++ tailWord_2001898) baseStart_2001898 baseEnd_2001898 := by
    simpa [prefixWord, tailWord_2001898, baseEnd_2001898] using wordTrace_append hprefix tailTrace_2001898
  have hstable : (prefixWord ++ tailWord_2001898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001898).length < 2 ^ (prefixWord ++ tailWord_2001898).sum := by decide
  have hdescent : baseEnd_2001898 < baseStart_2001898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001917 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_2001917 : Nat := 118140960795 + 2001917 * 2 ^ 59
def prefixEnd_2001917 : Nat := 4983230072969 + 3 ^ 40 * 2001917 * 2
def baseEnd_2001917 : Nat := 342648550468983074743619

theorem tailTrace_2001917 : CollatzResearch.WordTrace tailWord_2001917 prefixEnd_2001917 342648550468983074743619 := by
  unfold tailWord_2001917
  simp only [CollatzResearch.WordTrace]
  refine ⟨73015911488404084048644005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48677274325602722699096003 73015911488404084048644005)
  ·
    refine ⟨13690483404075765759120751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73015911488404084048644005 13690483404075765759120751)
    ·
      refine ⟨20535725106113648638681127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13690483404075765759120751 20535725106113648638681127)
      ·
        refine ⟨30803587659170472958021691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20535725106113648638681127 30803587659170472958021691)
        ·
          refine ⟨46205381488755709437032537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30803587659170472958021691 46205381488755709437032537)
          ·
            refine ⟨34654036116566782077774403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46205381488755709437032537 34654036116566782077774403)
            ·
              refine ⟨51981054174850173116661605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34654036116566782077774403 51981054174850173116661605)
              ·
                refine ⟨9746447657784407459374051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51981054174850173116661605 9746447657784407459374051)
                ·
                  refine ⟨14619671486676611189061077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9746447657784407459374051 14619671486676611189061077)
                  ·
                    refine ⟨342648550468983074743619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14619671486676611189061077 342648550468983074743619)
                    ·
                      rfl

theorem cell23_2001917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_2001917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001917 prefixEnd_2001917 := by exact prefixLift 2001917
  have htrace : WordTrace (prefixWord ++ tailWord_2001917) baseStart_2001917 baseEnd_2001917 := by
    simpa [prefixWord, tailWord_2001917, baseEnd_2001917] using wordTrace_append hprefix tailTrace_2001917
  have hstable : (prefixWord ++ tailWord_2001917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001917).length < 2 ^ (prefixWord ++ tailWord_2001917).sum := by decide
  have hdescent : baseEnd_2001917 < baseStart_2001917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001934 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_2001934 : Nat := 118140960795 + 2001934 * 2 ^ 59
def prefixEnd_2001934 : Nat := 4983230072969 + 3 ^ 40 * 2001934 * 2
def baseEnd_2001934 : Nat := 342651460192691885906093

theorem tailTrace_2001934 : CollatzResearch.WordTrace tailWord_2001934 prefixEnd_2001934 342651460192691885906093 := by
  unfold tailWord_2001934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127066441167811994001607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48677687686228330634675237 9127066441167811994001607)
  ·
    refine ⟨13690599661751717991002411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9127066441167811994001607 13690599661751717991002411)
    ·
      refine ⟨20535899492627576986503617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13690599661751717991002411 20535899492627576986503617)
      ·
        refine ⟨15401924619470682739877713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20535899492627576986503617 15401924619470682739877713)
        ·
          refine ⟨11551443464603012054908285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15401924619470682739877713 11551443464603012054908285)
          ·
            refine ⟨4331791299226129520590607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11551443464603012054908285 4331791299226129520590607)
            ·
              refine ⟨6497686948839194280885911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331791299226129520590607 6497686948839194280885911)
              ·
                refine ⟨9746530423258791421328867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6497686948839194280885911 9746530423258791421328867)
                ·
                  refine ⟨14619795634888187131993301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9746530423258791421328867 14619795634888187131993301)
                  ·
                    refine ⟨342651460192691885906093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14619795634888187131993301 342651460192691885906093)
                    ·
                      rfl

theorem cell23_2001934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_2001934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001934 prefixEnd_2001934 := by exact prefixLift 2001934
  have htrace : WordTrace (prefixWord ++ tailWord_2001934) baseStart_2001934 baseEnd_2001934 := by
    simpa [prefixWord, tailWord_2001934, baseEnd_2001934] using wordTrace_append hprefix tailTrace_2001934
  have hstable : (prefixWord ++ tailWord_2001934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001934).length < 2 ^ (prefixWord ++ tailWord_2001934).sum := by decide
  have hdescent : baseEnd_2001934 < baseStart_2001934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2001981 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_2001981 : Nat := 118140960795 + 2001981 * 2 ^ 59
def prefixEnd_2001981 : Nat := 4983230072969 + 3 ^ 40 * 2001981 * 2
def baseEnd_2001981 : Nat := 342659504722945657943521

theorem tailTrace_2001981 : CollatzResearch.WordTrace tailWord_2001981 prefixEnd_2001981 342659504722945657943521 := by
  unfold tailWord_2001981
  simp only [CollatzResearch.WordTrace]
  refine ⟨73018245760172222978973797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48678830506781481985982531 73018245760172222978973797)
  ·
    refine ⟨13690921080032291808557587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73018245760172222978973797 13690921080032291808557587)
    ·
      refine ⟨20536381620048437712836381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13690921080032291808557587 20536381620048437712836381)
      ·
        refine ⟨7701143107518164142313643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20536381620048437712836381 7701143107518164142313643)
        ·
          refine ⟨11551714661277246213470465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701143107518164142313643 11551714661277246213470465)
          ·
            refine ⟨8663785995957934660102849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11551714661277246213470465 8663785995957934660102849)
            ·
              refine ⟨6497839496968450995077137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8663785995957934660102849 6497839496968450995077137)
              ·
                refine ⟨4873379622726338246307853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497839496968450995077137 4873379622726338246307853)
                ·
                  refine ⟨1827517358522376842365445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4873379622726338246307853 1827517358522376842365445)
                  ·
                    refine ⟨342659504722945657943521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1827517358522376842365445 342659504722945657943521)
                    ·
                      rfl

theorem cell23_2001981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_2001981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2001981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2001981 prefixEnd_2001981 := by exact prefixLift 2001981
  have htrace : WordTrace (prefixWord ++ tailWord_2001981) baseStart_2001981 baseEnd_2001981 := by
    simpa [prefixWord, tailWord_2001981, baseEnd_2001981] using wordTrace_append hprefix tailTrace_2001981
  have hstable : (prefixWord ++ tailWord_2001981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2001981).length < 2 ^ (prefixWord ++ tailWord_2001981).sum := by decide
  have hdescent : baseEnd_2001981 < baseStart_2001981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2001981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002027 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 10]
def baseStart_2002027 : Nat := 118140960795 + 2002027 * 2 ^ 59
def prefixEnd_2002027 : Nat := 4983230072969 + 3 ^ 40 * 2002027 * 2
def baseEnd_2002027 : Nat := 1028002134278943793855351

theorem tailTrace_2002027 : CollatzResearch.WordTrace tailWord_2002027 prefixEnd_2002027 1028002134278943793855351 := by
  unfold tailWord_2002027
  simp only [CollatzResearch.WordTrace]
  refine ⟨73019923518005572835148335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48679949012003715223432223 73019923518005572835148335)
  ·
    refine ⟨109529885277008359252722503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73019923518005572835148335 109529885277008359252722503)
    ·
      refine ⟨164294827915512538879083755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109529885277008359252722503 164294827915512538879083755)
      ·
        refine ⟨246442241873268808318625633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164294827915512538879083755 246442241873268808318625633)
        ·
          refine ⟨184831681404951606238969225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246442241873268808318625633 184831681404951606238969225)
          ·
            refine ⟨138623761053713704679226919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184831681404951606238969225 138623761053713704679226919)
            ·
              refine ⟨207935641580570557018840379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138623761053713704679226919 207935641580570557018840379)
              ·
                refine ⟨311903462370855835528260569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207935641580570557018840379 311903462370855835528260569)
                ·
                  refine ⟨233927596778141876646195427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311903462370855835528260569 233927596778141876646195427)
                  ·
                    refine ⟨350891395167212814969293141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 233927596778141876646195427 350891395167212814969293141)
                    ·
                      refine ⟨1028002134278943793855351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 350891395167212814969293141 1028002134278943793855351)
                      ·
                        rfl

theorem cell23_2002027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_2002027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002027 prefixEnd_2002027 := by exact prefixLift 2002027
  have htrace : WordTrace (prefixWord ++ tailWord_2002027) baseStart_2002027 baseEnd_2002027 := by
    simpa [prefixWord, tailWord_2002027, baseEnd_2002027] using wordTrace_append hprefix tailTrace_2002027
  have hstable : (prefixWord ++ tailWord_2002027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002027).length < 2 ^ (prefixWord ++ tailWord_2002027).sum := by decide
  have hdescent : baseEnd_2002027 < baseStart_2002027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002031 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 4, 3, 2]
def baseStart_2002031 : Nat := 118140960795 + 2002031 * 2 ^ 59
def prefixEnd_2002031 : Nat := 4983230072969 + 3 ^ 40 * 2002031 * 2
def baseEnd_2002031 : Nat := 1028004188201561778205333

theorem tailTrace_2002031 : CollatzResearch.WordTrace tailWord_2002031 prefixEnd_2002031 1028004188201561778205333 := by
  unfold tailWord_2002031
  simp only [CollatzResearch.WordTrace]
  refine ⟨73020069409991081518293947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48680046273327387678862631 73020069409991081518293947)
  ·
    refine ⟨109530104114986622277440921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73020069409991081518293947 109530104114986622277440921)
    ·
      refine ⟨82147578086239966708080691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109530104114986622277440921 82147578086239966708080691)
      ·
        refine ⟨123221367129359950062121037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82147578086239966708080691 123221367129359950062121037)
        ·
          refine ⟨46208012673509981273295389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123221367129359950062121037 46208012673509981273295389)
          ·
            refine ⟨17328004752566242977485771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46208012673509981273295389 17328004752566242977485771)
            ·
              refine ⟨25992007128849364466228657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17328004752566242977485771 25992007128849364466228657)
              ·
                refine ⟨19494005346637023349671493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25992007128849364466228657 19494005346637023349671493)
                ·
                  refine ⟨3655126002494441878063405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19494005346637023349671493 3655126002494441878063405)
                  ·
                    refine ⟨1370672250935415704273777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655126002494441878063405 1370672250935415704273777)
                    ·
                      refine ⟨1028004188201561778205333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370672250935415704273777 1028004188201561778205333)
                      ·
                        rfl

theorem cell23_2002031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 3, 2].length) (baseStart_2002031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002031 prefixEnd_2002031 := by exact prefixLift 2002031
  have htrace : WordTrace (prefixWord ++ tailWord_2002031) baseStart_2002031 baseEnd_2002031 := by
    simpa [prefixWord, tailWord_2002031, baseEnd_2002031] using wordTrace_append hprefix tailTrace_2002031
  have hstable : (prefixWord ++ tailWord_2002031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002031).length < 2 ^ (prefixWord ++ tailWord_2002031).sum := by decide
  have hdescent : baseEnd_2002031 < baseStart_2002031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002038 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2002038 : Nat := 118140960795 + 2002038 * 2 ^ 59
def prefixEnd_2002038 : Nat := 4983230072969 + 3 ^ 40 * 2002038 * 2
def baseEnd_2002038 : Nat := 1028007782566143250817801

theorem tailTrace_2002038 : CollatzResearch.WordTrace tailWord_2002038 prefixEnd_2002038 1028007782566143250817801 := by
  unfold tailWord_2002038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563770295060357607112423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48680216480643814475865845 4563770295060357607112423)
  ·
    refine ⟨6845655442590536410668635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4563770295060357607112423 6845655442590536410668635)
    ·
      refine ⟨10268483163885804616002953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6845655442590536410668635 10268483163885804616002953)
      ·
        refine ⟨7701362372914353462002215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10268483163885804616002953 7701362372914353462002215)
        ·
          refine ⟨11552043559371530193003323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701362372914353462002215 11552043559371530193003323)
          ·
            refine ⟨17328065339057295289504985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552043559371530193003323 17328065339057295289504985)
            ·
              refine ⟨12996049004292971467128739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17328065339057295289504985 12996049004292971467128739)
              ·
                refine ⟨19494073506439457200693109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12996049004292971467128739 19494073506439457200693109)
                ·
                  refine ⟨1827569391228699112564979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19494073506439457200693109 1827569391228699112564979)
                  ·
                    refine ⟨2741354086843048668847469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1827569391228699112564979 2741354086843048668847469)
                    ·
                      refine ⟨1028007782566143250817801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741354086843048668847469 1028007782566143250817801)
                      ·
                        rfl

theorem cell23_2002038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2002038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002038 prefixEnd_2002038 := by exact prefixLift 2002038
  have htrace : WordTrace (prefixWord ++ tailWord_2002038) baseStart_2002038 baseEnd_2002038 := by
    simpa [prefixWord, tailWord_2002038, baseEnd_2002038] using wordTrace_append hprefix tailTrace_2002038
  have hstable : (prefixWord ++ tailWord_2002038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002038).length < 2 ^ (prefixWord ++ tailWord_2002038).sum := by decide
  have hdescent : baseEnd_2002038 < baseStart_2002038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002041 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 3, 5]
def baseStart_2002041 : Nat := 118140960795 + 2002041 * 2 ^ 59
def prefixEnd_2002041 : Nat := 4983230072969 + 3 ^ 40 * 2002041 * 2
def baseEnd_2002041 : Nat := 342669774336035579693429

theorem tailTrace_2002041 : CollatzResearch.WordTrace tailWord_2002041 prefixEnd_2002041 342669774336035579693429 := by
  unfold tailWord_2002041
  simp only [CollatzResearch.WordTrace]
  refine ⟨73020434139954853226157977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48680289426636568817438651 73020434139954853226157977)
  ·
    refine ⟨54765325604966139919618483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73020434139954853226157977 54765325604966139919618483)
    ·
      refine ⟨82147988407449209879427725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54765325604966139919618483 82147988407449209879427725)
      ·
        refine ⟨30805495652793453704785397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82147988407449209879427725 30805495652793453704785397)
        ·
          refine ⟨2888015217449386284823631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30805495652793453704785397 2888015217449386284823631)
          ·
            refine ⟨4332022826174079427235447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888015217449386284823631 4332022826174079427235447)
            ·
              refine ⟨6498034239261119140853171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332022826174079427235447 6498034239261119140853171)
              ·
                refine ⟨9747051358891678711279757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498034239261119140853171 9747051358891678711279757)
                ·
                  refine ⟨3655144259584379516729909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9747051358891678711279757 3655144259584379516729909)
                  ·
                    refine ⟨342669774336035579693429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3655144259584379516729909 342669774336035579693429)
                    ·
                      rfl

theorem cell23_2002041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_2002041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002041 prefixEnd_2002041 := by exact prefixLift 2002041
  have htrace : WordTrace (prefixWord ++ tailWord_2002041) baseStart_2002041 baseEnd_2002041 := by
    simpa [prefixWord, tailWord_2002041, baseEnd_2002041] using wordTrace_append hprefix tailTrace_2002041
  have hstable : (prefixWord ++ tailWord_2002041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002041).length < 2 ^ (prefixWord ++ tailWord_2002041).sum := by decide
  have hdescent : baseEnd_2002041 < baseStart_2002041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002058 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 1, 5]
def baseStart_2002058 : Nat := 118140960795 + 2002058 * 2 ^ 59
def prefixEnd_2002058 : Nat := 4983230072969 + 3 ^ 40 * 2002058 * 2
def baseEnd_2002058 : Nat := 342672684059744390855903

theorem tailTrace_2002058 : CollatzResearch.WordTrace tailWord_2002058 prefixEnd_2002058 342672684059744390855903 := by
  unfold tailWord_2002058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18255263545223316282381707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48680702787262176753017885 18255263545223316282381707)
  ·
    refine ⟨27382895317834974423572561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18255263545223316282381707 27382895317834974423572561)
    ·
      refine ⟨20537171488376230817679421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27382895317834974423572561 20537171488376230817679421)
      ·
        refine ⟨7701439308141086556629783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20537171488376230817679421 7701439308141086556629783)
        ·
          refine ⟨11552158962211629834944675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701439308141086556629783 11552158962211629834944675)
          ·
            refine ⟨17328238443317444752417013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552158962211629834944675 17328238443317444752417013)
            ·
              refine ⟨1624522354061010445539095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17328238443317444752417013 1624522354061010445539095)
              ·
                refine ⟨2436783531091515668308643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624522354061010445539095 2436783531091515668308643)
                ·
                  refine ⟨3655175296637273502462965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436783531091515668308643 3655175296637273502462965)
                  ·
                    refine ⟨342672684059744390855903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3655175296637273502462965 342672684059744390855903)
                    ·
                      rfl

theorem cell23_2002058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_2002058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002058 prefixEnd_2002058 := by exact prefixLift 2002058
  have htrace : WordTrace (prefixWord ++ tailWord_2002058) baseStart_2002058 baseEnd_2002058 := by
    simpa [prefixWord, tailWord_2002058, baseEnd_2002058] using wordTrace_append hprefix tailTrace_2002058
  have hstable : (prefixWord ++ tailWord_2002058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002058).length < 2 ^ (prefixWord ++ tailWord_2002058).sum := by decide
  have hdescent : baseEnd_2002058 < baseStart_2002058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002064 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_2002064 : Nat := 118140960795 + 2002064 * 2 ^ 59
def prefixEnd_2002064 : Nat := 4983230072969 + 3 ^ 40 * 2002064 * 2
def baseEnd_2002064 : Nat := 1028021133063160149092681

theorem tailTrace_2002064 : CollatzResearch.WordTrace tailWord_2002064 prefixEnd_2002064 1028021133063160149092681 := by
  unfold tailWord_2002064
  simp only [CollatzResearch.WordTrace]
  refine ⟨36510636509435764077122623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48680848679247685436163497 36510636509435764077122623)
  ·
    refine ⟨54765954764153646115683935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36510636509435764077122623 54765954764153646115683935)
    ·
      refine ⟨82148932146230469173525903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54765954764153646115683935 82148932146230469173525903)
      ·
        refine ⟨123223398219345703760288855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82148932146230469173525903 123223398219345703760288855)
        ·
          refine ⟨184835097329018555640433283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123223398219345703760288855 184835097329018555640433283)
          ·
            refine ⟨277252645993527833460649925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184835097329018555640433283 277252645993527833460649925)
            ·
              refine ⟨51984871123786468773871861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277252645993527833460649925 51984871123786468773871861)
              ·
                refine ⟨4873581667854981447550487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51984871123786468773871861 4873581667854981447550487)
                ·
                  refine ⟨7310372501782472171325731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873581667854981447550487 7310372501782472171325731)
                  ·
                    refine ⟨10965558752673708256988597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7310372501782472171325731 10965558752673708256988597)
                    ·
                      refine ⟨1028021133063160149092681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10965558752673708256988597 1028021133063160149092681)
                      ·
                        rfl

theorem cell23_2002064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_2002064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002064 prefixEnd_2002064 := by exact prefixLift 2002064
  have htrace : WordTrace (prefixWord ++ tailWord_2002064) baseStart_2002064 baseEnd_2002064 := by
    simpa [prefixWord, tailWord_2002064, baseEnd_2002064] using wordTrace_append hprefix tailTrace_2002064
  have hstable : (prefixWord ++ tailWord_2002064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002064).length < 2 ^ (prefixWord ++ tailWord_2002064).sum := by decide
  have hdescent : baseEnd_2002064 < baseStart_2002064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002072 : List Nat := [2, 1, 2, 4, 2, 1, 4, 2, 1, 1, 3]
def baseStart_2002072 : Nat := 118140960795 + 2002072 * 2 ^ 59
def prefixEnd_2002072 : Nat := 4983230072969 + 3 ^ 40 * 2002072 * 2
def baseEnd_2002072 : Nat := 1028025240908396117792645

theorem tailTrace_2002072 : CollatzResearch.WordTrace tailWord_2002072 prefixEnd_2002072 1028025240908396117792645 := by
  unfold tailWord_2002072
  simp only [CollatzResearch.WordTrace]
  refine ⟨36510782401421272760268235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48681043201895030347024313 36510782401421272760268235)
  ·
    refine ⟨54766173602131909140402353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36510782401421272760268235 54766173602131909140402353)
    ·
      refine ⟨41074630201598931855301765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54766173602131909140402353 41074630201598931855301765)
      ·
        refine ⟨7701493162799799722869081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41074630201598931855301765 7701493162799799722869081)
        ·
          refine ⟨5776119872099849792151811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7701493162799799722869081 5776119872099849792151811)
          ·
            refine ⟨8664179808149774688227717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5776119872099849792151811 8664179808149774688227717)
            ·
              refine ⟨1624533714028082754042697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8664179808149774688227717 1624533714028082754042697)
              ·
                refine ⟨1218400285521062065532023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624533714028082754042697 1218400285521062065532023)
                ·
                  refine ⟨1827600428281593098298035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218400285521062065532023 1827600428281593098298035)
                  ·
                    refine ⟨2741400642422389647447053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1827600428281593098298035 2741400642422389647447053)
                    ·
                      refine ⟨1028025240908396117792645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741400642422389647447053 1028025240908396117792645)
                      ·
                        rfl

theorem cell23_2002072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_2002072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002072 prefixEnd_2002072 := by exact prefixLift 2002072
  have htrace : WordTrace (prefixWord ++ tailWord_2002072) baseStart_2002072 baseEnd_2002072 := by
    simpa [prefixWord, tailWord_2002072, baseEnd_2002072] using wordTrace_append hprefix tailTrace_2002072
  have hstable : (prefixWord ++ tailWord_2002072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002072).length < 2 ^ (prefixWord ++ tailWord_2002072).sum := by decide
  have hdescent : baseEnd_2002072 < baseStart_2002072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002078 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2002078 : Nat := 118140960795 + 2002078 * 2 ^ 59
def prefixEnd_2002078 : Nat := 4983230072969 + 3 ^ 40 * 2002078 * 2
def baseEnd_2002078 : Nat := 1028028321792323094317617

theorem tailTrace_2002078 : CollatzResearch.WordTrace tailWord_2002078 prefixEnd_2002078 1028028321792323094317617 := by
  unfold tailWord_2002078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127722955102601068156861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48681189093880539030169925 9127722955102601068156861)
  ·
    refine ⟨3422896108163475400558823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9127722955102601068156861 3422896108163475400558823)
    ·
      refine ⟨5134344162245213100838235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422896108163475400558823 5134344162245213100838235)
      ·
        refine ⟨7701516243367819651257353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134344162245213100838235 7701516243367819651257353)
        ·
          refine ⟨5776137182525864738443015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7701516243367819651257353 5776137182525864738443015)
          ·
            refine ⟨8664205773788797107664523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5776137182525864738443015 8664205773788797107664523)
            ·
              refine ⟨12996308660683195661496785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8664205773788797107664523 12996308660683195661496785)
              ·
                refine ⟨9747231495512396746122589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12996308660683195661496785 9747231495512396746122589)
                ·
                  refine ⟨3655211810817148779795971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9747231495512396746122589 3655211810817148779795971)
                  ·
                    refine ⟨5482817716225723169693957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3655211810817148779795971 5482817716225723169693957)
                    ·
                      refine ⟨1028028321792323094317617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5482817716225723169693957 1028028321792323094317617)
                      ·
                        rfl

theorem cell23_2002078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2002078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002078 prefixEnd_2002078 := by exact prefixLift 2002078
  have htrace : WordTrace (prefixWord ++ tailWord_2002078) baseStart_2002078 baseEnd_2002078 := by
    simpa [prefixWord, tailWord_2002078, baseEnd_2002078] using wordTrace_append hprefix tailTrace_2002078
  have hstable : (prefixWord ++ tailWord_2002078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002078).length < 2 ^ (prefixWord ++ tailWord_2002078).sum := by decide
  have hdescent : baseEnd_2002078 < baseStart_2002078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002081 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2002081 : Nat := 118140960795 + 2002081 * 2 ^ 59
def prefixEnd_2002081 : Nat := 4983230072969 + 3 ^ 40 * 2002081 * 2
def baseEnd_2002081 : Nat := 1028029862234286582580103

theorem tailTrace_2002081 : CollatzResearch.WordTrace tailWord_2002081 prefixEnd_2002081 1028029862234286582580103 := by
  unfold tailWord_2002081
  simp only [CollatzResearch.WordTrace]
  refine ⟨73021893059809940057614097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48681262039873293371742731 73021893059809940057614097)
  ·
    refine ⟨54766419794857455043210573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73021893059809940057614097 54766419794857455043210573)
    ·
      refine ⟨20537407423071545641203965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54766419794857455043210573 20537407423071545641203965)
      ·
        refine ⟨7701527783651829615451487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20537407423071545641203965 7701527783651829615451487)
        ·
          refine ⟨11552291675477744423177231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701527783651829615451487 11552291675477744423177231)
          ·
            refine ⟨17328437513216616634765847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552291675477744423177231 17328437513216616634765847)
            ·
              refine ⟨25992656269824924952148771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17328437513216616634765847 25992656269824924952148771)
              ·
                refine ⟨38988984404737387428223157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25992656269824924952148771 38988984404737387428223157)
                ·
                  refine ⟨3655217287944130071395921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38988984404737387428223157 3655217287944130071395921)
                  ·
                    refine ⟨2741412965958097553546941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655217287944130071395921 2741412965958097553546941)
                    ·
                      refine ⟨1028029862234286582580103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741412965958097553546941 1028029862234286582580103)
                      ·
                        rfl

theorem cell23_2002081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2002081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002081 prefixEnd_2002081 := by exact prefixLift 2002081
  have htrace : WordTrace (prefixWord ++ tailWord_2002081) baseStart_2002081 baseEnd_2002081 := by
    simpa [prefixWord, tailWord_2002081, baseEnd_2002081] using wordTrace_append hprefix tailTrace_2002081
  have hstable : (prefixWord ++ tailWord_2002081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002081).length < 2 ^ (prefixWord ++ tailWord_2002081).sum := by decide
  have hdescent : baseEnd_2002081 < baseStart_2002081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002111 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 3]
def baseStart_2002111 : Nat := 118140960795 + 2002111 * 2 ^ 59
def prefixEnd_2002111 : Nat := 4983230072969 + 3 ^ 40 * 2002111 * 2
def baseEnd_2002111 : Nat := 1028045266653921465204965

theorem tailTrace_2002111 : CollatzResearch.WordTrace tailWord_2002111 prefixEnd_2002111 1028045266653921465204965 := by
  unfold tailWord_2002111
  simp only [CollatzResearch.WordTrace]
  refine ⟨73022987249701255181206187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48681991499800836787470791 73022987249701255181206187)
  ·
    refine ⟨109534480874551882771809281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73022987249701255181206187 109534480874551882771809281)
    ·
      refine ⟨82150860655913912078856961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109534480874551882771809281 82150860655913912078856961)
      ·
        refine ⟨61613145491935434059142721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82150860655913912078856961 61613145491935434059142721)
        ·
          refine ⟨46209859118951575544357041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61613145491935434059142721 46209859118951575544357041)
          ·
            refine ⟨34657394339213681658267781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46209859118951575544357041 34657394339213681658267781)
            ·
              refine ⟨6498261438602565310925209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34657394339213681658267781 6498261438602565310925209)
              ·
                refine ⟨4873696078951923983193907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498261438602565310925209 4873696078951923983193907)
                ·
                  refine ⟨7310544118427885974790861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873696078951923983193907 7310544118427885974790861)
                  ·
                    refine ⟨2741454044410457240546573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7310544118427885974790861 2741454044410457240546573)
                    ·
                      refine ⟨1028045266653921465204965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741454044410457240546573 1028045266653921465204965)
                      ·
                        rfl

theorem cell23_2002111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_2002111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002111 prefixEnd_2002111 := by exact prefixLift 2002111
  have htrace : WordTrace (prefixWord ++ tailWord_2002111) baseStart_2002111 baseEnd_2002111 := by
    simpa [prefixWord, tailWord_2002111, baseEnd_2002111] using wordTrace_append hprefix tailTrace_2002111
  have hstable : (prefixWord ++ tailWord_2002111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002111).length < 2 ^ (prefixWord ++ tailWord_2002111).sum := by decide
  have hdescent : baseEnd_2002111 < baseStart_2002111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002112 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 1, 1, 4]
def baseStart_2002112 : Nat := 118140960795 + 2002112 * 2 ^ 59
def prefixEnd_2002112 : Nat := 4983230072969 + 3 ^ 40 * 2002112 * 2
def baseEnd_2002112 : Nat := 1028045780134575961292461

theorem tailTrace_2002112 : CollatzResearch.WordTrace tailWord_2002112 prefixEnd_2002112 1028045780134575961292461 := by
  unfold tailWord_2002112
  simp only [CollatzResearch.WordTrace]
  refine ⟨36511511861348816175996295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48682015815131754901328393 36511511861348816175996295)
  ·
    refine ⟨54767267792023224263994443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36511511861348816175996295 54767267792023224263994443)
    ·
      refine ⟨82150901688034836395991665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54767267792023224263994443 82150901688034836395991665)
      ·
        refine ⟨61613176266026127296993749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82150901688034836395991665 61613176266026127296993749)
        ·
          refine ⟨1444058818734987358523291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 61613176266026127296993749 1444058818734987358523291)
          ·
            refine ⟨2166088228102481037784937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444058818734987358523291 2166088228102481037784937)
            ·
              refine ⟨1624566171076860778338703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166088228102481037784937 1624566171076860778338703)
              ·
                refine ⟨2436849256615291167508055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624566171076860778338703 2436849256615291167508055)
                ·
                  refine ⟨3655273884922936751262083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436849256615291167508055 3655273884922936751262083)
                  ·
                    refine ⟨5482910827384405126893125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3655273884922936751262083 5482910827384405126893125)
                    ·
                      refine ⟨1028045780134575961292461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5482910827384405126893125 1028045780134575961292461)
                      ·
                        rfl

theorem cell23_2002112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_2002112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002112 prefixEnd_2002112 := by exact prefixLift 2002112
  have htrace : WordTrace (prefixWord ++ tailWord_2002112) baseStart_2002112 baseEnd_2002112 := by
    simpa [prefixWord, tailWord_2002112, baseEnd_2002112] using wordTrace_append hprefix tailTrace_2002112
  have hstable : (prefixWord ++ tailWord_2002112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002112).length < 2 ^ (prefixWord ++ tailWord_2002112).sum := by decide
  have hdescent : baseEnd_2002112 < baseStart_2002112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002155 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 1, 3, 2]
def baseStart_2002155 : Nat := 118140960795 + 2002155 * 2 ^ 59
def prefixEnd_2002155 : Nat := 4983230072969 + 3 ^ 40 * 2002155 * 2
def baseEnd_2002155 : Nat := 1028067859802719293054763

theorem tailTrace_2002155 : CollatzResearch.WordTrace tailWord_2002155 prefixEnd_2002155 1028067859802719293054763 := by
  unfold tailWord_2002155
  simp only [CollatzResearch.WordTrace]
  refine ⟨73024592061541850695807919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48683061374361233797205279 73024592061541850695807919)
  ·
    refine ⟨109536888092312776043711879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73024592061541850695807919 109536888092312776043711879)
    ·
      refine ⟨164305332138469164065567819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109536888092312776043711879 164305332138469164065567819)
      ·
        refine ⟨246457998207703746098351729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164305332138469164065567819 246457998207703746098351729)
        ·
          refine ⟨184843498655777809573763797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 246457998207703746098351729 184843498655777809573763797)
          ·
            refine ⟨4332269499744792411885089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 184843498655777809573763797 4332269499744792411885089)
            ·
              refine ⟨3249202124808594308913817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4332269499744792411885089 3249202124808594308913817)
              ·
                refine ⟨2436901593606445731685363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3249202124808594308913817 2436901593606445731685363)
                ·
                  refine ⟨3655352390409668597528045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436901593606445731685363 3655352390409668597528045)
                  ·
                    refine ⟨1370757146403625724073017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655352390409668597528045 1370757146403625724073017)
                    ·
                      refine ⟨1028067859802719293054763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370757146403625724073017 1028067859802719293054763)
                      ·
                        rfl

theorem cell23_2002155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 3, 2].length) (baseStart_2002155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002155 prefixEnd_2002155 := by exact prefixLift 2002155
  have htrace : WordTrace (prefixWord ++ tailWord_2002155) baseStart_2002155 baseEnd_2002155 := by
    simpa [prefixWord, tailWord_2002155, baseEnd_2002155] using wordTrace_append hprefix tailTrace_2002155
  have hstable : (prefixWord ++ tailWord_2002155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002155).length < 2 ^ (prefixWord ++ tailWord_2002155).sum := by decide
  have hdescent : baseEnd_2002155 < baseStart_2002155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002185 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 2, 2, 2]
def baseStart_2002185 : Nat := 118140960795 + 2002185 * 2 ^ 59
def prefixEnd_2002185 : Nat := 4983230072969 + 3 ^ 40 * 2002185 * 2
def baseEnd_2002185 : Nat := 1028083264222354175679625

theorem tailTrace_2002185 : CollatzResearch.WordTrace tailWord_2002185 prefixEnd_2002185 1028083264222354175679625 := by
  unfold tailWord_2002185
  simp only [CollatzResearch.WordTrace]
  refine ⟨73025686251433165819400009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48683790834288777212933339 73025686251433165819400009)
  ·
    refine ⟨54769264688574874364550007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73025686251433165819400009 54769264688574874364550007)
    ·
      refine ⟨82153897032862311546825011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54769264688574874364550007 82153897032862311546825011)
      ·
        refine ⟨123230845549293467320237517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82153897032862311546825011 123230845549293467320237517)
        ·
          refine ⟨46211567080985050245089069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123230845549293467320237517 46211567080985050245089069)
          ·
            refine ⟨17329337655369393841908401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46211567080985050245089069 17329337655369393841908401)
            ·
              refine ⟨12997003241527045381431301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17329337655369393841908401 12997003241527045381431301)
              ·
                refine ⟨2436938107786321009018369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12997003241527045381431301 2436938107786321009018369)
                ·
                  refine ⟨1827703580839740756763777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2436938107786321009018369 1827703580839740756763777)
                  ·
                    refine ⟨1370777685629805567572833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827703580839740756763777 1370777685629805567572833)
                    ·
                      refine ⟨1028083264222354175679625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370777685629805567572833 1028083264222354175679625)
                      ·
                        rfl

theorem cell23_2002185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 2, 2].length) (baseStart_2002185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002185 prefixEnd_2002185 := by exact prefixLift 2002185
  have htrace : WordTrace (prefixWord ++ tailWord_2002185) baseStart_2002185 baseEnd_2002185 := by
    simpa [prefixWord, tailWord_2002185, baseEnd_2002185] using wordTrace_append hprefix tailTrace_2002185
  have hstable : (prefixWord ++ tailWord_2002185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002185).length < 2 ^ (prefixWord ++ tailWord_2002185).sum := by decide
  have hdescent : baseEnd_2002185 < baseStart_2002185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002202 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2]
def baseStart_2002202 : Nat := 118140960795 + 2002202 * 2 ^ 59
def prefixEnd_2002202 : Nat := 4983230072969 + 3 ^ 40 * 2002202 * 2
def baseEnd_2002202 : Nat := 1028091993393480609167047

theorem tailTrace_2002202 : CollatzResearch.WordTrace tailWord_2002202 prefixEnd_2002202 1028091993393480609167047 := by
  unfold tailWord_2002202
  simp only [CollatzResearch.WordTrace]
  refine ⟨18256576573092894430692215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48684204194914385148512573 18256576573092894430692215)
  ·
    refine ⟨27384864859639341646038323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18256576573092894430692215 27384864859639341646038323)
    ·
      refine ⟨41077297289459012469057485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27384864859639341646038323 41077297289459012469057485)
      ·
        refine ⟨15403986483547129675896557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41077297289459012469057485 15403986483547129675896557)
        ·
          refine ⟨5776494931330173628461209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15403986483547129675896557 5776494931330173628461209)
          ·
            refine ⟨4332371198497630221345907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5776494931330173628461209 4332371198497630221345907)
            ·
              refine ⟨6498556797746445332018861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4332371198497630221345907 6498556797746445332018861)
              ·
                refine ⟨2436958799154916999507073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6498556797746445332018861 2436958799154916999507073)
                ·
                  refine ⟨1827719099366187749630305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2436958799154916999507073 1827719099366187749630305)
                  ·
                    refine ⟨1370789324524640812222729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827719099366187749630305 1370789324524640812222729)
                    ·
                      refine ⟨1028091993393480609167047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370789324524640812222729 1028091993393480609167047)
                      ·
                        rfl

theorem cell23_2002202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_2002202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002202 prefixEnd_2002202 := by exact prefixLift 2002202
  have htrace : WordTrace (prefixWord ++ tailWord_2002202) baseStart_2002202 baseEnd_2002202 := by
    simpa [prefixWord, tailWord_2002202, baseEnd_2002202] using wordTrace_append hprefix tailTrace_2002202
  have hstable : (prefixWord ++ tailWord_2002202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002202).length < 2 ^ (prefixWord ++ tailWord_2002202).sum := by decide
  have hdescent : baseEnd_2002202 < baseStart_2002202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002206 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2002206 : Nat := 118140960795 + 2002206 * 2 ^ 59
def prefixEnd_2002206 : Nat := 4983230072969 + 3 ^ 40 * 2002206 * 2
def baseEnd_2002206 : Nat := 1028094047316098593517029

theorem tailTrace_2002206 : CollatzResearch.WordTrace tailWord_2002206 prefixEnd_2002206 1028094047316098593517029 := by
  unfold tailWord_2002206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9128306523044635800739309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48684301456238057603942981 9128306523044635800739309)
  ·
    refine ⟨3423114946141738425277241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9128306523044635800739309 3423114946141738425277241)
    ·
      refine ⟨2567336209606303818957931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3423114946141738425277241 2567336209606303818957931)
      ·
        refine ⟨3851004314409455728436897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567336209606303818957931 3851004314409455728436897)
        ·
          refine ⟨2888253235807091796327673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3851004314409455728436897 2888253235807091796327673)
          ·
            refine ⟨2166189926855318847245755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2888253235807091796327673 2166189926855318847245755)
            ·
              refine ⟨3249284890282978270868633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166189926855318847245755 3249284890282978270868633)
              ·
                refine ⟨2436963667712233703151475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3249284890282978270868633 2436963667712233703151475)
                ·
                  refine ⟨3655445501568350554727213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436963667712233703151475 3655445501568350554727213)
                  ·
                    refine ⟨1370792063088131458022705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655445501568350554727213 1370792063088131458022705)
                    ·
                      refine ⟨1028094047316098593517029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370792063088131458022705 1028094047316098593517029)
                      ·
                        rfl

theorem cell23_2002206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2002206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002206 prefixEnd_2002206 := by exact prefixLift 2002206
  have htrace : WordTrace (prefixWord ++ tailWord_2002206) baseStart_2002206 baseEnd_2002206 := by
    simpa [prefixWord, tailWord_2002206, baseEnd_2002206] using wordTrace_append hprefix tailTrace_2002206
  have hstable : (prefixWord ++ tailWord_2002206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002206).length < 2 ^ (prefixWord ++ tailWord_2002206).sum := by decide
  have hdescent : baseEnd_2002206 < baseStart_2002206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002238 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2002238 : Nat := 118140960795 + 2002238 * 2 ^ 59
def prefixEnd_2002238 : Nat := 4983230072969 + 3 ^ 40 * 2002238 * 2
def baseEnd_2002238 : Nat := 342703492899014156105627

theorem tailTrace_2002238 : CollatzResearch.WordTrace tailWord_2002238 prefixEnd_2002238 342703492899014156105627 := by
  unfold tailWord_2002238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9128452415030144483884921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48685079546827437247386245 9128452415030144483884921)
  ·
    refine ⟨6846339311272608362913691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9128452415030144483884921 6846339311272608362913691)
    ·
      refine ⟨10269508966908912544370537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6846339311272608362913691 10269508966908912544370537)
      ·
        refine ⟨7702131725181684408277903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10269508966908912544370537 7702131725181684408277903)
        ·
          refine ⟨11553197587772526612416855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7702131725181684408277903 11553197587772526612416855)
          ·
            refine ⟨17329796381658789918625283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11553197587772526612416855 17329796381658789918625283)
            ·
              refine ⟨25994694572488184877937925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17329796381658789918625283 25994694572488184877937925)
              ·
                refine ⟨4874005232341534664613361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25994694572488184877937925 4874005232341534664613361)
                ·
                  refine ⟨3655503924256150998460021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874005232341534664613361 3655503924256150998460021)
                  ·
                    refine ⟨342703492899014156105627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3655503924256150998460021 342703492899014156105627)
                    ·
                      rfl

theorem cell23_2002238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2002238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002238 prefixEnd_2002238 := by exact prefixLift 2002238
  have htrace : WordTrace (prefixWord ++ tailWord_2002238) baseStart_2002238 baseEnd_2002238 := by
    simpa [prefixWord, tailWord_2002238, baseEnd_2002238] using wordTrace_append hprefix tailTrace_2002238
  have hstable : (prefixWord ++ tailWord_2002238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002238).length < 2 ^ (prefixWord ++ tailWord_2002238).sum := by decide
  have hdescent : baseEnd_2002238 < baseStart_2002238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002275 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 4]
def baseStart_2002275 : Nat := 118140960795 + 2002275 * 2 ^ 59
def prefixEnd_2002275 : Nat := 4983230072969 + 3 ^ 40 * 2002275 * 2
def baseEnd_2002275 : Nat := 1028129477481258823554211

theorem tailTrace_2002275 : CollatzResearch.WordTrace tailWord_2002275 prefixEnd_2002275 1028129477481258823554211 := by
  unfold tailWord_2002275
  simp only [CollatzResearch.WordTrace]
  refine ⟨73028968821107111190176279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48685979214071407460117519 73028968821107111190176279)
  ·
    refine ⟨109543453231660666785264419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73028968821107111190176279 109543453231660666785264419)
    ·
      refine ⟨164315179847491000177896629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109543453231660666785264419 164315179847491000177896629)
      ·
        refine ⟨15404548110702281266677809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164315179847491000177896629 15404548110702281266677809)
        ·
          refine ⟨11553411083026710950008357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15404548110702281266677809 11553411083026710950008357)
          ·
            refine ⟨2166264578067508303126567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11553411083026710950008357 2166264578067508303126567)
            ·
              refine ⟨3249396867101262454689851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166264578067508303126567 3249396867101262454689851)
              ·
                refine ⟨4874095300651893682034777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249396867101262454689851 4874095300651893682034777)
                ·
                  refine ⟨3655571475488920261526083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874095300651893682034777 3655571475488920261526083)
                  ·
                    refine ⟨5483357213233380392289125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3655571475488920261526083 5483357213233380392289125)
                    ·
                      refine ⟨1028129477481258823554211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5483357213233380392289125 1028129477481258823554211)
                      ·
                        rfl

theorem cell23_2002275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_2002275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002275 prefixEnd_2002275 := by exact prefixLift 2002275
  have htrace : WordTrace (prefixWord ++ tailWord_2002275) baseStart_2002275 baseEnd_2002275 := by
    simpa [prefixWord, tailWord_2002275, baseEnd_2002275] using wordTrace_append hprefix tailTrace_2002275
  have hstable : (prefixWord ++ tailWord_2002275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002275).length < 2 ^ (prefixWord ++ tailWord_2002275).sum := by decide
  have hdescent : baseEnd_2002275 < baseStart_2002275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002301 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_2002301 : Nat := 118140960795 + 2002301 * 2 ^ 59
def prefixEnd_2002301 : Nat := 4983230072969 + 3 ^ 40 * 2002301 * 2
def baseEnd_2002301 : Nat := 1028142827978275721829091

theorem tailTrace_2002301 : CollatzResearch.WordTrace tailWord_2002301 prefixEnd_2002301 1028142827978275721829091 := by
  unfold tailWord_2002301
  simp only [CollatzResearch.WordTrace]
  refine ⟨73029917119012917630622757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48686611412675278420415171 73029917119012917630622757)
  ·
    refine ⟨13693109459814922055741767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73029917119012917630622757 13693109459814922055741767)
    ·
      refine ⟨20539664189722383083612651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13693109459814922055741767 20539664189722383083612651)
      ·
        refine ⟨30809496284583574625418977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20539664189722383083612651 30809496284583574625418977)
        ·
          refine ⟨23107122213437680969064233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30809496284583574625418977 23107122213437680969064233)
          ·
            refine ⟨17330341660078260726798175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23107122213437680969064233 17330341660078260726798175)
            ·
              refine ⟨25995512490117391090197263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17330341660078260726798175 25995512490117391090197263)
              ·
                refine ⟨38993268735176086635295895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25995512490117391090197263 38993268735176086635295895)
                ·
                  refine ⟨58489903102764129952943843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38993268735176086635295895 58489903102764129952943843)
                  ·
                    refine ⟨87734854654146194929415765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58489903102764129952943843 87734854654146194929415765)
                    ·
                      refine ⟨1028142827978275721829091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 87734854654146194929415765 1028142827978275721829091)
                      ·
                        rfl

theorem cell23_2002301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_2002301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002301 prefixEnd_2002301 := by exact prefixLift 2002301
  have htrace : WordTrace (prefixWord ++ tailWord_2002301) baseStart_2002301 baseEnd_2002301 := by
    simpa [prefixWord, tailWord_2002301, baseEnd_2002301] using wordTrace_append hprefix tailTrace_2002301
  have hstable : (prefixWord ++ tailWord_2002301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002301).length < 2 ^ (prefixWord ++ tailWord_2002301).sum := by decide
  have hdescent : baseEnd_2002301 < baseStart_2002301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002325 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_2002325 : Nat := 118140960795 + 2002325 * 2 ^ 59
def prefixEnd_2002325 : Nat := 4983230072969 + 3 ^ 40 * 2002325 * 2
def baseEnd_2002325 : Nat := 1028155151513983627928981

theorem tailTrace_2002325 : CollatzResearch.WordTrace tailWord_2002325 prefixEnd_2002325 1028155151513983627928981 := by
  unfold tailWord_2002325
  simp only [CollatzResearch.WordTrace]
  refine ⟨73030792470925969729496429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48687194980617313152997619 73030792470925969729496429)
  ·
    refine ⟨27386547176597238648561161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73030792470925969729496429 27386547176597238648561161)
    ·
      refine ⟨20539910382447928986420871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27386547176597238648561161 20539910382447928986420871)
      ·
        refine ⟨30809865573671893479631307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20539910382447928986420871 30809865573671893479631307)
        ·
          refine ⟨46214798360507840219446961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30809865573671893479631307 46214798360507840219446961)
          ·
            refine ⟨34661098770380880164585221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46214798360507840219446961 34661098770380880164585221)
            ·
              refine ⟨6498956019446415030859729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34661098770380880164585221 6498956019446415030859729)
              ·
                refine ⟨4874217014584811273144797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6498956019446415030859729 4874217014584811273144797)
                ·
                  refine ⟨1827831380469304227429299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4874217014584811273144797 1827831380469304227429299)
                  ·
                    refine ⟨2741747070703956341143949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1827831380469304227429299 2741747070703956341143949)
                    ·
                      refine ⟨1028155151513983627928981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741747070703956341143949 1028155151513983627928981)
                      ·
                        rfl

theorem cell23_2002325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_2002325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002325 prefixEnd_2002325 := by exact prefixLift 2002325
  have htrace : WordTrace (prefixWord ++ tailWord_2002325) baseStart_2002325 baseEnd_2002325 := by
    simpa [prefixWord, tailWord_2002325, baseEnd_2002325] using wordTrace_append hprefix tailTrace_2002325
  have hstable : (prefixWord ++ tailWord_2002325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002325).length < 2 ^ (prefixWord ++ tailWord_2002325).sum := by decide
  have hdescent : baseEnd_2002325 < baseStart_2002325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002335 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 1, 5, 2]
def baseStart_2002335 : Nat := 118140960795 + 2002335 * 2 ^ 59
def prefixEnd_2002335 : Nat := 4983230072969 + 3 ^ 40 * 2002335 * 2
def baseEnd_2002335 : Nat := 1028160286320528588803935

theorem tailTrace_2002335 : CollatzResearch.WordTrace tailWord_2002335 prefixEnd_2002335 1028160286320528588803935 := by
  unfold tailWord_2002335
  simp only [CollatzResearch.WordTrace]
  refine ⟨73031157200889741437360459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48687438133926494291573639 73031157200889741437360459)
  ·
    refine ⟨109546735801334612156040689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73031157200889741437360459 109546735801334612156040689)
    ·
      refine ⟨82160051851000959117030517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109546735801334612156040689 82160051851000959117030517)
      ·
        refine ⟨7702504861031339917221611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82160051851000959117030517 7702504861031339917221611)
        ·
          refine ⟨11553757291547009875832417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7702504861031339917221611 11553757291547009875832417)
          ·
            refine ⟨8665317968660257406874313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11553757291547009875832417 8665317968660257406874313)
            ·
              refine ⟨6498988476495193055155735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8665317968660257406874313 6498988476495193055155735)
              ·
                refine ⟨9748482714742789582733603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6498988476495193055155735 9748482714742789582733603)
                ·
                  refine ⟨14622724072114184374100405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748482714742789582733603 14622724072114184374100405)
                  ·
                    refine ⟨1370880381760704785071913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14622724072114184374100405 1370880381760704785071913)
                    ·
                      refine ⟨1028160286320528588803935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370880381760704785071913 1028160286320528588803935)
                      ·
                        rfl

theorem cell23_2002335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_2002335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002335 prefixEnd_2002335 := by exact prefixLift 2002335
  have htrace : WordTrace (prefixWord ++ tailWord_2002335) baseStart_2002335 baseEnd_2002335 := by
    simpa [prefixWord, tailWord_2002335, baseEnd_2002335] using wordTrace_append hprefix tailTrace_2002335
  have hstable : (prefixWord ++ tailWord_2002335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002335).length < 2 ^ (prefixWord ++ tailWord_2002335).sum := by decide
  have hdescent : baseEnd_2002335 < baseStart_2002335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002359 : List Nat := [1, 1, 3, 1, 3, 2, 5, 2, 1, 1, 3]
def baseStart_2002359 : Nat := 118140960795 + 2002359 * 2 ^ 59
def prefixEnd_2002359 : Nat := 4983230072969 + 3 ^ 40 * 2002359 * 2
def baseEnd_2002359 : Nat := 1028172609856236494903825

theorem tailTrace_2002359 : CollatzResearch.WordTrace tailWord_2002359 prefixEnd_2002359 1028172609856236494903825 := by
  unfold tailWord_2002359
  simp only [CollatzResearch.WordTrace]
  refine ⟨73032032552802793536234131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48688021701868529024156087 73032032552802793536234131)
  ·
    refine ⟨109548048829204190304351197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73032032552802793536234131 109548048829204190304351197)
    ·
      refine ⟨41080518310951571364131699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109548048829204190304351197 41080518310951571364131699)
      ·
        refine ⟨61620777466427357046197549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41080518310951571364131699 61620777466427357046197549)
        ·
          refine ⟨23107791549910258892324081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61620777466427357046197549 23107791549910258892324081)
          ·
            refine ⟨17330843662432694169243061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23107791549910258892324081 17330843662432694169243061)
            ·
              refine ⟨1624766593353065078366537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17330843662432694169243061 1624766593353065078366537)
              ·
                refine ⟨1218574945014798808774903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624766593353065078366537 1218574945014798808774903)
                ·
                  refine ⟨1827862417522198213162355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218574945014798808774903 1827862417522198213162355)
                  ·
                    refine ⟨2741793626283297319743533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1827862417522198213162355 2741793626283297319743533)
                    ·
                      refine ⟨1028172609856236494903825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741793626283297319743533 1028172609856236494903825)
                      ·
                        rfl

theorem cell23_2002359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_2002359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002359 prefixEnd_2002359 := by exact prefixLift 2002359
  have htrace : WordTrace (prefixWord ++ tailWord_2002359) baseStart_2002359 baseEnd_2002359 := by
    simpa [prefixWord, tailWord_2002359, baseEnd_2002359] using wordTrace_append hprefix tailTrace_2002359
  have hstable : (prefixWord ++ tailWord_2002359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002359).length < 2 ^ (prefixWord ++ tailWord_2002359).sum := by decide
  have hdescent : baseEnd_2002359 < baseStart_2002359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002368 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_2002368 : Nat := 118140960795 + 2002368 * 2 ^ 59
def prefixEnd_2002368 : Nat := 4983230072969 + 3 ^ 40 * 2002368 * 2
def baseEnd_2002368 : Nat := 1028177231182126959691283

theorem tailTrace_2002368 : CollatzResearch.WordTrace tailWord_2002368 prefixEnd_2002368 1028177231182126959691283 := by
  unfold tailWord_2002368
  simp only [CollatzResearch.WordTrace]
  refine ⟨36516180404885094036655879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48688240539846792048874505 36516180404885094036655879)
  ·
    refine ⟨54774270607327641054983819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36516180404885094036655879 54774270607327641054983819)
    ·
      refine ⟨82161405910991461582475729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54774270607327641054983819 82161405910991461582475729)
      ·
        refine ⟨61621054433243596186856797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82161405910991461582475729 61621054433243596186856797)
        ·
          refine ⟨23107895412466348570071299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61621054433243596186856797 23107895412466348570071299)
          ·
            refine ⟨34661843118699522855106949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23107895412466348570071299 34661843118699522855106949)
            ·
              refine ⟨6499095584756160535332553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34661843118699522855106949 6499095584756160535332553)
              ·
                refine ⟨4874321688567120401499415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6499095584756160535332553 4874321688567120401499415)
                ·
                  refine ⟨7311482532850680602249123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874321688567120401499415 7311482532850680602249123)
                  ·
                    refine ⟨10967223799276020903373685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7311482532850680602249123 10967223799276020903373685)
                    ·
                      refine ⟨1028177231182126959691283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10967223799276020903373685 1028177231182126959691283)
                      ·
                        rfl

theorem cell23_2002368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_2002368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002368 prefixEnd_2002368 := by exact prefixLift 2002368
  have htrace : WordTrace (prefixWord ++ tailWord_2002368) baseStart_2002368 baseEnd_2002368 := by
    simpa [prefixWord, tailWord_2002368, baseEnd_2002368] using wordTrace_append hprefix tailTrace_2002368
  have hstable : (prefixWord ++ tailWord_2002368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002368).length < 2 ^ (prefixWord ++ tailWord_2002368).sum := by decide
  have hdescent : baseEnd_2002368 < baseStart_2002368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002371 : List Nat := [1, 1, 1, 3, 1, 1, 5, 10]
def baseStart_2002371 : Nat := 118140960795 + 2002371 * 2 ^ 59
def prefixEnd_2002371 : Nat := 4983230072969 + 3 ^ 40 * 2002371 * 2
def baseEnd_2002371 : Nat := 38080695245336683257547

theorem tailTrace_2002371 : CollatzResearch.WordTrace tailWord_2002371 prefixEnd_2002371 38080695245336683257547 := by
  unfold tailWord_2002371
  simp only [CollatzResearch.WordTrace]
  refine ⟨73032470228759319585670967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48688313485839546390447311 73032470228759319585670967)
  ·
    refine ⟨109548705343138979378506451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73032470228759319585670967 109548705343138979378506451)
    ·
      refine ⟨164323058014708469067759677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109548705343138979378506451 164323058014708469067759677)
      ·
        refine ⟨61621146755515675900409879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164323058014708469067759677 61621146755515675900409879)
        ·
          refine ⟨92431720133273513850614819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61621146755515675900409879 92431720133273513850614819)
          ·
            refine ⟨138647580199910270775922229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92431720133273513850614819 138647580199910270775922229)
            ·
              refine ⟨12998210643741587885242709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138647580199910270775922229 12998210643741587885242709)
              ·
                refine ⟨38080695245336683257547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12998210643741587885242709 38080695245336683257547)
                ·
                  rfl

theorem cell23_2002371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 10].length) (baseStart_2002371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002371 prefixEnd_2002371 := by exact prefixLift 2002371
  have htrace : WordTrace (prefixWord ++ tailWord_2002371) baseStart_2002371 baseEnd_2002371 := by
    simpa [prefixWord, tailWord_2002371, baseEnd_2002371] using wordTrace_append hprefix tailTrace_2002371
  have hstable : (prefixWord ++ tailWord_2002371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002371).length < 2 ^ (prefixWord ++ tailWord_2002371).sum := by decide
  have hdescent : baseEnd_2002371 < baseStart_2002371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002375 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 2, 4]
def baseStart_2002375 : Nat := 118140960795 + 2002375 * 2 ^ 59
def prefixEnd_2002375 : Nat := 4983230072969 + 3 ^ 40 * 2002375 * 2
def baseEnd_2002375 : Nat := 342726941848902810767917

theorem tailTrace_2002375 : CollatzResearch.WordTrace tailWord_2002375 prefixEnd_2002375 342726941848902810767917 := by
  unfold tailWord_2002375
  simp only [CollatzResearch.WordTrace]
  refine ⟨73032616120744828268816579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48688410747163218845877719 73032616120744828268816579)
  ·
    refine ⟨109548924181117242403224869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73032616120744828268816579 109548924181117242403224869)
    ·
      refine ⟨20540423283959482950604663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109548924181117242403224869 20540423283959482950604663)
      ·
        refine ⟨30810634925939224425906995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20540423283959482950604663 30810634925939224425906995)
        ·
          refine ⟨46215952388908836638860493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30810634925939224425906995 46215952388908836638860493)
          ·
            refine ⟨17330982145840813739572685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46215952388908836638860493 17330982145840813739572685)
            ·
              refine ⟨6499118304690305152339757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17330982145840813739572685 6499118304690305152339757)
              ·
                refine ⟨2437169364258864432127409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6499118304690305152339757 2437169364258864432127409)
                ·
                  refine ⟨1827877023194148324095557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437169364258864432127409 1827877023194148324095557)
                  ·
                    refine ⟨342726941848902810767917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1827877023194148324095557 342726941848902810767917)
                    ·
                      rfl

theorem cell23_2002375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_2002375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002375 prefixEnd_2002375 := by exact prefixLift 2002375
  have htrace : WordTrace (prefixWord ++ tailWord_2002375) baseStart_2002375 baseEnd_2002375 := by
    simpa [prefixWord, tailWord_2002375, baseEnd_2002375] using wordTrace_append hprefix tailTrace_2002375
  have hstable : (prefixWord ++ tailWord_2002375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002375).length < 2 ^ (prefixWord ++ tailWord_2002375).sum := by decide
  have hdescent : baseEnd_2002375 < baseStart_2002375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002378 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2002378 : Nat := 118140960795 + 2002378 * 2 ^ 59
def prefixEnd_2002378 : Nat := 4983230072969 + 3 ^ 40 * 2002378 * 2
def baseEnd_2002378 : Nat := 1028182365988671920566237

theorem tailTrace_2002378 : CollatzResearch.WordTrace tailWord_2002378 prefixEnd_2002378 1028182365988671920566237 := by
  unfold tailWord_2002378
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258181384933489945293947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48688483693155973187450525 18258181384933489945293947)
  ·
    refine ⟨27387272077400234917940921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18258181384933489945293947 27387272077400234917940921)
    ·
      refine ⟨20540454058050176188455691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27387272077400234917940921 20540454058050176188455691)
      ·
        refine ⟨30810681087075264282683537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20540454058050176188455691 30810681087075264282683537)
        ·
          refine ⟨23108010815306448212012653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30810681087075264282683537 23108010815306448212012653)
          ·
            refine ⟨8665504055739918079504745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23108010815306448212012653 8665504055739918079504745)
            ·
              refine ⟨6499128041804938559628559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8665504055739918079504745 6499128041804938559628559)
              ·
                refine ⟨9748692062707407839442839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499128041804938559628559 9748692062707407839442839)
                ·
                  refine ⟨14623038094061111759164259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748692062707407839442839 14623038094061111759164259)
                  ·
                    refine ⟨21934557141091667638746389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14623038094061111759164259 21934557141091667638746389)
                    ·
                      refine ⟨1028182365988671920566237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21934557141091667638746389 1028182365988671920566237)
                      ·
                        rfl

theorem cell23_2002378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2002378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002378 prefixEnd_2002378 := by exact prefixLift 2002378
  have htrace : WordTrace (prefixWord ++ tailWord_2002378) baseStart_2002378 baseEnd_2002378 := by
    simpa [prefixWord, tailWord_2002378, baseEnd_2002378] using wordTrace_append hprefix tailTrace_2002378
  have hstable : (prefixWord ++ tailWord_2002378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002378).length < 2 ^ (prefixWord ++ tailWord_2002378).sum := by decide
  have hdescent : baseEnd_2002378 < baseStart_2002378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002382 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_2002382 : Nat := 118140960795 + 2002382 * 2 ^ 59
def prefixEnd_2002382 : Nat := 4983230072969 + 3 ^ 40 * 2002382 * 2
def baseEnd_2002382 : Nat := 1028184419911289904916219

theorem tailTrace_2002382 : CollatzResearch.WordTrace tailWord_2002382 prefixEnd_2002382 1028184419911289904916219 := by
  unfold tailWord_2002382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129108928964933558040175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48688580954479645642880933 9129108928964933558040175)
  ·
    refine ⟨13693663393447400337060263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9129108928964933558040175 13693663393447400337060263)
    ·
      refine ⟨20540495090171100505590395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13693663393447400337060263 20540495090171100505590395)
      ·
        refine ⟨30810742635256650758385593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20540495090171100505590395 30810742635256650758385593)
        ·
          refine ⟨23108056976442488068789195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30810742635256650758385593 23108056976442488068789195)
          ·
            refine ⟨34662085464663732103183793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23108056976442488068789195 34662085464663732103183793)
            ·
              refine ⟨25996564098497799077387845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34662085464663732103183793 25996564098497799077387845)
              ·
                refine ⟨4874355768468337327010221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25996564098497799077387845 4874355768468337327010221)
                ·
                  refine ⟨1827883413175626497628833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4874355768468337327010221 1827883413175626497628833)
                  ·
                    refine ⟨1370912559881719873221625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827883413175626497628833 1370912559881719873221625)
                    ·
                      refine ⟨1028184419911289904916219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370912559881719873221625 1028184419911289904916219)
                      ·
                        rfl

theorem cell23_2002382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_2002382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002382 prefixEnd_2002382 := by exact prefixLift 2002382
  have htrace : WordTrace (prefixWord ++ tailWord_2002382) baseStart_2002382 baseEnd_2002382 := by
    simpa [prefixWord, tailWord_2002382, baseEnd_2002382] using wordTrace_append hprefix tailTrace_2002382
  have hstable : (prefixWord ++ tailWord_2002382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002382).length < 2 ^ (prefixWord ++ tailWord_2002382).sum := by decide
  have hdescent : baseEnd_2002382 < baseStart_2002382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002399 : List Nat := [1, 1, 2, 3, 3, 1, 2, 5, 1, 2, 2]
def baseStart_2002399 : Nat := 118140960795 + 2002399 * 2 ^ 59
def prefixEnd_2002399 : Nat := 4983230072969 + 3 ^ 40 * 2002399 * 2
def baseEnd_2002399 : Nat := 1028193149082416338403641

theorem tailTrace_2002399 : CollatzResearch.WordTrace tailWord_2002399 prefixEnd_2002399 1028193149082416338403641 := by
  unfold tailWord_2002399
  simp only [CollatzResearch.WordTrace]
  refine ⟨73033491472657880367690251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48688994315105253578460167 73033491472657880367690251)
  ·
    refine ⟨109550237208986820551535377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73033491472657880367690251 109550237208986820551535377)
    ·
      refine ⟨82162677906740115413651533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109550237208986820551535377 82162677906740115413651533)
      ·
        refine ⟨30811004215027543280119325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82162677906740115413651533 30811004215027543280119325)
        ·
          refine ⟨11554126580635328730044747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30811004215027543280119325 11554126580635328730044747)
          ·
            refine ⟨17331189870952993095067121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11554126580635328730044747 17331189870952993095067121)
            ·
              refine ⟨12998392403214744821300341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17331189870952993095067121 12998392403214744821300341)
              ·
                refine ⟨1218599287801382326996907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12998392403214744821300341 1218599287801382326996907)
                ·
                  refine ⟨1827898931702073490495361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218599287801382326996907 1827898931702073490495361)
                  ·
                    refine ⟨1370924198776555117871521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827898931702073490495361 1370924198776555117871521)
                    ·
                      refine ⟨1028193149082416338403641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370924198776555117871521 1028193149082416338403641)
                      ·
                        rfl

theorem cell23_2002399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_2002399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002399 prefixEnd_2002399 := by exact prefixLift 2002399
  have htrace : WordTrace (prefixWord ++ tailWord_2002399) baseStart_2002399 baseEnd_2002399 := by
    simpa [prefixWord, tailWord_2002399, baseEnd_2002399] using wordTrace_append hprefix tailTrace_2002399
  have hstable : (prefixWord ++ tailWord_2002399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002399).length < 2 ^ (prefixWord ++ tailWord_2002399).sum := by decide
  have hdescent : baseEnd_2002399 < baseStart_2002399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002415 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 3]
def baseStart_2002415 : Nat := 118140960795 + 2002415 * 2 ^ 59
def prefixEnd_2002415 : Nat := 4983230072969 + 3 ^ 40 * 2002415 * 2
def baseEnd_2002415 : Nat := 1028201364772888275803567

theorem tailTrace_2002415 : CollatzResearch.WordTrace tailWord_2002415 prefixEnd_2002415 1028201364772888275803567 := by
  unfold tailWord_2002415
  simp only [CollatzResearch.WordTrace]
  refine ⟨73034075040599915100272699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48689383360399943400181799 73034075040599915100272699)
  ·
    refine ⟨109551112560899872650409049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73034075040599915100272699 109551112560899872650409049)
    ·
      refine ⟨82163334420674904487806787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109551112560899872650409049 82163334420674904487806787)
      ·
        refine ⟨123245001631012356731710181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82163334420674904487806787 123245001631012356731710181)
        ·
          refine ⟨23108437805814816887195659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123245001631012356731710181 23108437805814816887195659)
          ·
            refine ⟨34662656708722225330793489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23108437805814816887195659 34662656708722225330793489)
            ·
              refine ⟨25996992531541668998095117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34662656708722225330793489 25996992531541668998095117)
              ·
                refine ⟨9748872199328125874285669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25996992531541668998095117 9748872199328125874285669)
                ·
                  refine ⟨1827913537374023601428563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9748872199328125874285669 1827913537374023601428563)
                  ·
                    refine ⟨2741870306061035402142845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1827913537374023601428563 2741870306061035402142845)
                    ·
                      refine ⟨1028201364772888275803567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2741870306061035402142845 1028201364772888275803567)
                      ·
                        rfl

theorem cell23_2002415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 3].length) (baseStart_2002415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002415 prefixEnd_2002415 := by exact prefixLift 2002415
  have htrace : WordTrace (prefixWord ++ tailWord_2002415) baseStart_2002415 baseEnd_2002415 := by
    simpa [prefixWord, tailWord_2002415, baseEnd_2002415] using wordTrace_append hprefix tailTrace_2002415
  have hstable : (prefixWord ++ tailWord_2002415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002415).length < 2 ^ (prefixWord ++ tailWord_2002415).sum := by decide
  have hdescent : baseEnd_2002415 < baseStart_2002415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002416 : List Nat := [2, 1, 1, 1, 3, 4, 4, 2, 1, 2, 2]
def baseStart_2002416 : Nat := 118140960795 + 2002416 * 2 ^ 59
def prefixEnd_2002416 : Nat := 4983230072969 + 3 ^ 40 * 2002416 * 2
def baseEnd_2002416 : Nat := 1028201878253542771891063

theorem tailTrace_2002416 : CollatzResearch.WordTrace tailWord_2002416 prefixEnd_2002416 1028201878253542771891063 := by
  unfold tailWord_2002416
  simp only [CollatzResearch.WordTrace]
  refine ⟨36517055756798146135529551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48689407675730861514039401 36517055756798146135529551)
  ·
    refine ⟨54775583635197219203294327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36517055756798146135529551 54775583635197219203294327)
    ·
      refine ⟨82163375452795828804941491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54775583635197219203294327 82163375452795828804941491)
      ·
        refine ⟨123245063179193743207412237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82163375452795828804941491 123245063179193743207412237)
        ·
          refine ⟨46216898692197653702779589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123245063179193743207412237 46216898692197653702779589)
          ·
            refine ⟨8665668504787060069271173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46216898692197653702779589 8665668504787060069271173)
            ·
              refine ⟨1624812844647573762988345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8665668504787060069271173 1624812844647573762988345)
              ·
                refine ⟨1218609633485680322241259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624812844647573762988345 1218609633485680322241259)
                ·
                  refine ⟨1827914450228520483361889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218609633485680322241259 1827914450228520483361889)
                  ·
                    refine ⟨1370935837671390362521417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827914450228520483361889 1370935837671390362521417)
                    ·
                      refine ⟨1028201878253542771891063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370935837671390362521417 1028201878253542771891063)
                      ·
                        rfl

theorem cell23_2002416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 1, 2, 2].length) (baseStart_2002416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002416 prefixEnd_2002416 := by exact prefixLift 2002416
  have htrace : WordTrace (prefixWord ++ tailWord_2002416) baseStart_2002416 baseEnd_2002416 := by
    simpa [prefixWord, tailWord_2002416, baseEnd_2002416] using wordTrace_append hprefix tailTrace_2002416
  have hstable : (prefixWord ++ tailWord_2002416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002416).length < 2 ^ (prefixWord ++ tailWord_2002416).sum := by decide
  have hdescent : baseEnd_2002416 < baseStart_2002416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002442 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_2002442 : Nat := 118140960795 + 2002442 * 2 ^ 59
def prefixEnd_2002442 : Nat := 4983230072969 + 3 ^ 40 * 2002442 * 2
def baseEnd_2002442 : Nat := 1028215228750559670165943

theorem tailTrace_2002442 : CollatzResearch.WordTrace tailWord_2002442 prefixEnd_2002442 1028215228750559670165943 := by
  unfold tailWord_2002442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258764952875524677876395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48690039874334732474337053 18258764952875524677876395)
  ·
    refine ⟨27388147429313287016814593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18258764952875524677876395 27388147429313287016814593)
    ·
      refine ⟨20541110571984965262610945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27388147429313287016814593 20541110571984965262610945)
      ·
        refine ⟨15405832928988723946958209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20541110571984965262610945 15405832928988723946958209)
        ·
          refine ⟨11554374696741542960218657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15405832928988723946958209 11554374696741542960218657)
          ·
            refine ⟨8665781022556157220163993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11554374696741542960218657 8665781022556157220163993)
            ·
              refine ⟨6499335766917117915122995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8665781022556157220163993 6499335766917117915122995)
              ·
                refine ⟨9749003650375676872684493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499335766917117915122995 9749003650375676872684493)
                ·
                  refine ⟨3655876368890878827256685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9749003650375676872684493 3655876368890878827256685)
                  ·
                    refine ⟨1370953638334079560221257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3655876368890878827256685 1370953638334079560221257)
                    ·
                      refine ⟨1028215228750559670165943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370953638334079560221257 1028215228750559670165943)
                      ·
                        rfl

theorem cell23_2002442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_2002442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002442 prefixEnd_2002442 := by exact prefixLift 2002442
  have htrace : WordTrace (prefixWord ++ tailWord_2002442) baseStart_2002442 baseEnd_2002442 := by
    simpa [prefixWord, tailWord_2002442, baseEnd_2002442] using wordTrace_append hprefix tailTrace_2002442
  have hstable : (prefixWord ++ tailWord_2002442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002442).length < 2 ^ (prefixWord ++ tailWord_2002442).sum := by decide
  have hdescent : baseEnd_2002442 < baseStart_2002442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002458 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2002458 : Nat := 118140960795 + 2002458 * 2 ^ 59
def prefixEnd_2002458 : Nat := 4983230072969 + 3 ^ 40 * 2002458 * 2
def baseEnd_2002458 : Nat := 1028223444441031607565869

theorem tailTrace_2002458 : CollatzResearch.WordTrace tailWord_2002458 prefixEnd_2002458 1028223444441031607565869 := by
  unfold tailWord_2002458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258910844861033361022007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48690428919629422296058685 18258910844861033361022007)
  ·
    refine ⟨27388366267291550041533011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18258910844861033361022007 27388366267291550041533011)
    ·
      refine ⟨41082549400937325062299517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27388366267291550041533011 41082549400937325062299517)
      ·
        refine ⟨15405956025351496898362319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41082549400937325062299517 15405956025351496898362319)
        ·
          refine ⟨23108934038027245347543479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15405956025351496898362319 23108934038027245347543479)
          ·
            refine ⟨34663401057040868021315219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23108934038027245347543479 34663401057040868021315219)
            ·
              refine ⟨51995101585561302031972829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34663401057040868021315219 51995101585561302031972829)
              ·
                refine ⟨19498163094585488261989811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51995101585561302031972829 19498163094585488261989811)
                ·
                  refine ⟨29247244641878232392984717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19498163094585488261989811 29247244641878232392984717)
                  ·
                    refine ⟨10967716740704337147369269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29247244641878232392984717 10967716740704337147369269)
                    ·
                      refine ⟨1028223444441031607565869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10967716740704337147369269 1028223444441031607565869)
                      ·
                        rfl

theorem cell23_2002458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2002458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002458 prefixEnd_2002458 := by exact prefixLift 2002458
  have htrace : WordTrace (prefixWord ++ tailWord_2002458) baseStart_2002458 baseEnd_2002458 := by
    simpa [prefixWord, tailWord_2002458, baseEnd_2002458] using wordTrace_append hprefix tailTrace_2002458
  have hstable : (prefixWord ++ tailWord_2002458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002458).length < 2 ^ (prefixWord ++ tailWord_2002458).sum := by decide
  have hdescent : baseEnd_2002458 < baseStart_2002458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002485 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_2002485 : Nat := 118140960795 + 2002485 * 2 ^ 59
def prefixEnd_2002485 : Nat := 4983230072969 + 3 ^ 40 * 2002485 * 2
def baseEnd_2002485 : Nat := 1028237308418703001928245

theorem tailTrace_2002485 : CollatzResearch.WordTrace tailWord_2002485 prefixEnd_2002485 1028237308418703001928245 := by
  unfold tailWord_2002485
  simp only [CollatzResearch.WordTrace]
  refine ⟨73036628150346317055320909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48691085433564211370213939 73036628150346317055320909)
  ·
    refine ⟨27388735556379868895745341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73036628150346317055320909 27388735556379868895745341)
    ·
      refine ⟨10270775833642450835904503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27388735556379868895745341 10270775833642450835904503)
      ·
        refine ⟨15406163750463676253856755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10270775833642450835904503 15406163750463676253856755)
        ·
          refine ⟨23109245625695514380785133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15406163750463676253856755 23109245625695514380785133)
          ·
            refine ⟨8665967109635817892794425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23109245625695514380785133 8665967109635817892794425)
            ·
              refine ⟨6499475332226863419595819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8665967109635817892794425 6499475332226863419595819)
              ·
                refine ⟨9749212998340295129393729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499475332226863419595819 9749212998340295129393729)
                ·
                  refine ⟨7311909748755221347045297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9749212998340295129393729 7311909748755221347045297)
                  ·
                    refine ⟨5483932311566416010283973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7311909748755221347045297 5483932311566416010283973)
                    ·
                      refine ⟨1028237308418703001928245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5483932311566416010283973 1028237308418703001928245)
                      ·
                        rfl

theorem cell23_2002485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_2002485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002485 prefixEnd_2002485 := by exact prefixLift 2002485
  have htrace : WordTrace (prefixWord ++ tailWord_2002485) baseStart_2002485 baseEnd_2002485 := by
    simpa [prefixWord, tailWord_2002485, baseEnd_2002485] using wordTrace_append hprefix tailTrace_2002485
  have hstable : (prefixWord ++ tailWord_2002485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002485).length < 2 ^ (prefixWord ++ tailWord_2002485).sum := by decide
  have hdescent : baseEnd_2002485 < baseStart_2002485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002489 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 1, 4, 2]
def baseStart_2002489 : Nat := 118140960795 + 2002489 * 2 ^ 59
def prefixEnd_2002489 : Nat := 4983230072969 + 3 ^ 40 * 2002489 * 2
def baseEnd_2002489 : Nat := 1028239362341320986278227

theorem tailTrace_2002489 : CollatzResearch.WordTrace tailWord_2002489 prefixEnd_2002489 1028239362341320986278227 := by
  unfold tailWord_2002489
  simp only [CollatzResearch.WordTrace]
  refine ⟨73036774042331825738466521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48691182694887883825644347 73036774042331825738466521)
  ·
    refine ⟨54777580531748869303849891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73036774042331825738466521 54777580531748869303849891)
    ·
      refine ⟨82166370797623303955774837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54777580531748869303849891 82166370797623303955774837)
      ·
        refine ⟨7703097262277184745853891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82166370797623303955774837 7703097262277184745853891)
        ·
          refine ⟨11554645893415777118780837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703097262277184745853891 11554645893415777118780837)
          ·
            refine ⟨2166496105015458209771407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11554645893415777118780837 2166496105015458209771407)
            ·
              refine ⟨3249744157523187314657111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166496105015458209771407 3249744157523187314657111)
              ·
                refine ⟨4874616236284780971985667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249744157523187314657111 4874616236284780971985667)
                ·
                  refine ⟨7311924354427171457978501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874616236284780971985667 7311924354427171457978501)
                  ·
                    refine ⟨1370985816455094648370969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7311924354427171457978501 1370985816455094648370969)
                    ·
                      refine ⟨1028239362341320986278227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1370985816455094648370969 1028239362341320986278227)
                      ·
                        rfl

theorem cell23_2002489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_2002489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002489 prefixEnd_2002489 := by exact prefixLift 2002489
  have htrace : WordTrace (prefixWord ++ tailWord_2002489) baseStart_2002489 baseEnd_2002489 := by
    simpa [prefixWord, tailWord_2002489, baseEnd_2002489] using wordTrace_append hprefix tailTrace_2002489
  have hstable : (prefixWord ++ tailWord_2002489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002489).length < 2 ^ (prefixWord ++ tailWord_2002489).sum := by decide
  have hdescent : baseEnd_2002489 < baseStart_2002489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002515 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 6, 5, 2]
def baseStart_2002515 : Nat := 118140960795 + 2002515 * 2 ^ 59
def prefixEnd_2002515 : Nat := 4983230072969 + 3 ^ 40 * 2002515 * 2
def baseEnd_2002515 : Nat := 1028252712838337884553107

theorem tailTrace_2002515 : CollatzResearch.WordTrace tailWord_2002515 prefixEnd_2002515 1028252712838337884553107 := by
  unfold tailWord_2002515
  simp only [CollatzResearch.WordTrace]
  refine ⟨73037722340237632178912999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48691814893491754785941999 73037722340237632178912999)
  ·
    refine ⟨109556583510356448268369499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73037722340237632178912999 109556583510356448268369499)
    ·
      refine ⟨164334875265534672402554249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109556583510356448268369499 164334875265534672402554249)
      ·
        refine ⟨123251156449151004301915687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164334875265534672402554249 123251156449151004301915687)
        ·
          refine ⟨184876734673726506452873531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123251156449151004301915687 184876734673726506452873531)
          ·
            refine ⟨277315102010589759679310297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184876734673726506452873531 277315102010589759679310297)
            ·
              refine ⟨207986326507942319759482723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277315102010589759679310297 207986326507942319759482723)
              ·
                refine ⟨311979489761913479639224085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 207986326507942319759482723 311979489761913479639224085)
                ·
                  refine ⟨14624038582589694358088629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 311979489761913479639224085 14624038582589694358088629)
                  ·
                    refine ⟨1371003617117783846070809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14624038582589694358088629 1371003617117783846070809)
                    ·
                      refine ⟨1028252712838337884553107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371003617117783846070809 1028252712838337884553107)
                      ·
                        rfl

theorem cell23_2002515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 5, 2].length) (baseStart_2002515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002515 prefixEnd_2002515 := by exact prefixLift 2002515
  have htrace : WordTrace (prefixWord ++ tailWord_2002515) baseStart_2002515 baseEnd_2002515 := by
    simpa [prefixWord, tailWord_2002515, baseEnd_2002515] using wordTrace_append hprefix tailTrace_2002515
  have hstable : (prefixWord ++ tailWord_2002515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002515).length < 2 ^ (prefixWord ++ tailWord_2002515).sum := by decide
  have hdescent : baseEnd_2002515 < baseStart_2002515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002555 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 5, 4]
def baseStart_2002555 : Nat := 118140960795 + 2002555 * 2 ^ 59
def prefixEnd_2002555 : Nat := 4983230072969 + 3 ^ 40 * 2002555 * 2
def baseEnd_2002555 : Nat := 342757750688172576017641

theorem tailTrace_2002555 : CollatzResearch.WordTrace tailWord_2002555 prefixEnd_2002555 342757750688172576017641 := by
  unfold tailWord_2002555
  simp only [CollatzResearch.WordTrace]
  refine ⟨73039181260092719010369119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48692787506728479340246079 73039181260092719010369119)
  ·
    refine ⟨109558771890139078515553679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73039181260092719010369119 109558771890139078515553679)
    ·
      refine ⟨164338157835208617773330519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109558771890139078515553679 164338157835208617773330519)
      ·
        refine ⟨246507236752812926659995779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164338157835208617773330519 246507236752812926659995779)
        ·
          refine ⟨369760855129219389989993669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246507236752812926659995779 369760855129219389989993669)
          ·
            refine ⟨69330160336728635623123813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369760855129219389989993669 69330160336728635623123813)
            ·
              refine ⟨12999405063136619179335715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69330160336728635623123813 12999405063136619179335715)
              ·
                refine ⟨19499107594704928769003573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12999405063136619179335715 19499107594704928769003573)
                ·
                  refine ⟨1828041337003587072094085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19499107594704928769003573 1828041337003587072094085)
                  ·
                    refine ⟨342757750688172576017641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1828041337003587072094085 342757750688172576017641)
                    ·
                      rfl

theorem cell23_2002555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 4].length) (baseStart_2002555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002555 prefixEnd_2002555 := by exact prefixLift 2002555
  have htrace : WordTrace (prefixWord ++ tailWord_2002555) baseStart_2002555 baseEnd_2002555 := by
    simpa [prefixWord, tailWord_2002555, baseEnd_2002555] using wordTrace_append hprefix tailTrace_2002555
  have hstable : (prefixWord ++ tailWord_2002555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002555).length < 2 ^ (prefixWord ++ tailWord_2002555).sum := by decide
  have hdescent : baseEnd_2002555 < baseStart_2002555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002606 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2002606 : Nat := 118140960795 + 2002606 * 2 ^ 59
def prefixEnd_2002606 : Nat := 4983230072969 + 3 ^ 40 * 2002606 * 2
def baseEnd_2002606 : Nat := 342766479859299009505063

theorem tailTrace_2002606 : CollatzResearch.WordTrace tailWord_2002606 prefixEnd_2002606 342766479859299009505063 := by
  unfold tailWord_2002606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9130130172863494340059459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48694027588605303146983781 9130130172863494340059459)
  ·
    refine ⟨13695195259295241510089189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9130130172863494340059459 13695195259295241510089189)
    ·
      refine ⟨2567849111117857783141723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13695195259295241510089189 2567849111117857783141723)
      ·
        refine ⟨3851773666676786674712585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567849111117857783141723 3851773666676786674712585)
        ·
          refine ⟨2888830250007590006034439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3851773666676786674712585 2888830250007590006034439)
          ·
            refine ⟨4333245375011385009051659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888830250007590006034439 4333245375011385009051659)
            ·
              refine ⟨6499868062517077513577489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333245375011385009051659 6499868062517077513577489)
              ·
                refine ⟨4874901046887808135183117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6499868062517077513577489 4874901046887808135183117)
                ·
                  refine ⟨1828087892582928050693669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4874901046887808135183117 1828087892582928050693669)
                  ·
                    refine ⟨342766479859299009505063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1828087892582928050693669 342766479859299009505063)
                    ·
                      rfl

theorem cell23_2002606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2002606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002606 prefixEnd_2002606 := by exact prefixLift 2002606
  have htrace : WordTrace (prefixWord ++ tailWord_2002606) baseStart_2002606 baseEnd_2002606 := by
    simpa [prefixWord, tailWord_2002606, baseEnd_2002606] using wordTrace_append hprefix tailTrace_2002606
  have hstable : (prefixWord ++ tailWord_2002606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002606).length < 2 ^ (prefixWord ++ tailWord_2002606).sum := by decide
  have hdescent : baseEnd_2002606 < baseStart_2002606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002632 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 1, 5]
def baseStart_2002632 : Nat := 118140960795 + 2002632 * 2 ^ 59
def prefixEnd_2002632 : Nat := 4983230072969 + 3 ^ 40 * 2002632 * 2
def baseEnd_2002632 : Nat := 342770930024971308930023

theorem tailTrace_2002632 : CollatzResearch.WordTrace tailWord_2002632 prefixEnd_2002632 342770930024971308930023 := by
  unfold tailWord_2002632
  simp only [CollatzResearch.WordTrace]
  refine ⟨36520994840406880580461075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48694659787209174107281433 36520994840406880580461075)
  ·
    refine ⟨54781492260610320870691613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36520994840406880580461075 54781492260610320870691613)
    ·
      refine ⟨20543059597728870326509355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54781492260610320870691613 20543059597728870326509355)
      ·
        refine ⟨30814589396593305489764033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20543059597728870326509355 30814589396593305489764033)
        ·
          refine ⟨23110942047444979117323025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30814589396593305489764033 23110942047444979117323025)
          ·
            refine ⟨17333206535583734337992269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23110942047444979117323025 17333206535583734337992269)
            ·
              refine ⟨6499952450843900376747101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17333206535583734337992269 6499952450843900376747101)
              ·
                refine ⟨2437482169066462641280163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6499952450843900376747101 2437482169066462641280163)
                ·
                  refine ⟨3656223253599693961920245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437482169066462641280163 3656223253599693961920245)
                  ·
                    refine ⟨342770930024971308930023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3656223253599693961920245 342770930024971308930023)
                    ·
                      rfl

theorem cell23_2002632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_2002632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002632 prefixEnd_2002632 := by exact prefixLift 2002632
  have htrace : WordTrace (prefixWord ++ tailWord_2002632) baseStart_2002632 baseEnd_2002632 := by
    simpa [prefixWord, tailWord_2002632, baseEnd_2002632] using wordTrace_append hprefix tailTrace_2002632
  have hstable : (prefixWord ++ tailWord_2002632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002632).length < 2 ^ (prefixWord ++ tailWord_2002632).sum := by decide
  have hdescent : baseEnd_2002632 < baseStart_2002632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002636 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 6]
def baseStart_2002636 : Nat := 118140960795 + 2002636 * 2 ^ 59
def prefixEnd_2002636 : Nat := 4983230072969 + 3 ^ 40 * 2002636 * 2
def baseEnd_2002636 : Nat := 114257204888614656793339

theorem tailTrace_2002636 : CollatzResearch.WordTrace tailWord_2002636 prefixEnd_2002636 114257204888614656793339 := by
  unfold tailWord_2002636
  simp only [CollatzResearch.WordTrace]
  refine ⟨36521067786399634922033881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48694757048532846562711841 36521067786399634922033881)
  ·
    refine ⟨27390800839799726191525411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36521067786399634922033881 27390800839799726191525411)
    ·
      refine ⟨41086201259699589287288117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27390800839799726191525411 41086201259699589287288117)
      ·
        refine ⟨3851831368096836495683261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41086201259699589287288117 3851831368096836495683261)
        ·
          refine ⟨1444436763036313685881223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3851831368096836495683261 1444436763036313685881223)
          ·
            refine ⟨2166655144554470528821835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444436763036313685881223 2166655144554470528821835)
            ·
              refine ⟨3249982716831705793232753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166655144554470528821835 3249982716831705793232753)
              ·
                refine ⟨2437487037623779344924565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3249982716831705793232753 2437487037623779344924565)
                ·
                  refine ⟨114257204888614656793339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2437487037623779344924565 114257204888614656793339)
                  ·
                    rfl

theorem cell23_2002636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_2002636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002636 prefixEnd_2002636 := by exact prefixLift 2002636
  have htrace : WordTrace (prefixWord ++ tailWord_2002636) baseStart_2002636 baseEnd_2002636 := by
    simpa [prefixWord, tailWord_2002636, baseEnd_2002636] using wordTrace_append hprefix tailTrace_2002636
  have hstable : (prefixWord ++ tailWord_2002636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002636).length < 2 ^ (prefixWord ++ tailWord_2002636).sum := by decide
  have hdescent : baseEnd_2002636 < baseStart_2002636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002669 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2002669 : Nat := 118140960795 + 2002669 * 2 ^ 59
def prefixEnd_2002669 : Nat := 4983230072969 + 3 ^ 40 * 2002669 * 2
def baseEnd_2002669 : Nat := 1028331788859130282027399

theorem tailTrace_2002669 : CollatzResearch.WordTrace tailWord_2002669 prefixEnd_2002669 1028331788859130282027399 := by
  unfold tailWord_2002669
  simp only [CollatzResearch.WordTrace]
  refine ⟨73043339181679716480019061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48695559454453144320012707 73043339181679716480019061)
  ·
    refine ⟨6847813048282473420001787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73043339181679716480019061 6847813048282473420001787)
    ·
      refine ⟨10271719572423710130002681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6847813048282473420001787 10271719572423710130002681)
      ·
        refine ⟨7703789679317782597502011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10271719572423710130002681 7703789679317782597502011)
        ·
          refine ⟨11555684518976673896253017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703789679317782597502011 11555684518976673896253017)
          ·
            refine ⟨8666763389232505422189763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11555684518976673896253017 8666763389232505422189763)
            ·
              refine ⟨13000145083848758133284645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8666763389232505422189763 13000145083848758133284645)
              ·
                refine ⟨2437527203221642149990871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13000145083848758133284645 2437527203221642149990871)
                ·
                  refine ⟨3656290804832463224986307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437527203221642149990871 3656290804832463224986307)
                  ·
                    refine ⟨5484436207248694837479461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3656290804832463224986307 5484436207248694837479461)
                    ·
                      refine ⟨1028331788859130282027399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5484436207248694837479461 1028331788859130282027399)
                      ·
                        rfl

theorem cell23_2002669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2002669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002669 prefixEnd_2002669 := by exact prefixLift 2002669
  have htrace : WordTrace (prefixWord ++ tailWord_2002669) baseStart_2002669 baseEnd_2002669 := by
    simpa [prefixWord, tailWord_2002669, baseEnd_2002669] using wordTrace_append hprefix tailTrace_2002669
  have hstable : (prefixWord ++ tailWord_2002669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002669).length < 2 ^ (prefixWord ++ tailWord_2002669).sum := by decide
  have hdescent : baseEnd_2002669 < baseStart_2002669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002689 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_2002689 : Nat := 118140960795 + 2002689 * 2 ^ 59
def prefixEnd_2002689 : Nat := 4983230072969 + 3 ^ 40 * 2002689 * 2
def baseEnd_2002689 : Nat := 1028342058472220203777307

theorem tailTrace_2002689 : CollatzResearch.WordTrace tailWord_2002689 prefixEnd_2002689 1028342058472220203777307 := by
  unfold tailWord_2002689
  simp only [CollatzResearch.WordTrace]
  refine ⟨73044068641607259895747121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48696045761071506597164747 73044068641607259895747121)
  ·
    refine ⟨54783051481205444921810341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73044068641607259895747121 54783051481205444921810341)
    ·
      refine ⟨10271822152726020922839439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54783051481205444921810341 10271822152726020922839439)
      ·
        refine ⟨15407733229089031384259159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10271822152726020922839439 15407733229089031384259159)
        ·
          refine ⟨23111599843633547076388739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15407733229089031384259159 23111599843633547076388739)
          ·
            refine ⟨34667399765450320614583109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23111599843633547076388739 34667399765450320614583109)
            ·
              refine ⟨6500137456021935115234333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34667399765450320614583109 6500137456021935115234333)
              ·
                refine ⟨2437551546008225668212875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6500137456021935115234333 2437551546008225668212875)
                ·
                  refine ⟨3656327319012338502319313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437551546008225668212875 3656327319012338502319313)
                  ·
                    refine ⟨2742245489259253876739485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3656327319012338502319313 2742245489259253876739485)
                    ·
                      refine ⟨1028342058472220203777307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2742245489259253876739485 1028342058472220203777307)
                      ·
                        rfl

theorem cell23_2002689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_2002689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002689 prefixEnd_2002689 := by exact prefixLift 2002689
  have htrace : WordTrace (prefixWord ++ tailWord_2002689) baseStart_2002689 baseEnd_2002689 := by
    simpa [prefixWord, tailWord_2002689, baseEnd_2002689] using wordTrace_append hprefix tailTrace_2002689
  have hstable : (prefixWord ++ tailWord_2002689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002689).length < 2 ^ (prefixWord ++ tailWord_2002689).sum := by decide
  have hdescent : baseEnd_2002689 < baseStart_2002689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002692 : List Nat := [2, 3, 2, 2, 1, 4, 9]
def baseStart_2002692 : Nat := 118140960795 + 2002692 * 2 ^ 59
def prefixEnd_2002692 : Nat := 4983230072969 + 3 ^ 40 * 2002692 * 2
def baseEnd_2002692 : Nat := 12695599986594860395553

theorem tailTrace_2002692 : CollatzResearch.WordTrace tailWord_2002692 prefixEnd_2002692 12695599986594860395553 := by
  unfold tailWord_2002692
  simp only [CollatzResearch.WordTrace]
  refine ⟨36522089030298195704053165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48696118707064260938737553 36522089030298195704053165)
  ·
    refine ⟨13695783386361823389019937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36522089030298195704053165 13695783386361823389019937)
    ·
      refine ⟨10271837539771367541764953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13695783386361823389019937 10271837539771367541764953)
      ·
        refine ⟨7703878154828525656323715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10271837539771367541764953 7703878154828525656323715)
        ·
          refine ⟨11555817232242788484485573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703878154828525656323715 11555817232242788484485573)
          ·
            refine ⟨2166715731045522840841045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11555817232242788484485573 2166715731045522840841045)
            ·
              refine ⟨12695599986594860395553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2166715731045522840841045 12695599986594860395553)
              ·
                rfl

theorem cell23_2002692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 9].length) (baseStart_2002692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002692 prefixEnd_2002692 := by exact prefixLift 2002692
  have htrace : WordTrace (prefixWord ++ tailWord_2002692) baseStart_2002692 baseEnd_2002692 := by
    simpa [prefixWord, tailWord_2002692, baseEnd_2002692] using wordTrace_append hprefix tailTrace_2002692
  have hstable : (prefixWord ++ tailWord_2002692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002692).length < 2 ^ (prefixWord ++ tailWord_2002692).sum := by decide
  have hdescent : baseEnd_2002692 < baseStart_2002692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002705 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 2, 7]
def baseStart_2002705 : Nat := 118140960795 + 2002705 * 2 ^ 59
def prefixEnd_2002705 : Nat := 4983230072969 + 3 ^ 40 * 2002705 * 2
def baseEnd_2002705 : Nat := 342783424720897380392411

theorem tailTrace_2002705 : CollatzResearch.WordTrace tailWord_2002705 prefixEnd_2002705 342783424720897380392411 := by
  unfold tailWord_2002705
  simp only [CollatzResearch.WordTrace]
  refine ⟨73044652209549294628329569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48696434806366196418886379 73044652209549294628329569)
  ·
    refine ⟨54783489157161970971247177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73044652209549294628329569 54783489157161970971247177)
    ·
      refine ⟨41087616867871478228435383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54783489157161970971247177 41087616867871478228435383)
      ·
        refine ⟨61631425301807217342653075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41087616867871478228435383 61631425301807217342653075)
        ·
          refine ⟨92447137952710826013979613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61631425301807217342653075 92447137952710826013979613)
          ·
            refine ⟨34667676732266559755242355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92447137952710826013979613 34667676732266559755242355)
            ·
              refine ⟨52001515098399839632863533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34667676732266559755242355 52001515098399839632863533)
              ·
                refine ⟨19500568161899939862323825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52001515098399839632863533 19500568161899939862323825)
                ·
                  refine ⟨14625426121424954896742869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19500568161899939862323825 14625426121424954896742869)
                  ·
                    refine ⟨342783424720897380392411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14625426121424954896742869 342783424720897380392411)
                    ·
                      rfl

theorem cell23_2002705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_2002705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002705 prefixEnd_2002705 := by exact prefixLift 2002705
  have htrace : WordTrace (prefixWord ++ tailWord_2002705) baseStart_2002705 baseEnd_2002705 := by
    simpa [prefixWord, tailWord_2002705, baseEnd_2002705] using wordTrace_append hprefix tailTrace_2002705
  have hstable : (prefixWord ++ tailWord_2002705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002705).length < 2 ^ (prefixWord ++ tailWord_2002705).sum := by decide
  have hdescent : baseEnd_2002705 < baseStart_2002705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002715 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 5]
def baseStart_2002715 : Nat := 118140960795 + 2002715 * 2 ^ 59
def prefixEnd_2002715 : Nat := 4983230072969 + 3 ^ 40 * 2002715 * 2
def baseEnd_2002715 : Nat := 1028355408969237102052187

theorem tailTrace_2002715 : CollatzResearch.WordTrace tailWord_2002715 prefixEnd_2002715 1028355408969237102052187 := by
  unfold tailWord_2002715
  simp only [CollatzResearch.WordTrace]
  refine ⟨73045016939513066336193599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48696677959675377557462399 73045016939513066336193599)
  ·
    refine ⟨109567525409269599504290399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73045016939513066336193599 109567525409269599504290399)
    ·
      refine ⟨164351288113904399256435599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109567525409269599504290399 164351288113904399256435599)
      ·
        refine ⟨246526932170856598884653399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164351288113904399256435599 246526932170856598884653399)
        ·
          refine ⟨369790398256284898326980099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246526932170856598884653399 369790398256284898326980099)
          ·
            refine ⟨554685597384427347490470149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369790398256284898326980099 554685597384427347490470149)
            ·
              refine ⟨104003549509580127654463153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 554685597384427347490470149 104003549509580127654463153)
              ·
                refine ⟨78002662132185095740847365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104003549509580127654463153 78002662132185095740847365)
                ·
                  refine ⟨14625499149784705451408881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78002662132185095740847365 14625499149784705451408881)
                  ·
                    refine ⟨10969124362338529088556661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14625499149784705451408881 10969124362338529088556661)
                    ·
                      refine ⟨1028355408969237102052187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10969124362338529088556661 1028355408969237102052187)
                      ·
                        rfl

theorem cell23_2002715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_2002715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002715 prefixEnd_2002715 := by exact prefixLift 2002715
  have htrace : WordTrace (prefixWord ++ tailWord_2002715) baseStart_2002715 baseEnd_2002715 := by
    simpa [prefixWord, tailWord_2002715, baseEnd_2002715] using wordTrace_append hprefix tailTrace_2002715
  have hstable : (prefixWord ++ tailWord_2002715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002715).length < 2 ^ (prefixWord ++ tailWord_2002715).sum := by decide
  have hdescent : baseEnd_2002715 < baseStart_2002715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002735 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 1, 8]
def baseStart_2002735 : Nat := 118140960795 + 2002735 * 2 ^ 59
def prefixEnd_2002735 : Nat := 4983230072969 + 3 ^ 40 * 2002735 * 2
def baseEnd_2002735 : Nat := 342788559527442341267365

theorem tailTrace_2002735 : CollatzResearch.WordTrace tailWord_2002735 prefixEnd_2002735 342788559527442341267365 := by
  unfold tailWord_2002735
  simp only [CollatzResearch.WordTrace]
  refine ⟨73045746399440609751921659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48697164266293739834614439 73045746399440609751921659)
  ·
    refine ⟨109568619599160914627882489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73045746399440609751921659 109568619599160914627882489)
    ·
      refine ⟨82176464699370685970911867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109568619599160914627882489 82176464699370685970911867)
      ·
        refine ⟨123264697049056028956367801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82176464699370685970911867 123264697049056028956367801)
        ·
          refine ⟨92448522786792021717275851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123264697049056028956367801 92448522786792021717275851)
          ·
            refine ⟨138672784180188032575913777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92448522786792021717275851 138672784180188032575913777)
            ·
              refine ⟨104004588135141024431935333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138672784180188032575913777 104004588135141024431935333)
              ·
                refine ⟨19500860275338942080987875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104004588135141024431935333 19500860275338942080987875)
                ·
                  refine ⟨29251290413008413121481813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19500860275338942080987875 29251290413008413121481813)
                  ·
                    refine ⟨342788559527442341267365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29251290413008413121481813 342788559527442341267365)
                    ·
                      rfl

theorem cell23_2002735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_2002735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002735 prefixEnd_2002735 := by exact prefixLift 2002735
  have htrace : WordTrace (prefixWord ++ tailWord_2002735) baseStart_2002735 baseEnd_2002735 := by
    simpa [prefixWord, tailWord_2002735, baseEnd_2002735] using wordTrace_append hprefix tailTrace_2002735
  have hstable : (prefixWord ++ tailWord_2002735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002735).length < 2 ^ (prefixWord ++ tailWord_2002735).sum := by decide
  have hdescent : baseEnd_2002735 < baseStart_2002735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002762 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_2002762 : Nat := 118140960795 + 2002762 * 2 ^ 59
def prefixEnd_2002762 : Nat := 4983230072969 + 3 ^ 40 * 2002762 * 2
def baseEnd_2002762 : Nat := 1028379542559998418164471

theorem tailTrace_2002762 : CollatzResearch.WordTrace tailWord_2002762 prefixEnd_2002762 1028379542559998418164471 := by
  unfold tailWord_2002762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18261682792585698340788635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48697820780228528908769693 18261682792585698340788635)
  ·
    refine ⟨27392524188878547511182953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18261682792585698340788635 27392524188878547511182953)
    ·
      refine ⟨20544393141658910633387215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27392524188878547511182953 20544393141658910633387215)
      ·
        refine ⟨30816589712488365950080823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20544393141658910633387215 30816589712488365950080823)
        ·
          refine ⟨46224884568732548925121235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30816589712488365950080823 46224884568732548925121235)
          ·
            refine ⟨69337326853098823387681853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46224884568732548925121235 69337326853098823387681853)
            ·
              refine ⟨26001497569912058770380695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69337326853098823387681853 26001497569912058770380695)
              ·
                refine ⟨39002246354868088155571043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26001497569912058770380695 39002246354868088155571043)
                ·
                  refine ⟨58503369532302132233356565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39002246354868088155571043 58503369532302132233356565)
                  ·
                    refine ⟨2742345446826662448438589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58503369532302132233356565 2742345446826662448438589)
                    ·
                      refine ⟨1028379542559998418164471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2742345446826662448438589 1028379542559998418164471)
                      ·
                        rfl

theorem cell23_2002762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_2002762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002762 prefixEnd_2002762 := by exact prefixLift 2002762
  have htrace : WordTrace (prefixWord ++ tailWord_2002762) baseStart_2002762 baseEnd_2002762 := by
    simpa [prefixWord, tailWord_2002762, baseEnd_2002762] using wordTrace_append hprefix tailTrace_2002762
  have hstable : (prefixWord ++ tailWord_2002762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002762).length < 2 ^ (prefixWord ++ tailWord_2002762).sum := by decide
  have hdescent : baseEnd_2002762 < baseStart_2002762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002832 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_2002832 : Nat := 118140960795 + 2002832 * 2 ^ 59
def prefixEnd_2002832 : Nat := 4983230072969 + 3 ^ 40 * 2002832 * 2
def baseEnd_2002832 : Nat := 1028415486205813144289149

theorem tailTrace_2002832 : CollatzResearch.WordTrace tailWord_2002832 prefixEnd_2002832 1028415486205813144289149 := by
  unfold tailWord_2002832
  simp only [CollatzResearch.WordTrace]
  refine ⟨36524642140044597659101375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48699522853392796878801833 36524642140044597659101375)
  ·
    refine ⟨54786963210066896488652063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36524642140044597659101375 54786963210066896488652063)
    ·
      refine ⟨82180444815100344732978095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54786963210066896488652063 82180444815100344732978095)
      ·
        refine ⟨123270667222650517099467143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82180444815100344732978095 123270667222650517099467143)
        ·
          refine ⟨184906000833975775649200715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123270667222650517099467143 184906000833975775649200715)
          ·
            refine ⟨277359001250963663473801073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184906000833975775649200715 277359001250963663473801073)
            ·
              refine ⟨208019250938222747605350805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277359001250963663473801073 208019250938222747605350805)
              ·
                refine ⟨9750902387729191294000819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208019250938222747605350805 9750902387729191294000819)
                ·
                  refine ⟨14626353581593786941001229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9750902387729191294000819 14626353581593786941001229)
                  ·
                    refine ⟨5484882593097670102875461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14626353581593786941001229 5484882593097670102875461)
                    ·
                      refine ⟨1028415486205813144289149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5484882593097670102875461 1028415486205813144289149)
                      ·
                        rfl

theorem cell23_2002832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_2002832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002832 prefixEnd_2002832 := by exact prefixLift 2002832
  have htrace : WordTrace (prefixWord ++ tailWord_2002832) baseStart_2002832 baseEnd_2002832 := by
    simpa [prefixWord, tailWord_2002832, baseEnd_2002832] using wordTrace_append hprefix tailTrace_2002832
  have hstable : (prefixWord ++ tailWord_2002832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002832).length < 2 ^ (prefixWord ++ tailWord_2002832).sum := by decide
  have hdescent : baseEnd_2002832 < baseStart_2002832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002850 : List Nat := [3, 3, 1, 2, 4, 1, 1, 3, 5]
def baseStart_2002850 : Nat := 118140960795 + 2002850 * 2 ^ 59
def prefixEnd_2002850 : Nat := 4983230072969 + 3 ^ 40 * 2002850 * 2
def baseEnd_2002850 : Nat := 114269414317510452651563

theorem tailTrace_2002850 : CollatzResearch.WordTrace tailWord_2002850 prefixEnd_2002850 114269414317510452651563 := by
  unfold tailWord_2002850
  simp only [CollatzResearch.WordTrace]
  refine ⟨18262485198505996098089501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48699960529349322928238669 18262485198505996098089501)
  ·
    refine ⟨6848431949439748536783563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18262485198505996098089501 6848431949439748536783563)
    ·
      refine ⟨10272647924159622805175345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6848431949439748536783563 10272647924159622805175345)
      ·
        refine ⟨7704485943119717103881509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10272647924159622805175345 7704485943119717103881509)
        ·
          refine ⟨1444591114334946956977783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7704485943119717103881509 1444591114334946956977783)
          ·
            refine ⟨2166886671502420435466675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444591114334946956977783 2166886671502420435466675)
            ·
              refine ⟨3250330007253630653200013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166886671502420435466675 3250330007253630653200013)
              ·
                refine ⟨1218873752720111494950005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3250330007253630653200013 1218873752720111494950005)
                ·
                  refine ⟨114269414317510452651563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1218873752720111494950005 114269414317510452651563)
                  ·
                    rfl

theorem cell23_2002850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_2002850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002850 prefixEnd_2002850 := by exact prefixLift 2002850
  have htrace : WordTrace (prefixWord ++ tailWord_2002850) baseStart_2002850 baseEnd_2002850 := by
    simpa [prefixWord, tailWord_2002850, baseEnd_2002850] using wordTrace_append hprefix tailTrace_2002850
  have hstable : (prefixWord ++ tailWord_2002850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002850).length < 2 ^ (prefixWord ++ tailWord_2002850).sum := by decide
  have hdescent : baseEnd_2002850 < baseStart_2002850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002872 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 8]
def baseStart_2002872 : Nat := 118140960795 + 2002872 * 2 ^ 59
def prefixEnd_2002872 : Nat := 4983230072969 + 3 ^ 40 * 2002872 * 2
def baseEnd_2002872 : Nat := 114270669492443665309885

theorem tailTrace_2002872 : CollatzResearch.WordTrace tailWord_2002872 prefixEnd_2002872 114270669492443665309885 := by
  unfold tailWord_2002872
  simp only [CollatzResearch.WordTrace]
  refine ⟨36525371599972141074829435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48700495466629521433105913 36525371599972141074829435)
  ·
    refine ⟨54788057399958211612244153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36525371599972141074829435 54788057399958211612244153)
    ·
      refine ⟨41091043049968658709183115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54788057399958211612244153 41091043049968658709183115)
      ·
        refine ⟨61636564574952988063774673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41091043049968658709183115 61636564574952988063774673)
        ·
          refine ⟨46227423431214741047831005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61636564574952988063774673 46227423431214741047831005)
          ·
            refine ⟨17335283786705527892936627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46227423431214741047831005 17335283786705527892936627)
            ·
              refine ⟨26002925680058291839404941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17335283786705527892936627 26002925680058291839404941)
              ·
                refine ⟨9751097130021859439776853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26002925680058291839404941 9751097130021859439776853)
                ·
                  refine ⟨114270669492443665309885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9751097130021859439776853 114270669492443665309885)
                  ·
                    rfl

theorem cell23_2002872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 8].length) (baseStart_2002872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002872 prefixEnd_2002872 := by exact prefixLift 2002872
  have htrace : WordTrace (prefixWord ++ tailWord_2002872) baseStart_2002872 baseEnd_2002872 := by
    simpa [prefixWord, tailWord_2002872, baseEnd_2002872] using wordTrace_append hprefix tailTrace_2002872
  have hstable : (prefixWord ++ tailWord_2002872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002872).length < 2 ^ (prefixWord ++ tailWord_2002872).sum := by decide
  have hdescent : baseEnd_2002872 < baseStart_2002872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002912 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2002912 : Nat := 118140960795 + 2002912 * 2 ^ 59
def prefixEnd_2002912 : Nat := 4983230072969 + 3 ^ 40 * 2002912 * 2
def baseEnd_2002912 : Nat := 1028456564658172831288781

theorem tailTrace_2002912 : CollatzResearch.WordTrace tailWord_2002912 prefixEnd_2002912 1028456564658172831288781 := by
  unfold tailWord_2002912
  simp only [CollatzResearch.WordTrace]
  refine ⟨36526101059899684490557495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48701468079866245987409993 36526101059899684490557495)
  ·
    refine ⟨54789151589849526735836243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36526101059899684490557495 54789151589849526735836243)
    ·
      refine ⟨82183727384774290103754365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54789151589849526735836243 82183727384774290103754365)
      ·
        refine ⟨30818897769290358788907887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82183727384774290103754365 30818897769290358788907887)
        ·
          refine ⟨46228346653935538183361831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30818897769290358788907887 46228346653935538183361831)
          ·
            refine ⟨69342519980903307275042747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46228346653935538183361831 69342519980903307275042747)
            ·
              refine ⟨104013779971354960912564121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69342519980903307275042747 104013779971354960912564121)
              ·
                refine ⟨78010334978516220684423091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104013779971354960912564121 78010334978516220684423091)
                ·
                  refine ⟨117015502467774331026634637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78010334978516220684423091 117015502467774331026634637)
                  ·
                    refine ⟨43880813425415374134987989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117015502467774331026634637 43880813425415374134987989)
                    ·
                      refine ⟨1028456564658172831288781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43880813425415374134987989 1028456564658172831288781)
                      ·
                        rfl

theorem cell23_2002912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2002912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002912 prefixEnd_2002912 := by exact prefixLift 2002912
  have htrace : WordTrace (prefixWord ++ tailWord_2002912) baseStart_2002912 baseEnd_2002912 := by
    simpa [prefixWord, tailWord_2002912, baseEnd_2002912] using wordTrace_append hprefix tailTrace_2002912
  have hstable : (prefixWord ++ tailWord_2002912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002912).length < 2 ^ (prefixWord ++ tailWord_2002912).sum := by decide
  have hdescent : baseEnd_2002912 < baseStart_2002912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002939 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 4]
def baseStart_2002939 : Nat := 118140960795 + 2002939 * 2 ^ 59
def prefixEnd_2002939 : Nat := 4983230072969 + 3 ^ 40 * 2002939 * 2
def baseEnd_2002939 : Nat := 1028470428635844225651157

theorem tailTrace_2002939 : CollatzResearch.WordTrace tailWord_2002939 prefixEnd_2002939 1028470428635844225651157 := by
  unfold tailWord_2002939
  simp only [CollatzResearch.WordTrace]
  refine ⟨73053186890701552592347871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48702124593801035061565247 73053186890701552592347871)
  ·
    refine ⟨109579780336052328888521807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73053186890701552592347871 109579780336052328888521807)
    ·
      refine ⟨164369670504078493332782711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109579780336052328888521807 164369670504078493332782711)
      ·
        refine ⟨246554505756117739999174067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164369670504078493332782711 246554505756117739999174067)
        ·
          refine ⟨369831758634176609998761101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246554505756117739999174067 369831758634176609998761101)
          ·
            refine ⟨138686909487816228749535413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 369831758634176609998761101 138686909487816228749535413)
            ·
              refine ⟨13001897764482771445268945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 138686909487816228749535413 13001897764482771445268945)
              ·
                refine ⟨9751423323362078583951709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13001897764482771445268945 9751423323362078583951709)
                ·
                  refine ⟨3656783746260779468981891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9751423323362078583951709 3656783746260779468981891)
                  ·
                    refine ⟨5485175619391169203472837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3656783746260779468981891 5485175619391169203472837)
                    ·
                      refine ⟨1028470428635844225651157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5485175619391169203472837 1028470428635844225651157)
                      ·
                        rfl

theorem cell23_2002939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 4].length) (baseStart_2002939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002939 prefixEnd_2002939 := by exact prefixLift 2002939
  have htrace : WordTrace (prefixWord ++ tailWord_2002939) baseStart_2002939 baseEnd_2002939 := by
    simpa [prefixWord, tailWord_2002939, baseEnd_2002939] using wordTrace_append hprefix tailTrace_2002939
  have hstable : (prefixWord ++ tailWord_2002939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002939).length < 2 ^ (prefixWord ++ tailWord_2002939).sum := by decide
  have hdescent : baseEnd_2002939 < baseStart_2002939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002949 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_2002949 : Nat := 118140960795 + 2002949 * 2 ^ 59
def prefixEnd_2002949 : Nat := 4983230072969 + 3 ^ 40 * 2002949 * 2
def baseEnd_2002949 : Nat := 342825187814129728842037

theorem tailTrace_2002949 : CollatzResearch.WordTrace tailWord_2002949 prefixEnd_2002949 342825187814129728842037 := by
  unfold tailWord_2002949
  simp only [CollatzResearch.WordTrace]
  refine ⟨73053551620665324300211901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48702367747110216200141267 73053551620665324300211901)
  ·
    refine ⟨27395081857749496612579463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73053551620665324300211901 27395081857749496612579463)
    ·
      refine ⟨41092622786624244918869195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27395081857749496612579463 41092622786624244918869195)
      ·
        refine ⟨61638934179936367378303793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41092622786624244918869195 61638934179936367378303793)
        ·
          refine ⟨46229200634952275533727845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61638934179936367378303793 46229200634952275533727845)
          ·
            refine ⟨8667975119053551662573971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46229200634952275533727845 8667975119053551662573971)
            ·
              refine ⟨13001962678580327493860957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8667975119053551662573971 13001962678580327493860957)
              ·
                refine ⟨4875736004467622810197859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13001962678580327493860957 4875736004467622810197859)
                ·
                  refine ⟨7313604006701434215296789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4875736004467622810197859 7313604006701434215296789)
                  ·
                    refine ⟨342825187814129728842037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7313604006701434215296789 342825187814129728842037)
                    ·
                      rfl

theorem cell23_2002949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_2002949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002949 prefixEnd_2002949 := by exact prefixLift 2002949
  have htrace : WordTrace (prefixWord ++ tailWord_2002949) baseStart_2002949 baseEnd_2002949 := by
    simpa [prefixWord, tailWord_2002949, baseEnd_2002949] using wordTrace_append hprefix tailTrace_2002949
  have hstable : (prefixWord ++ tailWord_2002949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002949).length < 2 ^ (prefixWord ++ tailWord_2002949).sum := by decide
  have hdescent : baseEnd_2002949 < baseStart_2002949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002956 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_2002956 : Nat := 118140960795 + 2002956 * 2 ^ 59
def prefixEnd_2002956 : Nat := 4983230072969 + 3 ^ 40 * 2002956 * 2
def baseEnd_2002956 : Nat := 1028479157806970659138579

theorem tailTrace_2002956 : CollatzResearch.WordTrace tailWord_2002956 prefixEnd_2002956 1028479157806970659138579 := by
  unfold tailWord_2002956
  simp only [CollatzResearch.WordTrace]
  refine ⟨36526903465819982247858361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48702537954426642997144481 36526903465819982247858361)
  ·
    refine ⟨27395177599364986685893771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36526903465819982247858361 27395177599364986685893771)
    ·
      refine ⟨41092766399047480028840657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27395177599364986685893771 41092766399047480028840657)
      ·
        refine ⟨30819574799285610021630493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41092766399047480028840657 30819574799285610021630493)
        ·
          refine ⟨11557340549732103758111435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30819574799285610021630493 11557340549732103758111435)
          ·
            refine ⟨17336010824598155637167153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11557340549732103758111435 17336010824598155637167153)
            ·
              refine ⟨13002008118448616727875365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17336010824598155637167153 13002008118448616727875365)
              ·
                refine ⟨2437876522209115636476631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13002008118448616727875365 2437876522209115636476631)
                ·
                  refine ⟨3656814783313673454714947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437876522209115636476631 3656814783313673454714947)
                  ·
                    refine ⟨5485222174970510182072421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3656814783313673454714947 5485222174970510182072421)
                    ·
                      refine ⟨1028479157806970659138579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5485222174970510182072421 1028479157806970659138579)
                      ·
                        rfl

theorem cell23_2002956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_2002956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002956 prefixEnd_2002956 := by exact prefixLift 2002956
  have htrace : WordTrace (prefixWord ++ tailWord_2002956) baseStart_2002956 baseEnd_2002956 := by
    simpa [prefixWord, tailWord_2002956, baseEnd_2002956] using wordTrace_append hprefix tailTrace_2002956
  have hstable : (prefixWord ++ tailWord_2002956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002956).length < 2 ^ (prefixWord ++ tailWord_2002956).sum := by decide
  have hdescent : baseEnd_2002956 < baseStart_2002956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002967 : List Nat := [1, 1, 3, 5, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2002967 : Nat := 118140960795 + 2002967 * 2 ^ 59
def prefixEnd_2002967 : Nat := 4983230072969 + 3 ^ 40 * 2002967 * 2
def baseEnd_2002967 : Nat := 1028484806094170116101029

theorem tailTrace_2002967 : CollatzResearch.WordTrace tailWord_2002967 prefixEnd_2002967 1028484806094170116101029 := by
  unfold tailWord_2002967
  simp only [CollatzResearch.WordTrace]
  refine ⟨73054208134600113374367155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48702805423066742249578103 73054208134600113374367155)
  ·
    refine ⟨109581312201900170061550733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73054208134600113374367155 109581312201900170061550733)
    ·
      refine ⟨41092992075712563773081525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109581312201900170061550733 41092992075712563773081525)
      ·
        refine ⟨3852468007098052853726393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41092992075712563773081525 3852468007098052853726393)
        ·
          refine ⟨2889351005323539640294795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3852468007098052853726393 2889351005323539640294795)
          ·
            refine ⟨4334026507985309460442193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889351005323539640294795 4334026507985309460442193)
            ·
              refine ⟨3250519880988982095331645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334026507985309460442193 3250519880988982095331645)
              ·
                refine ⟨1218944955370868285749367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3250519880988982095331645 1218944955370868285749367)
                ·
                  refine ⟨1828417433056302428624051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218944955370868285749367 1828417433056302428624051)
                  ·
                    refine ⟨2742626149584453642936077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1828417433056302428624051 2742626149584453642936077)
                    ·
                      refine ⟨1028484806094170116101029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2742626149584453642936077 1028484806094170116101029)
                      ·
                        rfl

theorem cell23_2002967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2002967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002967 prefixEnd_2002967 := by exact prefixLift 2002967
  have htrace : WordTrace (prefixWord ++ tailWord_2002967) baseStart_2002967 baseEnd_2002967 := by
    simpa [prefixWord, tailWord_2002967, baseEnd_2002967] using wordTrace_append hprefix tailTrace_2002967
  have hstable : (prefixWord ++ tailWord_2002967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002967).length < 2 ^ (prefixWord ++ tailWord_2002967).sum := by decide
  have hdescent : baseEnd_2002967 < baseStart_2002967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002973 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2002973 : Nat := 118140960795 + 2002973 * 2 ^ 59
def prefixEnd_2002973 : Nat := 4983230072969 + 3 ^ 40 * 2002973 * 2
def baseEnd_2002973 : Nat := 1028487886978097092626001

theorem tailTrace_2002973 : CollatzResearch.WordTrace tailWord_2002973 prefixEnd_2002973 1028487886978097092626001 := by
  unfold tailWord_2002973
  simp only [CollatzResearch.WordTrace]
  refine ⟨73054426972578376399085573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48702951315052250932723715 73054426972578376399085573)
  ·
    refine ⟨13697705057358445574828545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73054426972578376399085573 13697705057358445574828545)
    ·
      refine ⟨10273278793018834181121409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13697705057358445574828545 10273278793018834181121409)
      ·
        refine ⟨7704959094764125635841057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10273278793018834181121409 7704959094764125635841057)
        ·
          refine ⟨5778719321073094226880793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7704959094764125635841057 5778719321073094226880793)
          ·
            refine ⟨4334039490804820670160595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5778719321073094226880793 4334039490804820670160595)
            ·
              refine ⟨6501059236207231005240893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334039490804820670160595 6501059236207231005240893)
              ·
                refine ⟨2437897213577711626965335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6501059236207231005240893 2437897213577711626965335)
                ·
                  refine ⟨3656845820366567440448003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437897213577711626965335 3656845820366567440448003)
                  ·
                    refine ⟨5485268730549851160672005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3656845820366567440448003 5485268730549851160672005)
                    ·
                      refine ⟨1028487886978097092626001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5485268730549851160672005 1028487886978097092626001)
                      ·
                        rfl

theorem cell23_2002973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2002973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002973 prefixEnd_2002973 := by exact prefixLift 2002973
  have htrace : WordTrace (prefixWord ++ tailWord_2002973) baseStart_2002973 baseEnd_2002973 := by
    simpa [prefixWord, tailWord_2002973, baseEnd_2002973] using wordTrace_append hprefix tailTrace_2002973
  have hstable : (prefixWord ++ tailWord_2002973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002973).length < 2 ^ (prefixWord ++ tailWord_2002973).sum := by decide
  have hdescent : baseEnd_2002973 < baseStart_2002973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2002990 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2002990 : Nat := 118140960795 + 2002990 * 2 ^ 59
def prefixEnd_2002990 : Nat := 4983230072969 + 3 ^ 40 * 2002990 * 2
def baseEnd_2002990 : Nat := 1028496616149223526113423

theorem tailTrace_2002990 : CollatzResearch.WordTrace tailWord_2002990 prefixEnd_2002990 1028496616149223526113423 := by
  unfold tailWord_2002990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9131880876689598537806803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48703364675677858868302949 9131880876689598537806803)
  ·
    refine ⟨13697821315034397806710205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9131880876689598537806803 13697821315034397806710205)
    ·
      refine ⟨5136682993137899177516327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13697821315034397806710205 5136682993137899177516327)
      ·
        refine ⟨7705024489706848766274491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5136682993137899177516327 7705024489706848766274491)
        ·
          refine ⟨11557536734560273149411737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7705024489706848766274491 11557536734560273149411737)
          ·
            refine ⟨8668152550920204862058803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11557536734560273149411737 8668152550920204862058803)
            ·
              refine ⟨13002228826380307293088205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668152550920204862058803 13002228826380307293088205)
              ·
                refine ⟨4875835809892615234908077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13002228826380307293088205 4875835809892615234908077)
                ·
                  refine ⟨1828438428709730713090529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4875835809892615234908077 1828438428709730713090529)
                  ·
                    refine ⟨1371328821532298034817897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1828438428709730713090529 1371328821532298034817897)
                    ·
                      refine ⟨1028496616149223526113423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371328821532298034817897 1028496616149223526113423)
                      ·
                        rfl

theorem cell23_2002990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2002990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2002990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2002990 prefixEnd_2002990 := by exact prefixLift 2002990
  have htrace : WordTrace (prefixWord ++ tailWord_2002990) baseStart_2002990 baseEnd_2002990 := by
    simpa [prefixWord, tailWord_2002990, baseEnd_2002990] using wordTrace_append hprefix tailTrace_2002990
  have hstable : (prefixWord ++ tailWord_2002990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2002990).length < 2 ^ (prefixWord ++ tailWord_2002990).sum := by decide
  have hdescent : baseEnd_2002990 < baseStart_2002990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2002990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003000 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 2, 4]
def baseStart_2003000 : Nat := 118140960795 + 2003000 * 2 ^ 59
def prefixEnd_2003000 : Nat := 4983230072969 + 3 ^ 40 * 2003000 * 2
def baseEnd_2003000 : Nat := 342833916985256162329459

theorem tailTrace_2003000 : CollatzResearch.WordTrace tailWord_2003000 prefixEnd_2003000 342833916985256162329459 := by
  unfold tailWord_2003000
  simp only [CollatzResearch.WordTrace]
  refine ⟨36527705871740280005159227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48703607828987040006878969 36527705871740280005159227)
  ·
    refine ⟨54791558807610420007738841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36527705871740280005159227 54791558807610420007738841)
    ·
      refine ⟨41093669105707815005804131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54791558807610420007738841 41093669105707815005804131)
      ·
        refine ⟨61640503658561722508706197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41093669105707815005804131 61640503658561722508706197)
        ·
          refine ⟨2889398608995080742595603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61640503658561722508706197 2889398608995080742595603)
          ·
            refine ⟨4334097913492621113893405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889398608995080742595603 4334097913492621113893405)
            ·
              refine ⟨1625286717559732917710027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4334097913492621113893405 1625286717559732917710027)
              ·
                refine ⟨2437930076339599376565041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625286717559732917710027 2437930076339599376565041)
                ·
                  refine ⟨1828447557254699532423781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437930076339599376565041 1828447557254699532423781)
                  ·
                    refine ⟨342833916985256162329459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1828447557254699532423781 342833916985256162329459)
                    ·
                      rfl

theorem cell23_2003000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_2003000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003000 prefixEnd_2003000 := by exact prefixLift 2003000
  have htrace : WordTrace (prefixWord ++ tailWord_2003000) baseStart_2003000 baseEnd_2003000 := by
    simpa [prefixWord, tailWord_2003000, baseEnd_2003000] using wordTrace_append hprefix tailTrace_2003000
  have hstable : (prefixWord ++ tailWord_2003000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003000).length < 2 ^ (prefixWord ++ tailWord_2003000).sum := by decide
  have hdescent : baseEnd_2003000 < baseStart_2003000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003033 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 1, 3, 2]
def baseStart_2003033 : Nat := 118140960795 + 2003033 * 2 ^ 59
def prefixEnd_2003033 : Nat := 4983230072969 + 3 ^ 40 * 2003033 * 2
def baseEnd_2003033 : Nat := 1028518695817366857875725

theorem tailTrace_2003033 : CollatzResearch.WordTrace tailWord_2003033 prefixEnd_2003033 1028518695817366857875725 := by
  unfold tailWord_2003033
  simp only [CollatzResearch.WordTrace]
  refine ⟨73056615352361006646269753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48704410234907337764179835 73056615352361006646269753)
  ·
    refine ⟨54792461514270754984702315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73056615352361006646269753 54792461514270754984702315)
    ·
      refine ⟨82188692271406132477053473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54792461514270754984702315 82188692271406132477053473)
      ·
        refine ⟨61641519203554599357790105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82188692271406132477053473 61641519203554599357790105)
        ·
          refine ⟨46231139402665949518342579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61641519203554599357790105 46231139402665949518342579)
          ·
            refine ⟨69346709103998924277513869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46231139402665949518342579 69346709103998924277513869)
            ·
              refine ⟨26005015913999596604067701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69346709103998924277513869 26005015913999596604067701)
              ·
                refine ⟨2437970241937462181631347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26005015913999596604067701 2437970241937462181631347)
                ·
                  refine ⟨3656955362906193272447021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2437970241937462181631347 3656955362906193272447021)
                  ·
                    refine ⟨1371358261089822477167633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656955362906193272447021 1371358261089822477167633)
                    ·
                      refine ⟨1028518695817366857875725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371358261089822477167633 1028518695817366857875725)
                      ·
                        rfl

theorem cell23_2003033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_2003033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003033 prefixEnd_2003033 := by exact prefixLift 2003033
  have htrace : WordTrace (prefixWord ++ tailWord_2003033) baseStart_2003033 baseEnd_2003033 := by
    simpa [prefixWord, tailWord_2003033, baseEnd_2003033] using wordTrace_append hprefix tailTrace_2003033
  have hstable : (prefixWord ++ tailWord_2003033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003033).length < 2 ^ (prefixWord ++ tailWord_2003033).sum := by decide
  have hdescent : baseEnd_2003033 < baseStart_2003033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003039 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 2, 6]
def baseStart_2003039 : Nat := 118140960795 + 2003039 * 2 ^ 59
def prefixEnd_2003039 : Nat := 4983230072969 + 3 ^ 40 * 2003039 * 2
def baseEnd_2003039 : Nat := 342840592233764611466899

theorem tailTrace_2003039 : CollatzResearch.WordTrace tailWord_2003039 prefixEnd_2003039 342840592233764611466899 := by
  unfold tailWord_2003039
  simp only [CollatzResearch.WordTrace]
  refine ⟨73056834190339269670988171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48704556126892846447325447 73056834190339269670988171)
  ·
    refine ⟨109585251285508904506482257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73056834190339269670988171 109585251285508904506482257)
    ·
      refine ⟨82188938464131678379861693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109585251285508904506482257 82188938464131678379861693)
      ·
        refine ⟨30820851924049379392448135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82188938464131678379861693 30820851924049379392448135)
        ·
          refine ⟨46231277886074069088672203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30820851924049379392448135 46231277886074069088672203)
          ·
            refine ⟨69346916829111103633008305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46231277886074069088672203 69346916829111103633008305)
            ·
              refine ⟨52010187621833327724756229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69346916829111103633008305 52010187621833327724756229)
              ·
                refine ⟨9751910179093748948391793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52010187621833327724756229 9751910179093748948391793)
                ·
                  refine ⟨7313932634320311711293845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9751910179093748948391793 7313932634320311711293845)
                  ·
                    refine ⟨342840592233764611466899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7313932634320311711293845 342840592233764611466899)
                    ·
                      rfl

theorem cell23_2003039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_2003039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003039 prefixEnd_2003039 := by exact prefixLift 2003039
  have htrace : WordTrace (prefixWord ++ tailWord_2003039) baseStart_2003039 baseEnd_2003039 := by
    simpa [prefixWord, tailWord_2003039, baseEnd_2003039] using wordTrace_append hprefix tailTrace_2003039
  have hstable : (prefixWord ++ tailWord_2003039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003039).length < 2 ^ (prefixWord ++ tailWord_2003039).sum := by decide
  have hdescent : baseEnd_2003039 < baseStart_2003039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003049 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_2003049 : Nat := 118140960795 + 2003049 * 2 ^ 59
def prefixEnd_2003049 : Nat := 4983230072969 + 3 ^ 40 * 2003049 * 2
def baseEnd_2003049 : Nat := 1028526911507838795275651

theorem tailTrace_2003049 : CollatzResearch.WordTrace tailWord_2003049 prefixEnd_2003049 1028526911507838795275651 := by
  unfold tailWord_2003049
  simp only [CollatzResearch.WordTrace]
  refine ⟨73057198920303041378852201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48704799280202027585901467 73057198920303041378852201)
  ·
    refine ⟨54792899190227281034139151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73057198920303041378852201 54792899190227281034139151)
    ·
      refine ⟨82189348785340921551208727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54792899190227281034139151 82189348785340921551208727)
      ·
        refine ⟨123284023178011382326813091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82189348785340921551208727 123284023178011382326813091)
        ·
          refine ⟨184926034767017073490219637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123284023178011382326813091 184926034767017073490219637)
          ·
            refine ⟨17336815759407850639708091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 184926034767017073490219637 17336815759407850639708091)
            ·
              refine ⟨26005223639111775959562137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17336815759407850639708091 26005223639111775959562137)
              ·
                refine ⟨19503917729333831969671603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26005223639111775959562137 19503917729333831969671603)
                ·
                  refine ⟨29255876594000747954507405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19503917729333831969671603 29255876594000747954507405)
                  ·
                    refine ⟨10970953722750280482940277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29255876594000747954507405 10970953722750280482940277)
                    ·
                      refine ⟨1028526911507838795275651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10970953722750280482940277 1028526911507838795275651)
                      ·
                        rfl

theorem cell23_2003049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_2003049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003049 prefixEnd_2003049 := by exact prefixLift 2003049
  have htrace : WordTrace (prefixWord ++ tailWord_2003049) baseStart_2003049 baseEnd_2003049 := by
    simpa [prefixWord, tailWord_2003049, baseEnd_2003049] using wordTrace_append hprefix tailTrace_2003049
  have hstable : (prefixWord ++ tailWord_2003049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003049).length < 2 ^ (prefixWord ++ tailWord_2003049).sum := by decide
  have hdescent : baseEnd_2003049 < baseStart_2003049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003080 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_2003080 : Nat := 118140960795 + 2003080 * 2 ^ 59
def prefixEnd_2003080 : Nat := 4983230072969 + 3 ^ 40 * 2003080 * 2
def baseEnd_2003080 : Nat := 1028542829408128173988009

theorem tailTrace_2003080 : CollatzResearch.WordTrace tailWord_2003080 prefixEnd_2003080 1028542829408128173988009 := by
  unfold tailWord_2003080
  simp only [CollatzResearch.WordTrace]
  refine ⟨36529164791595366836615347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48705553055460489115487129 36529164791595366836615347)
  ·
    refine ⟨54793747187393050254923021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36529164791595366836615347 54793747187393050254923021)
    ·
      refine ⟨20547655195272393845596133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54793747187393050254923021 20547655195272393845596133)
      ·
        refine ⟨3852685349113573846049275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20547655195272393845596133 3852685349113573846049275)
        ·
          refine ⟨5779028023670360769073913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3852685349113573846049275 5779028023670360769073913)
          ·
            refine ⟨4334271017752770576805435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5779028023670360769073913 4334271017752770576805435)
            ·
              refine ⟨6501406526629155865208153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334271017752770576805435 6501406526629155865208153)
              ·
                refine ⟨4876054894971866898906115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6501406526629155865208153 4876054894971866898906115)
                ·
                  refine ⟨7314082342457800348359173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876054894971866898906115 7314082342457800348359173)
                  ·
                    refine ⟨1371390439210837565317345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7314082342457800348359173 1371390439210837565317345)
                    ·
                      refine ⟨1028542829408128173988009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371390439210837565317345 1028542829408128173988009)
                      ·
                        rfl

theorem cell23_2003080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_2003080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003080 prefixEnd_2003080 := by exact prefixLift 2003080
  have htrace : WordTrace (prefixWord ++ tailWord_2003080) baseStart_2003080 baseEnd_2003080 := by
    simpa [prefixWord, tailWord_2003080, baseEnd_2003080] using wordTrace_append hprefix tailTrace_2003080
  have hstable : (prefixWord ++ tailWord_2003080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003080).length < 2 ^ (prefixWord ++ tailWord_2003080).sum := by decide
  have hdescent : baseEnd_2003080 < baseStart_2003080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003137 : List Nat := [1, 2, 6, 1, 2, 1, 2, 3, 5]
def baseStart_2003137 : Nat := 118140960795 + 2003137 * 2 ^ 59
def prefixEnd_2003137 : Nat := 4983230072969 + 3 ^ 40 * 2003137 * 2
def baseEnd_2003137 : Nat := 114285788645048272330583

theorem tailTrace_2003137 : CollatzResearch.WordTrace tailWord_2003137 prefixEnd_2003137 114285788645048272330583 := by
  unfold tailWord_2003137
  simp only [CollatzResearch.WordTrace]
  refine ⟨73060408543984232408055665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48706939029322821605370443 73060408543984232408055665)
  ·
    refine ⟨54795306407988174306041749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73060408543984232408055665 54795306407988174306041749)
    ·
      refine ⟨2568529987874445670595707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54795306407988174306041749 2568529987874445670595707)
      ·
        refine ⟨3852794981811668505893561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568529987874445670595707 3852794981811668505893561)
        ·
          refine ⟨2889596236358751379420171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3852794981811668505893561 2889596236358751379420171)
          ·
            refine ⟨4334394354538127069130257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889596236358751379420171 4334394354538127069130257)
            ·
              refine ⟨3250795765903595301847693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334394354538127069130257 3250795765903595301847693)
              ·
                refine ⟨1219048412213848238192885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3250795765903595301847693 1219048412213848238192885)
                ·
                  refine ⟨114285788645048272330583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1219048412213848238192885 114285788645048272330583)
                  ·
                    rfl

theorem cell23_2003137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 5].length) (baseStart_2003137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003137 prefixEnd_2003137 := by exact prefixLift 2003137
  have htrace : WordTrace (prefixWord ++ tailWord_2003137) baseStart_2003137 baseEnd_2003137 := by
    simpa [prefixWord, tailWord_2003137, baseEnd_2003137] using wordTrace_append hprefix tailTrace_2003137
  have hstable : (prefixWord ++ tailWord_2003137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003137).length < 2 ^ (prefixWord ++ tailWord_2003137).sum := by decide
  have hdescent : baseEnd_2003137 < baseStart_2003137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003153 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 2, 4, 2]
def baseStart_2003153 : Nat := 118140960795 + 2003153 * 2 ^ 59
def prefixEnd_2003153 : Nat := 4983230072969 + 3 ^ 40 * 2003153 * 2
def baseEnd_2003153 : Nat := 1028580313495906388375173

theorem tailTrace_2003153 : CollatzResearch.WordTrace tailWord_2003153 prefixEnd_2003153 1028580313495906388375173 := by
  unfold tailWord_2003153
  simp only [CollatzResearch.WordTrace]
  refine ⟨73060992111926267140638113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48707328074617511427092075 73060992111926267140638113)
  ·
    refine ⟨54795744083944700355478585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73060992111926267140638113 54795744083944700355478585)
    ·
      refine ⟨41096808062958525266608939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54795744083944700355478585 41096808062958525266608939)
      ·
        refine ⟨61645212094437787899913409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41096808062958525266608939 61645212094437787899913409)
        ·
          refine ⟨46233909070828340924935057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61645212094437787899913409 46233909070828340924935057)
          ·
            refine ⟨34675431803121255693701293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46233909070828340924935057 34675431803121255693701293)
            ·
              refine ⟨13003286926170470885137985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34675431803121255693701293 13003286926170470885137985)
              ·
                refine ⟨9752465194627853163853489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13003286926170470885137985 9752465194627853163853489)
                ·
                  refine ⟨7314348895970889872890117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9752465194627853163853489 7314348895970889872890117)
                  ·
                    refine ⟨1371440417994541851166897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7314348895970889872890117 1371440417994541851166897)
                    ·
                      refine ⟨1028580313495906388375173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371440417994541851166897 1028580313495906388375173)
                      ·
                        rfl

theorem cell23_2003153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_2003153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003153 prefixEnd_2003153 := by exact prefixLift 2003153
  have htrace : WordTrace (prefixWord ++ tailWord_2003153) baseStart_2003153 baseEnd_2003153 := by
    simpa [prefixWord, tailWord_2003153, baseEnd_2003153] using wordTrace_append hprefix tailTrace_2003153
  have hstable : (prefixWord ++ tailWord_2003153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003153).length < 2 ^ (prefixWord ++ tailWord_2003153).sum := by decide
  have hdescent : baseEnd_2003153 < baseStart_2003153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003173 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2003173 : Nat := 118140960795 + 2003173 * 2 ^ 59
def prefixEnd_2003173 : Nat := 4983230072969 + 3 ^ 40 * 2003173 * 2
def baseEnd_2003173 : Nat := 1028590583108996310125081

theorem tailTrace_2003173 : CollatzResearch.WordTrace tailWord_2003173 prefixEnd_2003173 1028590583108996310125081 := by
  unfold tailWord_2003173
  simp only [CollatzResearch.WordTrace]
  refine ⟨73061721571853810556366173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48707814381235873704244115 73061721571853810556366173)
  ·
    refine ⟨27398145589445178958637315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73061721571853810556366173 27398145589445178958637315)
    ·
      refine ⟨41097218384167768437955973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27398145589445178958637315 41097218384167768437955973)
      ·
        refine ⟨7705728447031456582116745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41097218384167768437955973 7705728447031456582116745)
        ·
          refine ⟨5779296335273592436587559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7705728447031456582116745 5779296335273592436587559)
          ·
            refine ⟨8668944502910388654881339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779296335273592436587559 8668944502910388654881339)
            ·
              refine ⟨13003416754365582982322009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668944502910388654881339 13003416754365582982322009)
              ·
                refine ⟨9752562565774187236741507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13003416754365582982322009 9752562565774187236741507)
                ·
                  refine ⟨14628843848661280855112261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9752562565774187236741507 14628843848661280855112261)
                  ·
                    refine ⟨2742908221623990160333549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14628843848661280855112261 2742908221623990160333549)
                    ·
                      refine ⟨1028590583108996310125081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2742908221623990160333549 1028590583108996310125081)
                      ·
                        rfl

theorem cell23_2003173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2003173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003173 prefixEnd_2003173 := by exact prefixLift 2003173
  have htrace : WordTrace (prefixWord ++ tailWord_2003173) baseStart_2003173 baseEnd_2003173 := by
    simpa [prefixWord, tailWord_2003173, baseEnd_2003173] using wordTrace_append hprefix tailTrace_2003173
  have hstable : (prefixWord ++ tailWord_2003173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003173).length < 2 ^ (prefixWord ++ tailWord_2003173).sum := by decide
  have hdescent : baseEnd_2003173 < baseStart_2003173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003207 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2003207 : Nat := 118140960795 + 2003207 * 2 ^ 59
def prefixEnd_2003207 : Nat := 4983230072969 + 3 ^ 40 * 2003207 * 2
def baseEnd_2003207 : Nat := 1028608041451249177099925

theorem tailTrace_2003207 : CollatzResearch.WordTrace tailWord_2003207 prefixEnd_2003207 1028608041451249177099925 := by
  unfold tailWord_2003207
  simp only [CollatzResearch.WordTrace]
  refine ⟨73062961653730634363103875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48708641102487089575402583 73062961653730634363103875)
  ·
    refine ⟨109594442480595951544655813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73062961653730634363103875 109594442480595951544655813)
    ·
      refine ⟨20548957965111740914622965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109594442480595951544655813 20548957965111740914622965)
      ·
        refine ⟨1926464809229225710745903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20548957965111740914622965 1926464809229225710745903)
        ·
          refine ⟨2889697213843838566118855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926464809229225710745903 2889697213843838566118855)
          ·
            refine ⟨4334545820765757849178283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889697213843838566118855 4334545820765757849178283)
            ·
              refine ⟨6501818731148636773767425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334545820765757849178283 6501818731148636773767425)
              ·
                refine ⟨4876364048361477580325569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6501818731148636773767425 4876364048361477580325569)
                ·
                  refine ⟨3657273036271108185244177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876364048361477580325569 3657273036271108185244177)
                  ·
                    refine ⟨2742954777203331138933133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3657273036271108185244177 2742954777203331138933133)
                    ·
                      refine ⟨1028608041451249177099925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2742954777203331138933133 1028608041451249177099925)
                      ·
                        rfl

theorem cell23_2003207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2003207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003207 prefixEnd_2003207 := by exact prefixLift 2003207
  have htrace : WordTrace (prefixWord ++ tailWord_2003207) baseStart_2003207 baseEnd_2003207 := by
    simpa [prefixWord, tailWord_2003207, baseEnd_2003207] using wordTrace_append hprefix tailTrace_2003207
  have hstable : (prefixWord ++ tailWord_2003207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003207).length < 2 ^ (prefixWord ++ tailWord_2003207).sum := by decide
  have hdescent : baseEnd_2003207 < baseStart_2003207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003240 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2003240 : Nat := 118140960795 + 2003240 * 2 ^ 59
def prefixEnd_2003240 : Nat := 4983230072969 + 3 ^ 40 * 2003240 * 2
def baseEnd_2003240 : Nat := 342874995437615849329091

theorem tailTrace_2003240 : CollatzResearch.WordTrace tailWord_2003240 prefixEnd_2003240 342874995437615849329091 := by
  unfold tailWord_2003240
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532082631305540499527587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48709443508407387332703449 36532082631305540499527587)
  ·
    refine ⟨54798123946958310749291381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36532082631305540499527587 54798123946958310749291381)
    ·
      refine ⟨5137324120027341632746067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54798123946958310749291381 5137324120027341632746067)
      ·
        refine ⟨7705986180041012449119101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137324120027341632746067 7705986180041012449119101)
        ·
          refine ⟨2889744817515379668419663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7705986180041012449119101 2889744817515379668419663)
          ·
            refine ⟨4334617226273069502629495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889744817515379668419663 4334617226273069502629495)
            ·
              refine ⟨6501925839409604253944243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4334617226273069502629495 6501925839409604253944243)
              ·
                refine ⟨9752888759114406380916365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501925839409604253944243 9752888759114406380916365)
                ·
                  refine ⟨3657333284667902392843637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9752888759114406380916365 3657333284667902392843637)
                  ·
                    refine ⟨342874995437615849329091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3657333284667902392843637 342874995437615849329091)
                    ·
                      rfl

theorem cell23_2003240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2003240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003240 prefixEnd_2003240 := by exact prefixLift 2003240
  have htrace : WordTrace (prefixWord ++ tailWord_2003240) baseStart_2003240 baseEnd_2003240 := by
    simpa [prefixWord, tailWord_2003240, baseEnd_2003240] using wordTrace_append hprefix tailTrace_2003240
  have hstable : (prefixWord ++ tailWord_2003240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003240).length < 2 ^ (prefixWord ++ tailWord_2003240).sum := by decide
  have hdescent : baseEnd_2003240 < baseStart_2003240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003253 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2003253 : Nat := 118140960795 + 2003253 * 2 ^ 59
def prefixEnd_2003253 : Nat := 4983230072969 + 3 ^ 40 * 2003253 * 2
def baseEnd_2003253 : Nat := 342877220520451999041571

theorem tailTrace_2003253 : CollatzResearch.WordTrace tailWord_2003253 prefixEnd_2003253 342877220520451999041571 := by
  unfold tailWord_2003253
  simp only [CollatzResearch.WordTrace]
  refine ⟨73064639411563984219278413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48709759607709322812852275 73064639411563984219278413)
  ·
    refine ⟨27399239779336494082229405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73064639411563984219278413 27399239779336494082229405)
    ·
      refine ⟨10274714917251185280836027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27399239779336494082229405 10274714917251185280836027)
      ·
        refine ⟨15412072375876777921254041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10274714917251185280836027 15412072375876777921254041)
        ·
          refine ⟨11559054281907583440940531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15412072375876777921254041 11559054281907583440940531)
          ·
            refine ⟨17338581422861375161410797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11559054281907583440940531 17338581422861375161410797)
            ·
              refine ⟨6501968033573015685529049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17338581422861375161410797 6501968033573015685529049)
              ·
                refine ⟨4876476025179761764146787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6501968033573015685529049 4876476025179761764146787)
                ·
                  refine ⟨7314714037769642646220181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876476025179761764146787 7314714037769642646220181)
                  ·
                    refine ⟨342877220520451999041571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7314714037769642646220181 342877220520451999041571)
                    ·
                      rfl

theorem cell23_2003253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2003253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003253 prefixEnd_2003253 := by exact prefixLift 2003253
  have htrace : WordTrace (prefixWord ++ tailWord_2003253) baseStart_2003253 baseEnd_2003253 := by
    simpa [prefixWord, tailWord_2003253, baseEnd_2003253] using wordTrace_append hprefix tailTrace_2003253
  have hstable : (prefixWord ++ tailWord_2003253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003253).length < 2 ^ (prefixWord ++ tailWord_2003253).sum := by decide
  have hdescent : baseEnd_2003253 < baseStart_2003253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003257 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 1, 5]
def baseStart_2003257 : Nat := 118140960795 + 2003257 * 2 ^ 59
def prefixEnd_2003257 : Nat := 4983230072969 + 3 ^ 40 * 2003257 * 2
def baseEnd_2003257 : Nat := 342877905161324660491565

theorem tailTrace_2003257 : CollatzResearch.WordTrace tailWord_2003257 prefixEnd_2003257 342877905161324660491565 := by
  unfold tailWord_2003257
  simp only [CollatzResearch.WordTrace]
  refine ⟨73064785303549492902424025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48709856869032995268282683 73064785303549492902424025)
  ·
    refine ⟨54798588977662119676818019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73064785303549492902424025 54798588977662119676818019)
    ·
      refine ⟨82197883466493179515227029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54798588977662119676818019 82197883466493179515227029)
      ·
        refine ⟨3853025787491867789776267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 82197883466493179515227029 3853025787491867789776267)
        ·
          refine ⟨5779538681237801684664401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853025787491867789776267 5779538681237801684664401)
          ·
            refine ⟨4334654010928351263498301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5779538681237801684664401 4334654010928351263498301)
            ·
              refine ⟨1625495254098131723811863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4334654010928351263498301 1625495254098131723811863)
              ·
                refine ⟨2438242881147197585717795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625495254098131723811863 2438242881147197585717795)
                ·
                  refine ⟨3657364321720796378576693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438242881147197585717795 3657364321720796378576693)
                  ·
                    refine ⟨342877905161324660491565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3657364321720796378576693 342877905161324660491565)
                    ·
                      rfl

theorem cell23_2003257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 5].length) (baseStart_2003257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003257 prefixEnd_2003257 := by exact prefixLift 2003257
  have htrace : WordTrace (prefixWord ++ tailWord_2003257) baseStart_2003257 baseEnd_2003257 := by
    simpa [prefixWord, tailWord_2003257, baseEnd_2003257] using wordTrace_append hprefix tailTrace_2003257
  have hstable : (prefixWord ++ tailWord_2003257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003257).length < 2 ^ (prefixWord ++ tailWord_2003257).sum := by decide
  have hdescent : baseEnd_2003257 < baseStart_2003257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003314 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_2003314 : Nat := 118140960795 + 2003314 * 2 ^ 59
def prefixEnd_2003314 : Nat := 4983230072969 + 3 ^ 40 * 2003314 * 2
def baseEnd_2003314 : Nat := 1028662983881280258461933

theorem tailTrace_2003314 : CollatzResearch.WordTrace tailWord_2003314 prefixEnd_2003314 1028662983881280258461933 := by
  unfold tailWord_2003314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18266716066085747909312249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48711242842895327758165997 18266716066085747909312249)
  ·
    refine ⟨13700037049564310931984187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18266716066085747909312249 13700037049564310931984187)
    ·
      refine ⟨20550055574346466397976281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13700037049564310931984187 20550055574346466397976281)
      ·
        refine ⟨15412541680759849798482211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20550055574346466397976281 15412541680759849798482211)
        ·
          refine ⟨23118812521139774697723317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15412541680759849798482211 23118812521139774697723317)
          ·
            refine ⟨2167388673856853877911561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23118812521139774697723317 2167388673856853877911561)
            ·
              refine ⟨1625541505392640408433671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167388673856853877911561 1625541505392640408433671)
              ·
                refine ⟨2438312258088960612650507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625541505392640408433671 2438312258088960612650507)
                ·
                  refine ⟨3657468387133440918975761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438312258088960612650507 3657468387133440918975761)
                  ·
                    refine ⟨2743101290350080689231821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3657468387133440918975761 2743101290350080689231821)
                    ·
                      refine ⟨1028662983881280258461933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2743101290350080689231821 1028662983881280258461933)
                      ·
                        rfl

theorem cell23_2003314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_2003314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003314 prefixEnd_2003314 := by exact prefixLift 2003314
  have htrace : WordTrace (prefixWord ++ tailWord_2003314) baseStart_2003314 baseEnd_2003314 := by
    simpa [prefixWord, tailWord_2003314, baseEnd_2003314] using wordTrace_append hprefix tailTrace_2003314
  have hstable : (prefixWord ++ tailWord_2003314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003314).length < 2 ^ (prefixWord ++ tailWord_2003314).sum := by decide
  have hdescent : baseEnd_2003314 < baseStart_2003314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003353 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_2003353 : Nat := 118140960795 + 2003353 * 2 ^ 59
def prefixEnd_2003353 : Nat := 4983230072969 + 3 ^ 40 * 2003353 * 2
def baseEnd_2003353 : Nat := 1028683009626805605874253

theorem tailTrace_2003353 : CollatzResearch.WordTrace tailWord_2003353 prefixEnd_2003353 1028683009626805605874253 := by
  unfold tailWord_2003353
  simp only [CollatzResearch.WordTrace]
  refine ⟨73068286711201701297918713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48712191140801134198612475 73068286711201701297918713)
  ·
    refine ⟨54801215033401275973439035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73068286711201701297918713 54801215033401275973439035)
    ·
      refine ⟨82201822550101913960158553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54801215033401275973439035 82201822550101913960158553)
      ·
        refine ⟨61651366912576435470118915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82201822550101913960158553 61651366912576435470118915)
        ·
          refine ⟨92477050368864653205178373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61651366912576435470118915 92477050368864653205178373)
          ·
            refine ⟨17339446944162122475970945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92477050368864653205178373 17339446944162122475970945)
            ·
              refine ⟨13004585208121591856978209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17339446944162122475970945 13004585208121591856978209)
              ·
                refine ⟨9753438906091193892733657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13004585208121591856978209 9753438906091193892733657)
                ·
                  refine ⟨7315079179568395419550243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9753438906091193892733657 7315079179568395419550243)
                  ·
                    refine ⟨10972618769352593129325365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7315079179568395419550243 10972618769352593129325365)
                    ·
                      refine ⟨1028683009626805605874253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10972618769352593129325365 1028683009626805605874253)
                      ·
                        rfl

theorem cell23_2003353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_2003353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003353 prefixEnd_2003353 := by exact prefixLift 2003353
  have htrace : WordTrace (prefixWord ++ tailWord_2003353) baseStart_2003353 baseEnd_2003353 := by
    simpa [prefixWord, tailWord_2003353, baseEnd_2003353] using wordTrace_append hprefix tailTrace_2003353
  have hstable : (prefixWord ++ tailWord_2003353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003353).length < 2 ^ (prefixWord ++ tailWord_2003353).sum := by decide
  have hdescent : baseEnd_2003353 < baseStart_2003353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003354 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2]
def baseStart_2003354 : Nat := 118140960795 + 2003354 * 2 ^ 59
def prefixEnd_2003354 : Nat := 4983230072969 + 3 ^ 40 * 2003354 * 2
def baseEnd_2003354 : Nat := 1028683523107460101961749

theorem tailTrace_2003354 : CollatzResearch.WordTrace tailWord_2003354 prefixEnd_2003354 1028683523107460101961749 := by
  unfold tailWord_2003354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18267080796049519617176279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48712215456132052312470077 18267080796049519617176279)
  ·
    refine ⟨27400621194074279425764419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18267080796049519617176279 27400621194074279425764419)
    ·
      refine ⟨41100931791111419138646629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27400621194074279425764419 41100931791111419138646629)
      ·
        refine ⟨7706424710833391088496243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41100931791111419138646629 7706424710833391088496243)
        ·
          refine ⟨11559637066250086632744365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7706424710833391088496243 11559637066250086632744365)
          ·
            refine ⟨4334863899843782487279137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11559637066250086632744365 4334863899843782487279137)
            ·
              refine ⟨3251147924882836865459353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4334863899843782487279137 3251147924882836865459353)
              ·
                refine ⟨2438360943662127649094515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251147924882836865459353 2438360943662127649094515)
                ·
                  refine ⟨3657541415493191473641773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438360943662127649094515 3657541415493191473641773)
                  ·
                    refine ⟨1371578030809946802615665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657541415493191473641773 1371578030809946802615665)
                    ·
                      refine ⟨1028683523107460101961749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371578030809946802615665 1028683523107460101961749)
                      ·
                        rfl

theorem cell23_2003354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_2003354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003354 prefixEnd_2003354 := by exact prefixLift 2003354
  have htrace : WordTrace (prefixWord ++ tailWord_2003354) baseStart_2003354 baseEnd_2003354 := by
    simpa [prefixWord, tailWord_2003354, baseEnd_2003354] using wordTrace_append hprefix tailTrace_2003354
  have hstable : (prefixWord ++ tailWord_2003354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003354).length < 2 ^ (prefixWord ++ tailWord_2003354).sum := by decide
  have hdescent : baseEnd_2003354 < baseStart_2003354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003390 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_2003390 : Nat := 118140960795 + 2003390 * 2 ^ 59
def prefixEnd_2003390 : Nat := 4983230072969 + 3 ^ 40 * 2003390 * 2
def baseEnd_2003390 : Nat := 114300223156780217901287

theorem tailTrace_2003390 : CollatzResearch.WordTrace tailWord_2003390 prefixEnd_2003390 114300223156780217901287 := by
  unfold tailWord_2003390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133704526508457077126953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48713090808045104411343749 9133704526508457077126953)
  ·
    refine ⟨6850278394881342807845215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9133704526508457077126953 6850278394881342807845215)
    ·
      refine ⟨10275417592322014211767823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850278394881342807845215 10275417592322014211767823)
      ·
        refine ⟨15413126388483021317651735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275417592322014211767823 15413126388483021317651735)
        ·
          refine ⟨23119689582724531976477603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15413126388483021317651735 23119689582724531976477603)
          ·
            refine ⟨34679534374086797964716405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23119689582724531976477603 34679534374086797964716405)
            ·
              refine ⟨3251206347570637309192163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34679534374086797964716405 3251206347570637309192163)
              ·
                refine ⟨4876809521355955963788245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251206347570637309192163 4876809521355955963788245)
                ·
                  refine ⟨114300223156780217901287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4876809521355955963788245 114300223156780217901287)
                  ·
                    rfl

theorem cell23_2003390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_2003390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003390 prefixEnd_2003390 := by exact prefixLift 2003390
  have htrace : WordTrace (prefixWord ++ tailWord_2003390) baseStart_2003390 baseEnd_2003390 := by
    simpa [prefixWord, tailWord_2003390, baseEnd_2003390] using wordTrace_append hprefix tailTrace_2003390
  have hstable : (prefixWord ++ tailWord_2003390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003390).length < 2 ^ (prefixWord ++ tailWord_2003390).sum := by decide
  have hdescent : baseEnd_2003390 < baseStart_2003390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003403 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 6, 5]
def baseStart_2003403 : Nat := 118140960795 + 2003403 * 2 ^ 59
def prefixEnd_2003403 : Nat := 4983230072969 + 3 ^ 40 * 2003403 * 2
def baseEnd_2003403 : Nat := 342902894553176803416341

theorem tailTrace_2003403 : CollatzResearch.WordTrace tailWord_2003403 prefixEnd_2003403 342902894553176803416341 := by
  unfold tailWord_2003403
  simp only [CollatzResearch.WordTrace]
  refine ⟨73070110361020559837238863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48713406907347039891492575 73070110361020559837238863)
  ·
    refine ⟨109605165541530839755858295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73070110361020559837238863 109605165541530839755858295)
    ·
      refine ⟨164407748312296259633787443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109605165541530839755858295 164407748312296259633787443)
      ·
        refine ⟨246611622468444389450681165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164407748312296259633787443 246611622468444389450681165)
        ·
          refine ⟨92479358425666646044005437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246611622468444389450681165 92479358425666646044005437)
          ·
            refine ⟨34679759409624992266502039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92479358425666646044005437 34679759409624992266502039)
            ·
              refine ⟨52019639114437488399753059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34679759409624992266502039 52019639114437488399753059)
              ·
                refine ⟨78029458671656232599629589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52019639114437488399753059 78029458671656232599629589)
                ·
                  refine ⟨3657630875233885903107637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78029458671656232599629589 3657630875233885903107637)
                  ·
                    refine ⟨342902894553176803416341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3657630875233885903107637 342902894553176803416341)
                    ·
                      rfl

theorem cell23_2003403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 5].length) (baseStart_2003403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003403 prefixEnd_2003403 := by exact prefixLift 2003403
  have htrace : WordTrace (prefixWord ++ tailWord_2003403) baseStart_2003403 baseEnd_2003403 := by
    simpa [prefixWord, tailWord_2003403, baseEnd_2003403] using wordTrace_append hprefix tailTrace_2003403
  have hstable : (prefixWord ++ tailWord_2003403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003403).length < 2 ^ (prefixWord ++ tailWord_2003403).sum := by decide
  have hdescent : baseEnd_2003403 < baseStart_2003403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003437 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2003437 : Nat := 118140960795 + 2003437 * 2 ^ 59
def prefixEnd_2003437 : Nat := 4983230072969 + 3 ^ 40 * 2003437 * 2
def baseEnd_2003437 : Nat := 342908714000594425741289

theorem tailTrace_2003437 : CollatzResearch.WordTrace tailWord_2003437 prefixEnd_2003437 342908714000594425741289 := by
  unfold tailWord_2003437
  simp only [CollatzResearch.WordTrace]
  refine ⟨73071350442897383643976565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48714233628598255762651043 73071350442897383643976565)
  ·
    refine ⟨6850439104021629716622803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73071350442897383643976565 6850439104021629716622803)
    ·
      refine ⟨10275658656032444574934205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850439104021629716622803 10275658656032444574934205)
      ·
        refine ⟨3853371996012166715600327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10275658656032444574934205 3853371996012166715600327)
        ·
          refine ⟨5780057994018250073400491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3853371996012166715600327 5780057994018250073400491)
          ·
            refine ⟨8670086991027375110100737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780057994018250073400491 8670086991027375110100737)
            ·
              refine ⟨6502565243270531332575553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8670086991027375110100737 6502565243270531332575553)
              ·
                refine ⟨4876923932452898499431665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502565243270531332575553 4876923932452898499431665)
                ·
                  refine ⟨3657692949339673874573749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876923932452898499431665 3657692949339673874573749)
                  ·
                    refine ⟨342908714000594425741289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3657692949339673874573749 342908714000594425741289)
                    ·
                      rfl

theorem cell23_2003437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2003437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003437 prefixEnd_2003437 := by exact prefixLift 2003437
  have htrace : WordTrace (prefixWord ++ tailWord_2003437) baseStart_2003437 baseEnd_2003437 := by
    simpa [prefixWord, tailWord_2003437, baseEnd_2003437] using wordTrace_append hprefix tailTrace_2003437
  have hstable : (prefixWord ++ tailWord_2003437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003437).length < 2 ^ (prefixWord ++ tailWord_2003437).sum := by decide
  have hdescent : baseEnd_2003437 < baseStart_2003437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003440 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_2003440 : Nat := 118140960795 + 2003440 * 2 ^ 59
def prefixEnd_2003440 : Nat := 4983230072969 + 3 ^ 40 * 2003440 * 2
def baseEnd_2003440 : Nat := 1028727682443746765486353

theorem tailTrace_2003440 : CollatzResearch.WordTrace tailWord_2003440 prefixEnd_2003440 1028727682443746765486353 := by
  unfold tailWord_2003440
  simp only [CollatzResearch.WordTrace]
  refine ⟨36535729930943257578167887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48714306574591010104223849 36535729930943257578167887)
  ·
    refine ⟨54803594896414886367251831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36535729930943257578167887 54803594896414886367251831)
    ·
      refine ⟨82205392344622329550877747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54803594896414886367251831 82205392344622329550877747)
      ·
        refine ⟨123308088516933494326316621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82205392344622329550877747 123308088516933494326316621)
        ·
          refine ⟨46240533193850060372368733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123308088516933494326316621 46240533193850060372368733)
          ·
            refine ⟨17340199947693772639638275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46240533193850060372368733 17340199947693772639638275)
            ·
              refine ⟨26010299921540658959457413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17340199947693772639638275 26010299921540658959457413)
              ·
                refine ⟨4876931235288873554898265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26010299921540658959457413 4876931235288873554898265)
                ·
                  refine ⟨3657698426466655166173699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876931235288873554898265 3657698426466655166173699)
                  ·
                    refine ⟨5486547639699982749260549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3657698426466655166173699 5486547639699982749260549)
                    ·
                      refine ⟨1028727682443746765486353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5486547639699982749260549 1028727682443746765486353)
                      ·
                        rfl

theorem cell23_2003440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_2003440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003440 prefixEnd_2003440 := by exact prefixLift 2003440
  have htrace : WordTrace (prefixWord ++ tailWord_2003440) baseStart_2003440 baseEnd_2003440 := by
    simpa [prefixWord, tailWord_2003440, baseEnd_2003440] using wordTrace_append hprefix tailTrace_2003440
  have hstable : (prefixWord ++ tailWord_2003440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003440).length < 2 ^ (prefixWord ++ tailWord_2003440).sum := by decide
  have hdescent : baseEnd_2003440 < baseStart_2003440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003443 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 5]
def baseStart_2003443 : Nat := 118140960795 + 2003443 * 2 ^ 59
def prefixEnd_2003443 : Nat := 4983230072969 + 3 ^ 40 * 2003443 * 2
def baseEnd_2003443 : Nat := 1028729222885710253748839

theorem tailTrace_2003443 : CollatzResearch.WordTrace tailWord_2003443 prefixEnd_2003443 1028729222885710253748839 := by
  unfold tailWord_2003443
  simp only [CollatzResearch.WordTrace]
  refine ⟨73071569280875646668694983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48714379520583764445796655 73071569280875646668694983)
  ·
    refine ⟨109607353921313470003042475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73071569280875646668694983 109607353921313470003042475)
    ·
      refine ⟨164411030881970205004563713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109607353921313470003042475 164411030881970205004563713)
      ·
        refine ⟨123308273161477653753422785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164411030881970205004563713 123308273161477653753422785)
        ·
          refine ⟨92481204871108240315067089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123308273161477653753422785 92481204871108240315067089)
          ·
            refine ⟨69360903653331180236300317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92481204871108240315067089 69360903653331180236300317)
            ·
              refine ⟨26010338869999192588612619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69360903653331180236300317 26010338869999192588612619)
              ·
                refine ⟨39015508304998788882918929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26010338869999192588612619 39015508304998788882918929)
                ·
                  refine ⟨29261631228749091662189197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39015508304998788882918929 29261631228749091662189197)
                  ·
                    refine ⟨10973111710780909373320949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29261631228749091662189197 10973111710780909373320949)
                    ·
                      refine ⟨1028729222885710253748839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10973111710780909373320949 1028729222885710253748839)
                      ·
                        rfl

theorem cell23_2003443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_2003443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003443 prefixEnd_2003443 := by exact prefixLift 2003443
  have htrace : WordTrace (prefixWord ++ tailWord_2003443) baseStart_2003443 baseEnd_2003443 := by
    simpa [prefixWord, tailWord_2003443, baseEnd_2003443] using wordTrace_append hprefix tailTrace_2003443
  have hstable : (prefixWord ++ tailWord_2003443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003443).length < 2 ^ (prefixWord ++ tailWord_2003443).sum := by decide
  have hdescent : baseEnd_2003443 < baseStart_2003443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003457 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_2003457 : Nat := 118140960795 + 2003457 * 2 ^ 59
def prefixEnd_2003457 : Nat := 4983230072969 + 3 ^ 40 * 2003457 * 2
def baseEnd_2003457 : Nat := 1028736411614873198973775

theorem tailTrace_2003457 : CollatzResearch.WordTrace tailWord_2003457 prefixEnd_2003457 1028736411614873198973775 := by
  unfold tailWord_2003457
  simp only [CollatzResearch.WordTrace]
  refine ⟨73072079902824927059704625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48714719935216618039803083 73072079902824927059704625)
  ·
    refine ⟨54804059927118695294778469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73072079902824927059704625 54804059927118695294778469)
    ·
      refine ⟨10275761236334755367770963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54804059927118695294778469 10275761236334755367770963)
      ·
        refine ⟨15413641854502133051656445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275761236334755367770963 15413641854502133051656445)
        ·
          refine ⟨5780115695438299894371167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15413641854502133051656445 5780115695438299894371167)
          ·
            refine ⟨8670173543157449841556751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780115695438299894371167 8670173543157449841556751)
            ·
              refine ⟨13005260314736174762335127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670173543157449841556751 13005260314736174762335127)
              ·
                refine ⟨19507890472104262143502691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13005260314736174762335127 19507890472104262143502691)
                ·
                  refine ⟨29261835708156393215254037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19507890472104262143502691 29261835708156393215254037)
                  ·
                    refine ⟨1371648548819830931965033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29261835708156393215254037 1371648548819830931965033)
                    ·
                      refine ⟨1028736411614873198973775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371648548819830931965033 1028736411614873198973775)
                      ·
                        rfl

theorem cell23_2003457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_2003457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003457 prefixEnd_2003457 := by exact prefixLift 2003457
  have htrace : WordTrace (prefixWord ++ tailWord_2003457) baseStart_2003457 baseEnd_2003457 := by
    simpa [prefixWord, tailWord_2003457, baseEnd_2003457] using wordTrace_append hprefix tailTrace_2003457
  have hstable : (prefixWord ++ tailWord_2003457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003457).length < 2 ^ (prefixWord ++ tailWord_2003457).sum := by decide
  have hdescent : baseEnd_2003457 < baseStart_2003457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003467 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 3, 4]
def baseStart_2003467 : Nat := 118140960795 + 2003467 * 2 ^ 59
def prefixEnd_2003467 : Nat := 4983230072969 + 3 ^ 40 * 2003467 * 2
def baseEnd_2003467 : Nat := 342913848807139386616243

theorem tailTrace_2003467 : CollatzResearch.WordTrace tailWord_2003467 prefixEnd_2003467 342913848807139386616243 := by
  unfold tailWord_2003467
  simp only [CollatzResearch.WordTrace]
  refine ⟨73072444632788698767568655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48714963088525799178379103 73072444632788698767568655)
  ·
    refine ⟨109608666949183048151352983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73072444632788698767568655 109608666949183048151352983)
    ·
      refine ⟨164413000423774572227029475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109608666949183048151352983 164413000423774572227029475)
      ·
        refine ⟨246619500635661858340544213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164413000423774572227029475 246619500635661858340544213)
        ·
          refine ⟨5780144546148324804856505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 246619500635661858340544213 5780144546148324804856505)
          ·
            refine ⟨4335108409611243603642379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5780144546148324804856505 4335108409611243603642379)
            ·
              refine ⟨6502662614416865405463569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335108409611243603642379 6502662614416865405463569)
              ·
                refine ⟨4876996960812649054097677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502662614416865405463569 4876996960812649054097677)
                ·
                  refine ⟨1828873860304743395286629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4876996960812649054097677 1828873860304743395286629)
                  ·
                    refine ⟨342913848807139386616243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1828873860304743395286629 342913848807139386616243)
                    ·
                      rfl

theorem cell23_2003467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 4].length) (baseStart_2003467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003467 prefixEnd_2003467 := by exact prefixLift 2003467
  have htrace : WordTrace (prefixWord ++ tailWord_2003467) baseStart_2003467 baseEnd_2003467 := by
    simpa [prefixWord, tailWord_2003467, baseEnd_2003467] using wordTrace_append hprefix tailTrace_2003467
  have hstable : (prefixWord ++ tailWord_2003467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003467).length < 2 ^ (prefixWord ++ tailWord_2003467).sum := by decide
  have hdescent : baseEnd_2003467 < baseStart_2003467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003483 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 6]
def baseStart_2003483 : Nat := 118140960795 + 2003483 * 2 ^ 59
def prefixEnd_2003483 : Nat := 4983230072969 + 3 ^ 40 * 2003483 * 2
def baseEnd_2003483 : Nat := 1028749762111890097248655

theorem tailTrace_2003483 : CollatzResearch.WordTrace tailWord_2003483 prefixEnd_2003483 1028749762111890097248655 := by
  unfold tailWord_2003483
  simp only [CollatzResearch.WordTrace]
  refine ⟨73073028200730733500151103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48715352133820489000100735 73073028200730733500151103)
  ·
    refine ⟨109609542301096100250226655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73073028200730733500151103 109609542301096100250226655)
    ·
      refine ⟨164414313451644150375339983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109609542301096100250226655 164414313451644150375339983)
      ·
        refine ⟨246621470177466225563009975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164414313451644150375339983 246621470177466225563009975)
        ·
          refine ⟨369932205266199338344514963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246621470177466225563009975 369932205266199338344514963)
          ·
            refine ⟨554898307899299007516772445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369932205266199338344514963 554898307899299007516772445)
            ·
              refine ⟨208086865462237127818789667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554898307899299007516772445 208086865462237127818789667)
              ·
                refine ⟨312130298193355691728184501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208086865462237127818789667 312130298193355691728184501)
                ·
                  refine ⟨29262215455627096099517297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312130298193355691728184501 29262215455627096099517297)
                  ·
                    refine ⟨21946661591720322074637973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29262215455627096099517297 21946661591720322074637973)
                    ·
                      refine ⟨1028749762111890097248655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21946661591720322074637973 1028749762111890097248655)
                      ·
                        rfl

theorem cell23_2003483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_2003483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003483 prefixEnd_2003483 := by exact prefixLift 2003483
  have htrace : WordTrace (prefixWord ++ tailWord_2003483) baseStart_2003483 baseEnd_2003483 := by
    simpa [prefixWord, tailWord_2003483, baseEnd_2003483] using wordTrace_append hprefix tailTrace_2003483
  have hstable : (prefixWord ++ tailWord_2003483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003483).length < 2 ^ (prefixWord ++ tailWord_2003483).sum := by decide
  have hdescent : baseEnd_2003483 < baseStart_2003483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003484 : List Nat := [2, 2, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_2003484 : Nat := 118140960795 + 2003484 * 2 ^ 59
def prefixEnd_2003484 : Nat := 4983230072969 + 3 ^ 40 * 2003484 * 2
def baseEnd_2003484 : Nat := 342916758530848197778717

theorem tailTrace_2003484 : CollatzResearch.WordTrace tailWord_2003484 prefixEnd_2003484 342916758530848197778717 := by
  unfold tailWord_2003484
  simp only [CollatzResearch.WordTrace]
  refine ⟨36536532336863555335468753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48715376449151407113958337 36536532336863555335468753)
  ·
    refine ⟨27402399252647666501601565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36536532336863555335468753 27402399252647666501601565)
    ·
      refine ⟨10275899719742874938100587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27402399252647666501601565 10275899719742874938100587)
      ·
        refine ⟨15413849579614312407150881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275899719742874938100587 15413849579614312407150881)
        ·
          refine ⟨11560387184710734305363161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15413849579614312407150881 11560387184710734305363161)
          ·
            refine ⟨8670290388533050729022371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11560387184710734305363161 8670290388533050729022371)
            ·
              refine ⟨13005435582799576093533557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670290388533050729022371 13005435582799576093533557)
              ·
                refine ⟨1219259585887460258768771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13005435582799576093533557 1219259585887460258768771)
                ·
                  refine ⟨1828889378831190388153157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219259585887460258768771 1828889378831190388153157)
                  ·
                    refine ⟨342916758530848197778717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1828889378831190388153157 342916758530848197778717)
                    ·
                      rfl

theorem cell23_2003484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_2003484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003484 prefixEnd_2003484 := by exact prefixLift 2003484
  have htrace : WordTrace (prefixWord ++ tailWord_2003484) baseStart_2003484 baseEnd_2003484 := by
    simpa [prefixWord, tailWord_2003484, baseEnd_2003484] using wordTrace_append hprefix tailTrace_2003484
  have hstable : (prefixWord ++ tailWord_2003484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003484).length < 2 ^ (prefixWord ++ tailWord_2003484).sum := by decide
  have hdescent : baseEnd_2003484 < baseStart_2003484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003527 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 1, 5]
def baseStart_2003527 : Nat := 118140960795 + 2003527 * 2 ^ 59
def prefixEnd_2003527 : Nat := 4983230072969 + 3 ^ 40 * 2003527 * 2
def baseEnd_2003527 : Nat := 342924118420229308366151

theorem tailTrace_2003527 : CollatzResearch.WordTrace tailWord_2003527 prefixEnd_2003527 342924118420229308366151 := by
  unfold tailWord_2003527
  simp only [CollatzResearch.WordTrace]
  refine ⟨73074633012571329014752835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48716422008380886009835223 73074633012571329014752835)
  ·
    refine ⟨109611949518856993522129253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73074633012571329014752835 109611949518856993522129253)
    ·
      refine ⟨20552240534785686285399235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109611949518856993522129253 20552240534785686285399235)
      ·
        refine ⟨30828360802178529428098853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20552240534785686285399235 30828360802178529428098853)
        ·
          refine ⟨5780317650408474267768535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30828360802178529428098853 5780317650408474267768535)
          ·
            refine ⟨8670476475612711401652803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780317650408474267768535 8670476475612711401652803)
            ·
              refine ⟨13005714713419067102479205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8670476475612711401652803 13005714713419067102479205)
              ·
                refine ⟨2438571508766075081714851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13005714713419067102479205 2438571508766075081714851)
                ·
                  refine ⟨3657857263149112622572277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438571508766075081714851 3657857263149112622572277)
                  ·
                    refine ⟨342924118420229308366151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3657857263149112622572277 342924118420229308366151)
                    ·
                      rfl

theorem cell23_2003527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_2003527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003527 prefixEnd_2003527 := by exact prefixLift 2003527
  have htrace : WordTrace (prefixWord ++ tailWord_2003527) baseStart_2003527 baseEnd_2003527 := by
    simpa [prefixWord, tailWord_2003527, baseEnd_2003527] using wordTrace_append hprefix tailTrace_2003527
  have hstable : (prefixWord ++ tailWord_2003527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003527).length < 2 ^ (prefixWord ++ tailWord_2003527).sum := by decide
  have hdescent : baseEnd_2003527 < baseStart_2003527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003541 : List Nat := [1, 3, 2, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_2003541 : Nat := 118140960795 + 2003541 * 2 ^ 59
def prefixEnd_2003541 : Nat := 4983230072969 + 3 ^ 40 * 2003541 * 2
def baseEnd_2003541 : Nat := 1028779543989850870323389

theorem tailTrace_2003541 : CollatzResearch.WordTrace tailWord_2003541 prefixEnd_2003541 1028779543989850870323389 := by
  unfold tailWord_2003541
  simp only [CollatzResearch.WordTrace]
  refine ⟨73075143634520609405762477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48716762423013739603841651 73075143634520609405762477)
  ·
    refine ⟨27403178862945228527160929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73075143634520609405762477 27403178862945228527160929)
    ·
      refine ⟨20552384147208921395370697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27403178862945228527160929 20552384147208921395370697)
      ·
        refine ⟨15414288110406691046528023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20552384147208921395370697 15414288110406691046528023)
        ·
          refine ⟨23121432165610036569792035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15414288110406691046528023 23121432165610036569792035)
          ·
            refine ⟨34682148248415054854688053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23121432165610036569792035 34682148248415054854688053)
            ·
              refine ⟨3251451398288911392627005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34682148248415054854688053 3251451398288911392627005)
              ·
                refine ⟨1219294274358341772235127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3251451398288911392627005 1219294274358341772235127)
                ·
                  refine ⟨1828941411537512658352691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219294274358341772235127 1828941411537512658352691)
                  ·
                    refine ⟨2743412117306268987529037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1828941411537512658352691 2743412117306268987529037)
                    ·
                      refine ⟨1028779543989850870323389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2743412117306268987529037 1028779543989850870323389)
                      ·
                        rfl

theorem cell23_2003541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_2003541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003541 prefixEnd_2003541 := by exact prefixLift 2003541
  have htrace : WordTrace (prefixWord ++ tailWord_2003541) baseStart_2003541 baseEnd_2003541 := by
    simpa [prefixWord, tailWord_2003541, baseEnd_2003541] using wordTrace_append hprefix tailTrace_2003541
  have hstable : (prefixWord ++ tailWord_2003541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003541).length < 2 ^ (prefixWord ++ tailWord_2003541).sum := by decide
  have hdescent : baseEnd_2003541 < baseStart_2003541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003581 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_2003581 : Nat := 118140960795 + 2003581 * 2 ^ 59
def prefixEnd_2003581 : Nat := 4983230072969 + 3 ^ 40 * 2003581 * 2
def baseEnd_2003581 : Nat := 1028800083216030713823205

theorem tailTrace_2003581 : CollatzResearch.WordTrace tailWord_2003581 prefixEnd_2003581 1028800083216030713823205 := by
  unfold tailWord_2003581
  simp only [CollatzResearch.WordTrace]
  refine ⟨73076602554375696237218597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48717735036250464158145731 73076602554375696237218597)
  ·
    refine ⟨13701862978945443044478487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73076602554375696237218597 13701862978945443044478487)
    ·
      refine ⟨20552794468418164566717731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13701862978945443044478487 20552794468418164566717731)
      ·
        refine ⟨30829191702627246850076597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20552794468418164566717731 30829191702627246850076597)
        ·
          refine ⟨2890236722121304392194681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30829191702627246850076597 2890236722121304392194681)
          ·
            refine ⟨2167677541590978294146011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2890236722121304392194681 2167677541590978294146011)
            ·
              refine ⟨3251516312386467441219017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167677541590978294146011 3251516312386467441219017)
              ·
                refine ⟨2438637234289850580914263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251516312386467441219017 2438637234289850580914263)
                ·
                  refine ⟨3657955851434775871371395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438637234289850580914263 3657955851434775871371395)
                  ·
                    refine ⟨5486933777152163807057093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3657955851434775871371395 5486933777152163807057093)
                    ·
                      refine ⟨1028800083216030713823205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5486933777152163807057093 1028800083216030713823205)
                      ·
                        rfl

theorem cell23_2003581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_2003581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003581 prefixEnd_2003581 := by exact prefixLift 2003581
  have htrace : WordTrace (prefixWord ++ tailWord_2003581) baseStart_2003581 baseEnd_2003581 := by
    simpa [prefixWord, tailWord_2003581, baseEnd_2003581] using wordTrace_append hprefix tailTrace_2003581
  have hstable : (prefixWord ++ tailWord_2003581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003581).length < 2 ^ (prefixWord ++ tailWord_2003581).sum := by decide
  have hdescent : baseEnd_2003581 < baseStart_2003581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003584 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 3]
def baseStart_2003584 : Nat := 118140960795 + 2003584 * 2 ^ 59
def prefixEnd_2003584 : Nat := 4983230072969 + 3 ^ 40 * 2003584 * 2
def baseEnd_2003584 : Nat := 1028801623657994202085691

theorem tailTrace_2003584 : CollatzResearch.WordTrace tailWord_2003584 prefixEnd_2003584 1028801623657994202085691 := by
  unfold tailWord_2003584
  simp only [CollatzResearch.WordTrace]
  refine ⟨36538355986682413874788903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48717807982243218499718537 36538355986682413874788903)
  ·
    refine ⟨54807533980023620812183355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36538355986682413874788903 54807533980023620812183355)
    ·
      refine ⟨82211300970035431218275033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54807533980023620812183355 82211300970035431218275033)
      ·
        refine ⟨61658475727526573413706275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82211300970035431218275033 61658475727526573413706275)
        ·
          refine ⟨92487713591289860120559413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61658475727526573413706275 92487713591289860120559413)
          ·
            refine ⟨8670723149183424386302445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92487713591289860120559413 8670723149183424386302445)
            ·
              refine ⟨3251521180943784144863417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8670723149183424386302445 3251521180943784144863417)
              ·
                refine ⟨2438640885707838108647563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251521180943784144863417 2438640885707838108647563)
                ·
                  refine ⟨3657961328561757162971345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438640885707838108647563 3657961328561757162971345)
                  ·
                    refine ⟨2743470996421317872228509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3657961328561757162971345 2743470996421317872228509)
                    ·
                      refine ⟨1028801623657994202085691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2743470996421317872228509 1028801623657994202085691)
                      ·
                        rfl

theorem cell23_2003584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_2003584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003584 prefixEnd_2003584 := by exact prefixLift 2003584
  have htrace : WordTrace (prefixWord ++ tailWord_2003584) baseStart_2003584 baseEnd_2003584 := by
    simpa [prefixWord, tailWord_2003584, baseEnd_2003584] using wordTrace_append hprefix tailTrace_2003584
  have hstable : (prefixWord ++ tailWord_2003584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003584).length < 2 ^ (prefixWord ++ tailWord_2003584).sum := by decide
  have hdescent : baseEnd_2003584 < baseStart_2003584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003594 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2003594 : Nat := 118140960795 + 2003594 * 2 ^ 59
def prefixEnd_2003594 : Nat := 4983230072969 + 3 ^ 40 * 2003594 * 2
def baseEnd_2003594 : Nat := 1028806758464539162960645

theorem tailTrace_2003594 : CollatzResearch.WordTrace tailWord_2003594 prefixEnd_2003594 1028806758464539162960645 := by
  unfold tailWord_2003594
  simp only [CollatzResearch.WordTrace]
  refine ⟨18269269175832149864360459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48718051135552399638294557 18269269175832149864360459)
  ·
    refine ⟨27403903763748224796540689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18269269175832149864360459 27403903763748224796540689)
    ·
      refine ⟨20552927822811168597405517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27403903763748224796540689 20552927822811168597405517)
      ·
        refine ⟨7707347933554188224027069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20552927822811168597405517 7707347933554188224027069)
        ·
          refine ⟨2890255475082820584010151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7707347933554188224027069 2890255475082820584010151)
          ·
            refine ⟨4335383212624230876015227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890255475082820584010151 4335383212624230876015227)
            ·
              refine ⟨6503074818936346314022841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335383212624230876015227 6503074818936346314022841)
              ·
                refine ⟨4877306114202259735517131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6503074818936346314022841 4877306114202259735517131)
                ·
                  refine ⟨7315959171303389603275697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877306114202259735517131 7315959171303389603275697)
                  ·
                    refine ⟨5486969378477542202456773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7315959171303389603275697 5486969378477542202456773)
                    ·
                      refine ⟨1028806758464539162960645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5486969378477542202456773 1028806758464539162960645)
                      ·
                        rfl

theorem cell23_2003594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2003594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003594 prefixEnd_2003594 := by exact prefixLift 2003594
  have htrace : WordTrace (prefixWord ++ tailWord_2003594) baseStart_2003594 baseEnd_2003594 := by
    simpa [prefixWord, tailWord_2003594, baseEnd_2003594] using wordTrace_append hprefix tailTrace_2003594
  have hstable : (prefixWord ++ tailWord_2003594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003594).length < 2 ^ (prefixWord ++ tailWord_2003594).sum := by decide
  have hdescent : baseEnd_2003594 < baseStart_2003594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003598 : List Nat := [4, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_2003598 : Nat := 118140960795 + 2003598 * 2 ^ 59
def prefixEnd_2003598 : Nat := 4983230072969 + 3 ^ 40 * 2003598 * 2
def baseEnd_2003598 : Nat := 1028808812387157147310627

theorem tailTrace_2003598 : CollatzResearch.WordTrace tailWord_2003598 prefixEnd_2003598 1028808812387157147310627 := by
  unfold tailWord_2003598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134652824414263517573431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48718148396876072093724965 9134652824414263517573431)
  ·
    refine ⟨13701979236621395276360147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9134652824414263517573431 13701979236621395276360147)
    ·
      refine ⟨20552968854932092914540221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13701979236621395276360147 20552968854932092914540221)
      ·
        refine ⟨7707363320599534842952583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20552968854932092914540221 7707363320599534842952583)
        ·
          refine ⟨11561044980899302264428875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7707363320599534842952583 11561044980899302264428875)
          ·
            refine ⟨17341567471348953396643313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11561044980899302264428875 17341567471348953396643313)
            ·
              refine ⟨13006175603511715047482485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17341567471348953396643313 13006175603511715047482485)
              ·
                refine ⟨1219328962829223285701483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13006175603511715047482485 1219328962829223285701483)
                ·
                  refine ⟨1828993444243834928552225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219328962829223285701483 1828993444243834928552225)
                  ·
                    refine ⟨1371745083182876196414169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1828993444243834928552225 1371745083182876196414169)
                    ·
                      refine ⟨1028808812387157147310627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371745083182876196414169 1028808812387157147310627)
                      ·
                        rfl

theorem cell23_2003598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_2003598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003598 prefixEnd_2003598 := by exact prefixLift 2003598
  have htrace : WordTrace (prefixWord ++ tailWord_2003598) baseStart_2003598 baseEnd_2003598 := by
    simpa [prefixWord, tailWord_2003598, baseEnd_2003598] using wordTrace_append hprefix tailTrace_2003598
  have hstable : (prefixWord ++ tailWord_2003598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003598).length < 2 ^ (prefixWord ++ tailWord_2003598).sum := by decide
  have hdescent : baseEnd_2003598 < baseStart_2003598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003614 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2003614 : Nat := 118140960795 + 2003614 * 2 ^ 59
def prefixEnd_2003614 : Nat := 4983230072969 + 3 ^ 40 * 2003614 * 2
def baseEnd_2003614 : Nat := 1028817028077629084710553

theorem tailTrace_2003614 : CollatzResearch.WordTrace tailWord_2003614 prefixEnd_2003614 1028817028077629084710553 := by
  unfold tailWord_2003614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134725770407017859146237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48718537442170761915446597 9134725770407017859146237)
  ·
    refine ⟨3425522163902631697179839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9134725770407017859146237 3425522163902631697179839)
    ·
      refine ⟨5138283245853947545769759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3425522163902631697179839 5138283245853947545769759)
      ·
        refine ⟨7707424868780921318654639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138283245853947545769759 7707424868780921318654639)
        ·
          refine ⟨11561137303171381977981959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7707424868780921318654639 11561137303171381977981959)
          ·
            refine ⟨17341705954757072966972939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11561137303171381977981959 17341705954757072966972939)
            ·
              refine ⟨26012558932135609450459409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17341705954757072966972939 26012558932135609450459409)
              ·
                refine ⟨19509419199101707087844557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26012558932135609450459409 19509419199101707087844557)
                ·
                  refine ⟨7316032199663140157941709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19509419199101707087844557 7316032199663140157941709)
                  ·
                    refine ⟨2743512074873677559228141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7316032199663140157941709 2743512074873677559228141)
                    ·
                      refine ⟨1028817028077629084710553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2743512074873677559228141 1028817028077629084710553)
                      ·
                        rfl

theorem cell23_2003614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2003614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003614 prefixEnd_2003614 := by exact prefixLift 2003614
  have htrace : WordTrace (prefixWord ++ tailWord_2003614) baseStart_2003614 baseEnd_2003614 := by
    simpa [prefixWord, tailWord_2003614, baseEnd_2003614] using wordTrace_append hprefix tailTrace_2003614
  have hstable : (prefixWord ++ tailWord_2003614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003614).length < 2 ^ (prefixWord ++ tailWord_2003614).sum := by decide
  have hdescent : baseEnd_2003614 < baseStart_2003614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003658 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_2003658 : Nat := 118140960795 + 2003658 * 2 ^ 59
def prefixEnd_2003658 : Nat := 4983230072969 + 3 ^ 40 * 2003658 * 2
def baseEnd_2003658 : Nat := 1028839621226426912560351

theorem tailTrace_2003658 : CollatzResearch.WordTrace tailWord_2003658 prefixEnd_2003658 1028839621226426912560351 := by
  unfold tailWord_2003658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18269852743774184596942907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48719607316731158925181085 18269852743774184596942907)
  ·
    refine ⟨27404779115661276895414361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18269852743774184596942907 27404779115661276895414361)
    ·
      refine ⟨20553584336745957671560771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27404779115661276895414361 20553584336745957671560771)
      ·
        refine ⟨30830376505118936507341157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20553584336745957671560771 30830376505118936507341157)
        ·
          refine ⟨5780695594709800595126467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30830376505118936507341157 5780695594709800595126467)
          ·
            refine ⟨8671043392064700892689701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780695594709800595126467 8671043392064700892689701)
            ·
              refine ⟨1625820636012131417379319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8671043392064700892689701 1625820636012131417379319)
              ·
                refine ⟨2438730954018197126068979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625820636012131417379319 2438730954018197126068979)
                ·
                  refine ⟨3658096431027295689103469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438730954018197126068979 3658096431027295689103469)
                  ·
                    refine ⟨1371786161635235883413801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658096431027295689103469 1371786161635235883413801)
                    ·
                      refine ⟨1028839621226426912560351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371786161635235883413801 1028839621226426912560351)
                      ·
                        rfl

theorem cell23_2003658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_2003658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003658 prefixEnd_2003658 := by exact prefixLift 2003658
  have htrace : WordTrace (prefixWord ++ tailWord_2003658) baseStart_2003658 baseEnd_2003658 := by
    simpa [prefixWord, tailWord_2003658, baseEnd_2003658] using wordTrace_append hprefix tailTrace_2003658
  have hstable : (prefixWord ++ tailWord_2003658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003658).length < 2 ^ (prefixWord ++ tailWord_2003658).sum := by decide
  have hdescent : baseEnd_2003658 < baseStart_2003658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003671 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 4, 2, 2]
def baseStart_2003671 : Nat := 118140960795 + 2003671 * 2 ^ 59
def prefixEnd_2003671 : Nat := 4983230072969 + 3 ^ 40 * 2003671 * 2
def baseEnd_2003671 : Nat := 1028846296474935361697791

theorem tailTrace_2003671 : CollatzResearch.WordTrace tailWord_2003671 prefixEnd_2003671 1028846296474935361697791 := by
  unfold tailWord_2003671
  simp only [CollatzResearch.WordTrace]
  refine ⟨73079885124049641607994867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48719923416033094405329911 73079885124049641607994867)
  ·
    refine ⟨109619827686074462411992301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73079885124049641607994867 109619827686074462411992301)
    ·
      refine ⟨41107435382277923404497113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109619827686074462411992301 41107435382277923404497113)
      ·
        refine ⟨30830576536708442553372835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41107435382277923404497113 30830576536708442553372835)
        ·
          refine ⟨46245864805062663830059253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30830576536708442553372835 46245864805062663830059253)
          ·
            refine ⟨4335549825474624734068055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46245864805062663830059253 4335549825474624734068055)
            ·
              refine ⟨6503324738211937101102083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335549825474624734068055 6503324738211937101102083)
              ·
                refine ⟨9754987107317905651653125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503324738211937101102083 9754987107317905651653125)
                ·
                  refine ⟨1829060082622107309684961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9754987107317905651653125 1829060082622107309684961)
                  ·
                    refine ⟨1371795061966580482263721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1829060082622107309684961 1371795061966580482263721)
                    ·
                      refine ⟨1028846296474935361697791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371795061966580482263721 1028846296474935361697791)
                      ·
                        rfl

theorem cell23_2003671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_2003671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003671 prefixEnd_2003671 := by exact prefixLift 2003671
  have htrace : WordTrace (prefixWord ++ tailWord_2003671) baseStart_2003671 baseEnd_2003671 := by
    simpa [prefixWord, tailWord_2003671, baseEnd_2003671] using wordTrace_append hprefix tailTrace_2003671
  have hstable : (prefixWord ++ tailWord_2003671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003671).length < 2 ^ (prefixWord ++ tailWord_2003671).sum := by decide
  have hdescent : baseEnd_2003671 < baseStart_2003671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003688 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_2003688 : Nat := 118140960795 + 2003688 * 2 ^ 59
def prefixEnd_2003688 : Nat := 4983230072969 + 3 ^ 40 * 2003688 * 2
def baseEnd_2003688 : Nat := 1028855025646061795185213

theorem tailTrace_2003688 : CollatzResearch.WordTrace tailWord_2003688 prefixEnd_2003688 1028855025646061795185213 := by
  unfold tailWord_2003688
  simp only [CollatzResearch.WordTrace]
  refine ⟨36540252582494026755681859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48720336776658702340909145 36540252582494026755681859)
  ·
    refine ⟨54810378873741040133522789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36540252582494026755681859 54810378873741040133522789)
    ·
      refine ⟨10276946038826445025035523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54810378873741040133522789 10276946038826445025035523)
      ·
        refine ⟨15415419058239667537553285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10276946038826445025035523 15415419058239667537553285)
        ·
          refine ⟨2890391073419937663291241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15415419058239667537553285 2890391073419937663291241)
          ·
            refine ⟨2167793305064953247468431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2890391073419937663291241 2167793305064953247468431)
            ·
              refine ⟨3251689957597429871202647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167793305064953247468431 3251689957597429871202647)
              ·
                refine ⟨4877534936396144806803971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251689957597429871202647 4877534936396144806803971)
                ·
                  refine ⟨7316302404594217210205957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877534936396144806803971 7316302404594217210205957)
                  ·
                    refine ⟨1371806700861415726913617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7316302404594217210205957 1371806700861415726913617)
                    ·
                      refine ⟨1028855025646061795185213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371806700861415726913617 1028855025646061795185213)
                      ·
                        rfl

theorem cell23_2003688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_2003688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003688 prefixEnd_2003688 := by exact prefixLift 2003688
  have htrace : WordTrace (prefixWord ++ tailWord_2003688) baseStart_2003688 baseEnd_2003688 := by
    simpa [prefixWord, tailWord_2003688, baseEnd_2003688] using wordTrace_append hprefix tailTrace_2003688
  have hstable : (prefixWord ++ tailWord_2003688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003688).length < 2 ^ (prefixWord ++ tailWord_2003688).sum := by decide
  have hdescent : baseEnd_2003688 < baseStart_2003688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003784 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 6]
def baseStart_2003784 : Nat := 118140960795 + 2003784 * 2 ^ 59
def prefixEnd_2003784 : Nat := 4983230072969 + 3 ^ 40 * 2003784 * 2
def baseEnd_2003784 : Nat := 114322702198765935509419

theorem tailTrace_2003784 : CollatzResearch.WordTrace tailWord_2003784 prefixEnd_2003784 114322702198765935509419 := by
  unfold tailWord_2003784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36542003286320130953429203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48722671048426841271238937 36542003286320130953429203)
  ·
    refine ⟨54813004929480196430143805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36542003286320130953429203 54813004929480196430143805)
    ·
      refine ⟨20554876848555073661303927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54813004929480196430143805 20554876848555073661303927)
      ·
        refine ⟨30832315272832610491955891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20554876848555073661303927 30832315272832610491955891)
        ·
          refine ⟨46248472909248915737933837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30832315272832610491955891 46248472909248915737933837)
          ·
            refine ⟨17343177340968343401725189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46248472909248915737933837 17343177340968343401725189)
            ·
              refine ⟨3251845751431564387823473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17343177340968343401725189 3251845751431564387823473)
              ·
                refine ⟨2438884313573673290867605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251845751431564387823473 2438884313573673290867605)
                ·
                  refine ⟨114322702198765935509419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2438884313573673290867605 114322702198765935509419)
                  ·
                    rfl

theorem cell23_2003784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 6].length) (baseStart_2003784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003784 prefixEnd_2003784 := by exact prefixLift 2003784
  have htrace : WordTrace (prefixWord ++ tailWord_2003784) baseStart_2003784 baseEnd_2003784 := by
    simpa [prefixWord, tailWord_2003784, baseEnd_2003784] using wordTrace_append hprefix tailTrace_2003784
  have hstable : (prefixWord ++ tailWord_2003784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003784).length < 2 ^ (prefixWord ++ tailWord_2003784).sum := by decide
  have hdescent : baseEnd_2003784 < baseStart_2003784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003788 : List Nat := [2, 2, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_2003788 : Nat := 118140960795 + 2003788 * 2 ^ 59
def prefixEnd_2003788 : Nat := 4983230072969 + 3 ^ 40 * 2003788 * 2
def baseEnd_2003788 : Nat := 342968791237170467978251

theorem tailTrace_2003788 : CollatzResearch.WordTrace tailWord_2003788 prefixEnd_2003788 342968791237170467978251 := by
  unfold tailWord_2003788
  simp only [CollatzResearch.WordTrace]
  refine ⟨36542076232312885295002009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48722768309750513726669345 36542076232312885295002009)
  ·
    refine ⟨27406557174234663971251507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36542076232312885295002009 27406557174234663971251507)
    ·
      refine ⟨41109835761351995956877261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27406557174234663971251507 41109835761351995956877261)
      ·
        refine ⟨15416188410506998483828973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41109835761351995956877261 15416188410506998483828973)
        ·
          refine ⟨5781070653940124431435865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15416188410506998483828973 5781070653940124431435865)
          ·
            refine ⟨4335802990455093323576899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781070653940124431435865 4335802990455093323576899)
            ·
              refine ⟨6503704485682639985365349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335802990455093323576899 6503704485682639985365349)
              ·
                refine ⟨1219444591065494997256003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6503704485682639985365349 1219444591065494997256003)
                ·
                  refine ⟨1829166886598242495884005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219444591065494997256003 1829166886598242495884005)
                  ·
                    refine ⟨342968791237170467978251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1829166886598242495884005 342968791237170467978251)
                    ·
                      rfl

theorem cell23_2003788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_2003788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003788 prefixEnd_2003788 := by exact prefixLift 2003788
  have htrace : WordTrace (prefixWord ++ tailWord_2003788) baseStart_2003788 baseEnd_2003788 := by
    simpa [prefixWord, tailWord_2003788, baseEnd_2003788] using wordTrace_append hprefix tailTrace_2003788
  have hstable : (prefixWord ++ tailWord_2003788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003788).length < 2 ^ (prefixWord ++ tailWord_2003788).sum := by decide
  have hdescent : baseEnd_2003788 < baseStart_2003788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003807 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_2003807 : Nat := 118140960795 + 2003807 * 2 ^ 59
def prefixEnd_2003807 : Nat := 4983230072969 + 3 ^ 40 * 2003807 * 2
def baseEnd_2003807 : Nat := 1028916129843946829597165

theorem tailTrace_2003807 : CollatzResearch.WordTrace tailWord_2003807 prefixEnd_2003807 1028916129843946829597165 := by
  unfold tailWord_2003807
  simp only [CollatzResearch.WordTrace]
  refine ⟨73084845451556936834945675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48723230301037957889963783 73084845451556936834945675)
  ·
    refine ⟨109627268177335405252418513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73084845451556936834945675 109627268177335405252418513)
    ·
      refine ⟨82220451133001553939313885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109627268177335405252418513 82220451133001553939313885)
      ·
        refine ⟨30832669174875582727242707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82220451133001553939313885 30832669174875582727242707)
        ·
          refine ⟨46249003762313374090864061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30832669174875582727242707 46249003762313374090864061)
          ·
            refine ⟨17343376410867515284074023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46249003762313374090864061 17343376410867515284074023)
            ·
              refine ⟨26015064616301272926111035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17343376410867515284074023 26015064616301272926111035)
              ·
                refine ⟨39022596924451909389166553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26015064616301272926111035 39022596924451909389166553)
                ·
                  refine ⟨29266947693338932041874915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39022596924451909389166553 29266947693338932041874915)
                  ·
                    refine ⟨43900421540008398062812373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29266947693338932041874915 43900421540008398062812373)
                    ·
                      refine ⟨1028916129843946829597165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43900421540008398062812373 1028916129843946829597165)
                      ·
                        rfl

theorem cell23_2003807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_2003807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003807 prefixEnd_2003807 := by exact prefixLift 2003807
  have htrace : WordTrace (prefixWord ++ tailWord_2003807) baseStart_2003807 baseEnd_2003807 := by
    simpa [prefixWord, tailWord_2003807, baseEnd_2003807] using wordTrace_append hprefix tailTrace_2003807
  have hstable : (prefixWord ++ tailWord_2003807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003807).length < 2 ^ (prefixWord ++ tailWord_2003807).sum := by decide
  have hdescent : baseEnd_2003807 < baseStart_2003807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003811 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 3]
def baseStart_2003811 : Nat := 118140960795 + 2003811 * 2 ^ 59
def prefixEnd_2003811 : Nat := 4983230072969 + 3 ^ 40 * 2003811 * 2
def baseEnd_2003811 : Nat := 1028918183766564813947147

theorem tailTrace_2003811 : CollatzResearch.WordTrace tailWord_2003811 prefixEnd_2003811 1028918183766564813947147 := by
  unfold tailWord_2003811
  simp only [CollatzResearch.WordTrace]
  refine ⟨73084991343542445518091287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48723327562361630345394191 73084991343542445518091287)
  ·
    refine ⟨109627487015313668277136931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73084991343542445518091287 109627487015313668277136931)
    ·
      refine ⟨164441230522970502415705397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109627487015313668277136931 164441230522970502415705397)
      ·
        refine ⟨15416365361528484601472381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164441230522970502415705397 15416365361528484601472381)
        ·
          refine ⟨5781137010573181725552143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15416365361528484601472381 5781137010573181725552143)
          ·
            refine ⟨8671705515859772588328215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781137010573181725552143 8671705515859772588328215)
            ·
              refine ⟨13007558273789658882492323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8671705515859772588328215 13007558273789658882492323)
              ·
                refine ⟨19511337410684488323738485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13007558273789658882492323 19511337410684488323738485)
                ·
                  refine ⟨1829187882251670780350483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19511337410684488323738485 1829187882251670780350483)
                  ·
                    refine ⟨2743781823377506170525725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829187882251670780350483 2743781823377506170525725)
                    ·
                      refine ⟨1028918183766564813947147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2743781823377506170525725 1028918183766564813947147)
                      ·
                        rfl

theorem cell23_2003811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_2003811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003811 prefixEnd_2003811 := by exact prefixLift 2003811
  have htrace : WordTrace (prefixWord ++ tailWord_2003811) baseStart_2003811 baseEnd_2003811 := by
    simpa [prefixWord, tailWord_2003811, baseEnd_2003811] using wordTrace_append hprefix tailTrace_2003811
  have hstable : (prefixWord ++ tailWord_2003811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003811).length < 2 ^ (prefixWord ++ tailWord_2003811).sum := by decide
  have hdescent : baseEnd_2003811 < baseStart_2003811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003857 : List Nat := [1, 2, 2, 1, 1, 1, 3, 12]
def baseStart_2003857 : Nat := 118140960795 + 2003857 * 2 ^ 59
def prefixEnd_2003857 : Nat := 4983230072969 + 3 ^ 40 * 2003857 * 2
def baseEnd_2003857 : Nat := 38108955699135986443405

theorem tailTrace_2003857 : CollatzResearch.WordTrace tailWord_2003857 prefixEnd_2003857 38108955699135986443405 := by
  unfold tailWord_2003857
  simp only [CollatzResearch.WordTrace]
  refine ⟨73086669101375795374265825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48724446067583863582843883 73086669101375795374265825)
  ·
    refine ⟨54815001826031846530699369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73086669101375795374265825 54815001826031846530699369)
    ·
      refine ⟨41111251369523884898024527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54815001826031846530699369 41111251369523884898024527)
      ·
        refine ⟨61666877054285827347036791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41111251369523884898024527 61666877054285827347036791)
        ·
          refine ⟨92500315581428741020555187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61666877054285827347036791 92500315581428741020555187)
          ·
            refine ⟨138750473372143111530832781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92500315581428741020555187 138750473372143111530832781)
            ·
              refine ⟨52031427514553666824062293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138750473372143111530832781 52031427514553666824062293)
              ·
                refine ⟨38108955699135986443405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 52031427514553666824062293 38108955699135986443405)
                ·
                  rfl

theorem cell23_2003857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 12].length) (baseStart_2003857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003857 prefixEnd_2003857 := by exact prefixLift 2003857
  have htrace : WordTrace (prefixWord ++ tailWord_2003857) baseStart_2003857 baseEnd_2003857 := by
    simpa [prefixWord, tailWord_2003857, baseEnd_2003857] using wordTrace_append hprefix tailTrace_2003857
  have hstable : (prefixWord ++ tailWord_2003857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003857).length < 2 ^ (prefixWord ++ tailWord_2003857).sum := by decide
  have hdescent : baseEnd_2003857 < baseStart_2003857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003861 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_2003861 : Nat := 118140960795 + 2003861 * 2 ^ 59
def prefixEnd_2003861 : Nat := 4983230072969 + 3 ^ 40 * 2003861 * 2
def baseEnd_2003861 : Nat := 342981285933096539440639

theorem tailTrace_2003861 : CollatzResearch.WordTrace tailWord_2003861 prefixEnd_2003861 342981285933096539440639 := by
  unfold tailWord_2003861
  simp only [CollatzResearch.WordTrace]
  refine ⟨73086814993361304057411437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48724543328907536038274291 73086814993361304057411437)
  ·
    refine ⟨27407555622510489021529289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73086814993361304057411437 27407555622510489021529289)
    ·
      refine ⟨20555666716882866766146967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27407555622510489021529289 20555666716882866766146967)
      ·
        refine ⟨30833500075324300149220451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20555666716882866766146967 30833500075324300149220451)
        ·
          refine ⟨46250250112986450223830677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30833500075324300149220451 46250250112986450223830677)
          ·
            refine ⟨2167980474046239854242063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46250250112986450223830677 2167980474046239854242063)
            ·
              refine ⟨3251970711069359781363095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167980474046239854242063 3251970711069359781363095)
              ·
                refine ⟨4877956066604039672044643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251970711069359781363095 4877956066604039672044643)
                ·
                  refine ⟨7316934099906059508066965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4877956066604039672044643 7316934099906059508066965)
                  ·
                    refine ⟨342981285933096539440639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7316934099906059508066965 342981285933096539440639)
                    ·
                      rfl

theorem cell23_2003861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_2003861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003861 prefixEnd_2003861 := by exact prefixLift 2003861
  have htrace : WordTrace (prefixWord ++ tailWord_2003861) baseStart_2003861 baseEnd_2003861 := by
    simpa [prefixWord, tailWord_2003861, baseEnd_2003861] using wordTrace_append hprefix tailTrace_2003861
  have hstable : (prefixWord ++ tailWord_2003861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003861).length < 2 ^ (prefixWord ++ tailWord_2003861).sum := by decide
  have hdescent : baseEnd_2003861 < baseStart_2003861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003862 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2003862 : Nat := 118140960795 + 2003862 * 2 ^ 59
def prefixEnd_2003862 : Nat := 4983230072969 + 3 ^ 40 * 2003862 * 2
def baseEnd_2003862 : Nat := 1028944371279944114409413

theorem tailTrace_2003862 : CollatzResearch.WordTrace tailWord_2003862 prefixEnd_2003862 1028944371279944114409413 := by
  unfold tailWord_2003862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567928216647355076762365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48724567644238454152131893 4567928216647355076762365)
  ·
    refine ⟨1712973081242758153785887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4567928216647355076762365 1712973081242758153785887)
    ·
      refine ⟨2569459621864137230678831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1712973081242758153785887 2569459621864137230678831)
      ·
        refine ⟨3854189432796205846018247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569459621864137230678831 3854189432796205846018247)
        ·
          refine ⟨5781284149194308769027371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854189432796205846018247 5781284149194308769027371)
          ·
            refine ⟨8671926223791463153541057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781284149194308769027371 8671926223791463153541057)
            ·
              refine ⟨6503944667843597365155793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8671926223791463153541057 6503944667843597365155793)
              ·
                refine ⟨4877958500882698023866845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6503944667843597365155793 4877958500882698023866845)
                ·
                  refine ⟨1829234437831011758950067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4877958500882698023866845 1829234437831011758950067)
                  ·
                    refine ⟨2743851656746517638425101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829234437831011758950067 2743851656746517638425101)
                    ·
                      refine ⟨1028944371279944114409413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2743851656746517638425101 1028944371279944114409413)
                      ·
                        rfl

theorem cell23_2003862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2003862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003862 prefixEnd_2003862 := by exact prefixLift 2003862
  have htrace : WordTrace (prefixWord ++ tailWord_2003862) baseStart_2003862 baseEnd_2003862 := by
    simpa [prefixWord, tailWord_2003862, baseEnd_2003862] using wordTrace_append hprefix tailTrace_2003862
  have hstable : (prefixWord ++ tailWord_2003862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003862).length < 2 ^ (prefixWord ++ tailWord_2003862).sum := by decide
  have hdescent : baseEnd_2003862 < baseStart_2003862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003879 : List Nat := [1, 1, 6, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_2003879 : Nat := 118140960795 + 2003879 * 2 ^ 59
def prefixEnd_2003879 : Nat := 4983230072969 + 3 ^ 40 * 2003879 * 2
def baseEnd_2003879 : Nat := 1028953100451070547896835

theorem tailTrace_2003879 : CollatzResearch.WordTrace tailWord_2003879 prefixEnd_2003879 1028953100451070547896835 := by
  unfold tailWord_2003879
  simp only [CollatzResearch.WordTrace]
  refine ⟨73087471507296093131566691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48724981004864062087711127 73087471507296093131566691)
  ·
    refine ⟨109631207260944139697350037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73087471507296093131566691 109631207260944139697350037)
    ·
      refine ⟨5138962840356756548313283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 109631207260944139697350037 5138962840356756548313283)
      ·
        refine ⟨7708444260535134822469925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138962840356756548313283 7708444260535134822469925)
        ·
          refine ⟨1445333298850337779213111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7708444260535134822469925 1445333298850337779213111)
          ·
            refine ⟨2167999948275506668819667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445333298850337779213111 2167999948275506668819667)
            ·
              refine ⟨3251999922413260003229501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167999948275506668819667 3251999922413260003229501)
              ·
                refine ⟨1219499970904972501211063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3251999922413260003229501 1219499970904972501211063)
                ·
                  refine ⟨1829249956357458751816595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219499970904972501211063 1829249956357458751816595)
                  ·
                    refine ⟨2743874934536188127724893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829249956357458751816595 2743874934536188127724893)
                    ·
                      refine ⟨1028953100451070547896835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2743874934536188127724893 1028953100451070547896835)
                      ·
                        rfl

theorem cell23_2003879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_2003879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003879 prefixEnd_2003879 := by exact prefixLift 2003879
  have htrace : WordTrace (prefixWord ++ tailWord_2003879) baseStart_2003879 baseEnd_2003879 := by
    simpa [prefixWord, tailWord_2003879, baseEnd_2003879] using wordTrace_append hprefix tailTrace_2003879
  have hstable : (prefixWord ++ tailWord_2003879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003879).length < 2 ^ (prefixWord ++ tailWord_2003879).sum := by decide
  have hdescent : baseEnd_2003879 < baseStart_2003879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003908 : List Nat := [2, 3, 3, 3, 1, 1, 2, 8]
def baseStart_2003908 : Nat := 118140960795 + 2003908 * 2 ^ 59
def prefixEnd_2003908 : Nat := 4983230072969 + 3 ^ 40 * 2003908 * 2
def baseEnd_2003908 : Nat := 38109925607038923497563

theorem tailTrace_2003908 : CollatzResearch.WordTrace tailWord_2003908 prefixEnd_2003908 38109925607038923497563 := by
  unfold tailWord_2003908
  simp only [CollatzResearch.WordTrace]
  refine ⟨36544264612095515542186189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48725686149460687389581585 36544264612095515542186189)
  ·
    refine ⟨13704099229535818328319821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36544264612095515542186189 13704099229535818328319821)
    ·
      refine ⟨5139037211075931873119933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13704099229535818328319821 5139037211075931873119933)
      ·
        refine ⟨1927138954153474452419975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5139037211075931873119933 1927138954153474452419975)
        ·
          refine ⟨2890708431230211678629963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927138954153474452419975 2890708431230211678629963)
          ·
            refine ⟨4336062646845317517944945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890708431230211678629963 4336062646845317517944945)
            ·
              refine ⟨3252046985133988138458709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4336062646845317517944945 3252046985133988138458709)
              ·
                refine ⟨38109925607038923497563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3252046985133988138458709 38109925607038923497563)
                ·
                  rfl

theorem cell23_2003908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 8].length) (baseStart_2003908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003908 prefixEnd_2003908 := by exact prefixLift 2003908
  have htrace : WordTrace (prefixWord ++ tailWord_2003908) baseStart_2003908 baseEnd_2003908 := by
    simpa [prefixWord, tailWord_2003908, baseEnd_2003908] using wordTrace_append hprefix tailTrace_2003908
  have hstable : (prefixWord ++ tailWord_2003908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003908).length < 2 ^ (prefixWord ++ tailWord_2003908).sum := by decide
  have hdescent : baseEnd_2003908 < baseStart_2003908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003912 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 2, 4]
def baseStart_2003912 : Nat := 118140960795 + 2003912 * 2 ^ 59
def prefixEnd_2003912 : Nat := 4983230072969 + 3 ^ 40 * 2003912 * 2
def baseEnd_2003912 : Nat := 342990015104222972928061

theorem tailTrace_2003912 : CollatzResearch.WordTrace tailWord_2003912 prefixEnd_2003912 342990015104222972928061 := by
  unfold tailWord_2003912
  simp only [CollatzResearch.WordTrace]
  refine ⟨36544337558088269883758995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48725783410784359845011993 36544337558088269883758995)
  ·
    refine ⟨54816506337132404825638493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36544337558088269883758995 54816506337132404825638493)
    ·
      refine ⟨20556189876424651809614435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54816506337132404825638493 20556189876424651809614435)
      ·
        refine ⟨30834284814636977714421653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20556189876424651809614435 30834284814636977714421653)
        ·
          refine ⟨1445357100686108330363515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30834284814636977714421653 1445357100686108330363515)
          ·
            refine ⟨2168035651029162495545273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445357100686108330363515 2168035651029162495545273)
            ·
              refine ⟨1626026738271871871658955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168035651029162495545273 1626026738271871871658955)
              ·
                refine ⟨2439040107407807807488433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626026738271871871658955 2439040107407807807488433)
                ·
                  refine ⟨1829280080555855855616325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2439040107407807807488433 1829280080555855855616325)
                  ·
                    refine ⟨342990015104222972928061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1829280080555855855616325 342990015104222972928061)
                    ·
                      rfl

theorem cell23_2003912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_2003912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003912 prefixEnd_2003912 := by exact prefixLift 2003912
  have htrace : WordTrace (prefixWord ++ tailWord_2003912) baseStart_2003912 baseEnd_2003912 := by
    simpa [prefixWord, tailWord_2003912, baseEnd_2003912] using wordTrace_append hprefix tailTrace_2003912
  have hstable : (prefixWord ++ tailWord_2003912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003912).length < 2 ^ (prefixWord ++ tailWord_2003912).sum := by decide
  have hdescent : baseEnd_2003912 < baseStart_2003912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003928 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 3, 3, 2]
def baseStart_2003928 : Nat := 118140960795 + 2003928 * 2 ^ 59
def prefixEnd_2003928 : Nat := 4983230072969 + 3 ^ 40 * 2003928 * 2
def baseEnd_2003928 : Nat := 1028978261003140856184109

theorem tailTrace_2003928 : CollatzResearch.WordTrace tailWord_2003928 prefixEnd_2003928 1028978261003140856184109 := by
  unfold tailWord_2003928
  simp only [CollatzResearch.WordTrace]
  refine ⟨36544629342059287250050219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48726172456079049666733625 36544629342059287250050219)
  ·
    refine ⟨54816944013088930875075329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36544629342059287250050219 54816944013088930875075329)
    ·
      refine ⟨41112708009816698156306497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54816944013088930875075329 41112708009816698156306497)
      ·
        refine ⟨30834531007362523617229873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41112708009816698156306497 30834531007362523617229873)
        ·
          refine ⟨23125898255521892712922405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30834531007362523617229873 23125898255521892712922405)
          ·
            refine ⟨4336105922910354883672951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23125898255521892712922405 4336105922910354883672951)
            ·
              refine ⟨6504158884365532325509427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336105922910354883672951 6504158884365532325509427)
              ·
                refine ⟨9756238326548298488264141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504158884365532325509427 9756238326548298488264141)
                ·
                  refine ⟨3658589372455611933099053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9756238326548298488264141 3658589372455611933099053)
                  ·
                    refine ⟨1371971014670854474912145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658589372455611933099053 1371971014670854474912145)
                    ·
                      refine ⟨1028978261003140856184109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1371971014670854474912145 1028978261003140856184109)
                      ·
                        rfl

theorem cell23_2003928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_2003928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003928 prefixEnd_2003928 := by exact prefixLift 2003928
  have htrace : WordTrace (prefixWord ++ tailWord_2003928) baseStart_2003928 baseEnd_2003928 := by
    simpa [prefixWord, tailWord_2003928, baseEnd_2003928] using wordTrace_append hprefix tailTrace_2003928
  have hstable : (prefixWord ++ tailWord_2003928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003928).length < 2 ^ (prefixWord ++ tailWord_2003928).sum := by decide
  have hdescent : baseEnd_2003928 < baseStart_2003928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2003975 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_2003975 : Nat := 118140960795 + 2003975 * 2 ^ 59
def prefixEnd_2003975 : Nat := 4983230072969 + 3 ^ 40 * 2003975 * 2
def baseEnd_2003975 : Nat := 1029002394593902172296393

theorem tailTrace_2003975 : CollatzResearch.WordTrace tailWord_2003975 prefixEnd_2003975 1029002394593902172296393 := by
  unfold tailWord_2003975
  simp only [CollatzResearch.WordTrace]
  refine ⟨73090972914948301527061379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48727315276632201018040919 73090972914948301527061379)
  ·
    refine ⟨109636459372422452290592069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73090972914948301527061379 109636459372422452290592069)
    ·
      refine ⟨20556836132329209804486013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109636459372422452290592069 20556836132329209804486013)
      ·
        refine ⟨7708813549623453676682255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20556836132329209804486013 7708813549623453676682255)
        ·
          refine ⟨11563220324435180515023383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7708813549623453676682255 11563220324435180515023383)
          ·
            refine ⟨17344830486652770772535075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563220324435180515023383 17344830486652770772535075)
            ·
              refine ⟨26017245729979156158802613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17344830486652770772535075 26017245729979156158802613)
              ·
                refine ⟨2439116787185545889887745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26017245729979156158802613 2439116787185545889887745)
                ·
                  refine ⟨1829337590389159417415809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2439116787185545889887745 1829337590389159417415809)
                  ·
                    refine ⟨1372003192791869563061857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1829337590389159417415809 1372003192791869563061857)
                    ·
                      refine ⟨1029002394593902172296393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372003192791869563061857 1029002394593902172296393)
                      ·
                        rfl

theorem cell23_2003975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_2003975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2003975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2003975 prefixEnd_2003975 := by exact prefixLift 2003975
  have htrace : WordTrace (prefixWord ++ tailWord_2003975) baseStart_2003975 baseEnd_2003975 := by
    simpa [prefixWord, tailWord_2003975, baseEnd_2003975] using wordTrace_append hprefix tailTrace_2003975
  have hstable : (prefixWord ++ tailWord_2003975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2003975).length < 2 ^ (prefixWord ++ tailWord_2003975).sum := by decide
  have hdescent : baseEnd_2003975 < baseStart_2003975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2003975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004041 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 5, 4]
def baseStart_2004041 : Nat := 118140960795 + 2004041 * 2 ^ 59
def prefixEnd_2004041 : Nat := 4983230072969 + 3 ^ 40 * 2004041 * 2
def baseEnd_2004041 : Nat := 343012094772366304690363

theorem tailTrace_2004041 : CollatzResearch.WordTrace tailWord_2004041 prefixEnd_2004041 343012094772366304690363 := by
  unfold tailWord_2004041
  simp only [CollatzResearch.WordTrace]
  refine ⟨73093380132709194798963977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48728920088472796532642651 73093380132709194798963977)
  ·
    refine ⟨54820035099531896099222983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73093380132709194798963977 54820035099531896099222983)
    ·
      refine ⟨82230052649297844148834475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54820035099531896099222983 82230052649297844148834475)
      ·
        refine ⟨123345078973946766223251713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82230052649297844148834475 123345078973946766223251713)
        ·
          refine ⟨92508809230460074667438785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123345078973946766223251713 92508809230460074667438785)
          ·
            refine ⟨69381606922845056000579089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92508809230460074667438785 69381606922845056000579089)
            ·
              refine ⟨52036205192133792000434317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69381606922845056000579089 52036205192133792000434317)
              ·
                refine ⟨19513576947050172000162869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52036205192133792000434317 19513576947050172000162869)
                ·
                  refine ⟨1829397838785953625015269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19513576947050172000162869 1829397838785953625015269)
                  ·
                    refine ⟨343012094772366304690363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1829397838785953625015269 343012094772366304690363)
                    ·
                      rfl

theorem cell23_2004041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 4].length) (baseStart_2004041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004041 prefixEnd_2004041 := by exact prefixLift 2004041
  have htrace : WordTrace (prefixWord ++ tailWord_2004041) baseStart_2004041 baseEnd_2004041 := by
    simpa [prefixWord, tailWord_2004041, baseEnd_2004041] using wordTrace_append hprefix tailTrace_2004041
  have hstable : (prefixWord ++ tailWord_2004041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004041).length < 2 ^ (prefixWord ++ tailWord_2004041).sum := by decide
  have hdescent : baseEnd_2004041 < baseStart_2004041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004062 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2004062 : Nat := 118140960795 + 2004062 * 2 ^ 59
def prefixEnd_2004062 : Nat := 4983230072969 + 3 ^ 40 * 2004062 * 2
def baseEnd_2004062 : Nat := 343015689136947777302831

theorem tailTrace_2004062 : CollatzResearch.WordTrace tailWord_2004062 prefixEnd_2004062 343015689136947777302831 := by
  unfold tailWord_2004062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136768258204139423184805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48729430710422076923652293 9136768258204139423184805)
  ·
    refine ⟨1713144048413276141847151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9136768258204139423184805 1713144048413276141847151)
    ·
      refine ⟨2569716072619914212770727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1713144048413276141847151 2569716072619914212770727)
      ·
        refine ⟨3854574108929871319156091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569716072619914212770727 3854574108929871319156091)
        ·
          refine ⟨5781861163394806978734137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854574108929871319156091 5781861163394806978734137)
          ·
            refine ⟨4336395872546105234050603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781861163394806978734137 4336395872546105234050603)
            ·
              refine ⟨6504593808819157851075905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336395872546105234050603 6504593808819157851075905)
              ·
                refine ⟨4878445356614368388306929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6504593808819157851075905 4878445356614368388306929)
                ·
                  refine ⟨3658834017460776291230197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4878445356614368388306929 3658834017460776291230197)
                  ·
                    refine ⟨343015689136947777302831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3658834017460776291230197 343015689136947777302831)
                    ·
                      rfl

theorem cell23_2004062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2004062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004062 prefixEnd_2004062 := by exact prefixLift 2004062
  have htrace : WordTrace (prefixWord ++ tailWord_2004062) baseStart_2004062 baseEnd_2004062 := by
    simpa [prefixWord, tailWord_2004062, baseEnd_2004062] using wordTrace_append hprefix tailTrace_2004062
  have hstable : (prefixWord ++ tailWord_2004062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004062).length < 2 ^ (prefixWord ++ tailWord_2004062).sum := by decide
  have hdescent : baseEnd_2004062 < baseStart_2004062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004071 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 8]
def baseStart_2004071 : Nat := 118140960795 + 2004071 * 2 ^ 59
def prefixEnd_2004071 : Nat := 4983230072969 + 3 ^ 40 * 2004071 * 2
def baseEnd_2004071 : Nat := 114339076526303755188439

theorem tailTrace_2004071 : CollatzResearch.WordTrace tailWord_2004071 prefixEnd_2004071 114339076526303755188439 := by
  unfold tailWord_2004071
  simp only [CollatzResearch.WordTrace]
  refine ⟨73094474322600509922556067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48729649548400339948370711 73094474322600509922556067)
  ·
    refine ⟨109641711483900764883834101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73094474322600509922556067 109641711483900764883834101)
    ·
      refine ⟨10278910451615696707859447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109641711483900764883834101 10278910451615696707859447)
      ·
        refine ⟨15418365677423545061789171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10278910451615696707859447 15418365677423545061789171)
        ·
          refine ⟨23127548516135317592683757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15418365677423545061789171 23127548516135317592683757)
          ·
            refine ⟨8672830693550744097256409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23127548516135317592683757 8672830693550744097256409)
            ·
              refine ⟨6504623020163058072942307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8672830693550744097256409 6504623020163058072942307)
              ·
                refine ⟨9756934530244587109413461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6504623020163058072942307 9756934530244587109413461)
                ·
                  refine ⟨114339076526303755188439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9756934530244587109413461 114339076526303755188439)
                  ·
                    rfl

theorem cell23_2004071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 8].length) (baseStart_2004071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004071 prefixEnd_2004071 := by exact prefixLift 2004071
  have htrace : WordTrace (prefixWord ++ tailWord_2004071) baseStart_2004071 baseEnd_2004071 := by
    simpa [prefixWord, tailWord_2004071, baseEnd_2004071] using wordTrace_append hprefix tailTrace_2004071
  have hstable : (prefixWord ++ tailWord_2004071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004071).length < 2 ^ (prefixWord ++ tailWord_2004071).sum := by decide
  have hdescent : baseEnd_2004071 < baseStart_2004071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004081 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_2004081 : Nat := 118140960795 + 2004081 * 2 ^ 59
def prefixEnd_2004081 : Nat := 4983230072969 + 3 ^ 40 * 2004081 * 2
def baseEnd_2004081 : Nat := 1029056823543278757570905

theorem tailTrace_2004081 : CollatzResearch.WordTrace tailWord_2004081 prefixEnd_2004081 1029056823543278757570905 := by
  unfold tailWord_2004081
  simp only [CollatzResearch.WordTrace]
  refine ⟨73094839052564281630420097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48729892701709521086946731 73094839052564281630420097)
  ·
    refine ⟨54821129289423211222815073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73094839052564281630420097 54821129289423211222815073)
    ·
      refine ⟨41115846967067408417111305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54821129289423211222815073 41115846967067408417111305)
      ·
        refine ⟨30836885225300556312833479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41115846967067408417111305 30836885225300556312833479)
        ·
          refine ⟨46255327837950834469250219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30836885225300556312833479 46255327837950834469250219)
          ·
            refine ⟨69382991756926251703875329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46255327837950834469250219 69382991756926251703875329)
            ·
              refine ⟨52037243817694688777906497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69382991756926251703875329 52037243817694688777906497)
              ·
                refine ⟨39027932863271016583429873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52037243817694688777906497 39027932863271016583429873)
                ·
                  refine ⟨29270949647453262437572405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39027932863271016583429873 29270949647453262437572405)
                  ·
                    refine ⟨2744151529448743353522413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29270949647453262437572405 2744151529448743353522413)
                    ·
                      refine ⟨1029056823543278757570905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2744151529448743353522413 1029056823543278757570905)
                      ·
                        rfl

theorem cell23_2004081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_2004081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004081 prefixEnd_2004081 := by exact prefixLift 2004081
  have htrace : WordTrace (prefixWord ++ tailWord_2004081) baseStart_2004081 baseEnd_2004081 := by
    simpa [prefixWord, tailWord_2004081, baseEnd_2004081] using wordTrace_append hprefix tailTrace_2004081
  have hstable : (prefixWord ++ tailWord_2004081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004081).length < 2 ^ (prefixWord ++ tailWord_2004081).sum := by decide
  have hdescent : baseEnd_2004081 < baseStart_2004081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004088 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 6]
def baseStart_2004088 : Nat := 118140960795 + 2004088 * 2 ^ 59
def prefixEnd_2004088 : Nat := 4983230072969 + 3 ^ 40 * 2004088 * 2
def baseEnd_2004088 : Nat := 114340046434206692242597

theorem tailTrace_2004088 : CollatzResearch.WordTrace tailWord_2004088 prefixEnd_2004088 114340046434206692242597 := by
  unfold tailWord_2004088
  simp only [CollatzResearch.WordTrace]
  refine ⟨36547547181769460912962459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48730062909025947883949945 36547547181769460912962459)
  ·
    refine ⟨54821320772654191369443689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36547547181769460912962459 54821320772654191369443689)
    ·
      refine ⟨41115990579490643527082767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54821320772654191369443689 41115990579490643527082767)
      ·
        refine ⟨61673985869235965290624151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41115990579490643527082767 61673985869235965290624151)
        ·
          refine ⟨92510978803853947935936227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61673985869235965290624151 92510978803853947935936227)
          ·
            refine ⟨138766468205780921903904341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92510978803853947935936227 138766468205780921903904341)
            ·
              refine ⟨1626169549286495178561379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 138766468205780921903904341 1626169549286495178561379)
              ·
                refine ⟨2439254323929742767842069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626169549286495178561379 2439254323929742767842069)
                ·
                  refine ⟨114340046434206692242597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2439254323929742767842069 114340046434206692242597)
                  ·
                    rfl

theorem cell23_2004088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 6].length) (baseStart_2004088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004088 prefixEnd_2004088 := by exact prefixLift 2004088
  have htrace : WordTrace (prefixWord ++ tailWord_2004088) baseStart_2004088 baseEnd_2004088 := by
    simpa [prefixWord, tailWord_2004088, baseEnd_2004088] using wordTrace_append hprefix tailTrace_2004088
  have hstable : (prefixWord ++ tailWord_2004088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004088).length < 2 ^ (prefixWord ++ tailWord_2004088).sum := by decide
  have hdescent : baseEnd_2004088 < baseStart_2004088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004108 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 1, 5, 2]
def baseStart_2004108 : Nat := 118140960795 + 2004108 * 2 ^ 59
def prefixEnd_2004108 : Nat := 4983230072969 + 3 ^ 40 * 2004108 * 2
def baseEnd_2004108 : Nat := 1029070687520950151933281

theorem tailTrace_2004108 : CollatzResearch.WordTrace tailWord_2004108 prefixEnd_2004108 1029070687520950151933281 := by
  unfold tailWord_2004108
  simp only [CollatzResearch.WordTrace]
  refine ⟨36547911911733232620826489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48730549215644310161101985 36547911911733232620826489)
  ·
    refine ⟨27410933933799924465619867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36547911911733232620826489 27410933933799924465619867)
    ·
      refine ⟨41116400900699886698429801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27410933933799924465619867 41116400900699886698429801)
      ·
        refine ⟨30837300675524915023822351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41116400900699886698429801 30837300675524915023822351)
        ·
          refine ⟨46255951013287372535733527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30837300675524915023822351 46255951013287372535733527)
          ·
            refine ⟨69383926519931058803600291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46255951013287372535733527 69383926519931058803600291)
            ·
              refine ⟨104075889779896588205400437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69383926519931058803600291 104075889779896588205400437)
              ·
                refine ⟨9757114666865305144256291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104075889779896588205400437 9757114666865305144256291)
                ·
                  refine ⟨14635672000297957716384437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9757114666865305144256291 14635672000297957716384437)
                  ·
                    refine ⟨1372094250027933535911041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14635672000297957716384437 1372094250027933535911041)
                    ·
                      refine ⟨1029070687520950151933281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372094250027933535911041 1029070687520950151933281)
                      ·
                        rfl

theorem cell23_2004108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_2004108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004108 prefixEnd_2004108 := by exact prefixLift 2004108
  have htrace : WordTrace (prefixWord ++ tailWord_2004108) baseStart_2004108 baseEnd_2004108 := by
    simpa [prefixWord, tailWord_2004108, baseEnd_2004108] using wordTrace_append hprefix tailTrace_2004108
  have hstable : (prefixWord ++ tailWord_2004108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004108).length < 2 ^ (prefixWord ++ tailWord_2004108).sum := by decide
  have hdescent : baseEnd_2004108 < baseStart_2004108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004125 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_2004125 : Nat := 118140960795 + 2004125 * 2 ^ 59
def prefixEnd_2004125 : Nat := 4983230072969 + 3 ^ 40 * 2004125 * 2
def baseEnd_2004125 : Nat := 1029079416692076585420703

theorem tailTrace_2004125 : CollatzResearch.WordTrace tailWord_2004125 prefixEnd_2004125 1029079416692076585420703 := by
  unfold tailWord_2004125
  simp only [CollatzResearch.WordTrace]
  refine ⟨73096443864404877145021829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48730962576269918096681219 73096443864404877145021829)
  ·
    refine ⟨13705583224575914464691593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73096443864404877145021829 13705583224575914464691593)
    ·
      refine ⟨10279187418431935848518695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13705583224575914464691593 10279187418431935848518695)
      ·
        refine ⟨15418781127647903772778043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10279187418431935848518695 15418781127647903772778043)
        ·
          refine ⟨23128171691471855659167065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15418781127647903772778043 23128171691471855659167065)
          ·
            refine ⟨17346128768603891744375299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23128171691471855659167065 17346128768603891744375299)
            ·
              refine ⟨26019193152905837616562949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17346128768603891744375299 26019193152905837616562949)
              ·
                refine ⟨4878598716169844553105553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26019193152905837616562949 4878598716169844553105553)
                ·
                  refine ⟨3658949037127383414829165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4878598716169844553105553 3658949037127383414829165)
                  ·
                    refine ⟨1372105888922768780560937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658949037127383414829165 1372105888922768780560937)
                    ·
                      refine ⟨1029079416692076585420703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372105888922768780560937 1029079416692076585420703)
                      ·
                        rfl

theorem cell23_2004125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_2004125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004125 prefixEnd_2004125 := by exact prefixLift 2004125
  have htrace : WordTrace (prefixWord ++ tailWord_2004125) baseStart_2004125 baseEnd_2004125 := by
    simpa [prefixWord, tailWord_2004125, baseEnd_2004125] using wordTrace_append hprefix tailTrace_2004125
  have hstable : (prefixWord ++ tailWord_2004125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004125).length < 2 ^ (prefixWord ++ tailWord_2004125).sum := by decide
  have hdescent : baseEnd_2004125 < baseStart_2004125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004126 : List Nat := [4, 3, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2004126 : Nat := 118140960795 + 2004126 * 2 ^ 59
def prefixEnd_2004126 : Nat := 4983230072969 + 3 ^ 40 * 2004126 * 2
def baseEnd_2004126 : Nat := 343026643390910360502733

theorem tailTrace_2004126 : CollatzResearch.WordTrace tailWord_2004126 prefixEnd_2004126 343026643390910360502733 := by
  unfold tailWord_2004126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9137060042175156789476029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48730986891600836210538821 9137060042175156789476029)
  ·
    refine ⟨3426397515815683796053511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9137060042175156789476029 3426397515815683796053511)
    ·
      refine ⟨5139596273723525694080267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3426397515815683796053511 5139596273723525694080267)
      ·
        refine ⟨7709394410585288541120401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139596273723525694080267 7709394410585288541120401)
        ·
          refine ⟨5782045807938966405840301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7709394410585288541120401 5782045807938966405840301)
          ·
            refine ⟨2168267177977112402190113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5782045807938966405840301 2168267177977112402190113)
            ·
              refine ⟨1626200383482834301642585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168267177977112402190113 1626200383482834301642585)
              ·
                refine ⟨1219650287612125726231939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626200383482834301642585 1219650287612125726231939)
                ·
                  refine ⟨1829475431418188589347909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219650287612125726231939 1829475431418188589347909)
                  ·
                    refine ⟨343026643390910360502733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1829475431418188589347909 343026643390910360502733)
                    ·
                      rfl

theorem cell23_2004126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2004126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004126 prefixEnd_2004126 := by exact prefixLift 2004126
  have htrace : WordTrace (prefixWord ++ tailWord_2004126) baseStart_2004126 baseEnd_2004126 := by
    simpa [prefixWord, tailWord_2004126, baseEnd_2004126] using wordTrace_append hprefix tailTrace_2004126
  have hstable : (prefixWord ++ tailWord_2004126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004126).length < 2 ^ (prefixWord ++ tailWord_2004126).sum := by decide
  have hdescent : baseEnd_2004126 < baseStart_2004126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004168 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_2004168 : Nat := 118140960795 + 2004168 * 2 ^ 59
def prefixEnd_2004168 : Nat := 4983230072969 + 3 ^ 40 * 2004168 * 2
def baseEnd_2004168 : Nat := 1029101496360219917183005

theorem tailTrace_2004168 : CollatzResearch.WordTrace tailWord_2004168 prefixEnd_2004168 1029101496360219917183005 := by
  unfold tailWord_2004168
  simp only [CollatzResearch.WordTrace]
  refine ⟨36549006101624547744418579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48732008135499396992558105 36549006101624547744418579)
  ·
    refine ⟨54823509152436821616627869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36549006101624547744418579 54823509152436821616627869)
    ·
      refine ⟨20558815932163808106235451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54823509152436821616627869 20558815932163808106235451)
      ·
        refine ⟨30838223898245712159353177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20558815932163808106235451 30838223898245712159353177)
        ·
          refine ⟨23128667923684284119514883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30838223898245712159353177 23128667923684284119514883)
          ·
            refine ⟨34693001885526426179272325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23128667923684284119514883 34693001885526426179272325)
            ·
              refine ⟨6504937853536204908613561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34693001885526426179272325 6504937853536204908613561)
              ·
                refine ⟨4878703390152153681460171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6504937853536204908613561 4878703390152153681460171)
                ·
                  refine ⟨7318055085228230522190257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878703390152153681460171 7318055085228230522190257)
                  ·
                    refine ⟨5488541313921172891642693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7318055085228230522190257 5488541313921172891642693)
                    ·
                      refine ⟨1029101496360219917183005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5488541313921172891642693 1029101496360219917183005)
                      ·
                        rfl

theorem cell23_2004168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_2004168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004168 prefixEnd_2004168 := by exact prefixLift 2004168
  have htrace : WordTrace (prefixWord ++ tailWord_2004168) baseStart_2004168 baseEnd_2004168 := by
    simpa [prefixWord, tailWord_2004168, baseEnd_2004168] using wordTrace_append hprefix tailTrace_2004168
  have hstable : (prefixWord ++ tailWord_2004168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004168).length < 2 ^ (prefixWord ++ tailWord_2004168).sum := by decide
  have hdescent : baseEnd_2004168 < baseStart_2004168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004191 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 1, 9]
def baseStart_2004191 : Nat := 118140960795 + 2004191 * 2 ^ 59
def prefixEnd_2004191 : Nat := 4983230072969 + 3 ^ 40 * 2004191 * 2
def baseEnd_2004191 : Nat := 343037768805091109065133

theorem tailTrace_2004191 : CollatzResearch.WordTrace tailWord_2004191 prefixEnd_2004191 343037768805091109065133 := by
  unfold tailWord_2004191
  simp only [CollatzResearch.WordTrace]
  refine ⟨73098851082165770416924427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48732567388110513611282951 73098851082165770416924427)
  ·
    refine ⟨109648276623248655625386641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73098851082165770416924427 109648276623248655625386641)
    ·
      refine ⟨82236207467436491719039981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109648276623248655625386641 82236207467436491719039981)
      ·
        refine ⟨30838577800288684394639993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82236207467436491719039981 30838577800288684394639993)
        ·
          refine ⟨23128933350216513295979995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30838577800288684394639993 23128933350216513295979995)
          ·
            refine ⟨34693400025324769943969993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23128933350216513295979995 34693400025324769943969993)
            ·
              refine ⟨26020050018993577457977495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34693400025324769943969993 26020050018993577457977495)
              ·
                refine ⟨39030075028490366186966243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26020050018993577457977495 39030075028490366186966243)
                ·
                  refine ⟨58545112542735549280449365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39030075028490366186966243 58545112542735549280449365)
                  ·
                    refine ⟨343037768805091109065133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 58545112542735549280449365 343037768805091109065133)
                    ·
                      rfl

theorem cell23_2004191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_2004191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004191 prefixEnd_2004191 := by exact prefixLift 2004191
  have htrace : WordTrace (prefixWord ++ tailWord_2004191) baseStart_2004191 baseEnd_2004191 := by
    simpa [prefixWord, tailWord_2004191, baseEnd_2004191] using wordTrace_append hprefix tailTrace_2004191
  have hstable : (prefixWord ++ tailWord_2004191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004191).length < 2 ^ (prefixWord ++ tailWord_2004191).sum := by decide
  have hdescent : baseEnd_2004191 < baseStart_2004191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004199 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 2, 4]
def baseStart_2004199 : Nat := 118140960795 + 2004199 * 2 ^ 59
def prefixEnd_2004199 : Nat := 4983230072969 + 3 ^ 40 * 2004199 * 2
def baseEnd_2004199 : Nat := 343039138086836431965121

theorem tailTrace_2004199 : CollatzResearch.WordTrace tailWord_2004199 prefixEnd_2004199 343039138086836431965121 := by
  unfold tailWord_2004199
  simp only [CollatzResearch.WordTrace]
  refine ⟨73099142866136787783215651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48732761910757858522143767 73099142866136787783215651)
  ·
    refine ⟨109648714299205181674823477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73099142866136787783215651 109648714299205181674823477)
    ·
      refine ⟨10279566965550485782014701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109648714299205181674823477 10279566965550485782014701)
      ·
        refine ⟨3854837612081432168255513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10279566965550485782014701 3854837612081432168255513)
        ·
          refine ⟨2891128209061074126191635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3854837612081432168255513 2891128209061074126191635)
          ·
            refine ⟨4336692313591611189287453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891128209061074126191635 4336692313591611189287453)
            ·
              refine ⟨1626259617596854195982795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4336692313591611189287453 1626259617596854195982795)
              ·
                refine ⟨2439389426395281293974193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626259617596854195982795 2439389426395281293974193)
                ·
                  refine ⟨1829542069796460970480645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2439389426395281293974193 1829542069796460970480645)
                  ·
                    refine ⟨343039138086836431965121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1829542069796460970480645 343039138086836431965121)
                    ·
                      rfl

theorem cell23_2004199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_2004199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004199 prefixEnd_2004199 := by exact prefixLift 2004199
  have htrace : WordTrace (prefixWord ++ tailWord_2004199) baseStart_2004199 baseEnd_2004199 := by
    simpa [prefixWord, tailWord_2004199, baseEnd_2004199] using wordTrace_append hprefix tailTrace_2004199
  have hstable : (prefixWord ++ tailWord_2004199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004199).length < 2 ^ (prefixWord ++ tailWord_2004199).sum := by decide
  have hdescent : baseEnd_2004199 < baseStart_2004199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004201 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_2004201 : Nat := 118140960795 + 2004201 * 2 ^ 59
def prefixEnd_2004201 : Nat := 4983230072969 + 3 ^ 40 * 2004201 * 2
def baseEnd_2004201 : Nat := 1029118441221818288070353

theorem tailTrace_2004201 : CollatzResearch.WordTrace tailWord_2004201 prefixEnd_2004201 1029118441221818288070353 := by
  unfold tailWord_2004201
  simp only [CollatzResearch.WordTrace]
  refine ⟨73099215812129542124788457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48732810541419694749858971 73099215812129542124788457)
  ·
    refine ⟨54824411859097156593591343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73099215812129542124788457 54824411859097156593591343)
    ·
      refine ⟨82236617788645734890387015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54824411859097156593591343 82236617788645734890387015)
      ·
        refine ⟨123354926682968602335580523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82236617788645734890387015 123354926682968602335580523)
        ·
          refine ⟨185032390024452903503370785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123354926682968602335580523 185032390024452903503370785)
          ·
            refine ⟨138774292518339677627528089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185032390024452903503370785 138774292518339677627528089)
            ·
              refine ⟨104080719388754758220646067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138774292518339677627528089 104080719388754758220646067)
              ·
                refine ⟨156121079083132137330969101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104080719388754758220646067 156121079083132137330969101)
                ·
                  refine ⟨58545404656174551499113413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156121079083132137330969101 58545404656174551499113413)
                  ·
                    refine ⟨10977263373032728406083765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58545404656174551499113413 10977263373032728406083765)
                    ·
                      refine ⟨1029118441221818288070353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10977263373032728406083765 1029118441221818288070353)
                      ·
                        rfl

theorem cell23_2004201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_2004201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004201 prefixEnd_2004201 := by exact prefixLift 2004201
  have htrace : WordTrace (prefixWord ++ tailWord_2004201) baseStart_2004201 baseEnd_2004201 := by
    simpa [prefixWord, tailWord_2004201, baseEnd_2004201] using wordTrace_append hprefix tailTrace_2004201
  have hstable : (prefixWord ++ tailWord_2004201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004201).length < 2 ^ (prefixWord ++ tailWord_2004201).sum := by decide
  have hdescent : baseEnd_2004201 < baseStart_2004201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004222 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_2004222 : Nat := 118140960795 + 2004222 * 2 ^ 59
def prefixEnd_2004222 : Nat := 4983230072969 + 3 ^ 40 * 2004222 * 2
def baseEnd_2004222 : Nat := 1029129224315562705907757

theorem tailTrace_2004222 : CollatzResearch.WordTrace tailWord_2004222 prefixEnd_2004222 1029129224315562705907757 := by
  unfold tailWord_2004222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9137497718131682838912865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48733321163368975140868613 9137497718131682838912865)
  ·
    refine ⟨6853123288598762129184649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9137497718131682838912865 6853123288598762129184649)
    ·
      refine ⟨5139842466449071596888487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6853123288598762129184649 5139842466449071596888487)
      ·
        refine ⟨7709763699673607395332731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139842466449071596888487 7709763699673607395332731)
        ·
          refine ⟨11564645549510411092999097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7709763699673607395332731 11564645549510411092999097)
          ·
            refine ⟨8673484162132808319749323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11564645549510411092999097 8673484162132808319749323)
            ·
              refine ⟨13010226243199212479623985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8673484162132808319749323 13010226243199212479623985)
              ·
                refine ⟨9757669682399409359717989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13010226243199212479623985 9757669682399409359717989)
                ·
                  refine ⟨1829563065449889254947123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9757669682399409359717989 1829563065449889254947123)
                  ·
                    refine ⟨2744344598174833882420685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829563065449889254947123 2744344598174833882420685)
                    ·
                      refine ⟨1029129224315562705907757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2744344598174833882420685 1029129224315562705907757)
                      ·
                        rfl

theorem cell23_2004222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_2004222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004222 prefixEnd_2004222 := by exact prefixLift 2004222
  have htrace : WordTrace (prefixWord ++ tailWord_2004222) baseStart_2004222 baseEnd_2004222 := by
    simpa [prefixWord, tailWord_2004222, baseEnd_2004222] using wordTrace_append hprefix tailTrace_2004222
  have hstable : (prefixWord ++ tailWord_2004222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004222).length < 2 ^ (prefixWord ++ tailWord_2004222).sum := by decide
  have hdescent : baseEnd_2004222 < baseStart_2004222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004256 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 2, 1, 3]
def baseStart_2004256 : Nat := 118140960795 + 2004256 * 2 ^ 59
def prefixEnd_2004256 : Nat := 4983230072969 + 3 ^ 40 * 2004256 * 2
def baseEnd_2004256 : Nat := 1029146682657815572882601

theorem tailTrace_2004256 : CollatzResearch.WordTrace tailWord_2004256 prefixEnd_2004256 1029146682657815572882601 := by
  unfold tailWord_2004256
  simp only [CollatzResearch.WordTrace]
  refine ⟨36550610913465143259020311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48734147884620191012027081 36550610913465143259020311)
  ·
    refine ⟨54825916370197714888530467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36550610913465143259020311 54825916370197714888530467)
    ·
      refine ⟨82238874555296572332795701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54825916370197714888530467 82238874555296572332795701)
      ·
        refine ⟨7709894489559053656199597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82238874555296572332795701 7709894489559053656199597)
        ·
          refine ⟨2891210433584645121074849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7709894489559053656199597 2891210433584645121074849)
          ·
            refine ⟨2168407825188483840806137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2891210433584645121074849 2168407825188483840806137)
            ·
              refine ⟨1626305868891362880604603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168407825188483840806137 1626305868891362880604603)
              ·
                refine ⟨2439458803337044320906905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626305868891362880604603 2439458803337044320906905)
                ·
                  refine ⟨1829594102502783240680179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2439458803337044320906905 1829594102502783240680179)
                  ·
                    refine ⟨2744391153754174861020269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829594102502783240680179 2744391153754174861020269)
                    ·
                      refine ⟨1029146682657815572882601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2744391153754174861020269 1029146682657815572882601)
                      ·
                        rfl

theorem cell23_2004256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_2004256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004256 prefixEnd_2004256 := by exact prefixLift 2004256
  have htrace : WordTrace (prefixWord ++ tailWord_2004256) baseStart_2004256 baseEnd_2004256 := by
    simpa [prefixWord, tailWord_2004256, baseEnd_2004256] using wordTrace_append hprefix tailTrace_2004256
  have hstable : (prefixWord ++ tailWord_2004256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004256).length < 2 ^ (prefixWord ++ tailWord_2004256).sum := by decide
  have hdescent : baseEnd_2004256 < baseStart_2004256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004266 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_2004266 : Nat := 118140960795 + 2004266 * 2 ^ 59
def prefixEnd_2004266 : Nat := 4983230072969 + 3 ^ 40 * 2004266 * 2
def baseEnd_2004266 : Nat := 1029151817464360533757555

theorem tailTrace_2004266 : CollatzResearch.WordTrace tailWord_2004266 prefixEnd_2004266 1029151817464360533757555 := by
  unfold tailWord_2004266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275396639223514556476163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48734391037929372150603101 18275396639223514556476163)
  ·
    refine ⟨27413094958835271834714245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18275396639223514556476163 27413094958835271834714245)
    ·
      refine ⟨5139955304781613469008921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27413094958835271834714245 5139955304781613469008921)
      ·
        refine ⟨3854966478586210101756691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5139955304781613469008921 3854966478586210101756691)
        ·
          refine ⟨5782449717879315152635037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854966478586210101756691 5782449717879315152635037)
          ·
            refine ⟨2168418644204743182238139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5782449717879315152635037 2168418644204743182238139)
            ·
              refine ⟨3252627966307114773357209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168418644204743182238139 3252627966307114773357209)
              ·
                refine ⟨2439470974730336080017907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3252627966307114773357209 2439470974730336080017907)
                ·
                  refine ⟨3659206462095504120026861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439470974730336080017907 3659206462095504120026861)
                  ·
                    refine ⟨1372202423285814045010073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3659206462095504120026861 1372202423285814045010073)
                    ·
                      refine ⟨1029151817464360533757555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372202423285814045010073 1029151817464360533757555)
                      ·
                        rfl

theorem cell23_2004266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_2004266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004266 prefixEnd_2004266 := by exact prefixLift 2004266
  have htrace : WordTrace (prefixWord ++ tailWord_2004266) baseStart_2004266 baseEnd_2004266 := by
    simpa [prefixWord, tailWord_2004266, baseEnd_2004266] using wordTrace_append hprefix tailTrace_2004266
  have hstable : (prefixWord ++ tailWord_2004266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004266).length < 2 ^ (prefixWord ++ tailWord_2004266).sum := by decide
  have hdescent : baseEnd_2004266 < baseStart_2004266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004305 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 1, 7, 2]
def baseStart_2004305 : Nat := 118140960795 + 2004305 * 2 ^ 59
def prefixEnd_2004305 : Nat := 4983230072969 + 3 ^ 40 * 2004305 * 2
def baseEnd_2004305 : Nat := 1029171843209885881169875

theorem tailTrace_2004305 : CollatzResearch.WordTrace tailWord_2004305 prefixEnd_2004305 1029171843209885881169875 := by
  unfold tailWord_2004305
  simp only [CollatzResearch.WordTrace]
  refine ⟨73103009003752767886574369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48735339335835178591049579 73103009003752767886574369)
  ·
    refine ⟨54827256752814575914930777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73103009003752767886574369 54827256752814575914930777)
    ·
      refine ⟨41120442564610931936198083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54827256752814575914930777 41120442564610931936198083)
      ·
        refine ⟨61680663846916397904297125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41120442564610931936198083 61680663846916397904297125)
        ·
          refine ⟨11565124471296824607055711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61680663846916397904297125 11565124471296824607055711)
          ·
            refine ⟨17347686706945236910583567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11565124471296824607055711 17347686706945236910583567)
            ·
              refine ⟨26021530060417855365875351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347686706945236910583567 26021530060417855365875351)
              ·
                refine ⟨39032295090626783048813027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26021530060417855365875351 39032295090626783048813027)
                ·
                  refine ⟨58548442635940174573219541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39032295090626783048813027 58548442635940174573219541)
                  ·
                    refine ⟨1372229124279847841559833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58548442635940174573219541 1372229124279847841559833)
                    ·
                      refine ⟨1029171843209885881169875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372229124279847841559833 1029171843209885881169875)
                      ·
                        rfl

theorem cell23_2004305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_2004305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004305 prefixEnd_2004305 := by exact prefixLift 2004305
  have htrace : WordTrace (prefixWord ++ tailWord_2004305) baseStart_2004305 baseEnd_2004305 := by
    simpa [prefixWord, tailWord_2004305, baseEnd_2004305] using wordTrace_append hprefix tailTrace_2004305
  have hstable : (prefixWord ++ tailWord_2004305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004305).length < 2 ^ (prefixWord ++ tailWord_2004305).sum := by decide
  have hdescent : baseEnd_2004305 < baseStart_2004305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004322 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_2004322 : Nat := 118140960795 + 2004322 * 2 ^ 59
def prefixEnd_2004322 : Nat := 4983230072969 + 3 ^ 40 * 2004322 * 2
def baseEnd_2004322 : Nat := 1029180572381012314657297

theorem tailTrace_2004322 : CollatzResearch.WordTrace tailWord_2004322 prefixEnd_2004322 1029180572381012314657297 := by
  unfold tailWord_2004322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275907261172794947485805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48735752696460786526628813 18275907261172794947485805)
  ·
    refine ⟨6853465222939798105307177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18275907261172794947485805 6853465222939798105307177)
    ·
      refine ⟨5140098917204848578980383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6853465222939798105307177 5140098917204848578980383)
      ·
        refine ⟨7710148375807272868470575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140098917204848578980383 7710148375807272868470575)
        ·
          refine ⟨11565222563710909302705863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710148375807272868470575 11565222563710909302705863)
          ·
            refine ⟨17347833845566363954058795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11565222563710909302705863 17347833845566363954058795)
            ·
              refine ⟨26021750768349545931088193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17347833845566363954058795 26021750768349545931088193)
              ·
                refine ⟨19516313076262159448316145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26021750768349545931088193 19516313076262159448316145)
                ·
                  refine ⟨14637234807196619586237109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19516313076262159448316145 14637234807196619586237109)
                  ·
                    refine ⟨1372240763174683086209729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14637234807196619586237109 1372240763174683086209729)
                    ·
                      refine ⟨1029180572381012314657297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372240763174683086209729 1029180572381012314657297)
                      ·
                        rfl

theorem cell23_2004322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_2004322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004322 prefixEnd_2004322 := by exact prefixLift 2004322
  have htrace : WordTrace (prefixWord ++ tailWord_2004322) baseStart_2004322 baseEnd_2004322 := by
    simpa [prefixWord, tailWord_2004322, baseEnd_2004322] using wordTrace_append hprefix tailTrace_2004322
  have hstable : (prefixWord ++ tailWord_2004322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004322).length < 2 ^ (prefixWord ++ tailWord_2004322).sum := by decide
  have hdescent : baseEnd_2004322 < baseStart_2004322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004332 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_2004332 : Nat := 118140960795 + 2004332 * 2 ^ 59
def prefixEnd_2004332 : Nat := 4983230072969 + 3 ^ 40 * 2004332 * 2
def baseEnd_2004332 : Nat := 343061902395852425177417

theorem tailTrace_2004332 : CollatzResearch.WordTrace tailWord_2004332 prefixEnd_2004332 343061902395852425177417 := by
  unfold tailWord_2004332
  simp only [CollatzResearch.WordTrace]
  refine ⟨36551996887327475748903625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48735995849769967665204833 36551996887327475748903625)
  ·
    refine ⟨27413997665495606811677719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36551996887327475748903625 27413997665495606811677719)
    ·
      refine ⟨41120996498243410217516579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27413997665495606811677719 41120996498243410217516579)
      ·
        refine ⟨61681494747365115326274869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41120996498243410217516579 61681494747365115326274869)
        ·
          refine ⟨5782640132565479561838269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61681494747365115326274869 5782640132565479561838269)
          ·
            refine ⟨2168490049712054835689351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5782640132565479561838269 2168490049712054835689351)
            ·
              refine ⟨3252735074568082253534027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168490049712054835689351 3252735074568082253534027)
              ·
                refine ⟨4879102611852123380301041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252735074568082253534027 4879102611852123380301041)
                ·
                  refine ⟨3659326958889092535225781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4879102611852123380301041 3659326958889092535225781)
                  ·
                    refine ⟨343061902395852425177417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3659326958889092535225781 343061902395852425177417)
                    ·
                      rfl

theorem cell23_2004332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_2004332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004332 prefixEnd_2004332 := by exact prefixLift 2004332
  have htrace : WordTrace (prefixWord ++ tailWord_2004332) baseStart_2004332 baseEnd_2004332 := by
    simpa [prefixWord, tailWord_2004332, baseEnd_2004332] using wordTrace_append hprefix tailTrace_2004332
  have hstable : (prefixWord ++ tailWord_2004332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004332).length < 2 ^ (prefixWord ++ tailWord_2004332).sum := by decide
  have hdescent : baseEnd_2004332 < baseStart_2004332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004335 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 1, 6, 2]
def baseStart_2004335 : Nat := 118140960795 + 2004335 * 2 ^ 59
def prefixEnd_2004335 : Nat := 4983230072969 + 3 ^ 40 * 2004335 * 2
def baseEnd_2004335 : Nat := 1029187247629520763794737

theorem tailTrace_2004335 : CollatzResearch.WordTrace tailWord_2004335 prefixEnd_2004335 1029187247629520763794737 := by
  unfold tailWord_2004335
  simp only [CollatzResearch.WordTrace]
  refine ⟨73104103193644083010166459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48736068795762722006777639 73104103193644083010166459)
  ·
    refine ⟨109656154790466124515249689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73104103193644083010166459 109656154790466124515249689)
    ·
      refine ⟨82242116092849593386437267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109656154790466124515249689 82242116092849593386437267)
      ·
        refine ⟨123363174139274390079655901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82242116092849593386437267 123363174139274390079655901)
        ·
          refine ⟨46261190302227896279870963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123363174139274390079655901 46261190302227896279870963)
          ·
            refine ⟨69391785453341844419806445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46261190302227896279870963 69391785453341844419806445)
            ·
              refine ⟨26021919545003191657427417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69391785453341844419806445 26021919545003191657427417)
              ·
                refine ⟨19516439658752393743070563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26021919545003191657427417 19516439658752393743070563)
                ·
                  refine ⟨29274659488128590614605845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19516439658752393743070563 29274659488128590614605845)
                  ·
                    refine ⟨1372249663506027685059649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29274659488128590614605845 1372249663506027685059649)
                    ·
                      refine ⟨1029187247629520763794737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1372249663506027685059649 1029187247629520763794737)
                      ·
                        rfl

theorem cell23_2004335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 6, 2].length) (baseStart_2004335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004335 prefixEnd_2004335 := by exact prefixLift 2004335
  have htrace : WordTrace (prefixWord ++ tailWord_2004335) baseStart_2004335 baseEnd_2004335 := by
    simpa [prefixWord, tailWord_2004335, baseEnd_2004335] using wordTrace_append hprefix tailTrace_2004335
  have hstable : (prefixWord ++ tailWord_2004335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004335).length < 2 ^ (prefixWord ++ tailWord_2004335).sum := by decide
  have hdescent : baseEnd_2004335 < baseStart_2004335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004348 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_2004348 : Nat := 118140960795 + 2004348 * 2 ^ 59
def prefixEnd_2004348 : Nat := 4983230072969 + 3 ^ 40 * 2004348 * 2
def baseEnd_2004348 : Nat := 1029193922878029212932177

theorem tailTrace_2004348 : CollatzResearch.WordTrace tailWord_2004348 prefixEnd_2004348 1029193922878029212932177 := by
  unfold tailWord_2004348
  simp only [CollatzResearch.WordTrace]
  refine ⟨36552288671298493115194849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48736384895064657486926465 36552288671298493115194849)
  ·
    refine ⟨27414216503473869836396137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36552288671298493115194849 27414216503473869836396137)
    ·
      refine ⟨20560662377605402377297103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27414216503473869836396137 20560662377605402377297103)
      ·
        refine ⟨30840993566408103565945655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20560662377605402377297103 30840993566408103565945655)
        ·
          refine ⟨46261490349612155348918483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30840993566408103565945655 46261490349612155348918483)
          ·
            refine ⟨69392235524418233023377725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46261490349612155348918483 69392235524418233023377725)
            ·
              refine ⟨26022088321656837383766647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69392235524418233023377725 26022088321656837383766647)
              ·
                refine ⟨39033132482485256075649971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26022088321656837383766647 39033132482485256075649971)
                ·
                  refine ⟨58549698723727884113474957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39033132482485256075649971 58549698723727884113474957)
                  ·
                    refine ⟨21956137021397956542553109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58549698723727884113474957 21956137021397956542553109)
                    ·
                      refine ⟨1029193922878029212932177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21956137021397956542553109 1029193922878029212932177)
                      ·
                        rfl

theorem cell23_2004348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_2004348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004348 prefixEnd_2004348 := by exact prefixLift 2004348
  have htrace : WordTrace (prefixWord ++ tailWord_2004348) baseStart_2004348 baseEnd_2004348 := by
    simpa [prefixWord, tailWord_2004348, baseEnd_2004348] using wordTrace_append hprefix tailTrace_2004348
  have hstable : (prefixWord ++ tailWord_2004348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004348).length < 2 ^ (prefixWord ++ tailWord_2004348).sum := by decide
  have hdescent : baseEnd_2004348 < baseStart_2004348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004372 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2004372 : Nat := 118140960795 + 2004372 * 2 ^ 59
def prefixEnd_2004372 : Nat := 4983230072969 + 3 ^ 40 * 2004372 * 2
def baseEnd_2004372 : Nat := 1029206246413737119032067

theorem tailTrace_2004372 : CollatzResearch.WordTrace tailWord_2004372 prefixEnd_2004372 1029206246413737119032067 := by
  unfold tailWord_2004372
  simp only [CollatzResearch.WordTrace]
  refine ⟨36552726347255019164631685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48736968463006692219508913 36552726347255019164631685)
  ·
    refine ⟨6853636190110316093368441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36552726347255019164631685 6853636190110316093368441)
    ·
      refine ⟨5140227142582737070026331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6853636190110316093368441 5140227142582737070026331)
      ·
        refine ⟨7710340713874105605039497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140227142582737070026331 7710340713874105605039497)
        ·
          refine ⟨5782755535405579203779623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7710340713874105605039497 5782755535405579203779623)
          ·
            refine ⟨8674133303108368805669435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5782755535405579203779623 8674133303108368805669435)
            ·
              refine ⟨13011199954662553208504153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8674133303108368805669435 13011199954662553208504153)
              ·
                refine ⟨9758399965996914906378115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13011199954662553208504153 9758399965996914906378115)
                ·
                  refine ⟨14637599948995372359567173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9758399965996914906378115 14637599948995372359567173)
                  ·
                    refine ⟨2744549990436632317418845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14637599948995372359567173 2744549990436632317418845)
                    ·
                      refine ⟨1029206246413737119032067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2744549990436632317418845 1029206246413737119032067)
                      ·
                        rfl

theorem cell23_2004372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2004372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004372 prefixEnd_2004372 := by exact prefixLift 2004372
  have htrace : WordTrace (prefixWord ++ tailWord_2004372) baseStart_2004372 baseEnd_2004372 := by
    simpa [prefixWord, tailWord_2004372, baseEnd_2004372] using wordTrace_append hprefix tailTrace_2004372
  have hstable : (prefixWord ++ tailWord_2004372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004372).length < 2 ^ (prefixWord ++ tailWord_2004372).sum := by decide
  have hdescent : baseEnd_2004372 < baseStart_2004372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004419 : List Nat := [1, 1, 1, 3, 1, 1, 4, 6, 1, 1, 3]
def baseStart_2004419 : Nat := 118140960795 + 2004419 * 2 ^ 59
def prefixEnd_2004419 : Nat := 4983230072969 + 3 ^ 40 * 2004419 * 2
def baseEnd_2004419 : Nat := 1029230380004498435144351

theorem tailTrace_2004419 : CollatzResearch.WordTrace tailWord_2004419 prefixEnd_2004419 1029230380004498435144351 := by
  unfold tailWord_2004419
  simp only [CollatzResearch.WordTrace]
  refine ⟨73107166925339765356224311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48738111283559843570816207 73107166925339765356224311)
  ·
    refine ⟨109660750388009648034336467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73107166925339765356224311 109660750388009648034336467)
    ·
      refine ⟨164491125582014472051504701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109660750388009648034336467 164491125582014472051504701)
      ·
        refine ⟨61684172093255427019314263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164491125582014472051504701 61684172093255427019314263)
        ·
          refine ⟨92526258139883140528971395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61684172093255427019314263 92526258139883140528971395)
          ·
            refine ⟨138789387209824710793457093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92526258139883140528971395 138789387209824710793457093)
            ·
              refine ⟨26023010101842133273773205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138789387209824710793457093 26023010101842133273773205)
              ·
                refine ⟨1219828598523849997208119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26023010101842133273773205 1219828598523849997208119)
                ·
                  refine ⟨1829742897785774995812179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219828598523849997208119 1829742897785774995812179)
                  ·
                    refine ⟨2744614346678662493718269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829742897785774995812179 2744614346678662493718269)
                    ·
                      refine ⟨1029230380004498435144351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2744614346678662493718269 1029230380004498435144351)
                      ·
                        rfl

theorem cell23_2004419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_2004419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004419 prefixEnd_2004419 := by exact prefixLift 2004419
  have htrace : WordTrace (prefixWord ++ tailWord_2004419) baseStart_2004419 baseEnd_2004419 := by
    simpa [prefixWord, tailWord_2004419, baseEnd_2004419] using wordTrace_append hprefix tailTrace_2004419
  have hstable : (prefixWord ++ tailWord_2004419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004419).length < 2 ^ (prefixWord ++ tailWord_2004419).sum := by decide
  have hdescent : baseEnd_2004419 < baseStart_2004419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004425 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_2004425 : Nat := 118140960795 + 2004425 * 2 ^ 59
def prefixEnd_2004425 : Nat := 4983230072969 + 3 ^ 40 * 2004425 * 2
def baseEnd_2004425 : Nat := 1029233460888425411669323

theorem tailTrace_2004425 : CollatzResearch.WordTrace tailWord_2004425 prefixEnd_2004425 1029233460888425411669323 := by
  unfold tailWord_2004425
  simp only [CollatzResearch.WordTrace]
  refine ⟨73107385763318028380942729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48738257175545352253961819 73107385763318028380942729)
  ·
    refine ⟨54830539322488521285707047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73107385763318028380942729 54830539322488521285707047)
    ·
      refine ⟨82245808983732781928560571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54830539322488521285707047 82245808983732781928560571)
      ·
        refine ⟨123368713475599172892840857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82245808983732781928560571 123368713475599172892840857)
        ·
          refine ⟨92526535106699379669630643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123368713475599172892840857 92526535106699379669630643)
          ·
            refine ⟨138789802660049069504445965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92526535106699379669630643 138789802660049069504445965)
            ·
              refine ⟨52046175997518401064167237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138789802660049069504445965 52046175997518401064167237)
              ·
                refine ⟨9758657999534700199531357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52046175997518401064167237 9758657999534700199531357)
                ·
                  refine ⟨3659496749825512574824259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9758657999534700199531357 3659496749825512574824259)
                  ·
                    refine ⟨5489245124738268862236389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3659496749825512574824259 5489245124738268862236389)
                    ·
                      refine ⟨1029233460888425411669323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5489245124738268862236389 1029233460888425411669323)
                      ·
                        rfl

theorem cell23_2004425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_2004425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004425 prefixEnd_2004425 := by exact prefixLift 2004425
  have htrace : WordTrace (prefixWord ++ tailWord_2004425) baseStart_2004425 baseEnd_2004425 := by
    simpa [prefixWord, tailWord_2004425, baseEnd_2004425] using wordTrace_append hprefix tailTrace_2004425
  have hstable : (prefixWord ++ tailWord_2004425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004425).length < 2 ^ (prefixWord ++ tailWord_2004425).sum := by decide
  have hdescent : baseEnd_2004425 < baseStart_2004425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004442 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_2004442 : Nat := 118140960795 + 2004442 * 2 ^ 59
def prefixEnd_2004442 : Nat := 4983230072969 + 3 ^ 40 * 2004442 * 2
def baseEnd_2004442 : Nat := 1029242190059551845156745

theorem tailTrace_2004442 : CollatzResearch.WordTrace tailWord_2004442 prefixEnd_2004442 1029242190059551845156745 := by
  unfold tailWord_2004442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277001451064110071077895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48738670536170960189541053 18277001451064110071077895)
  ·
    refine ⟨27415502176596165106616843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18277001451064110071077895 27415502176596165106616843)
    ·
      refine ⟨41123253264894247659925265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27415502176596165106616843 41123253264894247659925265)
      ·
        refine ⟨30842439948670685744943949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41123253264894247659925265 30842439948670685744943949)
        ·
          refine ⟨11565914980751507154353981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30842439948670685744943949 11565914980751507154353981)
          ·
            refine ⟨4337218117781815182882743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11565914980751507154353981 4337218117781815182882743)
            ·
              refine ⟨6505827176672722774324115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337218117781815182882743 6505827176672722774324115)
              ·
                refine ⟨9758740765009084161486173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6505827176672722774324115 9758740765009084161486173)
                ·
                  refine ⟨3659527786878406560557315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9758740765009084161486173 3659527786878406560557315)
                  ·
                    refine ⟨5489291680317609840835973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3659527786878406560557315 5489291680317609840835973)
                    ·
                      refine ⟨1029242190059551845156745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5489291680317609840835973 1029242190059551845156745)
                      ·
                        rfl

theorem cell23_2004442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_2004442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004442 prefixEnd_2004442 := by exact prefixLift 2004442
  have htrace : WordTrace (prefixWord ++ tailWord_2004442) baseStart_2004442 baseEnd_2004442 := by
    simpa [prefixWord, tailWord_2004442, baseEnd_2004442] using wordTrace_append hprefix tailTrace_2004442
  have hstable : (prefixWord ++ tailWord_2004442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004442).length < 2 ^ (prefixWord ++ tailWord_2004442).sum := by decide
  have hdescent : baseEnd_2004442 < baseStart_2004442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004470 : List Nat := [5, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_2004470 : Nat := 118140960795 + 2004470 * 2 ^ 59
def prefixEnd_2004470 : Nat := 4983230072969 + 3 ^ 40 * 2004470 * 2
def baseEnd_2004470 : Nat := 1029256567517877735606617

theorem tailTrace_2004470 : CollatzResearch.WordTrace tailWord_2004470 prefixEnd_2004470 1029256567517877735606617 := by
  unfold tailWord_2004470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569314190509687566645679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48739351365436667377553909 4569314190509687566645679)
  ·
    refine ⟨6853971285764531349968519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4569314190509687566645679 6853971285764531349968519)
    ·
      refine ⟨10280956928646797024952779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6853971285764531349968519 10280956928646797024952779)
      ·
        refine ⟨15421435392970195537429169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280956928646797024952779 15421435392970195537429169)
        ·
          refine ⟨11566076544727646653071877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15421435392970195537429169 11566076544727646653071877)
          ·
            refine ⟨2168639352136433747450977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11566076544727646653071877 2168639352136433747450977)
            ·
              refine ⟨1626479514102325310588233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168639352136433747450977 1626479514102325310588233)
              ·
                refine ⟨1219859635576743982941175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626479514102325310588233 1219859635576743982941175)
                ·
                  refine ⟨1829789453365115974411763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219859635576743982941175 1829789453365115974411763)
                  ·
                    refine ⟨2744684180047673961617645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829789453365115974411763 2744684180047673961617645)
                    ·
                      refine ⟨1029256567517877735606617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2744684180047673961617645 1029256567517877735606617)
                      ·
                        rfl

theorem cell23_2004470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_2004470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004470 prefixEnd_2004470 := by exact prefixLift 2004470
  have htrace : WordTrace (prefixWord ++ tailWord_2004470) baseStart_2004470 baseEnd_2004470 := by
    simpa [prefixWord, tailWord_2004470, baseEnd_2004470] using wordTrace_append hprefix tailTrace_2004470
  have hstable : (prefixWord ++ tailWord_2004470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004470).length < 2 ^ (prefixWord ++ tailWord_2004470).sum := by decide
  have hdescent : baseEnd_2004470 < baseStart_2004470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004509 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2004509 : Nat := 118140960795 + 2004509 * 2 ^ 59
def prefixEnd_2004509 : Nat := 4983230072969 + 3 ^ 40 * 2004509 * 2
def baseEnd_2004509 : Nat := 1029276593263403083018937

theorem tailTrace_2004509 : CollatzResearch.WordTrace tailWord_2004509 prefixEnd_2004509 1029276593263403083018937 := by
  unfold tailWord_2004509
  simp only [CollatzResearch.WordTrace]
  refine ⟨73110449495013710727000581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48740299663342473818000387 73110449495013710727000581)
  ·
    refine ⟨13708209280315070761312609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73110449495013710727000581 13708209280315070761312609)
    ·
      refine ⟨10281156960236303070984457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13708209280315070761312609 10281156960236303070984457)
      ·
        refine ⟨7710867720177227303238343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10281156960236303070984457 7710867720177227303238343)
        ·
          refine ⟨11566301580265840954857515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710867720177227303238343 11566301580265840954857515)
          ·
            refine ⟨17349452370398761432286273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11566301580265840954857515 17349452370398761432286273)
            ·
              refine ⟨13012089277799071074214705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17349452370398761432286273 13012089277799071074214705)
              ·
                refine ⟨9759066958349303305661029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13012089277799071074214705 9759066958349303305661029)
                ·
                  refine ⟨1829825054690494369811443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9759066958349303305661029 1829825054690494369811443)
                  ·
                    refine ⟨2744737582035741554717165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829825054690494369811443 2744737582035741554717165)
                    ·
                      refine ⟨1029276593263403083018937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2744737582035741554717165 1029276593263403083018937)
                      ·
                        rfl

theorem cell23_2004509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2004509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004509 prefixEnd_2004509 := by exact prefixLift 2004509
  have htrace : WordTrace (prefixWord ++ tailWord_2004509) baseStart_2004509 baseEnd_2004509 := by
    simpa [prefixWord, tailWord_2004509, baseEnd_2004509] using wordTrace_append hprefix tailTrace_2004509
  have hstable : (prefixWord ++ tailWord_2004509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004509).length < 2 ^ (prefixWord ++ tailWord_2004509).sum := by decide
  have hdescent : baseEnd_2004509 < baseStart_2004509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004510 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2004510 : Nat := 118140960795 + 2004510 * 2 ^ 59
def prefixEnd_2004510 : Nat := 4983230072969 + 3 ^ 40 * 2004510 * 2
def baseEnd_2004510 : Nat := 1029277106744057579106433

theorem tailTrace_2004510 : CollatzResearch.WordTrace tailWord_2004510 prefixEnd_2004510 1029277106744057579106433 := by
  unfold tailWord_2004510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138810746001260987223373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48740323978673391931857989 9138810746001260987223373)
  ·
    refine ⟨3427054029750472870208765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9138810746001260987223373 3427054029750472870208765)
    ·
      refine ⟨1285145261156427326328287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3427054029750472870208765 1285145261156427326328287)
      ·
        refine ⟨1927717891734640989492431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285145261156427326328287 1927717891734640989492431)
        ·
          refine ⟨2891576837601961484238647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1927717891734640989492431 2891576837601961484238647)
          ·
            refine ⟨4337365256402942226357971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891576837601961484238647 4337365256402942226357971)
            ·
              refine ⟨6506047884604413339536957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337365256402942226357971 6506047884604413339536957)
              ·
                refine ⟨2439767956726655002326359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6506047884604413339536957 2439767956726655002326359)
                ·
                  refine ⟨3659651935089982503489539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439767956726655002326359 3659651935089982503489539)
                  ·
                    refine ⟨5489477902634973755234309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3659651935089982503489539 5489477902634973755234309)
                    ·
                      refine ⟨1029277106744057579106433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5489477902634973755234309 1029277106744057579106433)
                      ·
                        rfl

theorem cell23_2004510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2004510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004510 prefixEnd_2004510 := by exact prefixLift 2004510
  have htrace : WordTrace (prefixWord ++ tailWord_2004510) baseStart_2004510 baseEnd_2004510 := by
    simpa [prefixWord, tailWord_2004510, baseEnd_2004510] using wordTrace_append hprefix tailTrace_2004510
  have hstable : (prefixWord ++ tailWord_2004510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004510).length < 2 ^ (prefixWord ++ tailWord_2004510).sum := by decide
  have hdescent : baseEnd_2004510 < baseStart_2004510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004526 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2004526 : Nat := 118140960795 + 2004526 * 2 ^ 59
def prefixEnd_2004526 : Nat := 4983230072969 + 3 ^ 40 * 2004526 * 2
def baseEnd_2004526 : Nat := 1029285322434529516506359

theorem tailTrace_2004526 : CollatzResearch.WordTrace tailWord_2004526 prefixEnd_2004526 1029285322434529516506359 := by
  unfold tailWord_2004526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138883691994015328796179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48740713023968081753579621 9138883691994015328796179)
  ·
    refine ⟨13708325537991022993194269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9138883691994015328796179 13708325537991022993194269)
    ·
      refine ⟨5140622076746633622447851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13708325537991022993194269 5140622076746633622447851)
      ·
        refine ⟨7710933115119950433671777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5140622076746633622447851 7710933115119950433671777)
        ·
          refine ⟨5783199836339962825253833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7710933115119950433671777 5783199836339962825253833)
          ·
            refine ⟨4337399877254972118940375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5783199836339962825253833 4337399877254972118940375)
            ·
              refine ⟨6506099815882458178410563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4337399877254972118940375 6506099815882458178410563)
              ·
                refine ⟨9759149723823687267615845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6506099815882458178410563 9759149723823687267615845)
                ·
                  refine ⟨1829840573216941362677971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9759149723823687267615845 1829840573216941362677971)
                  ·
                    refine ⟨2744760859825412044016957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829840573216941362677971 2744760859825412044016957)
                    ·
                      refine ⟨1029285322434529516506359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2744760859825412044016957 1029285322434529516506359)
                      ·
                        rfl

theorem cell23_2004526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2004526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004526 prefixEnd_2004526 := by exact prefixLift 2004526
  have htrace : WordTrace (prefixWord ++ tailWord_2004526) baseStart_2004526 baseEnd_2004526 := by
    simpa [prefixWord, tailWord_2004526, baseEnd_2004526] using wordTrace_append hprefix tailTrace_2004526
  have hstable : (prefixWord ++ tailWord_2004526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004526).length < 2 ^ (prefixWord ++ tailWord_2004526).sum := by decide
  have hdescent : baseEnd_2004526 < baseStart_2004526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004575 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_2004575 : Nat := 118140960795 + 2004575 * 2 ^ 59
def prefixEnd_2004575 : Nat := 4983230072969 + 3 ^ 40 * 2004575 * 2
def baseEnd_2004575 : Nat := 1029310482986599824793633

theorem tailTrace_2004575 : CollatzResearch.WordTrace tailWord_2004575 prefixEnd_2004575 1029310482986599824793633 := by
  unfold tailWord_2004575
  simp only [CollatzResearch.WordTrace]
  refine ⟨73112856712774603998903179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48741904475183069332602119 73112856712774603998903179)
  ·
    refine ⟨109669285069161905998354769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73112856712774603998903179 109669285069161905998354769)
    ·
      refine ⟨82251963801871429498766077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109669285069161905998354769 82251963801871429498766077)
      ·
        refine ⟨30844486425701786062037279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82251963801871429498766077 30844486425701786062037279)
        ·
          refine ⟨46266729638552679093055919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30844486425701786062037279 46266729638552679093055919)
          ·
            refine ⟨69400094457829018639583879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46266729638552679093055919 69400094457829018639583879)
            ·
              refine ⟨104100141686743527959375819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69400094457829018639583879 104100141686743527959375819)
              ·
                refine ⟨156150212530115291939063729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104100141686743527959375819 156150212530115291939063729)
                ·
                  refine ⟨117112659397586468954297797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156150212530115291939063729 117112659397586468954297797)
                  ·
                    refine ⟨21958623637047462928930837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117112659397586468954297797 21958623637047462928930837)
                    ·
                      refine ⟨1029310482986599824793633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21958623637047462928930837 1029310482986599824793633)
                      ·
                        rfl

theorem cell23_2004575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_2004575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004575 prefixEnd_2004575 := by exact prefixLift 2004575
  have htrace : WordTrace (prefixWord ++ tailWord_2004575) baseStart_2004575 baseEnd_2004575 := by
    simpa [prefixWord, tailWord_2004575, baseEnd_2004575] using wordTrace_append hprefix tailTrace_2004575
  have hstable : (prefixWord ++ tailWord_2004575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004575).length < 2 ^ (prefixWord ++ tailWord_2004575).sum := by decide
  have hdescent : baseEnd_2004575 < baseStart_2004575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004726 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_2004726 : Nat := 118140960795 + 2004726 * 2 ^ 59
def prefixEnd_2004726 : Nat := 4983230072969 + 3 ^ 40 * 2004726 * 2
def baseEnd_2004726 : Nat := 343129339521809578001813

theorem tailTrace_2004726 : CollatzResearch.WordTrace tailWord_2004726 prefixEnd_2004726 343129339521809578001813 := by
  unfold tailWord_2004726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4569897758451722299228127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48745576090151704525100021 4569897758451722299228127)
  ·
    refine ⟨6854846637677583448842191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4569897758451722299228127 6854846637677583448842191)
    ·
      refine ⟨10282269956516375173263287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6854846637677583448842191 10282269956516375173263287)
      ·
        refine ⟨15423404934774562759894931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10282269956516375173263287 15423404934774562759894931)
        ·
          refine ⟨23135107402161844139842397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423404934774562759894931 23135107402161844139842397)
          ·
            refine ⟨8675665275810691552440899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23135107402161844139842397 8675665275810691552440899)
            ·
              refine ⟨13013497913716037328661349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8675665275810691552440899 13013497913716037328661349)
              ·
                refine ⟨2440030858821756999124003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13013497913716037328661349 2440030858821756999124003)
                ·
                  refine ⟨3660046288232635498686005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440030858821756999124003 3660046288232635498686005)
                  ·
                    refine ⟨343129339521809578001813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3660046288232635498686005 343129339521809578001813)
                    ·
                      rfl

theorem cell23_2004726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_2004726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004726 prefixEnd_2004726 := by exact prefixLift 2004726
  have htrace : WordTrace (prefixWord ++ tailWord_2004726) baseStart_2004726 baseEnd_2004726 := by
    simpa [prefixWord, tailWord_2004726, baseEnd_2004726] using wordTrace_append hprefix tailTrace_2004726
  have hstable : (prefixWord ++ tailWord_2004726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004726).length < 2 ^ (prefixWord ++ tailWord_2004726).sum := by decide
  have hdescent : baseEnd_2004726 < baseStart_2004726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004739 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 4, 4]
def baseStart_2004739 : Nat := 118140960795 + 2004739 * 2 ^ 59
def prefixEnd_2004739 : Nat := 4983230072969 + 3 ^ 40 * 2004739 * 2
def baseEnd_2004739 : Nat := 343131564604645727714293

theorem tailTrace_2004739 : CollatzResearch.WordTrace tailWord_2004739 prefixEnd_2004739 343131564604645727714293 := by
  unfold tailWord_2004739
  simp only [CollatzResearch.WordTrace]
  refine ⟨73118838284180460007873271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48745892189453640005248847 73118838284180460007873271)
  ·
    refine ⟨109678257426270690011809907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73118838284180460007873271 109678257426270690011809907)
    ·
      refine ⟨164517386139406035017714861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109678257426270690011809907 164517386139406035017714861)
      ·
        refine ⟨61694019802277263131643073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164517386139406035017714861 61694019802277263131643073)
        ·
          refine ⟨46270514851707947348732305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61694019802277263131643073 46270514851707947348732305)
          ·
            refine ⟨34702886138780960511549229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46270514851707947348732305 34702886138780960511549229)
            ·
              refine ⟨13013582302042860191830961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34702886138780960511549229 13013582302042860191830961)
              ·
                refine ⟨9760186726532145143873221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13013582302042860191830961 9760186726532145143873221)
                ·
                  refine ⟨1830035011224777214476229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9760186726532145143873221 1830035011224777214476229)
                  ·
                    refine ⟨343131564604645727714293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830035011224777214476229 343131564604645727714293)
                    ·
                      rfl

theorem cell23_2004739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 4].length) (baseStart_2004739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004739 prefixEnd_2004739 := by exact prefixLift 2004739
  have htrace : WordTrace (prefixWord ++ tailWord_2004739) baseStart_2004739 baseEnd_2004739 := by
    simpa [prefixWord, tailWord_2004739, baseEnd_2004739] using wordTrace_append hprefix tailTrace_2004739
  have hstable : (prefixWord ++ tailWord_2004739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004739).length < 2 ^ (prefixWord ++ tailWord_2004739).sum := by decide
  have hdescent : baseEnd_2004739 < baseStart_2004739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004740 : List Nat := [2, 3, 2, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_2004740 : Nat := 118140960795 + 2004740 * 2 ^ 59
def prefixEnd_2004740 : Nat := 4983230072969 + 3 ^ 40 * 2004740 * 2
def baseEnd_2004740 : Nat := 1029395207294591679230375

theorem tailTrace_2004740 : CollatzResearch.WordTrace tailWord_2004740 prefixEnd_2004740 1029395207294591679230375 := by
  unfold tailWord_2004740
  simp only [CollatzResearch.WordTrace]
  refine ⟨36559437378588418589329837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48745916504784558119106449 36559437378588418589329837)
  ·
    refine ⟨13709789016970656970998689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36559437378588418589329837 13709789016970656970998689)
    ·
      refine ⟨10282341762727992728249017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13709789016970656970998689 10282341762727992728249017)
      ·
        refine ⟨7711756322045994546186763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10282341762727992728249017 7711756322045994546186763)
        ·
          refine ⟨11567634483068991819280145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7711756322045994546186763 11567634483068991819280145)
          ·
            refine ⟨8675725862301743864460109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11567634483068991819280145 8675725862301743864460109)
            ·
              refine ⟨3253397198363153949172541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8675725862301743864460109 3253397198363153949172541)
              ·
                refine ⟨1220023949386182730939703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3253397198363153949172541 1220023949386182730939703)
                ·
                  refine ⟨1830035924079274096409555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220023949386182730939703 1830035924079274096409555)
                  ·
                    refine ⟨2745053886118911144614333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830035924079274096409555 2745053886118911144614333)
                    ·
                      refine ⟨1029395207294591679230375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2745053886118911144614333 1029395207294591679230375)
                      ·
                        rfl

theorem cell23_2004740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_2004740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004740 prefixEnd_2004740 := by exact prefixLift 2004740
  have htrace : WordTrace (prefixWord ++ tailWord_2004740) baseStart_2004740 baseEnd_2004740 := by
    simpa [prefixWord, tailWord_2004740, baseEnd_2004740] using wordTrace_append hprefix tailTrace_2004740
  have hstable : (prefixWord ++ tailWord_2004740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004740).length < 2 ^ (prefixWord ++ tailWord_2004740).sum := by decide
  have hdescent : baseEnd_2004740 < baseStart_2004740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004746 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2004746 : Nat := 118140960795 + 2004746 * 2 ^ 59
def prefixEnd_2004746 : Nat := 4983230072969 + 3 ^ 40 * 2004746 * 2
def baseEnd_2004746 : Nat := 1029398288178518655755347

theorem tailTrace_2004746 : CollatzResearch.WordTrace tailWord_2004746 prefixEnd_2004746 1029398288178518655755347 := by
  unfold tailWord_2004746
  simp only [CollatzResearch.WordTrace]
  refine ⟨18279773398788775050844523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48746062396770066802252061 18279773398788775050844523)
  ·
    refine ⟨27419660098183162576266785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18279773398788775050844523 27419660098183162576266785)
    ·
      refine ⟨20564745073637371932200089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27419660098183162576266785 20564745073637371932200089)
      ·
        refine ⟨15423558805228028949150067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20564745073637371932200089 15423558805228028949150067)
        ·
          refine ⟨23135338207842043423725101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15423558805228028949150067 23135338207842043423725101)
          ·
            refine ⟨8675751827940766283896913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23135338207842043423725101 8675751827940766283896913)
            ·
              refine ⟨6506813870955574712922685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8675751827940766283896913 6506813870955574712922685)
              ·
                refine ⟨2440055201608340517346007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6506813870955574712922685 2440055201608340517346007)
                ·
                  refine ⟨3660082802412510776019011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440055201608340517346007 3660082802412510776019011)
                  ·
                    refine ⟨5490124203618766164028517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3660082802412510776019011 5490124203618766164028517)
                    ·
                      refine ⟨1029398288178518655755347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5490124203618766164028517 1029398288178518655755347)
                      ·
                        rfl

theorem cell23_2004746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2004746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004746 prefixEnd_2004746 := by exact prefixLift 2004746
  have htrace : WordTrace (prefixWord ++ tailWord_2004746) baseStart_2004746 baseEnd_2004746 := by
    simpa [prefixWord, tailWord_2004746, baseEnd_2004746] using wordTrace_append hprefix tailTrace_2004746
  have hstable : (prefixWord ++ tailWord_2004746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004746).length < 2 ^ (prefixWord ++ tailWord_2004746).sum := by decide
  have hdescent : baseEnd_2004746 < baseStart_2004746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2004759 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2004759 : Nat := 118140960795 + 2004759 * 2 ^ 59
def prefixEnd_2004759 : Nat := 4983230072969 + 3 ^ 40 * 2004759 * 2
def baseEnd_2004759 : Nat := 1029404963427027104892787

theorem tailTrace_2004759 : CollatzResearch.WordTrace tailWord_2004759 prefixEnd_2004759 1029404963427027104892787 := by
  unfold tailWord_2004759
  simp only [CollatzResearch.WordTrace]
  refine ⟨73119567744108003423601331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48746378496072002282400887 73119567744108003423601331)
  ·
    refine ⟨109679351616162005135401997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73119567744108003423601331 109679351616162005135401997)
    ·
      refine ⟨41129756856060751925775749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109679351616162005135401997 41129756856060751925775749)
      ·
        refine ⟨7711829410511390986082953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41129756856060751925775749 7711829410511390986082953)
        ·
          refine ⟨5783872057883543239562215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7711829410511390986082953 5783872057883543239562215)
          ·
            refine ⟨8675808086825314859343323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5783872057883543239562215 8675808086825314859343323)
            ·
              refine ⟨13013712130237972289014985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8675808086825314859343323 13013712130237972289014985)
              ·
                refine ⟨9760284097678479216761239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13013712130237972289014985 9760284097678479216761239)
                ·
                  refine ⟨14640426146517718825141859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9760284097678479216761239 14640426146517718825141859)
                  ·
                    refine ⟨21960639219776578237712789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14640426146517718825141859 21960639219776578237712789)
                    ·
                      refine ⟨1029404963427027104892787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21960639219776578237712789 1029404963427027104892787)
                      ·
                        rfl

theorem cell23_2004759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2004759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2004759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2004759 prefixEnd_2004759 := by exact prefixLift 2004759
  have htrace : WordTrace (prefixWord ++ tailWord_2004759) baseStart_2004759 baseEnd_2004759 := by
    simpa [prefixWord, tailWord_2004759, baseEnd_2004759] using wordTrace_append hprefix tailTrace_2004759
  have hstable : (prefixWord ++ tailWord_2004759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2004759).length < 2 ^ (prefixWord ++ tailWord_2004759).sum := by decide
  have hdescent : baseEnd_2004759 < baseStart_2004759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2004759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
