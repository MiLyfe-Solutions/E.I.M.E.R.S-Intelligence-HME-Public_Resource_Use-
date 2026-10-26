import V185TrunkScan23Chunk0953

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5648198 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5648198 : Nat := 118140960795 + 5648198 * 2 ^ 59
def prefixEnd_5648198 : Nat := 4983230072969 + 3 ^ 40 * 5648198 * 2
def baseEnd_5648198 : Nat := 2900240405763597633049417

theorem tailTrace_5648198 : CollatzResearch.WordTrace tailWord_5648198 prefixEnd_5648198 2900240405763597633049417 := by
  unfold tailWord_5648198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437709537235961133280039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137337803461033837509974165 6437709537235961133280039)
  ·
    refine ⟨9656564305853941699920059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6437709537235961133280039 9656564305853941699920059)
    ·
      refine ⟨14484846458780912549880089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9656564305853941699920059 14484846458780912549880089)
      ·
        refine ⟨10863634844085684412410067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14484846458780912549880089 10863634844085684412410067)
        ·
          refine ⟨16295452266128526618615101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10863634844085684412410067 16295452266128526618615101)
          ·
            refine ⟨6110794599798197481980663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16295452266128526618615101 6110794599798197481980663)
            ·
              refine ⟨9166191899697296222970995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110794599798197481980663 9166191899697296222970995)
              ·
                refine ⟨13749287849545944334456493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9166191899697296222970995 13749287849545944334456493)
                ·
                  refine ⟨5155982943579729125421185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13749287849545944334456493 5155982943579729125421185)
                  ·
                    refine ⟨3866987207684796844065889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5155982943579729125421185 3866987207684796844065889)
                    ·
                      refine ⟨2900240405763597633049417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3866987207684796844065889 2900240405763597633049417)
                      ·
                        rfl

theorem cell23_5648198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5648198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648198 prefixEnd_5648198 := by exact prefixLift 5648198
  have htrace : WordTrace (prefixWord ++ tailWord_5648198) baseStart_5648198 baseEnd_5648198 := by
    simpa [prefixWord, tailWord_5648198, baseEnd_5648198] using wordTrace_append hprefix tailTrace_5648198
  have hstable : (prefixWord ++ tailWord_5648198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648198).length < 2 ^ (prefixWord ++ tailWord_5648198).sum := by decide
  have hdescent : baseEnd_5648198 < baseStart_5648198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648223 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 5]
def baseStart_5648223 : Nat := 118140960795 + 5648223 * 2 ^ 59
def prefixEnd_5648223 : Nat := 4983230072969 + 3 ^ 40 * 5648223 * 2
def baseEnd_5648223 : Nat := 2900253242779960035236801

theorem tailTrace_5648223 : CollatzResearch.WordTrace tailWord_5648223 prefixEnd_5648223 2900253242779960035236801 := by
  unfold tailWord_5648223
  simp only [CollatzResearch.WordTrace]
  refine ⟨206007617016460185534621323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137338411344306790356414215 206007617016460185534621323)
  ·
    refine ⟨309011425524690278301931985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206007617016460185534621323 309011425524690278301931985)
    ·
      refine ⟨231758569143517708726448989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309011425524690278301931985 231758569143517708726448989)
      ·
        refine ⟨86909463428819140772418371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231758569143517708726448989 86909463428819140772418371)
        ·
          refine ⟨130364195143228711158627557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86909463428819140772418371 130364195143228711158627557)
          ·
            refine ⟨24443286589355383342242667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130364195143228711158627557 24443286589355383342242667)
            ·
              refine ⟨36664929884033075013364001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24443286589355383342242667 36664929884033075013364001)
              ·
                refine ⟨27498697413024806260023001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36664929884033075013364001 27498697413024806260023001)
                ·
                  refine ⟨20624023059768604695017251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27498697413024806260023001 20624023059768604695017251)
                  ·
                    refine ⟨30936034589652907042525877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20624023059768604695017251 30936034589652907042525877)
                    ·
                      refine ⟨2900253242779960035236801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30936034589652907042525877 2900253242779960035236801)
                      ·
                        rfl

theorem cell23_5648223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_5648223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648223 prefixEnd_5648223 := by exact prefixLift 5648223
  have htrace : WordTrace (prefixWord ++ tailWord_5648223) baseStart_5648223 baseEnd_5648223 := by
    simpa [prefixWord, tailWord_5648223, baseEnd_5648223] using wordTrace_append hprefix tailTrace_5648223
  have hstable : (prefixWord ++ tailWord_5648223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648223).length < 2 ^ (prefixWord ++ tailWord_5648223).sum := by decide
  have hdescent : baseEnd_5648223 < baseStart_5648223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648224 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 1, 3, 2]
def baseStart_5648224 : Nat := 118140960795 + 5648224 * 2 ^ 59
def prefixEnd_5648224 : Nat := 4983230072969 + 3 ^ 40 * 5648224 * 2
def baseEnd_5648224 : Nat := 2900253756260614531324297

theorem tailTrace_5648224 : CollatzResearch.WordTrace tailWord_5648224 prefixEnd_5648224 2900253756260614531324297 := by
  unfold tailWord_5648224
  simp only [CollatzResearch.WordTrace]
  refine ⟨103003826744728281352703863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137338435659637708470271817 103003826744728281352703863)
  ·
    refine ⟨154505740117092422029055795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103003826744728281352703863 154505740117092422029055795)
    ·
      refine ⟨231758610175638633043583693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154505740117092422029055795 231758610175638633043583693)
      ·
        refine ⟨86909478815864487391343885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231758610175638633043583693 86909478815864487391343885)
        ·
          refine ⟨32591054555949182771753957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86909478815864487391343885 32591054555949182771753957)
          ·
            refine ⟨6110822729240471769703867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32591054555949182771753957 6110822729240471769703867)
            ·
              refine ⟨9166234093860707654555801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110822729240471769703867 9166234093860707654555801)
              ·
                refine ⟨6874675570395530740916851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9166234093860707654555801 6874675570395530740916851)
                ·
                  refine ⟨10312013355593296111375277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6874675570395530740916851 10312013355593296111375277)
                  ·
                    refine ⟨3867005008347486041765729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10312013355593296111375277 3867005008347486041765729)
                    ·
                      refine ⟨2900253756260614531324297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867005008347486041765729 2900253756260614531324297)
                      ·
                        rfl

theorem cell23_5648224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_5648224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648224 prefixEnd_5648224 := by exact prefixLift 5648224
  have htrace : WordTrace (prefixWord ++ tailWord_5648224) baseStart_5648224 baseEnd_5648224 := by
    simpa [prefixWord, tailWord_5648224, baseEnd_5648224] using wordTrace_append hprefix tailTrace_5648224
  have hstable : (prefixWord ++ tailWord_5648224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648224).length < 2 ^ (prefixWord ++ tailWord_5648224).sum := by decide
  have hdescent : baseEnd_5648224 < baseStart_5648224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648237 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_5648237 : Nat := 118140960795 + 5648237 * 2 ^ 59
def prefixEnd_5648237 : Nat := 4983230072969 + 3 ^ 40 * 5648237 * 2
def baseEnd_5648237 : Nat := 2900260431509122980461737

theorem tailTrace_5648237 : CollatzResearch.WordTrace tailWord_5648237 prefixEnd_5648237 2900260431509122980461737 := by
  unfold tailWord_5648237
  simp only [CollatzResearch.WordTrace]
  refine ⟨206008127638409465925630965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137338751758939643950420643 206008127638409465925630965)
  ·
    refine ⟨19313261966100887430527903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206008127638409465925630965 19313261966100887430527903)
    ·
      refine ⟨28969892949151331145791855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19313261966100887430527903 28969892949151331145791855)
      ·
        refine ⟨43454839423726996718687783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28969892949151331145791855 43454839423726996718687783)
        ·
          refine ⟨65182259135590495078031675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43454839423726996718687783 65182259135590495078031675)
          ·
            refine ⟨97773388703385742617047513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65182259135590495078031675 97773388703385742617047513)
            ·
              refine ⟨73330041527539306962785635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97773388703385742617047513 73330041527539306962785635)
              ·
                refine ⟨109995062291308960444178453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73330041527539306962785635 109995062291308960444178453)
                ·
                  refine ⟨5156018544905107520820865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109995062291308960444178453 5156018544905107520820865)
                  ·
                    refine ⟨3867013908678830640615649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5156018544905107520820865 3867013908678830640615649)
                    ·
                      refine ⟨2900260431509122980461737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867013908678830640615649 2900260431509122980461737)
                      ·
                        rfl

theorem cell23_5648237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_5648237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648237 prefixEnd_5648237 := by exact prefixLift 5648237
  have htrace : WordTrace (prefixWord ++ tailWord_5648237) baseStart_5648237 baseEnd_5648237 := by
    simpa [prefixWord, tailWord_5648237, baseEnd_5648237] using wordTrace_append hprefix tailTrace_5648237
  have hstable : (prefixWord ++ tailWord_5648237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648237).length < 2 ^ (prefixWord ++ tailWord_5648237).sum := by decide
  have hdescent : baseEnd_5648237 < baseStart_5648237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648273 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 4, 5]
def baseStart_5648273 : Nat := 118140960795 + 5648273 * 2 ^ 59
def prefixEnd_5648273 : Nat := 4983230072969 + 3 ^ 40 * 5648273 * 2
def baseEnd_5648273 : Nat := 966759638937561613203857

theorem tailTrace_5648273 : CollatzResearch.WordTrace tailWord_5648273 prefixEnd_5648273 966759638937561613203857 := by
  unfold tailWord_5648273
  simp only [CollatzResearch.WordTrace]
  refine ⟨206009440666279044073941473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137339627110852696049294315 206009440666279044073941473)
  ·
    refine ⟨154507080499709283055456105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206009440666279044073941473 154507080499709283055456105)
    ·
      refine ⟨115880310374781962291592079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154507080499709283055456105 115880310374781962291592079)
      ·
        refine ⟨173820465562172943437388119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115880310374781962291592079 173820465562172943437388119)
        ·
          refine ⟨260730698343259415156082179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173820465562172943437388119 260730698343259415156082179)
          ·
            refine ⟨391096047514889122734123269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260730698343259415156082179 391096047514889122734123269)
            ·
              refine ⟨73330508909041710512648113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 391096047514889122734123269 73330508909041710512648113)
              ·
                refine ⟨54997881681781282884486085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73330508909041710512648113 54997881681781282884486085)
                ·
                  refine ⟨10312102815333990540841141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54997881681781282884486085 10312102815333990540841141)
                  ·
                    refine ⟨966759638937561613203857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10312102815333990540841141 966759638937561613203857)
                    ·
                      rfl

theorem cell23_5648273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_5648273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648273 prefixEnd_5648273 := by exact prefixLift 5648273
  have htrace : WordTrace (prefixWord ++ tailWord_5648273) baseStart_5648273 baseEnd_5648273 := by
    simpa [prefixWord, tailWord_5648273, baseEnd_5648273] using wordTrace_append hprefix tailTrace_5648273
  have hstable : (prefixWord ++ tailWord_5648273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648273).length < 2 ^ (prefixWord ++ tailWord_5648273).sum := by decide
  have hdescent : baseEnd_5648273 < baseStart_5648273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648323 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 4]
def baseStart_5648323 : Nat := 118140960795 + 5648323 * 2 ^ 59
def prefixEnd_5648323 : Nat := 4983230072969 + 3 ^ 40 * 5648323 * 2
def baseEnd_5648323 : Nat := 2900304590845409643986341

theorem tailTrace_5648323 : CollatzResearch.WordTrace tailWord_5648323 prefixEnd_5648323 2900304590845409643986341 := by
  unfold tailWord_5648323
  simp only [CollatzResearch.WordTrace]
  refine ⟨206011264316097902613261623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137340842877398601742174415 206011264316097902613261623)
  ·
    refine ⟨309016896474146853919892435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206011264316097902613261623 309016896474146853919892435)
    ·
      refine ⟨463525344711220280879838653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309016896474146853919892435 463525344711220280879838653)
      ·
        refine ⟨173822004266707605329939495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 463525344711220280879838653 173822004266707605329939495)
        ·
          refine ⟨260733006400061407994909243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173822004266707605329939495 260733006400061407994909243)
          ·
            refine ⟨391099509600092111992363865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260733006400061407994909243 391099509600092111992363865)
            ·
              refine ⟨293324632200069083994272899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391099509600092111992363865 293324632200069083994272899)
              ·
                refine ⟨439986948300103625991409349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293324632200069083994272899 439986948300103625991409349)
                ·
                  refine ⟨82497552806269429873389253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439986948300103625991409349 82497552806269429873389253)
                  ·
                    refine ⟨15468291151175518101260485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82497552806269429873389253 15468291151175518101260485)
                    ·
                      refine ⟨2900304590845409643986341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15468291151175518101260485 2900304590845409643986341)
                      ·
                        rfl

theorem cell23_5648323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_5648323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648323 prefixEnd_5648323 := by exact prefixLift 5648323
  have htrace : WordTrace (prefixWord ++ tailWord_5648323) baseStart_5648323 baseEnd_5648323 := by
    simpa [prefixWord, tailWord_5648323, baseEnd_5648323] using wordTrace_append hprefix tailTrace_5648323
  have hstable : (prefixWord ++ tailWord_5648323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648323).length < 2 ^ (prefixWord ++ tailWord_5648323).sum := by decide
  have hdescent : baseEnd_5648323 < baseStart_5648323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648330 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_5648330 : Nat := 118140960795 + 5648330 * 2 ^ 59
def prefixEnd_5648330 : Nat := 4983230072969 + 3 ^ 40 * 5648330 * 2
def baseEnd_5648330 : Nat := 2900308185209991116598809

theorem tailTrace_5648330 : CollatzResearch.WordTrace tailWord_5648330 prefixEnd_5648330 2900308185209991116598809 := by
  unfold tailWord_5648330
  simp only [CollatzResearch.WordTrace]
  refine ⟨51502879906768135702191611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137341013084715028539177629 51502879906768135702191611)
  ·
    refine ⟨77254319860152203553287417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51502879906768135702191611 77254319860152203553287417)
    ·
      refine ⟨57940739895114152664965563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77254319860152203553287417 57940739895114152664965563)
      ·
        refine ⟨86911109842671228997448345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57940739895114152664965563 86911109842671228997448345)
        ·
          refine ⟨65183332382003421748086259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86911109842671228997448345 65183332382003421748086259)
          ·
            refine ⟨97774998573005132622129389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65183332382003421748086259 97774998573005132622129389)
            ·
              refine ⟨36665624464876924733298521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97774998573005132622129389 36665624464876924733298521)
              ·
                refine ⟨27499218348657693549973891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36665624464876924733298521 27499218348657693549973891)
                ·
                  refine ⟨41248827522986540324960837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27499218348657693549973891 41248827522986540324960837)
                  ·
                    refine ⟨7734155160559976310930157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41248827522986540324960837 7734155160559976310930157)
                    ·
                      refine ⟨2900308185209991116598809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7734155160559976310930157 2900308185209991116598809)
                      ·
                        rfl

theorem cell23_5648330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_5648330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648330 prefixEnd_5648330 := by exact prefixLift 5648330
  have htrace : WordTrace (prefixWord ++ tailWord_5648330) baseStart_5648330 baseEnd_5648330 := by
    simpa [prefixWord, tailWord_5648330, baseEnd_5648330] using wordTrace_append hprefix tailTrace_5648330
  have hstable : (prefixWord ++ tailWord_5648330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648330).length < 2 ^ (prefixWord ++ tailWord_5648330).sum := by decide
  have hdescent : baseEnd_5648330 < baseStart_5648330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648340 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5648340 : Nat := 118140960795 + 5648340 * 2 ^ 59
def prefixEnd_5648340 : Nat := 4983230072969 + 3 ^ 40 * 5648340 * 2
def baseEnd_5648340 : Nat := 2900313320016536077473763

theorem tailTrace_5648340 : CollatzResearch.WordTrace tailWord_5648340 prefixEnd_5648340 2900313320016536077473763 := by
  unfold tailWord_5648340
  simp only [CollatzResearch.WordTrace]
  refine ⟨103005942178518157258315237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137341256238024209677753649 103005942178518157258315237)
  ·
    refine ⟨19313614158472154485934107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103005942178518157258315237 19313614158472154485934107)
    ·
      refine ⟨28970421237708231728901161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19313614158472154485934107 28970421237708231728901161)
      ·
        refine ⟨21727815928281173796675871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28970421237708231728901161 21727815928281173796675871)
        ·
          refine ⟨32591723892421760695013807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21727815928281173796675871 32591723892421760695013807)
          ·
            refine ⟨48887585838632641042520711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32591723892421760695013807 48887585838632641042520711)
            ·
              refine ⟨73331378757948961563781067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48887585838632641042520711 73331378757948961563781067)
              ·
                refine ⟨109997068136923442345671601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73331378757948961563781067 109997068136923442345671601)
                ·
                  refine ⟨82497801102692581759253701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109997068136923442345671601 82497801102692581759253701)
                  ·
                    refine ⟨15468337706754859079860069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82497801102692581759253701 15468337706754859079860069)
                    ·
                      refine ⟨2900313320016536077473763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15468337706754859079860069 2900313320016536077473763)
                      ·
                        rfl

theorem cell23_5648340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5648340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648340 prefixEnd_5648340 := by exact prefixLift 5648340
  have htrace : WordTrace (prefixWord ++ tailWord_5648340) baseStart_5648340 baseEnd_5648340 := by
    simpa [prefixWord, tailWord_5648340, baseEnd_5648340] using wordTrace_append hprefix tailTrace_5648340
  have hstable : (prefixWord ++ tailWord_5648340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648340).length < 2 ^ (prefixWord ++ tailWord_5648340).sum := by decide
  have hdescent : baseEnd_5648340 < baseStart_5648340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648380 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_5648380 : Nat := 118140960795 + 5648380 * 2 ^ 59
def prefixEnd_5648380 : Nat := 4983230072969 + 3 ^ 40 * 5648380 * 2
def baseEnd_5648380 : Nat := 966777953080905306991193

theorem tailTrace_5648380 : CollatzResearch.WordTrace tailWord_5648380 prefixEnd_5648380 966777953080905306991193 := by
  unfold tailWord_5648380
  simp only [CollatzResearch.WordTrace]
  refine ⟨103006671638445700674043297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137342228851260934232057729 103006671638445700674043297)
  ·
    refine ⟨77255003728834275505532473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103006671638445700674043297 77255003728834275505532473)
    ·
      refine ⟨57941252796625706629149355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77255003728834275505532473 57941252796625706629149355)
      ·
        refine ⟨86911879194938559943724033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57941252796625706629149355 86911879194938559943724033)
        ·
          refine ⟨65183909396203919957793025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86911879194938559943724033 65183909396203919957793025)
          ·
            refine ⟨48887932047152939968344769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65183909396203919957793025 48887932047152939968344769)
            ·
              refine ⟨36665949035364704976258577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48887932047152939968344769 36665949035364704976258577)
              ·
                refine ⟨27499461776523528732193933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36665949035364704976258577 27499461776523528732193933)
                ·
                  refine ⟨10312298166196323274572725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27499461776523528732193933 10312298166196323274572725)
                  ·
                    refine ⟨966777953080905306991193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10312298166196323274572725 966777953080905306991193)
                    ·
                      rfl

theorem cell23_5648380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_5648380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648380 prefixEnd_5648380 := by exact prefixLift 5648380
  have htrace : WordTrace (prefixWord ++ tailWord_5648380) baseStart_5648380 baseEnd_5648380 := by
    simpa [prefixWord, tailWord_5648380, baseEnd_5648380] using wordTrace_append hprefix tailTrace_5648380
  have hstable : (prefixWord ++ tailWord_5648380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648380).length < 2 ^ (prefixWord ++ tailWord_5648380).sum := by decide
  have hdescent : baseEnd_5648380 < baseStart_5648380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648400 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_5648400 : Nat := 118140960795 + 5648400 * 2 ^ 59
def prefixEnd_5648400 : Nat := 4983230072969 + 3 ^ 40 * 5648400 * 2
def baseEnd_5648400 : Nat := 2900344128855805842723487

theorem tailTrace_5648400 : CollatzResearch.WordTrace tailWord_5648400 prefixEnd_5648400 2900344128855805842723487 := by
  unfold tailWord_5648400
  simp only [CollatzResearch.WordTrace]
  refine ⟨103007036368409472381907327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137342715157879296509209769 103007036368409472381907327)
  ·
    refine ⟨154510554552614208572860991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103007036368409472381907327 154510554552614208572860991)
    ·
      refine ⟨231765831828921312859291487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154510554552614208572860991 231765831828921312859291487)
      ·
        refine ⟨347648747743381969288937231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231765831828921312859291487 347648747743381969288937231)
        ·
          refine ⟨521473121615072953933405847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347648747743381969288937231 521473121615072953933405847)
          ·
            refine ⟨782209682422609430900108771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521473121615072953933405847 782209682422609430900108771)
            ·
              refine ⟨1173314523633914146350163157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782209682422609430900108771 1173314523633914146350163157)
              ·
                refine ⟨27499559147669862805081949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1173314523633914146350163157 27499559147669862805081949)
                ·
                  refine ⟨10312334680376198551905731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27499559147669862805081949 10312334680376198551905731)
                  ·
                    refine ⟨15468502020564297827858597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10312334680376198551905731 15468502020564297827858597)
                    ·
                      refine ⟨2900344128855805842723487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15468502020564297827858597 2900344128855805842723487)
                      ·
                        rfl

theorem cell23_5648400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_5648400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648400 prefixEnd_5648400 := by exact prefixLift 5648400
  have htrace : WordTrace (prefixWord ++ tailWord_5648400) baseStart_5648400 baseEnd_5648400 := by
    simpa [prefixWord, tailWord_5648400, baseEnd_5648400] using wordTrace_append hprefix tailTrace_5648400
  have hstable : (prefixWord ++ tailWord_5648400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648400).length < 2 ^ (prefixWord ++ tailWord_5648400).sum := by decide
  have hdescent : baseEnd_5648400 < baseStart_5648400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648410 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_5648410 : Nat := 118140960795 + 5648410 * 2 ^ 59
def prefixEnd_5648410 : Nat := 4983230072969 + 3 ^ 40 * 5648410 * 2
def baseEnd_5648410 : Nat := 966783087887450267866147

theorem tailTrace_5648410 : CollatzResearch.WordTrace tailWord_5648410 prefixEnd_5648410 966783087887450267866147 := by
  unfold tailWord_5648410
  simp only [CollatzResearch.WordTrace]
  refine ⟨51503609366695679117919671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137342958311188477647785789 51503609366695679117919671)
  ·
    refine ⟨77255414050043518676879507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51503609366695679117919671 77255414050043518676879507)
    ·
      refine ⟨115883121075065278015319261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77255414050043518676879507 115883121075065278015319261)
      ·
        refine ⟨43456170403149479255744723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115883121075065278015319261 43456170403149479255744723)
        ·
          refine ⟨65184255604724218883617085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43456170403149479255744723 65184255604724218883617085)
          ·
            refine ⟨24444095851771582081356407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65184255604724218883617085 24444095851771582081356407)
            ·
              refine ⟨36666143777657373122034611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24444095851771582081356407 36666143777657373122034611)
              ·
                refine ⟨54999215666486059683051917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36666143777657373122034611 54999215666486059683051917)
                ·
                  refine ⟨20624705874932272381144469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54999215666486059683051917 20624705874932272381144469)
                  ·
                    refine ⟨966783087887450267866147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20624705874932272381144469 966783087887450267866147)
                    ·
                      rfl

theorem cell23_5648410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_5648410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648410 prefixEnd_5648410 := by exact prefixLift 5648410
  have htrace : WordTrace (prefixWord ++ tailWord_5648410) baseStart_5648410 baseEnd_5648410 := by
    simpa [prefixWord, tailWord_5648410, baseEnd_5648410] using wordTrace_append hprefix tailTrace_5648410
  have hstable : (prefixWord ++ tailWord_5648410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648410).length < 2 ^ (prefixWord ++ tailWord_5648410).sum := by decide
  have hdescent : baseEnd_5648410 < baseStart_5648410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648437 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_5648437 : Nat := 118140960795 + 5648437 * 2 ^ 59
def prefixEnd_5648437 : Nat := 4983230072969 + 3 ^ 40 * 5648437 * 2
def baseEnd_5648437 : Nat := 2900363127640022197960817

theorem tailTrace_5648437 : CollatzResearch.WordTrace tailWord_5648437 prefixEnd_5648437 2900363127640022197960817 := by
  unfold tailWord_5648437
  simp only [CollatzResearch.WordTrace]
  refine ⟨206015422237684900082911565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137343614825123266721941043 206015422237684900082911565)
  ·
    refine ⟨77255783339131837531091837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206015422237684900082911565 77255783339131837531091837)
    ·
      refine ⟨28970918752174439074159439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77255783339131837531091837 28970918752174439074159439)
      ·
        refine ⟨43456378128261658611239159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28970918752174439074159439 43456378128261658611239159)
        ·
          refine ⟨65184567192392487916858739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43456378128261658611239159 65184567192392487916858739)
          ·
            refine ⟨97776850788588731875288109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65184567192392487916858739 97776850788588731875288109)
            ·
              refine ⟨36666319045720774453233041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97776850788588731875288109 36666319045720774453233041)
              ·
                refine ⟨27499739284290580839924781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36666319045720774453233041 27499739284290580839924781)
                ·
                  refine ⟨10312402231608967814971793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27499739284290580839924781 10312402231608967814971793)
                  ·
                    refine ⟨7734301673706725861228845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10312402231608967814971793 7734301673706725861228845)
                    ·
                      refine ⟨2900363127640022197960817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7734301673706725861228845 2900363127640022197960817)
                      ·
                        rfl

theorem cell23_5648437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_5648437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648437 prefixEnd_5648437 := by exact prefixLift 5648437
  have htrace : WordTrace (prefixWord ++ tailWord_5648437) baseStart_5648437 baseEnd_5648437 := by
    simpa [prefixWord, tailWord_5648437, baseEnd_5648437] using wordTrace_append hprefix tailTrace_5648437
  have hstable : (prefixWord ++ tailWord_5648437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648437).length < 2 ^ (prefixWord ++ tailWord_5648437).sum := by decide
  have hdescent : baseEnd_5648437 < baseStart_5648437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648478 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_5648478 : Nat := 118140960795 + 5648478 * 2 ^ 59
def prefixEnd_5648478 : Nat := 4983230072969 + 3 ^ 40 * 5648478 * 2
def baseEnd_5648478 : Nat := 966794726782285512516043

theorem tailTrace_5648478 : CollatzResearch.WordTrace tailWord_5648478 prefixEnd_5648478 966794726782285512516043 := by
  unfold tailWord_5648478
  simp only [CollatzResearch.WordTrace]
  refine ⟨25752114703817045510644261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137344611753690909390102725 25752114703817045510644261)
  ·
    refine ⟨4828521506965696033245799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25752114703817045510644261 4828521506965696033245799)
    ·
      refine ⟨7242782260448544049868699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4828521506965696033245799 7242782260448544049868699)
      ·
        refine ⟨10864173390672816074803049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7242782260448544049868699 10864173390672816074803049)
        ·
          refine ⟨8148130043004612056102287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10864173390672816074803049 8148130043004612056102287)
          ·
            refine ⟨12222195064506918084153431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8148130043004612056102287 12222195064506918084153431)
            ·
              refine ⟨18333292596760377126230147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12222195064506918084153431 18333292596760377126230147)
              ·
                refine ⟨27499938895140565689345221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18333292596760377126230147 27499938895140565689345221)
                ·
                  refine ⟨5156238542838856066752229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27499938895140565689345221 5156238542838856066752229)
                  ·
                    refine ⟨966794726782285512516043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5156238542838856066752229 966794726782285512516043)
                    ·
                      rfl

theorem cell23_5648478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_5648478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648478 prefixEnd_5648478 := by exact prefixLift 5648478
  have htrace : WordTrace (prefixWord ++ tailWord_5648478) baseStart_5648478 baseEnd_5648478 := by
    simpa [prefixWord, tailWord_5648478, baseEnd_5648478] using wordTrace_append hprefix tailTrace_5648478
  have hstable : (prefixWord ++ tailWord_5648478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648478).length < 2 ^ (prefixWord ++ tailWord_5648478).sum := by decide
  have hdescent : baseEnd_5648478 < baseStart_5648478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648541 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_5648541 : Nat := 118140960795 + 5648541 * 2 ^ 59
def prefixEnd_5648541 : Nat := 4983230072969 + 3 ^ 40 * 5648541 * 2
def baseEnd_5648541 : Nat := 2900416529628089791060339

theorem tailTrace_5648541 : CollatzResearch.WordTrace tailWord_5648541 prefixEnd_5648541 2900416529628089791060339 := by
  unfold tailWord_5648541
  simp only [CollatzResearch.WordTrace]
  refine ⟨206019215429308125844697477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137346143619538750563131651 206019215429308125844697477)
  ·
    refine ⟨38628602892995273595880777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206019215429308125844697477 38628602892995273595880777)
    ·
      refine ⟨28971452169746455196910583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38628602892995273595880777 28971452169746455196910583)
      ·
        refine ⟨43457178254619682795365875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28971452169746455196910583 43457178254619682795365875)
        ·
          refine ⟨65185767381929524193048813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43457178254619682795365875 65185767381929524193048813)
          ·
            refine ⟨24444662768223571572393305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65185767381929524193048813 24444662768223571572393305)
            ·
              refine ⟨18333497076167678679294979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24444662768223571572393305 18333497076167678679294979)
              ·
                refine ⟨27500245614251518018942469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18333497076167678679294979 27500245614251518018942469)
                ·
                  refine ⟨5156296052672159628551713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27500245614251518018942469 5156296052672159628551713)
                  ·
                    refine ⟨3867222039504119721413785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5156296052672159628551713 3867222039504119721413785)
                    ·
                      refine ⟨2900416529628089791060339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867222039504119721413785 2900416529628089791060339)
                      ·
                        rfl

theorem cell23_5648541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_5648541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648541 prefixEnd_5648541 := by exact prefixLift 5648541
  have htrace : WordTrace (prefixWord ++ tailWord_5648541) baseStart_5648541 baseEnd_5648541 := by
    simpa [prefixWord, tailWord_5648541, baseEnd_5648541] using wordTrace_append hprefix tailTrace_5648541
  have hstable : (prefixWord ++ tailWord_5648541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648541).length < 2 ^ (prefixWord ++ tailWord_5648541).sum := by decide
  have hdescent : baseEnd_5648541 < baseStart_5648541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648594 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_5648594 : Nat := 118140960795 + 5648594 * 2 ^ 59
def prefixEnd_5648594 : Nat := 4983230072969 + 3 ^ 40 * 5648594 * 2
def baseEnd_5648594 : Nat := 966814581367592694565865

theorem tailTrace_5648594 : CollatzResearch.WordTrace tailWord_5648594 prefixEnd_5648594 966814581367592694565865 := by
  unfold tailWord_5648594
  simp only [CollatzResearch.WordTrace]
  refine ⟨51505287124529028974094209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137347432332077410597584557 51505287124529028974094209)
  ·
    refine ⟨38628965343396771730570657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51505287124529028974094209 38628965343396771730570657)
    ·
      refine ⟨28971724007547578797927993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38628965343396771730570657 28971724007547578797927993)
      ·
        refine ⟨21728793005660684098445995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28971724007547578797927993 21728793005660684098445995)
        ·
          refine ⟨32593189508491026147668993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21728793005660684098445995 32593189508491026147668993)
          ·
            refine ⟨24444892131368269610751745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32593189508491026147668993 24444892131368269610751745)
            ·
              refine ⟨18333669098526202208063809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24444892131368269610751745 18333669098526202208063809)
              ·
                refine ⟨13750251823894651656047857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18333669098526202208063809 13750251823894651656047857)
                ·
                  refine ⟨10312688867920988742035893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13750251823894651656047857 10312688867920988742035893)
                  ·
                    refine ⟨966814581367592694565865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10312688867920988742035893 966814581367592694565865)
                    ·
                      rfl

theorem cell23_5648594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_5648594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648594 prefixEnd_5648594 := by exact prefixLift 5648594
  have htrace : WordTrace (prefixWord ++ tailWord_5648594) baseStart_5648594 baseEnd_5648594 := by
    simpa [prefixWord, tailWord_5648594, baseEnd_5648594] using wordTrace_append hprefix tailTrace_5648594
  have hstable : (prefixWord ++ tailWord_5648594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648594).length < 2 ^ (prefixWord ++ tailWord_5648594).sum := by decide
  have hdescent : baseEnd_5648594 < baseStart_5648594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648598 : List Nat := [5, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_5648598 : Nat := 118140960795 + 5648598 * 2 ^ 59
def prefixEnd_5648598 : Nat := 4983230072969 + 3 ^ 40 * 5648598 * 2
def baseEnd_5648598 : Nat := 322271755336155118671953

theorem tailTrace_5648598 : CollatzResearch.WordTrace tailWord_5648598 prefixEnd_5648598 322271755336155118671953 := by
  unfold tailWord_5648598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12876330899381351536220153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137347529593401083053014965 12876330899381351536220153)
  ·
    refine ⟨9657248174536013652165115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12876330899381351536220153 9657248174536013652165115)
    ·
      refine ⟨14485872261804020478247673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9657248174536013652165115 14485872261804020478247673)
      ·
        refine ⟨10864404196353015358685755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14485872261804020478247673 10864404196353015358685755)
        ·
          refine ⟨16296606294529523038028633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10864404196353015358685755 16296606294529523038028633)
          ·
            refine ⟨12222454720897142278521475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16296606294529523038028633 12222454720897142278521475)
            ·
              refine ⟨18333682081345713417782213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12222454720897142278521475 18333682081345713417782213)
              ·
                refine ⟨3437565390252321265834165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18333682081345713417782213 3437565390252321265834165)
                ·
                  refine ⟨322271755336155118671953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3437565390252321265834165 322271755336155118671953)
                  ·
                    rfl

theorem cell23_5648598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_5648598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648598 prefixEnd_5648598 := by exact prefixLift 5648598
  have htrace : WordTrace (prefixWord ++ tailWord_5648598) baseStart_5648598 baseEnd_5648598 := by
    simpa [prefixWord, tailWord_5648598, baseEnd_5648598] using wordTrace_append hprefix tailTrace_5648598
  have hstable : (prefixWord ++ tailWord_5648598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648598).length < 2 ^ (prefixWord ++ tailWord_5648598).sum := by decide
  have hdescent : baseEnd_5648598 < baseStart_5648598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648617 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 3]
def baseStart_5648617 : Nat := 118140960795 + 5648617 * 2 ^ 59
def prefixEnd_5648617 : Nat := 4983230072969 + 3 ^ 40 * 5648617 * 2
def baseEnd_5648617 : Nat := 2900455554157831493709989

theorem tailTrace_5648617 : CollatzResearch.WordTrace tailWord_5648617 prefixEnd_5648617 2900455554157831493709989 := by
  unfold tailWord_5648617
  simp only [CollatzResearch.WordTrace]
  refine ⟨206021987377032790824464105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137347991584688527216309403 206021987377032790824464105)
  ·
    refine ⟨154516490532774593118348079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206021987377032790824464105 154516490532774593118348079)
    ·
      refine ⟨231774735799161889677522119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154516490532774593118348079 231774735799161889677522119)
      ·
        refine ⟨347662103698742834516283179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231774735799161889677522119 347662103698742834516283179)
        ·
          refine ⟨521493155548114251774424769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347662103698742834516283179 521493155548114251774424769)
          ·
            refine ⟨391119866661085688830818577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521493155548114251774424769 391119866661085688830818577)
            ·
              refine ⟨293339899995814266623113933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391119866661085688830818577 293339899995814266623113933)
              ·
                refine ⟨110002462498430349983667725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293339899995814266623113933 110002462498430349983667725)
                ·
                  refine ⟨41250923436911381243875397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110002462498430349983667725 41250923436911381243875397)
                  ·
                    refine ⟨7734548144420883983226637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41250923436911381243875397 7734548144420883983226637)
                    ·
                      refine ⟨2900455554157831493709989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7734548144420883983226637 2900455554157831493709989)
                      ·
                        rfl

theorem cell23_5648617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_5648617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648617 prefixEnd_5648617 := by exact prefixLift 5648617
  have htrace : WordTrace (prefixWord ++ tailWord_5648617) baseStart_5648617 baseEnd_5648617 := by
    simpa [prefixWord, tailWord_5648617, baseEnd_5648617] using wordTrace_append hprefix tailTrace_5648617
  have hstable : (prefixWord ++ tailWord_5648617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648617).length < 2 ^ (prefixWord ++ tailWord_5648617).sum := by decide
  have hdescent : baseEnd_5648617 < baseStart_5648617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648634 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3]
def baseStart_5648634 : Nat := 118140960795 + 5648634 * 2 ^ 59
def prefixEnd_5648634 : Nat := 4983230072969 + 3 ^ 40 * 5648634 * 2
def baseEnd_5648634 : Nat := 2900464283328957927197411

theorem tailTrace_5648634 : CollatzResearch.WordTrace tailWord_5648634 prefixEnd_5648634 2900464283328957927197411 := by
  unfold tailWord_5648634
  simp only [CollatzResearch.WordTrace]
  refine ⟨51505651854492800681958239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137348404945314135151888637 51505651854492800681958239)
  ·
    refine ⟨77258477781739201022937359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51505651854492800681958239 77258477781739201022937359)
    ·
      refine ⟨115887716672608801534406039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77258477781739201022937359 115887716672608801534406039)
      ·
        refine ⟨173831575008913202301609059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115887716672608801534406039 173831575008913202301609059)
        ·
          refine ⟨260747362513369803452413589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173831575008913202301609059 260747362513369803452413589)
          ·
            refine ⟨12222532617814209536831887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 260747362513369803452413589 12222532617814209536831887)
            ·
              refine ⟨18333798926721314305247831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12222532617814209536831887 18333798926721314305247831)
              ·
                refine ⟨27500698390081971457871747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18333798926721314305247831 27500698390081971457871747)
                ·
                  refine ⟨41251047585122957186807621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27500698390081971457871747 41251047585122957186807621)
                  ·
                    refine ⟨7734571422210554472526429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41251047585122957186807621 7734571422210554472526429)
                    ·
                      refine ⟨2900464283328957927197411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7734571422210554472526429 2900464283328957927197411)
                      ·
                        rfl

theorem cell23_5648634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_5648634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648634 prefixEnd_5648634 := by exact prefixLift 5648634
  have htrace : WordTrace (prefixWord ++ tailWord_5648634) baseStart_5648634 baseEnd_5648634 := by
    simpa [prefixWord, tailWord_5648634, baseEnd_5648634] using wordTrace_append hprefix tailTrace_5648634
  have hstable : (prefixWord ++ tailWord_5648634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648634).length < 2 ^ (prefixWord ++ tailWord_5648634).sum := by decide
  have hdescent : baseEnd_5648634 < baseStart_5648634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648657 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_5648657 : Nat := 118140960795 + 5648657 * 2 ^ 59
def prefixEnd_5648657 : Nat := 4983230072969 + 3 ^ 40 * 5648657 * 2
def baseEnd_5648657 : Nat := 2900476093384011337209805

theorem tailTrace_5648657 : CollatzResearch.WordTrace tailWord_5648657 prefixEnd_5648657 2900476093384011337209805 := by
  unfold tailWord_5648657
  simp only [CollatzResearch.WordTrace]
  refine ⟨206023446296887877655920225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137348964197925251770613483 206023446296887877655920225)
  ·
    refine ⟨154517584722665908241940169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206023446296887877655920225 154517584722665908241940169)
    ·
      refine ⟨115888188541999431181455127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154517584722665908241940169 115888188541999431181455127)
      ·
        refine ⟨173832282812999146772182691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115888188541999431181455127 173832282812999146772182691)
        ·
          refine ⟨260748424219498720158274037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173832282812999146772182691 260748424219498720158274037)
          ·
            refine ⟨24445164770578005014838191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260748424219498720158274037 24445164770578005014838191)
            ·
              refine ⟨36667747155867007522257287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24445164770578005014838191 36667747155867007522257287)
              ·
                refine ⟨55001620733800511283385931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36667747155867007522257287 55001620733800511283385931)
                ·
                  refine ⟨82502431100700766925078897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55001620733800511283385931 82502431100700766925078897)
                  ·
                    refine ⟨61876823325525575193809173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82502431100700766925078897 61876823325525575193809173)
                    ·
                      refine ⟨2900476093384011337209805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61876823325525575193809173 2900476093384011337209805)
                      ·
                        rfl

theorem cell23_5648657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_5648657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648657 prefixEnd_5648657 := by exact prefixLift 5648657
  have htrace : WordTrace (prefixWord ++ tailWord_5648657) baseStart_5648657 baseEnd_5648657 := by
    simpa [prefixWord, tailWord_5648657, baseEnd_5648657] using wordTrace_append hprefix tailTrace_5648657
  have hstable : (prefixWord ++ tailWord_5648657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648657).length < 2 ^ (prefixWord ++ tailWord_5648657).sum := by decide
  have hdescent : baseEnd_5648657 < baseStart_5648657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648667 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 5, 5]
def baseStart_5648667 : Nat := 118140960795 + 5648667 * 2 ^ 59
def prefixEnd_5648667 : Nat := 4983230072969 + 3 ^ 40 * 5648667 * 2
def baseEnd_5648667 : Nat := 966827076063518766028253

theorem tailTrace_5648667 : CollatzResearch.WordTrace tailWord_5648667 prefixEnd_5648667 966827076063518766028253 := by
  unfold tailWord_5648667
  simp only [CollatzResearch.WordTrace]
  refine ⟨206023811026851649363784255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137349207351234432909189503 206023811026851649363784255)
  ·
    refine ⟨309035716540277474045676383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206023811026851649363784255 309035716540277474045676383)
    ·
      refine ⟨463553574810416211068514575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309035716540277474045676383 463553574810416211068514575)
      ·
        refine ⟨695330362215624316602771863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463553574810416211068514575 695330362215624316602771863)
        ·
          refine ⟨1042995543323436474904157795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695330362215624316602771863 1042995543323436474904157795)
          ·
            refine ⟨1564493314985154712356236693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042995543323436474904157795 1564493314985154712356236693)
            ·
              refine ⟨73335624139929127141698595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1564493314985154712356236693 73335624139929127141698595)
              ·
                refine ⟨110003436209893690712547893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73335624139929127141698595 110003436209893690712547893)
                ·
                  refine ⟨10312822144677533504301365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110003436209893690712547893 10312822144677533504301365)
                  ·
                    refine ⟨966827076063518766028253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10312822144677533504301365 966827076063518766028253)
                    ·
                      rfl

theorem cell23_5648667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 5].length) (baseStart_5648667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648667 prefixEnd_5648667 := by exact prefixLift 5648667
  have htrace : WordTrace (prefixWord ++ tailWord_5648667) baseStart_5648667 baseEnd_5648667 := by
    simpa [prefixWord, tailWord_5648667, baseEnd_5648667] using wordTrace_append hprefix tailTrace_5648667
  have hstable : (prefixWord ++ tailWord_5648667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648667).length < 2 ^ (prefixWord ++ tailWord_5648667).sum := by decide
  have hdescent : baseEnd_5648667 < baseStart_5648667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648671 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 6]
def baseStart_5648671 : Nat := 118140960795 + 5648671 * 2 ^ 59
def prefixEnd_5648671 : Nat := 4983230072969 + 3 ^ 40 * 5648671 * 2
def baseEnd_5648671 : Nat := 322275920234797142492749

theorem tailTrace_5648671 : CollatzResearch.WordTrace tailWord_5648671 prefixEnd_5648671 322275920234797142492749 := by
  unfold tailWord_5648671
  simp only [CollatzResearch.WordTrace]
  refine ⟨206023956918837158046929867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137349304612558105364619911 206023956918837158046929867)
  ·
    refine ⟨309035935378255737070394801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206023956918837158046929867 309035935378255737070394801)
    ·
      refine ⟨231776951533691802802796101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309035935378255737070394801 231776951533691802802796101)
      ·
        refine ⟨43458178412567213025524269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231776951533691802802796101 43458178412567213025524269)
        ·
          refine ⟨16296816904712704884571601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43458178412567213025524269 16296816904712704884571601)
          ·
            refine ⟨12222612678534528663428701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16296816904712704884571601 12222612678534528663428701)
            ·
              refine ⟨4583479754450448248785763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12222612678534528663428701 4583479754450448248785763)
              ·
                refine ⟨6875219631675672373178645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4583479754450448248785763 6875219631675672373178645)
                ·
                  refine ⟨322275920234797142492749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6875219631675672373178645 322275920234797142492749)
                  ·
                    rfl

theorem cell23_5648671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 6].length) (baseStart_5648671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648671 prefixEnd_5648671 := by exact prefixLift 5648671
  have htrace : WordTrace (prefixWord ++ tailWord_5648671) baseStart_5648671 baseEnd_5648671 := by
    simpa [prefixWord, tailWord_5648671, baseEnd_5648671] using wordTrace_append hprefix tailTrace_5648671
  have hstable : (prefixWord ++ tailWord_5648671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648671).length < 2 ^ (prefixWord ++ tailWord_5648671).sum := by decide
  have hdescent : baseEnd_5648671 < baseStart_5648671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648684 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_5648684 : Nat := 118140960795 + 5648684 * 2 ^ 59
def prefixEnd_5648684 : Nat := 4983230072969 + 3 ^ 40 * 5648684 * 2
def baseEnd_5648684 : Nat := 966829985787227577190727

theorem tailTrace_5648684 : CollatzResearch.WordTrace tailWord_5648684 prefixEnd_5648684 966829985787227577190727 := by
  unfold tailWord_5648684
  simp only [CollatzResearch.WordTrace]
  refine ⟨103012215533895030633576553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137349620711860040844768737 103012215533895030633576553)
  ·
    refine ⟨77259161650421272975182415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103012215533895030633576553 77259161650421272975182415)
    ·
      refine ⟨115888742475631909462773623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77259161650421272975182415 115888742475631909462773623)
      ·
        refine ⟨173833113713447864194160435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115888742475631909462773623 173833113713447864194160435)
        ·
          refine ⟨260749670570171796291240653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173833113713447864194160435 260749670570171796291240653)
          ·
            refine ⟨97781126463814423609215245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260749670570171796291240653 97781126463814423609215245)
            ·
              refine ⟨36667922423930408853455717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97781126463814423609215245 36667922423930408853455717)
              ·
                refine ⟨6875235454486951660022947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36667922423930408853455717 6875235454486951660022947)
                ·
                  refine ⟨10312853181730427490034421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6875235454486951660022947 10312853181730427490034421)
                  ·
                    refine ⟨966829985787227577190727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10312853181730427490034421 966829985787227577190727)
                    ·
                      rfl

theorem cell23_5648684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_5648684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648684 prefixEnd_5648684 := by exact prefixLift 5648684
  have htrace : WordTrace (prefixWord ++ tailWord_5648684) baseStart_5648684 baseEnd_5648684 := by
    simpa [prefixWord, tailWord_5648684, baseEnd_5648684] using wordTrace_append hprefix tailTrace_5648684
  have hstable : (prefixWord ++ tailWord_5648684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648684).length < 2 ^ (prefixWord ++ tailWord_5648684).sum := by decide
  have hdescent : baseEnd_5648684 < baseStart_5648684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648691 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 2, 3, 2]
def baseStart_5648691 : Nat := 118140960795 + 5648691 * 2 ^ 59
def prefixEnd_5648691 : Nat := 4983230072969 + 3 ^ 40 * 5648691 * 2
def baseEnd_5648691 : Nat := 2900493551726264204184649

theorem tailTrace_5648691 : CollatzResearch.WordTrace tailWord_5648691 prefixEnd_5648691 2900493551726264204184649 := by
  unfold tailWord_5648691
  simp only [CollatzResearch.WordTrace]
  refine ⟨206024686378764701462657927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137349790919176467641771951 206024686378764701462657927)
  ·
    refine ⟨309037029568147052193986891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206024686378764701462657927 309037029568147052193986891)
    ·
      refine ⟨463555544352220578290980337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309037029568147052193986891 463555544352220578290980337)
      ·
        refine ⟨347666658264165433718235253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463555544352220578290980337 347666658264165433718235253)
        ·
          refine ⟨32593749212265509411084555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 347666658264165433718235253 32593749212265509411084555)
          ·
            refine ⟨48890623818398264116626833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32593749212265509411084555 48890623818398264116626833)
            ·
              refine ⟨36667967863798698087470125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48890623818398264116626833 36667967863798698087470125)
              ·
                refine ⟨13750487948924511782801297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36667967863798698087470125 13750487948924511782801297)
                ·
                  refine ⟨10312865961693383837100973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13750487948924511782801297 10312865961693383837100973)
                  ·
                    refine ⟨3867324735635018938912865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10312865961693383837100973 3867324735635018938912865)
                    ·
                      refine ⟨2900493551726264204184649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867324735635018938912865 2900493551726264204184649)
                      ·
                        rfl

theorem cell23_5648691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 3, 2].length) (baseStart_5648691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648691 prefixEnd_5648691 := by exact prefixLift 5648691
  have htrace : WordTrace (prefixWord ++ tailWord_5648691) baseStart_5648691 baseEnd_5648691 := by
    simpa [prefixWord, tailWord_5648691, baseEnd_5648691] using wordTrace_append hprefix tailTrace_5648691
  have hstable : (prefixWord ++ tailWord_5648691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648691).length < 2 ^ (prefixWord ++ tailWord_5648691).sum := by decide
  have hdescent : baseEnd_5648691 < baseStart_5648691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648738 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_5648738 : Nat := 118140960795 + 5648738 * 2 ^ 59
def prefixEnd_5648738 : Nat := 4983230072969 + 3 ^ 40 * 5648738 * 2
def baseEnd_5648738 : Nat := 2900517685317025520296933

theorem tailTrace_5648738 : CollatzResearch.WordTrace tailWord_5648738 prefixEnd_5648738 2900517685317025520296933 := by
  unfold tailWord_5648738
  simp only [CollatzResearch.WordTrace]
  refine ⟨51506600152398607122404717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137350933739729618993079245 51506600152398607122404717)
  ·
    refine ⟨19314975057149477670901769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51506600152398607122404717 19314975057149477670901769)
    ·
      refine ⟨14486231292862108253176327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19314975057149477670901769 14486231292862108253176327)
      ·
        refine ⟨21729346939293162379764491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14486231292862108253176327 21729346939293162379764491)
        ·
          refine ⟨32594020408939743569646737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21729346939293162379764491 32594020408939743569646737)
          ·
            refine ⟨24445515306704807677235053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32594020408939743569646737 24445515306704807677235053)
            ·
              refine ⟨9167068240014302878963145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24445515306704807677235053 9167068240014302878963145)
              ·
                refine ⟨6875301180010727159222359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9167068240014302878963145 6875301180010727159222359)
                ·
                  refine ⟨10312951770016090738833539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6875301180010727159222359 10312951770016090738833539)
                  ·
                    refine ⟨15469427655024136108250309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10312951770016090738833539 15469427655024136108250309)
                    ·
                      refine ⟨2900517685317025520296933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15469427655024136108250309 2900517685317025520296933)
                      ·
                        rfl

theorem cell23_5648738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_5648738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648738 prefixEnd_5648738 := by exact prefixLift 5648738
  have htrace : WordTrace (prefixWord ++ tailWord_5648738) baseStart_5648738 baseEnd_5648738 := by
    simpa [prefixWord, tailWord_5648738, baseEnd_5648738] using wordTrace_append hprefix tailTrace_5648738
  have hstable : (prefixWord ++ tailWord_5648738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648738).length < 2 ^ (prefixWord ++ tailWord_5648738).sum := by decide
  have hdescent : baseEnd_5648738 < baseStart_5648738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648741 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_5648741 : Nat := 118140960795 + 5648741 * 2 ^ 59
def prefixEnd_5648741 : Nat := 4983230072969 + 3 ^ 40 * 5648741 * 2
def baseEnd_5648741 : Nat := 2900519225758989008559419

theorem tailTrace_5648741 : CollatzResearch.WordTrace tailWord_5648741 prefixEnd_5648741 2900519225758989008559419 := by
  unfold tailWord_5648741
  simp only [CollatzResearch.WordTrace]
  refine ⟨206026510028583560001978077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137351006685722373334652051 206026510028583560001978077)
  ·
    refine ⟨77259941260718835000741779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206026510028583560001978077 77259941260718835000741779)
    ·
      refine ⟨115889911891078252501112669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77259941260718835000741779 115889911891078252501112669)
      ·
        refine ⟨43458716959154344687917251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115889911891078252501112669 43458716959154344687917251)
        ·
          refine ⟨65188075438731517031875877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43458716959154344687917251 65188075438731517031875877)
          ·
            refine ⟨12222764144762159443476727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65188075438731517031875877 12222764144762159443476727)
            ·
              refine ⟨18334146217143239165215091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12222764144762159443476727 18334146217143239165215091)
              ·
                refine ⟨27501219325714858747822637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18334146217143239165215091 27501219325714858747822637)
                ·
                  refine ⟨10312957247143072030433489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27501219325714858747822637 10312957247143072030433489)
                  ·
                    refine ⟨7734717935357304022825117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10312957247143072030433489 7734717935357304022825117)
                    ·
                      refine ⟨2900519225758989008559419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7734717935357304022825117 2900519225758989008559419)
                      ·
                        rfl

theorem cell23_5648741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_5648741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648741 prefixEnd_5648741 := by exact prefixLift 5648741
  have htrace : WordTrace (prefixWord ++ tailWord_5648741) baseStart_5648741 baseEnd_5648741 := by
    simpa [prefixWord, tailWord_5648741, baseEnd_5648741] using wordTrace_append hprefix tailTrace_5648741
  have hstable : (prefixWord ++ tailWord_5648741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648741).length < 2 ^ (prefixWord ++ tailWord_5648741).sum := by decide
  have hdescent : baseEnd_5648741 < baseStart_5648741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648744 : List Nat := [2, 1, 4, 2, 2, 1, 2, 9]
def baseStart_5648744 : Nat := 118140960795 + 5648744 * 2 ^ 59
def prefixEnd_5648744 : Nat := 4983230072969 + 3 ^ 40 * 5648744 * 2
def baseEnd_5648744 : Nat := 107426695044479722104515

theorem tailTrace_5648744 : CollatzResearch.WordTrace tailWord_5648744 prefixEnd_5648744 107426695044479722104515 := by
  unfold tailWord_5648744
  simp only [CollatzResearch.WordTrace]
  refine ⟨103013309723786345757168643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137351079631715127676224857 103013309723786345757168643)
  ·
    refine ⟨154519964585679518635752965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103013309723786345757168643 154519964585679518635752965)
    ·
      refine ⟨28972493359814909744203681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154519964585679518635752965 28972493359814909744203681)
      ·
        refine ⟨21729370019861182308152761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28972493359814909744203681 21729370019861182308152761)
        ·
          refine ⟨16297027514895886731114571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21729370019861182308152761 16297027514895886731114571)
          ·
            refine ⟨24445541272343830096671857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16297027514895886731114571 24445541272343830096671857)
            ·
              refine ⟨18334155954257872572503893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24445541272343830096671857 18334155954257872572503893)
              ·
                refine ⟨107426695044479722104515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18334155954257872572503893 107426695044479722104515)
                ·
                  rfl

theorem cell23_5648744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 9].length) (baseStart_5648744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648744 prefixEnd_5648744 := by exact prefixLift 5648744
  have htrace : WordTrace (prefixWord ++ tailWord_5648744) baseStart_5648744 baseEnd_5648744 := by
    simpa [prefixWord, tailWord_5648744, baseEnd_5648744] using wordTrace_append hprefix tailTrace_5648744
  have hstable : (prefixWord ++ tailWord_5648744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648744).length < 2 ^ (prefixWord ++ tailWord_5648744).sum := by decide
  have hdescent : baseEnd_5648744 < baseStart_5648744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648747 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 6]
def baseStart_5648747 : Nat := 118140960795 + 5648747 * 2 ^ 59
def prefixEnd_5648747 : Nat := 4983230072969 + 3 ^ 40 * 5648747 * 2
def baseEnd_5648747 : Nat := 2900522306642915985084391

theorem tailTrace_5648747 : CollatzResearch.WordTrace tailWord_5648747 prefixEnd_5648747 2900522306642915985084391 := by
  unfold tailWord_5648747
  simp only [CollatzResearch.WordTrace]
  refine ⟨206026728866561823026696495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137351152577707882017797663 206026728866561823026696495)
  ·
    refine ⟨309040093299842734540044743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206026728866561823026696495 309040093299842734540044743)
    ·
      refine ⟨463560139949764101810067115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309040093299842734540044743 463560139949764101810067115)
      ·
        refine ⟨695340209924646152715100673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463560139949764101810067115 695340209924646152715100673)
        ·
          refine ⟨521505157443484614536325505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695340209924646152715100673 521505157443484614536325505)
          ·
            refine ⟨391128868082613460902244129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521505157443484614536325505 391128868082613460902244129)
            ·
              refine ⟨293346651061960095676683097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391128868082613460902244129 293346651061960095676683097)
              ·
                refine ⟨220009988296470071757512323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293346651061960095676683097 220009988296470071757512323)
                ·
                  refine ⟨330014982444705107636268485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220009988296470071757512323 330014982444705107636268485)
                  ·
                    refine ⟨61877809208382207681800341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 330014982444705107636268485 61877809208382207681800341)
                    ·
                      refine ⟨2900522306642915985084391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61877809208382207681800341 2900522306642915985084391)
                      ·
                        rfl

theorem cell23_5648747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 6].length) (baseStart_5648747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648747 prefixEnd_5648747 := by exact prefixLift 5648747
  have htrace : WordTrace (prefixWord ++ tailWord_5648747) baseStart_5648747 baseEnd_5648747 := by
    simpa [prefixWord, tailWord_5648747, baseEnd_5648747] using wordTrace_append hprefix tailTrace_5648747
  have hstable : (prefixWord ++ tailWord_5648747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648747).length < 2 ^ (prefixWord ++ tailWord_5648747).sum := by decide
  have hdescent : baseEnd_5648747 < baseStart_5648747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648778 : List Nat := [3, 1, 2, 5, 1, 2, 1, 8]
def baseStart_5648778 : Nat := 118140960795 + 5648778 * 2 ^ 59
def prefixEnd_5648778 : Nat := 4983230072969 + 3 ^ 40 * 5648778 * 2
def baseEnd_5648778 : Nat := 107427341649748346807287

theorem tailTrace_5648778 : CollatzResearch.WordTrace tailWord_5648778 prefixEnd_5648778 107427341649748346807287 := by
  unfold tailWord_5648778
  simp only [CollatzResearch.WordTrace]
  refine ⟨51506964882362378830268747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137351906352966343547383325 51506964882362378830268747)
  ·
    refine ⟨77260447323543568245403121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51506964882362378830268747 77260447323543568245403121)
    ·
      refine ⟨57945335492657676184052341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77260447323543568245403121 57945335492657676184052341)
      ·
        refine ⟨5432375202436657142254907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57945335492657676184052341 5432375202436657142254907)
        ·
          refine ⟨8148562803654985713382361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432375202436657142254907 8148562803654985713382361)
          ·
            refine ⟨6111422102741239285036771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8148562803654985713382361 6111422102741239285036771)
            ·
              refine ⟨9167133154111858927555157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111422102741239285036771 9167133154111858927555157)
              ·
                refine ⟨107427341649748346807287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9167133154111858927555157 107427341649748346807287)
                ·
                  rfl

theorem cell23_5648778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 8].length) (baseStart_5648778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648778 prefixEnd_5648778 := by exact prefixLift 5648778
  have htrace : WordTrace (prefixWord ++ tailWord_5648778) baseStart_5648778 baseEnd_5648778 := by
    simpa [prefixWord, tailWord_5648778, baseEnd_5648778] using wordTrace_append hprefix tailTrace_5648778
  have hstable : (prefixWord ++ tailWord_5648778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648778).length < 2 ^ (prefixWord ++ tailWord_5648778).sum := by decide
  have hdescent : baseEnd_5648778 < baseStart_5648778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648864 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 1, 7]
def baseStart_5648864 : Nat := 118140960795 + 5648864 * 2 ^ 59
def prefixEnd_5648864 : Nat := 4983230072969 + 3 ^ 40 * 5648864 * 2
def baseEnd_5648864 : Nat := 966860794626497342440451

theorem tailTrace_5648864 : CollatzResearch.WordTrace tailWord_5648864 prefixEnd_5648864 966860794626497342440451 := by
  unfold tailWord_5648864
  simp only [CollatzResearch.WordTrace]
  refine ⟨103015498103568976004352823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137353997471425301339137097 103015498103568976004352823)
  ·
    refine ⟨154523247155353464006529235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103015498103568976004352823 154523247155353464006529235)
    ·
      refine ⟨231784870733030196009793853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154523247155353464006529235 231784870733030196009793853)
      ·
        refine ⟨86919326524886323503672695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231784870733030196009793853 86919326524886323503672695)
        ·
          refine ⟨130378989787329485255509043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86919326524886323503672695 130378989787329485255509043)
          ·
            refine ⟨195568484680994227883263565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130378989787329485255509043 195568484680994227883263565)
            ·
              refine ⟨73338181755372835456223837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195568484680994227883263565 73338181755372835456223837)
              ·
                refine ⟨27501818158264813296083939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73338181755372835456223837 27501818158264813296083939)
                ·
                  refine ⟨41252727237397219944125909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27501818158264813296083939 41252727237397219944125909)
                  ·
                    refine ⟨966860794626497342440451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41252727237397219944125909 966860794626497342440451)
                    ·
                      rfl

theorem cell23_5648864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_5648864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648864 prefixEnd_5648864 := by exact prefixLift 5648864
  have htrace : WordTrace (prefixWord ++ tailWord_5648864) baseStart_5648864 baseEnd_5648864 := by
    simpa [prefixWord, tailWord_5648864, baseEnd_5648864] using wordTrace_append hprefix tailTrace_5648864
  have hstable : (prefixWord ++ tailWord_5648864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648864).length < 2 ^ (prefixWord ++ tailWord_5648864).sum := by decide
  have hdescent : baseEnd_5648864 < baseStart_5648864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648881 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 2, 5]
def baseStart_5648881 : Nat := 118140960795 + 5648881 * 2 ^ 59
def prefixEnd_5648881 : Nat := 4983230072969 + 3 ^ 40 * 5648881 * 2
def baseEnd_5648881 : Nat := 966863704350206153602925

theorem tailTrace_5648881 : CollatzResearch.WordTrace tailWord_5648881 prefixEnd_5648881 966863704350206153602925 := by
  unfold tailWord_5648881
  simp only [CollatzResearch.WordTrace]
  refine ⟨206031616248076363912074497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137354410832050909274716331 206031616248076363912074497)
  ·
    refine ⟨154523712186057272934055873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206031616248076363912074497 154523712186057272934055873)
    ·
      refine ⟨115892784139542954700541905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154523712186057272934055873 115892784139542954700541905)
      ·
        refine ⟨86919588104657216025406429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115892784139542954700541905 86919588104657216025406429)
        ·
          refine ⟨32594845539246456009527411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86919588104657216025406429 32594845539246456009527411)
          ·
            refine ⟨48892268308869684014291117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32594845539246456009527411 48892268308869684014291117)
            ·
              refine ⟨18334600615826131505359169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48892268308869684014291117 18334600615826131505359169)
              ·
                refine ⟨13750950461869598629019377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18334600615826131505359169 13750950461869598629019377)
                ·
                  refine ⟨10313212846402198971764533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13750950461869598629019377 10313212846402198971764533)
                  ·
                    refine ⟨966863704350206153602925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10313212846402198971764533 966863704350206153602925)
                    ·
                      rfl

theorem cell23_5648881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_5648881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648881 prefixEnd_5648881 := by exact prefixLift 5648881
  have htrace : WordTrace (prefixWord ++ tailWord_5648881) baseStart_5648881 baseEnd_5648881 := by
    simpa [prefixWord, tailWord_5648881, baseEnd_5648881] using wordTrace_append hprefix tailTrace_5648881
  have hstable : (prefixWord ++ tailWord_5648881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648881).length < 2 ^ (prefixWord ++ tailWord_5648881).sum := by decide
  have hdescent : baseEnd_5648881 < baseStart_5648881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648885 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 7]
def baseStart_5648885 : Nat := 118140960795 + 5648885 * 2 ^ 59
def prefixEnd_5648885 : Nat := 4983230072969 + 3 ^ 40 * 5648885 * 2
def baseEnd_5648885 : Nat := 322288129663692938350973

theorem tailTrace_5648885 : CollatzResearch.WordTrace tailWord_5648885 prefixEnd_5648885 322288129663692938350973 := by
  unfold tailWord_5648885
  simp only [CollatzResearch.WordTrace]
  refine ⟨206031762140061872595220109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137354508093374581730146739 206031762140061872595220109)
  ·
    refine ⟨77261910802523202223207541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206031762140061872595220109 77261910802523202223207541)
    ·
      refine ⟨7243304137736550208425707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77261910802523202223207541 7243304137736550208425707)
      ·
        refine ⟨10864956206604825312638561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7243304137736550208425707 10864956206604825312638561)
        ·
          refine ⟨8148717154953618984478921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10864956206604825312638561 8148717154953618984478921)
          ·
            refine ⟨6111537866215214238359191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8148717154953618984478921 6111537866215214238359191)
            ·
              refine ⟨9167306799322821357538787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111537866215214238359191 9167306799322821357538787)
              ·
                refine ⟨13750960198984232036308181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9167306799322821357538787 13750960198984232036308181)
                ·
                  refine ⟨322288129663692938350973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13750960198984232036308181 322288129663692938350973)
                  ·
                    rfl

theorem cell23_5648885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_5648885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648885 prefixEnd_5648885 := by exact prefixLift 5648885
  have htrace : WordTrace (prefixWord ++ tailWord_5648885) baseStart_5648885 baseEnd_5648885 := by
    simpa [prefixWord, tailWord_5648885, baseEnd_5648885] using wordTrace_append hprefix tailTrace_5648885
  have hstable : (prefixWord ++ tailWord_5648885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648885).length < 2 ^ (prefixWord ++ tailWord_5648885).sum := by decide
  have hdescent : baseEnd_5648885 < baseStart_5648885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648921 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 3]
def baseStart_5648921 : Nat := 118140960795 + 5648921 * 2 ^ 59
def prefixEnd_5648921 : Nat := 4983230072969 + 3 ^ 40 * 5648921 * 2
def baseEnd_5648921 : Nat := 2900611652276798304308591

theorem tailTrace_5648921 : CollatzResearch.WordTrace tailWord_5648921 prefixEnd_5648921 2900611652276798304308591 := by
  unfold tailWord_5648921
  simp only [CollatzResearch.WordTrace]
  refine ⟨206033075167931450743530617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137355383445287633829020411 206033075167931450743530617)
  ·
    refine ⟨154524806375948588057647963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206033075167931450743530617 154524806375948588057647963)
    ·
      refine ⟨231787209563922882086471945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154524806375948588057647963 231787209563922882086471945)
      ·
        refine ⟨173840407172942161564853959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231787209563922882086471945 173840407172942161564853959)
        ·
          refine ⟨260760610759413242347280939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173840407172942161564853959 260760610759413242347280939)
          ·
            refine ⟨391140916139119863520921409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260760610759413242347280939 391140916139119863520921409)
            ·
              refine ⟨293355687104339897640691057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391140916139119863520921409 293355687104339897640691057)
              ·
                refine ⟨220016765328254923230518293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293355687104339897640691057 220016765328254923230518293)
                ·
                  refine ⟨10313285874761949526430545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220016765328254923230518293 10313285874761949526430545)
                  ·
                    refine ⟨7734964406071462144822909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10313285874761949526430545 7734964406071462144822909)
                    ·
                      refine ⟨2900611652276798304308591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7734964406071462144822909 2900611652276798304308591)
                      ·
                        rfl

theorem cell23_5648921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_5648921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648921 prefixEnd_5648921 := by exact prefixLift 5648921
  have htrace : WordTrace (prefixWord ++ tailWord_5648921) baseStart_5648921 baseEnd_5648921 := by
    simpa [prefixWord, tailWord_5648921, baseEnd_5648921] using wordTrace_append hprefix tailTrace_5648921
  have hstable : (prefixWord ++ tailWord_5648921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648921).length < 2 ^ (prefixWord ++ tailWord_5648921).sum := by decide
  have hdescent : baseEnd_5648921 < baseStart_5648921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5648971 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 3, 5]
def baseStart_5648971 : Nat := 118140960795 + 5648971 * 2 ^ 59
def prefixEnd_5648971 : Nat := 4983230072969 + 3 ^ 40 * 5648971 * 2
def baseEnd_5648971 : Nat := 966879108769841036227787

theorem tailTrace_5648971 : CollatzResearch.WordTrace tailWord_5648971 prefixEnd_5648971 966879108769841036227787 := by
  unfold tailWord_5648971
  simp only [CollatzResearch.WordTrace]
  refine ⟨206034898817750309282850767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137356599211833539521900511 206034898817750309282850767)
  ·
    refine ⟨309052348226625463924276151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206034898817750309282850767 309052348226625463924276151)
    ·
      refine ⟨463578522339938195886414227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309052348226625463924276151 463578522339938195886414227)
      ·
        refine ⟨695367783509907293829621341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463578522339938195886414227 695367783509907293829621341)
        ·
          refine ⟨260762918816215235186108003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695367783509907293829621341 260762918816215235186108003)
          ·
            refine ⟨391144378224322852779162005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260762918816215235186108003 391144378224322852779162005)
            ·
              refine ⟨18334892729265133724023219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 391144378224322852779162005 18334892729265133724023219)
              ·
                refine ⟨27502339093897700586034829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18334892729265133724023219 27502339093897700586034829)
                ·
                  refine ⟨10313377160211637719763061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27502339093897700586034829 10313377160211637719763061)
                  ·
                    refine ⟨966879108769841036227787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10313377160211637719763061 966879108769841036227787)
                    ·
                      rfl

theorem cell23_5648971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 5].length) (baseStart_5648971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5648971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5648971 prefixEnd_5648971 := by exact prefixLift 5648971
  have htrace : WordTrace (prefixWord ++ tailWord_5648971) baseStart_5648971 baseEnd_5648971 := by
    simpa [prefixWord, tailWord_5648971, baseEnd_5648971] using wordTrace_append hprefix tailTrace_5648971
  have hstable : (prefixWord ++ tailWord_5648971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5648971).length < 2 ^ (prefixWord ++ tailWord_5648971).sum := by decide
  have hdescent : baseEnd_5648971 < baseStart_5648971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5648971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649002 : List Nat := [3, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_5649002 : Nat := 118140960795 + 5649002 * 2 ^ 59
def prefixEnd_5649002 : Nat := 4983230072969 + 3 ^ 40 * 5649002 * 2
def baseEnd_5649002 : Nat := 2900653244209812487395719

theorem tailTrace_5649002 : CollatzResearch.WordTrace tailWord_5649002 prefixEnd_5649002 2900653244209812487395719 := by
  unfold tailWord_5649002
  simp only [CollatzResearch.WordTrace]
  refine ⟨51509007370159500394307315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137357352987092001051486173 51509007370159500394307315)
  ·
    refine ⟨77263511055239250591460973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51509007370159500394307315 77263511055239250591460973)
    ·
      refine ⟨28973816645714718971797865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77263511055239250591460973 28973816645714718971797865)
      ·
        refine ⟨21730362484286039228848399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28973816645714718971797865 21730362484286039228848399)
        ·
          refine ⟨32595543726429058843272599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21730362484286039228848399 32595543726429058843272599)
          ·
            refine ⟨48893315589643588264908899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32595543726429058843272599 48893315589643588264908899)
            ·
              refine ⟨73339973384465382397363349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48893315589643588264908899 73339973384465382397363349)
              ·
                refine ⟨3437811252396814799876407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73339973384465382397363349 3437811252396814799876407)
                ·
                  refine ⟨5156716878595222199814611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437811252396814799876407 5156716878595222199814611)
                  ·
                    refine ⟨7735075317892833299721917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5156716878595222199814611 7735075317892833299721917)
                    ·
                      refine ⟨2900653244209812487395719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7735075317892833299721917 2900653244209812487395719)
                      ·
                        rfl

theorem cell23_5649002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_5649002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649002 prefixEnd_5649002 := by exact prefixLift 5649002
  have htrace : WordTrace (prefixWord ++ tailWord_5649002) baseStart_5649002 baseEnd_5649002 := by
    simpa [prefixWord, tailWord_5649002, baseEnd_5649002] using wordTrace_append hprefix tailTrace_5649002
  have hstable : (prefixWord ++ tailWord_5649002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649002).length < 2 ^ (prefixWord ++ tailWord_5649002).sum := by decide
  have hdescent : baseEnd_5649002 < baseStart_5649002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649011 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 3]
def baseStart_5649011 : Nat := 118140960795 + 5649011 * 2 ^ 59
def prefixEnd_5649011 : Nat := 4983230072969 + 3 ^ 40 * 5649011 * 2
def baseEnd_5649011 : Nat := 2900657865535702952183177

theorem tailTrace_5649011 : CollatzResearch.WordTrace tailWord_5649011 prefixEnd_5649011 2900657865535702952183177 := by
  unfold tailWord_5649011
  simp only [CollatzResearch.WordTrace]
  refine ⟨206036357737605396114306887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137357571825070264076204591 206036357737605396114306887)
  ·
    refine ⟨309054536606408094171460331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206036357737605396114306887 309054536606408094171460331)
    ·
      refine ⟨463581804909612141257190497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309054536606408094171460331 463581804909612141257190497)
      ·
        refine ⟨347686353682209105942892873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463581804909612141257190497 347686353682209105942892873)
        ·
          refine ⟨260764765261656829457169655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347686353682209105942892873 260764765261656829457169655)
          ·
            refine ⟨391147147892485244185754483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260764765261656829457169655 391147147892485244185754483)
            ·
              refine ⟨586720721838727866278631725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391147147892485244185754483 586720721838727866278631725)
              ·
                refine ⟨220020270689522949854486897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586720721838727866278631725 220020270689522949854486897)
                ·
                  refine ⟨165015203017142212390865173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220020270689522949854486897 165015203017142212390865173)
                  ·
                    refine ⟨7735087641428541205821805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 165015203017142212390865173 7735087641428541205821805)
                    ·
                      refine ⟨2900657865535702952183177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7735087641428541205821805 2900657865535702952183177)
                      ·
                        rfl

theorem cell23_5649011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_5649011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649011 prefixEnd_5649011 := by exact prefixLift 5649011
  have htrace : WordTrace (prefixWord ++ tailWord_5649011) baseStart_5649011 baseEnd_5649011 := by
    simpa [prefixWord, tailWord_5649011, baseEnd_5649011] using wordTrace_append hprefix tailTrace_5649011
  have hstable : (prefixWord ++ tailWord_5649011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649011).length < 2 ^ (prefixWord ++ tailWord_5649011).sum := by decide
  have hdescent : baseEnd_5649011 < baseStart_5649011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649025 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_5649025 : Nat := 118140960795 + 5649025 * 2 ^ 59
def prefixEnd_5649025 : Nat := 4983230072969 + 3 ^ 40 * 5649025 * 2
def baseEnd_5649025 : Nat := 2900665054264865897408113

theorem tailTrace_5649025 : CollatzResearch.WordTrace tailWord_5649025 prefixEnd_5649025 2900665054264865897408113 := by
  unfold tailWord_5649025
  simp only [CollatzResearch.WordTrace]
  refine ⟨206036868359554676505316529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137357912239703117670211019 206036868359554676505316529)
  ·
    refine ⟨154527651269666007378987397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206036868359554676505316529 154527651269666007378987397)
    ·
      refine ⟨28973934613062376383560137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154527651269666007378987397 28973934613062376383560137)
      ·
        refine ⟨21730450959796782287670103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28973934613062376383560137 21730450959796782287670103)
        ·
          refine ⟨32595676439695173431505155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21730450959796782287670103 32595676439695173431505155)
          ·
            refine ⟨48893514659542760147257733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32595676439695173431505155 48893514659542760147257733)
            ·
              refine ⟨9167533998664267527610825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48893514659542760147257733 9167533998664267527610825)
              ·
                refine ⟨6875650498998200645708119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9167533998664267527610825 6875650498998200645708119)
                ·
                  refine ⟨10313475748497300968562179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6875650498998200645708119 10313475748497300968562179)
                  ·
                    refine ⟨15470213622745951452843269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10313475748497300968562179 15470213622745951452843269)
                    ·
                      refine ⟨2900665054264865897408113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15470213622745951452843269 2900665054264865897408113)
                      ·
                        rfl

theorem cell23_5649025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_5649025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649025 prefixEnd_5649025 := by exact prefixLift 5649025
  have htrace : WordTrace (prefixWord ++ tailWord_5649025) baseStart_5649025 baseEnd_5649025 := by
    simpa [prefixWord, tailWord_5649025, baseEnd_5649025] using wordTrace_append hprefix tailTrace_5649025
  have hstable : (prefixWord ++ tailWord_5649025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649025).length < 2 ^ (prefixWord ++ tailWord_5649025).sum := by decide
  have hdescent : baseEnd_5649025 < baseStart_5649025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649031 : List Nat := [1, 1, 4, 2, 1, 2, 3, 9]
def baseStart_5649031 : Nat := 118140960795 + 5649031 * 2 ^ 59
def prefixEnd_5649031 : Nat := 4983230072969 + 3 ^ 40 * 5649031 * 2
def baseEnd_5649031 : Nat := 107432153153658995330855

theorem tailTrace_5649031 : CollatzResearch.WordTrace tailWord_5649031 prefixEnd_5649031 107432153153658995330855 := by
  unfold tailWord_5649031
  simp only [CollatzResearch.WordTrace]
  refine ⟨206037087197532939530034947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137358058131688626353356631 206037087197532939530034947)
  ·
    refine ⟨309055630796299409295052421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206037087197532939530034947 309055630796299409295052421)
    ·
      refine ⟨57947930774306139242822329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 309055630796299409295052421 57947930774306139242822329)
      ·
        refine ⟨43460948080729604432116747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57947930774306139242822329 43460948080729604432116747)
        ·
          refine ⟨65191422121094406648175121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43460948080729604432116747 65191422121094406648175121)
          ·
            refine ⟨48893566590820804986131341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65191422121094406648175121 48893566590820804986131341)
            ·
              refine ⟨18335087471557801869799253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48893566590820804986131341 18335087471557801869799253)
              ·
                refine ⟨107432153153658995330855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18335087471557801869799253 107432153153658995330855)
                ·
                  rfl

theorem cell23_5649031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 9].length) (baseStart_5649031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649031 prefixEnd_5649031 := by exact prefixLift 5649031
  have htrace : WordTrace (prefixWord ++ tailWord_5649031) baseStart_5649031 baseEnd_5649031 := by
    simpa [prefixWord, tailWord_5649031, baseEnd_5649031] using wordTrace_append hprefix tailTrace_5649031
  have hstable : (prefixWord ++ tailWord_5649031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649031).length < 2 ^ (prefixWord ++ tailWord_5649031).sum := by decide
  have hdescent : baseEnd_5649031 < baseStart_5649031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649038 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5649038 : Nat := 118140960795 + 5649038 * 2 ^ 59
def prefixEnd_5649038 : Nat := 4983230072969 + 3 ^ 40 * 5649038 * 2
def baseEnd_5649038 : Nat := 2900671729513374346545553

theorem tailTrace_5649038 : CollatzResearch.WordTrace tailWord_5649038 prefixEnd_5649038 2900671729513374346545553 := by
  unfold tailWord_5649038
  simp only [CollatzResearch.WordTrace]
  refine ⟨25754667813563447465692471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137358228339005053150359845 25754667813563447465692471)
  ·
    refine ⟨38632001720345171198538707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25754667813563447465692471 38632001720345171198538707)
    ·
      refine ⟨57948002580517756797808061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38632001720345171198538707 57948002580517756797808061)
      ·
        refine ⟨21730500967694158799178023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57948002580517756797808061 21730500967694158799178023)
        ·
          refine ⟨32595751451541238198767035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21730500967694158799178023 32595751451541238198767035)
          ·
            refine ⟨48893627177311857298150553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32595751451541238198767035 48893627177311857298150553)
            ·
              refine ⟨36670220382983892973612915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48893627177311857298150553 36670220382983892973612915)
              ·
                refine ⟨55005330574475839460419373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36670220382983892973612915 55005330574475839460419373)
                ·
                  refine ⟨20626998965428439797657265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55005330574475839460419373 20626998965428439797657265)
                  ·
                    refine ⟨15470249224071329848242949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20626998965428439797657265 15470249224071329848242949)
                    ·
                      refine ⟨2900671729513374346545553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15470249224071329848242949 2900671729513374346545553)
                      ·
                        rfl

theorem cell23_5649038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5649038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649038 prefixEnd_5649038 := by exact prefixLift 5649038
  have htrace : WordTrace (prefixWord ++ tailWord_5649038) baseStart_5649038 baseEnd_5649038 := by
    simpa [prefixWord, tailWord_5649038, baseEnd_5649038] using wordTrace_append hprefix tailTrace_5649038
  have hstable : (prefixWord ++ tailWord_5649038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649038).length < 2 ^ (prefixWord ++ tailWord_5649038).sum := by decide
  have hdescent : baseEnd_5649038 < baseStart_5649038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649061 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_5649061 : Nat := 118140960795 + 5649061 * 2 ^ 59
def prefixEnd_5649061 : Nat := 4983230072969 + 3 ^ 40 * 5649061 * 2
def baseEnd_5649061 : Nat := 966894513189475918852649

theorem tailTrace_5649061 : CollatzResearch.WordTrace tailWord_5649061 prefixEnd_5649061 966894513189475918852649 := by
  unfold tailWord_5649061
  simp only [CollatzResearch.WordTrace]
  refine ⟨206038181387424254653627037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137358787591616169769084691 206038181387424254653627037)
  ·
    refine ⟨77264318020284095495110139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206038181387424254653627037 77264318020284095495110139)
    ·
      refine ⟨115896477030426143242665209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77264318020284095495110139 115896477030426143242665209)
      ·
        refine ⟨86922357772819607431998907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115896477030426143242665209 86922357772819607431998907)
        ·
          refine ⟨130383536659229411147998361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86922357772819607431998907 130383536659229411147998361)
          ·
            refine ⟨97787652494422058360998771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130383536659229411147998361 97787652494422058360998771)
            ·
              refine ⟨146681478741633087541498157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97787652494422058360998771 146681478741633087541498157)
              ·
                refine ⟨55005554528112407828061809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146681478741633087541498157 55005554528112407828061809)
                ·
                  refine ⟨41254165896084305871046357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55005554528112407828061809 41254165896084305871046357)
                  ·
                    refine ⟨966894513189475918852649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41254165896084305871046357 966894513189475918852649)
                    ·
                      rfl

theorem cell23_5649061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_5649061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649061 prefixEnd_5649061 := by exact prefixLift 5649061
  have htrace : WordTrace (prefixWord ++ tailWord_5649061) baseStart_5649061 baseEnd_5649061 := by
    simpa [prefixWord, tailWord_5649061, baseEnd_5649061] using wordTrace_append hprefix tailTrace_5649061
  have hstable : (prefixWord ++ tailWord_5649061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649061).length < 2 ^ (prefixWord ++ tailWord_5649061).sum := by decide
  have hdescent : baseEnd_5649061 < baseStart_5649061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649069 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_5649069 : Nat := 118140960795 + 5649069 * 2 ^ 59
def prefixEnd_5649069 : Nat := 4983230072969 + 3 ^ 40 * 5649069 * 2
def baseEnd_5649069 : Nat := 966895882471221241752637

theorem tailTrace_5649069 : CollatzResearch.WordTrace tailWord_5649069 prefixEnd_5649069 966895882471221241752637 := by
  unfold tailWord_5649069
  simp only [CollatzResearch.WordTrace]
  refine ⟨206038473171395272019918261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137358982114263514679945507 206038473171395272019918261)
  ·
    refine ⟨19316106859818306751867337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206038473171395272019918261 19316106859818306751867337)
    ·
      refine ⟨14487080144863730063900503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19316106859818306751867337 14487080144863730063900503)
      ·
        refine ⟨21730620217295595095850755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14487080144863730063900503 21730620217295595095850755)
        ·
          refine ⟨32595930325943392643776133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21730620217295595095850755 32595930325943392643776133)
          ·
            refine ⟨6111736936114386120708025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32595930325943392643776133 6111736936114386120708025)
            ·
              refine ⟨4583802702085789590531019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6111736936114386120708025 4583802702085789590531019)
              ·
                refine ⟨6875704053128684385796529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4583802702085789590531019 6875704053128684385796529)
                ·
                  refine ⟨5156778039846513289347397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6875704053128684385796529 5156778039846513289347397)
                  ·
                    refine ⟨966895882471221241752637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5156778039846513289347397 966895882471221241752637)
                    ·
                      rfl

theorem cell23_5649069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_5649069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649069 prefixEnd_5649069 := by exact prefixLift 5649069
  have htrace : WordTrace (prefixWord ++ tailWord_5649069) baseStart_5649069 baseEnd_5649069 := by
    simpa [prefixWord, tailWord_5649069, baseEnd_5649069] using wordTrace_append hprefix tailTrace_5649069
  have hstable : (prefixWord ++ tailWord_5649069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649069).length < 2 ^ (prefixWord ++ tailWord_5649069).sum := by decide
  have hdescent : baseEnd_5649069 < baseStart_5649069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649079 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 1, 2, 3]
def baseStart_5649079 : Nat := 118140960795 + 5649079 * 2 ^ 59
def prefixEnd_5649079 : Nat := 4983230072969 + 3 ^ 40 * 5649079 * 2
def baseEnd_5649079 : Nat := 2900692782220208686132865

theorem tailTrace_5649079 : CollatzResearch.WordTrace tailWord_5649079 prefixEnd_5649079 2900692782220208686132865 := by
  unfold tailWord_5649079
  simp only [CollatzResearch.WordTrace]
  refine ⟨206038837901359043727782291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137359225267572695818521527 206038837901359043727782291)
  ·
    refine ⟨309058256852038565591673437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206038837901359043727782291 309058256852038565591673437)
    ·
      refine ⟨115896846319514462096877539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309058256852038565591673437 115896846319514462096877539)
      ·
        refine ⟨173845269479271693145316309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115896846319514462096877539 173845269479271693145316309)
        ·
          refine ⟨4074498503420430308093351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 173845269479271693145316309 4074498503420430308093351)
          ·
            refine ⟨6111747755130645462140027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074498503420430308093351 6111747755130645462140027)
            ·
              refine ⟨9167621632695968193210041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111747755130645462140027 9167621632695968193210041)
              ·
                refine ⟨6875716224521976144907531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9167621632695968193210041 6875716224521976144907531)
                ·
                  refine ⟨10313574336782964217361297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6875716224521976144907531 10313574336782964217361297)
                  ·
                    refine ⟨7735180752587223163020973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10313574336782964217361297 7735180752587223163020973)
                    ·
                      refine ⟨2900692782220208686132865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7735180752587223163020973 2900692782220208686132865)
                      ·
                        rfl

theorem cell23_5649079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_5649079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649079 prefixEnd_5649079 := by exact prefixLift 5649079
  have htrace : WordTrace (prefixWord ++ tailWord_5649079) baseStart_5649079 baseEnd_5649079 := by
    simpa [prefixWord, tailWord_5649079, baseEnd_5649079] using wordTrace_append hprefix tailTrace_5649079
  have hstable : (prefixWord ++ tailWord_5649079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649079).length < 2 ^ (prefixWord ++ tailWord_5649079).sum := by decide
  have hdescent : baseEnd_5649079 < baseStart_5649079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649081 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 8]
def baseStart_5649081 : Nat := 118140960795 + 5649081 * 2 ^ 59
def prefixEnd_5649081 : Nat := 4983230072969 + 3 ^ 40 * 5649081 * 2
def baseEnd_5649081 : Nat := 2900693809181517678307855

theorem tailTrace_5649081 : CollatzResearch.WordTrace tailWord_5649081 prefixEnd_5649081 2900693809181517678307855 := by
  unfold tailWord_5649081
  simp only [CollatzResearch.WordTrace]
  refine ⟨206038910847351798069355097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137359273898234532046236731 206038910847351798069355097)
  ·
    refine ⟨154529183135513848552016323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206038910847351798069355097 154529183135513848552016323)
    ·
      refine ⟨231793774703270772828024485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154529183135513848552016323 231793774703270772828024485)
      ·
        refine ⟨43461332756863269905254591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231793774703270772828024485 43461332756863269905254591)
        ·
          refine ⟨65191999135294904857881887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43461332756863269905254591 65191999135294904857881887)
          ·
            refine ⟨97787998702942357286822831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65191999135294904857881887 97787998702942357286822831)
            ·
              refine ⟨146681998054413535930234247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97787998702942357286822831 146681998054413535930234247)
              ·
                refine ⟨220022997081620303895351371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146681998054413535930234247 220022997081620303895351371)
                ·
                  refine ⟨330034495622430455843027057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220022997081620303895351371 330034495622430455843027057)
                  ·
                    refine ⟨247525871716822841882270293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 330034495622430455843027057 247525871716822841882270293)
                    ·
                      refine ⟨2900693809181517678307855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 247525871716822841882270293 2900693809181517678307855)
                      ·
                        rfl

theorem cell23_5649081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_5649081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649081 prefixEnd_5649081 := by exact prefixLift 5649081
  have htrace : WordTrace (prefixWord ++ tailWord_5649081) baseStart_5649081 baseEnd_5649081 := by
    simpa [prefixWord, tailWord_5649081, baseEnd_5649081] using wordTrace_append hprefix tailTrace_5649081
  have hstable : (prefixWord ++ tailWord_5649081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649081).length < 2 ^ (prefixWord ++ tailWord_5649081).sum := by decide
  have hdescent : baseEnd_5649081 < baseStart_5649081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649138 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 9]
def baseStart_5649138 : Nat := 118140960795 + 5649138 * 2 ^ 59
def prefixEnd_5649138 : Nat := 4983230072969 + 3 ^ 40 * 5649138 * 2
def baseEnd_5649138 : Nat := 322302564175424883921677

theorem tailTrace_5649138 : CollatzResearch.WordTrace tailWord_5649138 prefixEnd_5649138 322302564175424883921677 := by
  unfold tailWord_5649138
  simp only [CollatzResearch.WordTrace]
  refine ⟨51510247452036324201045017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137360659872096864536120045 51510247452036324201045017)
  ·
    refine ⟨38632685589027243150783763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51510247452036324201045017 38632685589027243150783763)
    ·
      refine ⟨57949028383540864726175645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38632685589027243150783763 57949028383540864726175645)
      ·
        refine ⟨21730885643827824272315867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57949028383540864726175645 21730885643827824272315867)
        ·
          refine ⟨32596328465741736408473801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21730885643827824272315867 32596328465741736408473801)
          ·
            refine ⟨24447246349306302306355351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32596328465741736408473801 24447246349306302306355351)
            ·
              refine ⟨36670869523959453459533027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24447246349306302306355351 36670869523959453459533027)
              ·
                refine ⟨55006304285939180189299541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36670869523959453459533027 55006304285939180189299541)
                ·
                  refine ⟨322302564175424883921677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55006304285939180189299541 322302564175424883921677)
                  ·
                    rfl

theorem cell23_5649138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_5649138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649138 prefixEnd_5649138 := by exact prefixLift 5649138
  have htrace : WordTrace (prefixWord ++ tailWord_5649138) baseStart_5649138 baseEnd_5649138 := by
    simpa [prefixWord, tailWord_5649138, baseEnd_5649138] using wordTrace_append hprefix tailTrace_5649138
  have hstable : (prefixWord ++ tailWord_5649138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649138).length < 2 ^ (prefixWord ++ tailWord_5649138).sum := by decide
  have hdescent : baseEnd_5649138 < baseStart_5649138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649178 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7]
def baseStart_5649178 : Nat := 118140960795 + 5649178 * 2 ^ 59
def prefixEnd_5649178 : Nat := 4983230072969 + 3 ^ 40 * 5649178 * 2
def baseEnd_5649178 : Nat := 2900743616805003798794909

theorem tailTrace_5649178 : CollatzResearch.WordTrace tailWord_5649178 prefixEnd_5649178 2900743616805003798794909 := by
  unfold tailWord_5649178
  simp only [CollatzResearch.WordTrace]
  refine ⟨51510612182000095908909047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137361632485333589090424125 51510612182000095908909047)
  ·
    refine ⟨77265918273000143863363571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51510612182000095908909047 77265918273000143863363571)
    ·
      refine ⟨115898877409500215795045357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77265918273000143863363571 115898877409500215795045357)
      ·
        refine ⟨43462079028562580923142009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115898877409500215795045357 43462079028562580923142009)
        ·
          refine ⟨32596559271421935692356507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43462079028562580923142009 32596559271421935692356507)
          ·
            refine ⟨48894838907132903538534761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32596559271421935692356507 48894838907132903538534761)
            ·
              refine ⟨36671129180349677653901071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48894838907132903538534761 36671129180349677653901071)
              ·
                refine ⟨55006693770524516480851607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36671129180349677653901071 55006693770524516480851607)
                ·
                  refine ⟨82510040655786774721277411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55006693770524516480851607 82510040655786774721277411)
                  ·
                    refine ⟨123765060983680162081916117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82510040655786774721277411 123765060983680162081916117)
                    ·
                      refine ⟨2900743616805003798794909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123765060983680162081916117 2900743616805003798794909)
                      ·
                        rfl

theorem cell23_5649178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_5649178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649178 prefixEnd_5649178 := by exact prefixLift 5649178
  have htrace : WordTrace (prefixWord ++ tailWord_5649178) baseStart_5649178 baseEnd_5649178 := by
    simpa [prefixWord, tailWord_5649178, baseEnd_5649178] using wordTrace_append hprefix tailTrace_5649178
  have hstable : (prefixWord ++ tailWord_5649178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649178).length < 2 ^ (prefixWord ++ tailWord_5649178).sum := by decide
  have hdescent : baseEnd_5649178 < baseStart_5649178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649205 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_5649205 : Nat := 118140960795 + 5649205 * 2 ^ 59
def prefixEnd_5649205 : Nat := 4983230072969 + 3 ^ 40 * 5649205 * 2
def baseEnd_5649205 : Nat := 2900757480782675193157285

theorem tailTrace_5649205 : CollatzResearch.WordTrace tailWord_5649205 prefixEnd_5649205 2900757480782675193157285 := by
  unfold tailWord_5649205
  simp only [CollatzResearch.WordTrace]
  refine ⟨206043433498902567246869069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137362288999268378164579379 206043433498902567246869069)
  ·
    refine ⟨77266287562088462717575901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206043433498902567246869069 77266287562088462717575901)
    ·
      refine ⟨28974857835783173519090963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77266287562088462717575901 28974857835783173519090963)
      ·
        refine ⟨43462286753674760278636445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28974857835783173519090963 43462286753674760278636445)
        ·
          refine ⟨16298357532628035104488667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43462286753674760278636445 16298357532628035104488667)
          ·
            refine ⟨24447536298942052656733001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16298357532628035104488667 24447536298942052656733001)
            ·
              refine ⟨18335652224206539492549751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24447536298942052656733001 18335652224206539492549751)
              ·
                refine ⟨27503478336309809238824627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18335652224206539492549751 27503478336309809238824627)
                ·
                  refine ⟨41255217504464713858236941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27503478336309809238824627 41255217504464713858236941)
                  ·
                    refine ⟨15470706564174267696838853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41255217504464713858236941 15470706564174267696838853)
                    ·
                      refine ⟨2900757480782675193157285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15470706564174267696838853 2900757480782675193157285)
                      ·
                        rfl

theorem cell23_5649205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_5649205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649205 prefixEnd_5649205 := by exact prefixLift 5649205
  have htrace : WordTrace (prefixWord ++ tailWord_5649205) baseStart_5649205 baseEnd_5649205 := by
    simpa [prefixWord, tailWord_5649205, baseEnd_5649205] using wordTrace_append hprefix tailTrace_5649205
  have hstable : (prefixWord ++ tailWord_5649205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649205).length < 2 ^ (prefixWord ++ tailWord_5649205).sum := by decide
  have hdescent : baseEnd_5649205 < baseStart_5649205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649206 : List Nat := [5, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_5649206 : Nat := 118140960795 + 5649206 * 2 ^ 59
def prefixEnd_5649206 : Nat := 4983230072969 + 3 ^ 40 * 5649206 * 2
def baseEnd_5649206 : Nat := 322306443807036632138309

theorem tailTrace_5649206 : CollatzResearch.WordTrace tailWord_5649206 prefixEnd_5649206 322306443807036632138309 := by
  unfold tailWord_5649206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12877716873243684026103467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137362313314599296278436981 12877716873243684026103467)
  ·
    refine ⟨19316575309865526039155201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12877716873243684026103467 19316575309865526039155201)
    ·
      refine ⟨14487431482399144529366401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19316575309865526039155201 14487431482399144529366401)
      ·
        refine ⟨10865573611799358397024801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14487431482399144529366401 10865573611799358397024801)
        ·
          refine ⟨8149180208849518797768601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10865573611799358397024801 8149180208849518797768601)
          ·
            refine ⟨6111885156637139098326451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8149180208849518797768601 6111885156637139098326451)
            ·
              refine ⟨9167827734955708647489677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111885156637139098326451 9167827734955708647489677)
              ·
                refine ⟨3437935400608390742808629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9167827734955708647489677 3437935400608390742808629)
                ·
                  refine ⟨322306443807036632138309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3437935400608390742808629 322306443807036632138309)
                  ·
                    rfl

theorem cell23_5649206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_5649206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649206 prefixEnd_5649206 := by exact prefixLift 5649206
  have htrace : WordTrace (prefixWord ++ tailWord_5649206) baseStart_5649206 baseEnd_5649206 := by
    simpa [prefixWord, tailWord_5649206, baseEnd_5649206] using wordTrace_append hprefix tailTrace_5649206
  have hstable : (prefixWord ++ tailWord_5649206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649206).length < 2 ^ (prefixWord ++ tailWord_5649206).sum := by decide
  have hdescent : baseEnd_5649206 < baseStart_5649206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649225 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 3]
def baseStart_5649225 : Nat := 118140960795 + 5649225 * 2 ^ 59
def prefixEnd_5649225 : Nat := 4983230072969 + 3 ^ 40 * 5649225 * 2
def baseEnd_5649225 : Nat := 2900767750395765114907193

theorem tailTrace_5649225 : CollatzResearch.WordTrace tailWord_5649225 prefixEnd_5649225 2900767750395765114907193 := by
  unfold tailWord_5649225
  simp only [CollatzResearch.WordTrace]
  refine ⟨206044162958830110662597129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137362775305886740441731419 206044162958830110662597129)
  ·
    refine ⟨154533122219122582996947847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206044162958830110662597129 154533122219122582996947847)
    ·
      refine ⟨231799683328683874495421771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154533122219122582996947847 231799683328683874495421771)
      ·
        refine ⟨347699524993025811743132657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231799683328683874495421771 347699524993025811743132657)
        ·
          refine ⟨260774643744769358807349493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347699524993025811743132657 260774643744769358807349493)
          ·
            refine ⟨24447622851072127388189015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260774643744769358807349493 24447622851072127388189015)
            ·
              refine ⟨36671434276608191082283523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24447622851072127388189015 36671434276608191082283523)
              ·
                refine ⟨55007151414912286623425285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36671434276608191082283523 55007151414912286623425285)
                ·
                  refine ⟨10313840890296053741892241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55007151414912286623425285 10313840890296053741892241)
                  ·
                    refine ⟨7735380667722040306419181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10313840890296053741892241 7735380667722040306419181)
                    ·
                      refine ⟨2900767750395765114907193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7735380667722040306419181 2900767750395765114907193)
                      ·
                        rfl

theorem cell23_5649225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_5649225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649225 prefixEnd_5649225 := by exact prefixLift 5649225
  have htrace : WordTrace (prefixWord ++ tailWord_5649225) baseStart_5649225 baseEnd_5649225 := by
    simpa [prefixWord, tailWord_5649225, baseEnd_5649225] using wordTrace_append hprefix tailTrace_5649225
  have hstable : (prefixWord ++ tailWord_5649225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649225).length < 2 ^ (prefixWord ++ tailWord_5649225).sum := by decide
  have hdescent : baseEnd_5649225 < baseStart_5649225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649232 : List Nat := [2, 1, 1, 1, 1, 4, 2, 6, 1, 4]
def baseStart_5649232 : Nat := 118140960795 + 5649232 * 2 ^ 59
def prefixEnd_5649232 : Nat := 4983230072969 + 3 ^ 40 * 5649232 * 2
def baseEnd_5649232 : Nat := 966923781586782195839887

theorem tailTrace_5649232 : CollatzResearch.WordTrace tailWord_5649232 prefixEnd_5649232 966923781586782195839887 := by
  unfold tailWord_5649232
  simp only [CollatzResearch.WordTrace]
  refine ⟨103022209134902375429050975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137362945513203167238734633 103022209134902375429050975)
  ·
    refine ⟨154533313702353563143576463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103022209134902375429050975 154533313702353563143576463)
    ·
      refine ⟨231799970553530344715364695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154533313702353563143576463 231799970553530344715364695)
      ·
        refine ⟨347699955830295517073047043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231799970553530344715364695 347699955830295517073047043)
        ·
          refine ⟨521549933745443275609570565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347699955830295517073047043 521549933745443275609570565)
          ·
            refine ⟨97790612577270614176794481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 521549933745443275609570565 97790612577270614176794481)
            ·
              refine ⟨73342959432952960632595861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97790612577270614176794481 73342959432952960632595861)
              ·
                refine ⟨3437951223419670029652931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73342959432952960632595861 3437951223419670029652931)
                ·
                  refine ⟨5156926835129505044479397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437951223419670029652931 5156926835129505044479397)
                  ·
                    refine ⟨966923781586782195839887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5156926835129505044479397 966923781586782195839887)
                    ·
                      rfl

theorem cell23_5649232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 4].length) (baseStart_5649232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649232 prefixEnd_5649232 := by exact prefixLift 5649232
  have htrace : WordTrace (prefixWord ++ tailWord_5649232) baseStart_5649232 baseEnd_5649232 := by
    simpa [prefixWord, tailWord_5649232, baseEnd_5649232] using wordTrace_append hprefix tailTrace_5649232
  have hstable : (prefixWord ++ tailWord_5649232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649232).length < 2 ^ (prefixWord ++ tailWord_5649232).sum := by decide
  have hdescent : baseEnd_5649232 < baseStart_5649232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649275 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 1, 5]
def baseStart_5649275 : Nat := 118140960795 + 5649275 * 2 ^ 59
def prefixEnd_5649275 : Nat := 4983230072969 + 3 ^ 40 * 5649275 * 2
def baseEnd_5649275 : Nat := 966931141476163306427321

theorem tailTrace_5649275 : CollatzResearch.WordTrace tailWord_5649275 prefixEnd_5649275 966931141476163306427321 := by
  unfold tailWord_5649275
  simp only [CollatzResearch.WordTrace]
  refine ⟨206045986608648969201917279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137363991072432646134611519 206045986608648969201917279)
  ·
    refine ⟨309068979912973453802875919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206045986608648969201917279 309068979912973453802875919)
    ·
      refine ⟨463603469869460180704313879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309068979912973453802875919 463603469869460180704313879)
      ·
        refine ⟨695405204804190271056470819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463603469869460180704313879 695405204804190271056470819)
        ·
          refine ⟨1043107807206285406584706229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695405204804190271056470819 1043107807206285406584706229)
          ·
            refine ⟨97791356925589256867316209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1043107807206285406584706229 97791356925589256867316209)
            ·
              refine ⟨73343517694191942650487157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97791356925589256867316209 73343517694191942650487157)
              ·
                refine ⟨6875954783830494623483171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73343517694191942650487157 6875954783830494623483171)
                ·
                  refine ⟨10313932175745741935224757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6875954783830494623483171 10313932175745741935224757)
                  ·
                    refine ⟨966931141476163306427321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10313932175745741935224757 966931141476163306427321)
                    ·
                      rfl

theorem cell23_5649275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 5].length) (baseStart_5649275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649275 prefixEnd_5649275 := by exact prefixLift 5649275
  have htrace : WordTrace (prefixWord ++ tailWord_5649275) baseStart_5649275 baseEnd_5649275 := by
    simpa [prefixWord, tailWord_5649275, baseEnd_5649275] using wordTrace_append hprefix tailTrace_5649275
  have hstable : (prefixWord ++ tailWord_5649275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649275).length < 2 ^ (prefixWord ++ tailWord_5649275).sum := by decide
  have hdescent : baseEnd_5649275 < baseStart_5649275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649305 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 6, 4]
def baseStart_5649305 : Nat := 118140960795 + 5649305 * 2 ^ 59
def prefixEnd_5649305 : Nat := 4983230072969 + 3 ^ 40 * 5649305 * 2
def baseEnd_5649305 : Nat := 966936276282708267302275

theorem tailTrace_5649305 : CollatzResearch.WordTrace tailWord_5649305 prefixEnd_5649305 966936276282708267302275 := by
  unfold tailWord_5649305
  simp only [CollatzResearch.WordTrace]
  refine ⟨206047080798540284325509369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137364720532360189550339579 206047080798540284325509369)
  ·
    refine ⟨154535310598905213244132027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206047080798540284325509369 154535310598905213244132027)
    ·
      refine ⟨231802965898357819866198041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154535310598905213244132027 231802965898357819866198041)
      ·
        refine ⟨173852224423768364899648531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231802965898357819866198041 173852224423768364899648531)
        ·
          refine ⟨260778336635652547349472797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173852224423768364899648531 260778336635652547349472797)
          ·
            refine ⟨97791876238369705256052299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260778336635652547349472797 97791876238369705256052299)
            ·
              refine ⟨146687814357554557884078449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97791876238369705256052299 146687814357554557884078449)
              ·
                refine ⟨110015860768165918413058837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146687814357554557884078449 110015860768165918413058837)
                ·
                  refine ⟨5156993473507777425612133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110015860768165918413058837 5156993473507777425612133)
                  ·
                    refine ⟨966936276282708267302275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5156993473507777425612133 966936276282708267302275)
                    ·
                      rfl

theorem cell23_5649305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 4].length) (baseStart_5649305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649305 prefixEnd_5649305 := by exact prefixLift 5649305
  have htrace : WordTrace (prefixWord ++ tailWord_5649305) baseStart_5649305 baseEnd_5649305 := by
    simpa [prefixWord, tailWord_5649305, baseEnd_5649305] using wordTrace_append hprefix tailTrace_5649305
  have hstable : (prefixWord ++ tailWord_5649305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649305).length < 2 ^ (prefixWord ++ tailWord_5649305).sum := by decide
  have hdescent : baseEnd_5649305 < baseStart_5649305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649329 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_5649329 : Nat := 118140960795 + 5649329 * 2 ^ 59
def prefixEnd_5649329 : Nat := 4983230072969 + 3 ^ 40 * 5649329 * 2
def baseEnd_5649329 : Nat := 2900821152383832708006715

theorem tailTrace_5649329 : CollatzResearch.WordTrace tailWord_5649329 prefixEnd_5649329 2900821152383832708006715 := by
  unfold tailWord_5649329
  simp only [CollatzResearch.WordTrace]
  refine ⟨206047956150453336424383041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137365304100302224282922027 206047956150453336424383041)
  ·
    refine ⟨154535967112840002318287281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206047956150453336424383041 154535967112840002318287281)
    ·
      refine ⟨115901975334630001738715461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154535967112840002318287281 115901975334630001738715461)
      ·
        refine ⟨21731620375243125326009149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115901975334630001738715461 21731620375243125326009149)
        ·
          refine ⟨8149357640716171997253431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21731620375243125326009149 8149357640716171997253431)
          ·
            refine ⟨12224036461074257995880147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149357640716171997253431 12224036461074257995880147)
            ·
              refine ⟨18336054691611386993820221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12224036461074257995880147 18336054691611386993820221)
              ·
                refine ⟨6876020509354270122682583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18336054691611386993820221 6876020509354270122682583)
                ·
                  refine ⟨10314030764031405184023875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6876020509354270122682583 10314030764031405184023875)
                  ·
                    refine ⟨15471046146047107776035813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10314030764031405184023875 15471046146047107776035813)
                    ·
                      refine ⟨2900821152383832708006715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15471046146047107776035813 2900821152383832708006715)
                      ·
                        rfl

theorem cell23_5649329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_5649329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649329 prefixEnd_5649329 := by exact prefixLift 5649329
  have htrace : WordTrace (prefixWord ++ tailWord_5649329) baseStart_5649329 baseEnd_5649329 := by
    simpa [prefixWord, tailWord_5649329, baseEnd_5649329] using wordTrace_append hprefix tailTrace_5649329
  have hstable : (prefixWord ++ tailWord_5649329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649329).length < 2 ^ (prefixWord ++ tailWord_5649329).sum := by decide
  have hdescent : baseEnd_5649329 < baseStart_5649329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649366 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_5649366 : Nat := 118140960795 + 5649366 * 2 ^ 59
def prefixEnd_5649366 : Nat := 4983230072969 + 3 ^ 40 * 5649366 * 2
def baseEnd_5649366 : Nat := 2900840151168049063244045

theorem tailTrace_5649366 : CollatzResearch.WordTrace tailWord_5649366 prefixEnd_5649366 2900840151168049063244045 := by
  unfold tailWord_5649366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878081603207455733967497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137366203767546194495653301 12878081603207455733967497)
  ·
    refine ⟨9658561202405591800475623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12878081603207455733967497 9658561202405591800475623)
    ·
      refine ⟨14487841803608387700713435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9658561202405591800475623 14487841803608387700713435)
      ·
        refine ⟨21731762705412581551070153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14487841803608387700713435 21731762705412581551070153)
        ·
          refine ⟨16298822029059436163302615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21731762705412581551070153 16298822029059436163302615)
          ·
            refine ⟨24448233043589154244953923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16298822029059436163302615 24448233043589154244953923)
            ·
              refine ⟨36672349565383731367430885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24448233043589154244953923 36672349565383731367430885)
              ·
                refine ⟨6876065543509449631393291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36672349565383731367430885 6876065543509449631393291)
                ·
                  refine ⟨10314098315264174447089937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6876065543509449631393291 10314098315264174447089937)
                  ·
                    refine ⟨7735573736448130835317453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10314098315264174447089937 7735573736448130835317453)
                    ·
                      refine ⟨2900840151168049063244045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7735573736448130835317453 2900840151168049063244045)
                      ·
                        rfl

theorem cell23_5649366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_5649366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649366 prefixEnd_5649366 := by exact prefixLift 5649366
  have htrace : WordTrace (prefixWord ++ tailWord_5649366) baseStart_5649366 baseEnd_5649366 := by
    simpa [prefixWord, tailWord_5649366, baseEnd_5649366] using wordTrace_append hprefix tailTrace_5649366
  have hstable : (prefixWord ++ tailWord_5649366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649366).length < 2 ^ (prefixWord ++ tailWord_5649366).sum := by decide
  have hdescent : baseEnd_5649366 < baseStart_5649366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649397 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5649397 : Nat := 118140960795 + 5649397 * 2 ^ 59
def prefixEnd_5649397 : Nat := 4983230072969 + 3 ^ 40 * 5649397 * 2
def baseEnd_5649397 : Nat := 2900856069068338441956403

theorem tailTrace_5649397 : CollatzResearch.WordTrace tailWord_5649397 prefixEnd_5649397 2900856069068338441956403 := by
  unfold tailWord_5649397
  simp only [CollatzResearch.WordTrace]
  refine ⟨206050436314206984037858445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137366957542804656025238963 206050436314206984037858445)
  ·
    refine ⟨77268913617827619014196917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206050436314206984037858445 77268913617827619014196917)
    ·
      refine ⟨7243960651671339282580961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77268913617827619014196917 7243960651671339282580961)
      ·
        refine ⟨5432970488753504461935721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7243960651671339282580961 5432970488753504461935721)
        ·
          refine ⟨4074727866565128346451791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5432970488753504461935721 4074727866565128346451791)
          ·
            refine ⟨6112091799847692519677687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074727866565128346451791 6112091799847692519677687)
            ·
              refine ⟨9168137699771538779516531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112091799847692519677687 9168137699771538779516531)
              ·
                refine ⟨13752206549657308169274797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9168137699771538779516531 13752206549657308169274797)
                ·
                  refine ⟨5157077456121490563478049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13752206549657308169274797 5157077456121490563478049)
                  ·
                    refine ⟨3867808092091117922608537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5157077456121490563478049 3867808092091117922608537)
                    ·
                      refine ⟨2900856069068338441956403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867808092091117922608537 2900856069068338441956403)
                      ·
                        rfl

theorem cell23_5649397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5649397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649397 prefixEnd_5649397 := by exact prefixLift 5649397
  have htrace : WordTrace (prefixWord ++ tailWord_5649397) baseStart_5649397 baseEnd_5649397 := by
    simpa [prefixWord, tailWord_5649397, baseEnd_5649397] using wordTrace_append hprefix tailTrace_5649397
  have hstable : (prefixWord ++ tailWord_5649397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649397).length < 2 ^ (prefixWord ++ tailWord_5649397).sum := by decide
  have hdescent : baseEnd_5649397 < baseStart_5649397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649405 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_5649405 : Nat := 118140960795 + 5649405 * 2 ^ 59
def prefixEnd_5649405 : Nat := 4983230072969 + 3 ^ 40 * 5649405 * 2
def baseEnd_5649405 : Nat := 2900860176913574410656365

theorem tailTrace_5649405 : CollatzResearch.WordTrace tailWord_5649405 prefixEnd_5649405 2900860176913574410656365 := by
  unfold tailWord_5649405
  simp only [CollatzResearch.WordTrace]
  refine ⟨206050728098178001404149669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137367152065452000936099779 206050728098178001404149669)
  ·
    refine ⟨38634511518408375263278063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206050728098178001404149669 38634511518408375263278063)
    ·
      refine ⟨57951767277612562894917095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38634511518408375263278063 57951767277612562894917095)
      ·
        refine ⟨86927650916418844342375643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57951767277612562894917095 86927650916418844342375643)
        ·
          refine ⟨130391476374628266513563465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86927650916418844342375643 130391476374628266513563465)
          ·
            refine ⟨97793607280971199885172599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130391476374628266513563465 97793607280971199885172599)
            ·
              refine ⟨146690410921456799827758899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97793607280971199885172599 146690410921456799827758899)
              ·
                refine ⟨220035616382185199741638349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146690410921456799827758899 220035616382185199741638349)
                ·
                  refine ⟨82513356143319449903114381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220035616382185199741638349 82513356143319449903114381)
                  ·
                    refine ⟨30942508553744793713667893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82513356143319449903114381 30942508553744793713667893)
                    ·
                      refine ⟨2900860176913574410656365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30942508553744793713667893 2900860176913574410656365)
                      ·
                        rfl

theorem cell23_5649405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_5649405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649405 prefixEnd_5649405 := by exact prefixLift 5649405
  have htrace : WordTrace (prefixWord ++ tailWord_5649405) baseStart_5649405 baseEnd_5649405 := by
    simpa [prefixWord, tailWord_5649405, baseEnd_5649405] using wordTrace_append hprefix tailTrace_5649405
  have hstable : (prefixWord ++ tailWord_5649405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649405).length < 2 ^ (prefixWord ++ tailWord_5649405).sum := by decide
  have hdescent : baseEnd_5649405 < baseStart_5649405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649422 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5649422 : Nat := 118140960795 + 5649422 * 2 ^ 59
def prefixEnd_5649422 : Nat := 4983230072969 + 3 ^ 40 * 5649422 * 2
def baseEnd_5649422 : Nat := 2900868906084700844143787

theorem tailTrace_5649422 : CollatzResearch.WordTrace tailWord_5649422 prefixEnd_5649422 2900868906084700844143787 := by
  unfold tailWord_5649422
  simp only [CollatzResearch.WordTrace]
  refine ⟨25756418517389551663439815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137367565426077608871679013 25756418517389551663439815)
  ·
    refine ⟨38634627776084327495159723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25756418517389551663439815 38634627776084327495159723)
    ·
      refine ⟨57951941664126491242739585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38634627776084327495159723 57951941664126491242739585)
      ·
        refine ⟨43463956248094868432054689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57951941664126491242739585 43463956248094868432054689)
        ·
          refine ⟨32597967186071151324041017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43463956248094868432054689 32597967186071151324041017)
          ·
            refine ⟨24448475389553363493030763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32597967186071151324041017 24448475389553363493030763)
            ·
              refine ⟨36672713084330045239546145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24448475389553363493030763 36672713084330045239546145)
              ·
                refine ⟨27504534813247533929659609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36672713084330045239546145 27504534813247533929659609)
                ·
                  refine ⟨20628401109935650447244707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27504534813247533929659609 20628401109935650447244707)
                  ·
                    refine ⟨30942601664903475670867061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20628401109935650447244707 30942601664903475670867061)
                    ·
                      refine ⟨2900868906084700844143787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30942601664903475670867061 2900868906084700844143787)
                      ·
                        rfl

theorem cell23_5649422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5649422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649422 prefixEnd_5649422 := by exact prefixLift 5649422
  have htrace : WordTrace (prefixWord ++ tailWord_5649422) baseStart_5649422 baseEnd_5649422 := by
    simpa [prefixWord, tailWord_5649422, baseEnd_5649422] using wordTrace_append hprefix tailTrace_5649422
  have hstable : (prefixWord ++ tailWord_5649422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649422).length < 2 ^ (prefixWord ++ tailWord_5649422).sum := by decide
  have hdescent : baseEnd_5649422 < baseStart_5649422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649425 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 7]
def baseStart_5649425 : Nat := 118140960795 + 5649425 * 2 ^ 59
def prefixEnd_5649425 : Nat := 4983230072969 + 3 ^ 40 * 5649425 * 2
def baseEnd_5649425 : Nat := 322318938502962703600697

theorem tailTrace_5649425 : CollatzResearch.WordTrace tailWord_5649425 prefixEnd_5649425 322318938502962703600697 := by
  unfold tailWord_5649425
  simp only [CollatzResearch.WordTrace]
  refine ⟨206051457558105544819877729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137367638372070363213251819 206051457558105544819877729)
  ·
    refine ⟨154538593168579158614908297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206051457558105544819877729 154538593168579158614908297)
    ·
      refine ⟨115903944876434368961181223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154538593168579158614908297 115903944876434368961181223)
      ·
        refine ⟨173855917314651553441771835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115903944876434368961181223 173855917314651553441771835)
        ·
          refine ⟨260783875971977330162657753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173855917314651553441771835 260783875971977330162657753)
          ·
            refine ⟨195587906978982997621993315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260783875971977330162657753 195587906978982997621993315)
            ·
              refine ⟨293381860468474496432989973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195587906978982997621993315 293381860468474496432989973)
              ·
                refine ⟨13752274709459742020296405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 293381860468474496432989973 13752274709459742020296405)
                ·
                  refine ⟨322318938502962703600697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13752274709459742020296405 322318938502962703600697)
                  ·
                    rfl

theorem cell23_5649425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 7].length) (baseStart_5649425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649425 prefixEnd_5649425 := by exact prefixLift 5649425
  have htrace : WordTrace (prefixWord ++ tailWord_5649425) baseStart_5649425 baseEnd_5649425 := by
    simpa [prefixWord, tailWord_5649425, baseEnd_5649425] using wordTrace_append hprefix tailTrace_5649425
  have hstable : (prefixWord ++ tailWord_5649425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649425).length < 2 ^ (prefixWord ++ tailWord_5649425).sum := by decide
  have hdescent : baseEnd_5649425 < baseStart_5649425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649436 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_5649436 : Nat := 118140960795 + 5649436 * 2 ^ 59
def prefixEnd_5649436 : Nat := 4983230072969 + 3 ^ 40 * 5649436 * 2
def baseEnd_5649436 : Nat := 2900876094813863789368723

theorem tailTrace_5649436 : CollatzResearch.WordTrace tailWord_5649436 prefixEnd_5649436 2900876094813863789368723 := by
  unfold tailWord_5649436
  simp only [CollatzResearch.WordTrace]
  refine ⟨103025929380532846849264081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137367905840710462465685441 103025929380532846849264081)
  ·
    refine ⟨77269447035399635136948061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103025929380532846849264081 77269447035399635136948061)
    ·
      refine ⟨28976042638274863176355523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77269447035399635136948061 28976042638274863176355523)
      ·
        refine ⟨43464063957412294764533285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28976042638274863176355523 43464063957412294764533285)
        ·
          refine ⟨8149511992014805268349991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43464063957412294764533285 8149511992014805268349991)
          ·
            refine ⟨12224267988022207902524987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149511992014805268349991 12224267988022207902524987)
            ·
              refine ⟨18336401982033311853787481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12224267988022207902524987 18336401982033311853787481)
              ·
                refine ⟨13752301486524983890340611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18336401982033311853787481 13752301486524983890340611)
                ·
                  refine ⟨20628452229787475835510917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13752301486524983890340611 20628452229787475835510917)
                  ·
                    refine ⟨3867834793085151719158297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20628452229787475835510917 3867834793085151719158297)
                    ·
                      refine ⟨2900876094813863789368723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867834793085151719158297 2900876094813863789368723)
                      ·
                        rfl

theorem cell23_5649436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_5649436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649436 prefixEnd_5649436 := by exact prefixLift 5649436
  have htrace : WordTrace (prefixWord ++ tailWord_5649436) baseStart_5649436 baseEnd_5649436 := by
    simpa [prefixWord, tailWord_5649436, baseEnd_5649436] using wordTrace_append hprefix tailTrace_5649436
  have hstable : (prefixWord ++ tailWord_5649436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649436).length < 2 ^ (prefixWord ++ tailWord_5649436).sum := by decide
  have hdescent : baseEnd_5649436 < baseStart_5649436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649440 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5649440 : Nat := 118140960795 + 5649440 * 2 ^ 59
def prefixEnd_5649440 : Nat := 4983230072969 + 3 ^ 40 * 5649440 * 2
def baseEnd_5649440 : Nat := 2900878148736481773718705

theorem tailTrace_5649440 : CollatzResearch.WordTrace tailWord_5649440 prefixEnd_5649440 2900878148736481773718705 := by
  unfold tailWord_5649440
  simp only [CollatzResearch.WordTrace]
  refine ⟨103026002326525601190836887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137368003102034134921115849 103026002326525601190836887)
  ·
    refine ⟨154539003489788401786255331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103026002326525601190836887 154539003489788401786255331)
    ·
      refine ⟨231808505234682602679382997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154539003489788401786255331 231808505234682602679382997)
      ·
        refine ⟨5433011841437873500298039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 231808505234682602679382997 5433011841437873500298039)
        ·
          refine ⟨8149517762156810250447059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433011841437873500298039 8149517762156810250447059)
          ·
            refine ⟨12224276643235215375670589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149517762156810250447059 12224276643235215375670589)
            ·
              refine ⟨4584103741213205765876471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12224276643235215375670589 4584103741213205765876471)
              ·
                refine ⟨6876155611819808648814707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4584103741213205765876471 6876155611819808648814707)
                ·
                  refine ⟨10314233417729712973222061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6876155611819808648814707 10314233417729712973222061)
                  ·
                    refine ⟨3867837531648642364958273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10314233417729712973222061 3867837531648642364958273)
                    ·
                      refine ⟨2900878148736481773718705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867837531648642364958273 2900878148736481773718705)
                      ·
                        rfl

theorem cell23_5649440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5649440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649440 prefixEnd_5649440 := by exact prefixLift 5649440
  have htrace : WordTrace (prefixWord ++ tailWord_5649440) baseStart_5649440 baseEnd_5649440 := by
    simpa [prefixWord, tailWord_5649440, baseEnd_5649440] using wordTrace_append hprefix tailTrace_5649440
  have hstable : (prefixWord ++ tailWord_5649440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649440).length < 2 ^ (prefixWord ++ tailWord_5649440).sum := by decide
  have hdescent : baseEnd_5649440 < baseStart_5649440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649452 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_5649452 : Nat := 118140960795 + 5649452 * 2 ^ 59
def prefixEnd_5649452 : Nat := 4983230072969 + 3 ^ 40 * 5649452 * 2
def baseEnd_5649452 : Nat := 2900884310504335726768649

theorem tailTrace_5649452 : CollatzResearch.WordTrace tailWord_5649452 prefixEnd_5649452 2900884310504335726768649 := by
  unfold tailWord_5649452
  simp only [CollatzResearch.WordTrace]
  refine ⟨103026221164503864215555305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137368294886005152287407073 103026221164503864215555305)
  ·
    refine ⟨77269665873377898161666479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103026221164503864215555305 77269665873377898161666479)
    ·
      refine ⟨115904498810066847242499719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77269665873377898161666479 115904498810066847242499719)
      ·
        refine ⟨173856748215100270863749579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115904498810066847242499719 173856748215100270863749579)
        ·
          refine ⟨260785122322650406295624369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173856748215100270863749579 260785122322650406295624369)
          ·
            refine ⟨195588841741987804721718277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260785122322650406295624369 195588841741987804721718277)
            ·
              refine ⟨36672907826622713385322177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195588841741987804721718277 36672907826622713385322177)
              ·
                refine ⟨27504680869967035038991633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36672907826622713385322177 27504680869967035038991633)
                ·
                  refine ⟨20628510652475276279243725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27504680869967035038991633 20628510652475276279243725)
                  ·
                    refine ⟨7735691494678228604716397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20628510652475276279243725 7735691494678228604716397)
                    ·
                      refine ⟨2900884310504335726768649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7735691494678228604716397 2900884310504335726768649)
                      ·
                        rfl

theorem cell23_5649452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_5649452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649452 prefixEnd_5649452 := by exact prefixLift 5649452
  have htrace : WordTrace (prefixWord ++ tailWord_5649452) baseStart_5649452 baseEnd_5649452 := by
    simpa [prefixWord, tailWord_5649452, baseEnd_5649452] using wordTrace_append hprefix tailTrace_5649452
  have hstable : (prefixWord ++ tailWord_5649452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649452).length < 2 ^ (prefixWord ++ tailWord_5649452).sum := by decide
  have hdescent : baseEnd_5649452 < baseStart_5649452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649469 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_5649469 : Nat := 118140960795 + 5649469 * 2 ^ 59
def prefixEnd_5649469 : Nat := 4983230072969 + 3 ^ 40 * 5649469 * 2
def baseEnd_5649469 : Nat := 2900893039675462160256071

theorem tailTrace_5649469 : CollatzResearch.WordTrace tailWord_5649469 prefixEnd_5649469 2900893039675462160256071 := by
  unfold tailWord_5649469
  simp only [CollatzResearch.WordTrace]
  refine ⟨206053062369946140334479461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137368708246630760222986307 206053062369946140334479461)
  ·
    refine ⟨38634949194364901312714899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206053062369946140334479461 38634949194364901312714899)
    ·
      refine ⟨57952423791547351969072349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38634949194364901312714899 57952423791547351969072349)
      ·
        refine ⟨21732158921830256988402131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57952423791547351969072349 21732158921830256988402131)
        ·
          refine ⟨32598238382745385482603197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21732158921830256988402131 32598238382745385482603197)
          ·
            refine ⟨12224339393529519555976199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32598238382745385482603197 12224339393529519555976199)
            ·
              refine ⟨18336509090294279333964299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12224339393529519555976199 18336509090294279333964299)
              ·
                refine ⟨27504763635441419000946449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18336509090294279333964299 27504763635441419000946449)
                ·
                  refine ⟨20628572726581064250709837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27504763635441419000946449 20628572726581064250709837)
                  ·
                    refine ⟨7735714772467899094016189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20628572726581064250709837 7735714772467899094016189)
                    ·
                      refine ⟨2900893039675462160256071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7735714772467899094016189 2900893039675462160256071)
                      ·
                        rfl

theorem cell23_5649469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_5649469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649469 prefixEnd_5649469 := by exact prefixLift 5649469
  have htrace : WordTrace (prefixWord ++ tailWord_5649469) baseStart_5649469 baseEnd_5649469 := by
    simpa [prefixWord, tailWord_5649469, baseEnd_5649469] using wordTrace_append hprefix tailTrace_5649469
  have hstable : (prefixWord ++ tailWord_5649469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649469).length < 2 ^ (prefixWord ++ tailWord_5649469).sum := by decide
  have hdescent : baseEnd_5649469 < baseStart_5649469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649509 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 4, 4, 2]
def baseStart_5649509 : Nat := 118140960795 + 5649509 * 2 ^ 59
def prefixEnd_5649509 : Nat := 4983230072969 + 3 ^ 40 * 5649509 * 2
def baseEnd_5649509 : Nat := 2900913578901642003755887

theorem tailTrace_5649509 : CollatzResearch.WordTrace tailWord_5649509 prefixEnd_5649509 2900913578901642003755887 := by
  unfold tailWord_5649509
  simp only [CollatzResearch.WordTrace]
  refine ⟨206054521289801227165935581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137369680859867484777290387 206054521289801227165935581)
  ·
    refine ⟨77270445483675460187225843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206054521289801227165935581 77270445483675460187225843)
    ·
      refine ⟨115905668225513190280838765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77270445483675460187225843 115905668225513190280838765)
      ·
        refine ⟨43464625584567446355314537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115905668225513190280838765 43464625584567446355314537)
        ·
          refine ⟨32598469188425584766485903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43464625584567446355314537 32598469188425584766485903)
          ·
            refine ⟨48897703782638377149728855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32598469188425584766485903 48897703782638377149728855)
            ·
              refine ⟨73346555673957565724593283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48897703782638377149728855 73346555673957565724593283)
              ·
                refine ⟨110019833510936348586889925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73346555673957565724593283 110019833510936348586889925)
                ·
                  refine ⟨20628718783300565360041861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110019833510936348586889925 20628718783300565360041861)
                  ·
                    refine ⟨3867884771868856005007849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20628718783300565360041861 3867884771868856005007849)
                    ·
                      refine ⟨2900913578901642003755887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867884771868856005007849 2900913578901642003755887)
                      ·
                        rfl

theorem cell23_5649509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_5649509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649509 prefixEnd_5649509 := by exact prefixLift 5649509
  have htrace : WordTrace (prefixWord ++ tailWord_5649509) baseStart_5649509 baseEnd_5649509 := by
    simpa [prefixWord, tailWord_5649509, baseEnd_5649509] using wordTrace_append hprefix tailTrace_5649509
  have hstable : (prefixWord ++ tailWord_5649509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649509).length < 2 ^ (prefixWord ++ tailWord_5649509).sum := by decide
  have hdescent : baseEnd_5649509 < baseStart_5649509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649519 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 3, 4]
def baseStart_5649519 : Nat := 118140960795 + 5649519 * 2 ^ 59
def prefixEnd_5649519 : Nat := 4983230072969 + 3 ^ 40 * 5649519 * 2
def baseEnd_5649519 : Nat := 966972904569395654876947

theorem tailTrace_5649519 : CollatzResearch.WordTrace tailWord_5649519 prefixEnd_5649519 966972904569395654876947 := by
  unfold tailWord_5649519
  simp only [CollatzResearch.WordTrace]
  refine ⟨206054886019764998873799611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137369924013176665915866407 206054886019764998873799611)
  ·
    refine ⟨309082329029647498310699417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206054886019764998873799611 309082329029647498310699417)
    ·
      refine ⟨231811746772235623733024563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309082329029647498310699417 231811746772235623733024563)
      ·
        refine ⟨347717620158353435599536845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231811746772235623733024563 347717620158353435599536845)
        ·
          refine ⟨130394107559382538349826317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347717620158353435599536845 130394107559382538349826317)
          ·
            refine ⟨48897790334768451881184869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130394107559382538349826317 48897790334768451881184869)
            ·
              refine ⟨9168335687769084727722163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48897790334768451881184869 9168335687769084727722163)
              ·
                refine ⟨13752503531653627091583245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9168335687769084727722163 13752503531653627091583245)
                ·
                  refine ⟨5157188824370110159343717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13752503531653627091583245 5157188824370110159343717)
                  ·
                    refine ⟨966972904569395654876947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157188824370110159343717 966972904569395654876947)
                    ·
                      rfl

theorem cell23_5649519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 4].length) (baseStart_5649519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649519 prefixEnd_5649519 := by exact prefixLift 5649519
  have htrace : WordTrace (prefixWord ++ tailWord_5649519) baseStart_5649519 baseEnd_5649519 := by
    simpa [prefixWord, tailWord_5649519, baseEnd_5649519] using wordTrace_append hprefix tailTrace_5649519
  have hstable : (prefixWord ++ tailWord_5649519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649519).length < 2 ^ (prefixWord ++ tailWord_5649519).sum := by decide
  have hdescent : baseEnd_5649519 < baseStart_5649519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649522 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5649522 : Nat := 118140960795 + 5649522 * 2 ^ 59
def prefixEnd_5649522 : Nat := 4983230072969 + 3 ^ 40 * 5649522 * 2
def baseEnd_5649522 : Nat := 2900920254150150452893327

theorem tailTrace_5649522 : CollatzResearch.WordTrace tailWord_5649522 prefixEnd_5649522 2900920254150150452893327 := by
  unfold tailWord_5649522
  simp only [CollatzResearch.WordTrace]
  refine ⟨51513748859688532596539705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137369996959169420257439213 51513748859688532596539705)
  ·
    refine ⟨38635311644766399447404779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51513748859688532596539705 38635311644766399447404779)
    ·
      refine ⟨57952967467149599171107169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38635311644766399447404779 57952967467149599171107169)
      ·
        refine ⟨43464725600362199378330377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57952967467149599171107169 43464725600362199378330377)
        ·
          refine ⟨32598544200271649533747783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43464725600362199378330377 32598544200271649533747783)
          ·
            refine ⟨48897816300407474300621675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32598544200271649533747783 48897816300407474300621675)
            ·
              refine ⟨73346724450611211450932513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48897816300407474300621675 73346724450611211450932513)
              ·
                refine ⟨55010043337958408588199385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73346724450611211450932513 55010043337958408588199385)
                ·
                  refine ⟨41257532503468806441149539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55010043337958408588199385 41257532503468806441149539)
                  ·
                    refine ⟨61886298755203209661724309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41257532503468806441149539 61886298755203209661724309)
                    ·
                      refine ⟨2900920254150150452893327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61886298755203209661724309 2900920254150150452893327)
                      ·
                        rfl

theorem cell23_5649522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5649522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649522 prefixEnd_5649522 := by exact prefixLift 5649522
  have htrace : WordTrace (prefixWord ++ tailWord_5649522) baseStart_5649522 baseEnd_5649522 := by
    simpa [prefixWord, tailWord_5649522, baseEnd_5649522] using wordTrace_append hprefix tailTrace_5649522
  have hstable : (prefixWord ++ tailWord_5649522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649522).length < 2 ^ (prefixWord ++ tailWord_5649522).sum := by decide
  have hdescent : baseEnd_5649522 < baseStart_5649522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649526 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_5649526 : Nat := 118140960795 + 5649526 * 2 ^ 59
def prefixEnd_5649526 : Nat := 4983230072969 + 3 ^ 40 * 5649526 * 2
def baseEnd_5649526 : Nat := 2900922308072768437243309

theorem tailTrace_5649526 : CollatzResearch.WordTrace tailWord_5649526 prefixEnd_5649526 2900922308072768437243309 := by
  unfold tailWord_5649526
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878446333171227441831527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137370094220493092712869621 12878446333171227441831527)
  ·
    refine ⟨19317669499756841162747291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12878446333171227441831527 19317669499756841162747291)
    ·
      refine ⟨28976504249635261744120937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19317669499756841162747291 28976504249635261744120937)
      ·
        refine ⟨21732378187226446308090703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28976504249635261744120937 21732378187226446308090703)
        ·
          refine ⟨32598567280839669462136055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21732378187226446308090703 32598567280839669462136055)
          ·
            refine ⟨48897850921259504193204083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32598567280839669462136055 48897850921259504193204083)
            ·
              refine ⟨73346776381889256289806125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48897850921259504193204083 73346776381889256289806125)
              ·
                refine ⟨27505041143208471108677297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73346776381889256289806125 27505041143208471108677297)
                ·
                  refine ⟨20628780857406353331507973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27505041143208471108677297 20628780857406353331507973)
                  ·
                    refine ⟨3867896410763691249657745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20628780857406353331507973 3867896410763691249657745)
                    ·
                      refine ⟨2900922308072768437243309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867896410763691249657745 2900922308072768437243309)
                      ·
                        rfl

theorem cell23_5649526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_5649526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649526 prefixEnd_5649526 := by exact prefixLift 5649526
  have htrace : WordTrace (prefixWord ++ tailWord_5649526) baseStart_5649526 baseEnd_5649526 := by
    simpa [prefixWord, tailWord_5649526, baseEnd_5649526] using wordTrace_append hprefix tailTrace_5649526
  have hstable : (prefixWord ++ tailWord_5649526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649526).length < 2 ^ (prefixWord ++ tailWord_5649526).sum := by decide
  have hdescent : baseEnd_5649526 < baseStart_5649526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649570 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_5649570 : Nat := 118140960795 + 5649570 * 2 ^ 59
def prefixEnd_5649570 : Nat := 4983230072969 + 3 ^ 40 * 5649570 * 2
def baseEnd_5649570 : Nat := 966981633740522088364369

theorem tailTrace_5649570 : CollatzResearch.WordTrace tailWord_5649570 prefixEnd_5649570 966981633740522088364369 := by
  unfold tailWord_5649570
  simp only [CollatzResearch.WordTrace]
  refine ⟨51514186535645058645976541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137371164095053489722604109 51514186535645058645976541)
  ·
    refine ⟨19317819950866896992241203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51514186535645058645976541 19317819950866896992241203)
    ·
      refine ⟨28976729926300345488361805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19317819950866896992241203 28976729926300345488361805)
      ·
        refine ⟨10866273722362629558135677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28976729926300345488361805 10866273722362629558135677)
        ·
          refine ⟨4074852645885986084300879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10866273722362629558135677 4074852645885986084300879)
          ·
            refine ⟨6112278968828979126451319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074852645885986084300879 6112278968828979126451319)
            ·
              refine ⟨9168418453243468689676979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112278968828979126451319 9168418453243468689676979)
              ·
                refine ⟨13752627679865203034515469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9168418453243468689676979 13752627679865203034515469)
                ·
                  refine ⟨5157235379949451137943301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13752627679865203034515469 5157235379949451137943301)
                  ·
                    refine ⟨966981633740522088364369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157235379949451137943301 966981633740522088364369)
                    ·
                      rfl

theorem cell23_5649570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_5649570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649570 prefixEnd_5649570 := by exact prefixLift 5649570
  have htrace : WordTrace (prefixWord ++ tailWord_5649570) baseStart_5649570 baseEnd_5649570 := by
    simpa [prefixWord, tailWord_5649570, baseEnd_5649570] using wordTrace_append hprefix tailTrace_5649570
  have hstable : (prefixWord ++ tailWord_5649570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649570).length < 2 ^ (prefixWord ++ tailWord_5649570).sum := by decide
  have hdescent : baseEnd_5649570 < baseStart_5649570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649596 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_5649596 : Nat := 118140960795 + 5649596 * 2 ^ 59
def prefixEnd_5649596 : Nat := 4983230072969 + 3 ^ 40 * 5649596 * 2
def baseEnd_5649596 : Nat := 966986083906194387789329

theorem tailTrace_5649596 : CollatzResearch.WordTrace tailWord_5649596 prefixEnd_5649596 966986083906194387789329 := by
  unfold tailWord_5649596
  simp only [CollatzResearch.WordTrace]
  refine ⟨103028847220243020512176321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137371796293657360682901761 103028847220243020512176321)
  ·
    refine ⟨77271635415182265384132241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103028847220243020512176321 77271635415182265384132241)
    ·
      refine ⟨57953726561386699038099181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77271635415182265384132241 57953726561386699038099181)
      ·
        refine ⟨21732647460520012139287193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57953726561386699038099181 21732647460520012139287193)
        ·
          refine ⟨16299485595390009104465395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21732647460520012139287193 16299485595390009104465395)
          ·
            refine ⟨24449228393085013656698093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16299485595390009104465395 24449228393085013656698093)
            ·
              refine ⟨9168460647406880121261785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24449228393085013656698093 9168460647406880121261785)
              ·
                refine ⟨6876345485555160090946339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9168460647406880121261785 6876345485555160090946339)
                ·
                  refine ⟨10314518228332740136419509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6876345485555160090946339 10314518228332740136419509)
                  ·
                    refine ⟨966986083906194387789329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10314518228332740136419509 966986083906194387789329)
                    ·
                      rfl

theorem cell23_5649596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_5649596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649596 prefixEnd_5649596 := by exact prefixLift 5649596
  have htrace : WordTrace (prefixWord ++ tailWord_5649596) baseStart_5649596 baseEnd_5649596 := by
    simpa [prefixWord, tailWord_5649596, baseEnd_5649596] using wordTrace_append hprefix tailTrace_5649596
  have hstable : (prefixWord ++ tailWord_5649596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649596).length < 2 ^ (prefixWord ++ tailWord_5649596).sum := by decide
  have hdescent : baseEnd_5649596 < baseStart_5649596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649599 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 2, 6, 2]
def baseStart_5649599 : Nat := 118140960795 + 5649599 * 2 ^ 59
def prefixEnd_5649599 : Nat := 4983230072969 + 3 ^ 40 * 5649599 * 2
def baseEnd_5649599 : Nat := 2900959792160546651630473

theorem tailTrace_5649599 : CollatzResearch.WordTrace tailWord_5649599 prefixEnd_5649599 2900959792160546651630473 := by
  unfold tailWord_5649599
  simp only [CollatzResearch.WordTrace]
  refine ⟨206057803859475172536711851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137371869239650115024474567 206057803859475172536711851)
  ·
    refine ⟨309086705789212758805067777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206057803859475172536711851 309086705789212758805067777)
    ·
      refine ⟨231815029341909569103800833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309086705789212758805067777 231815029341909569103800833)
      ·
        refine ⟨173861272006432176827850625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231815029341909569103800833 173861272006432176827850625)
        ·
          refine ⟨130395954004824132620887969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173861272006432176827850625 130395954004824132620887969)
          ·
            refine ⟨97796965503618099465665977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130395954004824132620887969 97796965503618099465665977)
            ·
              refine ⟨73347724127713574599249483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97796965503618099465665977 73347724127713574599249483)
              ·
                refine ⟨110021586191570361898874225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73347724127713574599249483 110021586191570361898874225)
                ·
                  refine ⟨82516189643677771424155669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110021586191570361898874225 82516189643677771424155669)
                  ·
                    refine ⟨3867946389547395535507297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82516189643677771424155669 3867946389547395535507297)
                    ·
                      refine ⟨2900959792160546651630473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867946389547395535507297 2900959792160546651630473)
                      ·
                        rfl

theorem cell23_5649599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_5649599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649599 prefixEnd_5649599 := by exact prefixLift 5649599
  have htrace : WordTrace (prefixWord ++ tailWord_5649599) baseStart_5649599 baseEnd_5649599 := by
    simpa [prefixWord, tailWord_5649599, baseEnd_5649599] using wordTrace_append hprefix tailTrace_5649599
  have hstable : (prefixWord ++ tailWord_5649599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649599).length < 2 ^ (prefixWord ++ tailWord_5649599).sum := by decide
  have hdescent : baseEnd_5649599 < baseStart_5649599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649650 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_5649650 : Nat := 118140960795 + 5649650 * 2 ^ 59
def prefixEnd_5649650 : Nat := 4983230072969 + 3 ^ 40 * 5649650 * 2
def baseEnd_5649650 : Nat := 2900985979673925952092739

theorem tailTrace_5649650 : CollatzResearch.WordTrace tailWord_5649650 prefixEnd_5649650 2900985979673925952092739 := by
  unfold tailWord_5649650
  simp only [CollatzResearch.WordTrace]
  refine ⟨51514915995572602061704601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137373109321526938831212269 51514915995572602061704601)
  ·
    refine ⟨38636186996679451546278451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51514915995572602061704601 38636186996679451546278451)
    ·
      refine ⟨57954280495019177319417677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38636186996679451546278451 57954280495019177319417677)
      ·
        refine ⟨21732855185632191494781629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57954280495019177319417677 21732855185632191494781629)
        ·
          refine ⟨8149820694612071810543111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21732855185632191494781629 8149820694612071810543111)
          ·
            refine ⟨12224731041918107715814667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149820694612071810543111 12224731041918107715814667)
            ·
              refine ⟨18337096562877161573722001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12224731041918107715814667 18337096562877161573722001)
              ·
                refine ⟨13752822422157871180291501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18337096562877161573722001 13752822422157871180291501)
                ·
                  refine ⟨5157308408309201692609313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13752822422157871180291501 5157308408309201692609313)
                  ·
                    refine ⟨3867981306231901269456985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5157308408309201692609313 3867981306231901269456985)
                    ·
                      refine ⟨2900985979673925952092739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3867981306231901269456985 2900985979673925952092739)
                      ·
                        rfl

theorem cell23_5649650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_5649650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649650 prefixEnd_5649650 := by exact prefixLift 5649650
  have htrace : WordTrace (prefixWord ++ tailWord_5649650) baseStart_5649650 baseEnd_5649650 := by
    simpa [prefixWord, tailWord_5649650, baseEnd_5649650] using wordTrace_append hprefix tailTrace_5649650
  have hstable : (prefixWord ++ tailWord_5649650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649650).length < 2 ^ (prefixWord ++ tailWord_5649650).sum := by decide
  have hdescent : baseEnd_5649650 < baseStart_5649650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649699 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 2, 6]
def baseStart_5649699 : Nat := 118140960795 + 5649699 * 2 ^ 59
def prefixEnd_5649699 : Nat := 4983230072969 + 3 ^ 40 * 5649699 * 2
def baseEnd_5649699 : Nat := 967003713408665420126671

theorem tailTrace_5649699 : CollatzResearch.WordTrace tailWord_5649699 prefixEnd_5649699 967003713408665420126671 := by
  unfold tailWord_5649699
  simp only [CollatzResearch.WordTrace]
  refine ⟨206061451159112889615352151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137374300772741926410234767 206061451159112889615352151)
  ·
    refine ⟨309092176738669334423028227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206061451159112889615352151 309092176738669334423028227)
    ·
      refine ⟨463638265108004001634542341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309092176738669334423028227 463638265108004001634542341)
      ·
        refine ⟨86932174707750750306476689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 463638265108004001634542341 86932174707750750306476689)
        ·
          refine ⟨65199131030813062729857517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86932174707750750306476689 65199131030813062729857517)
          ·
            refine ⟨24449674136554898523696569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65199131030813062729857517 24449674136554898523696569)
            ·
              refine ⟨18337255602416173892772427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24449674136554898523696569 18337255602416173892772427)
              ·
                refine ⟨27505883403624260839158641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18337255602416173892772427 27505883403624260839158641)
                ·
                  refine ⟨20629412552718195629368981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27505883403624260839158641 20629412552718195629368981)
                  ·
                    refine ⟨967003713408665420126671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20629412552718195629368981 967003713408665420126671)
                    ·
                      rfl

theorem cell23_5649699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 6].length) (baseStart_5649699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649699 prefixEnd_5649699 := by exact prefixLift 5649699
  have htrace : WordTrace (prefixWord ++ tailWord_5649699) baseStart_5649699 baseEnd_5649699 := by
    simpa [prefixWord, tailWord_5649699, baseEnd_5649699] using wordTrace_append hprefix tailTrace_5649699
  have hstable : (prefixWord ++ tailWord_5649699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649699).length < 2 ^ (prefixWord ++ tailWord_5649699).sum := by decide
  have hdescent : baseEnd_5649699 < baseStart_5649699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649700 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_5649700 : Nat := 118140960795 + 5649700 * 2 ^ 59
def prefixEnd_5649700 : Nat := 4983230072969 + 3 ^ 40 * 5649700 * 2
def baseEnd_5649700 : Nat := 2901011653706650756467509

theorem tailTrace_5649700 : CollatzResearch.WordTrace tailWord_5649700 prefixEnd_5649700 2901011653706650756467509 := by
  unfold tailWord_5649700
  simp only [CollatzResearch.WordTrace]
  refine ⟨103030743816054633393069277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137374325088072844524092369 103030743816054633393069277)
  ·
    refine ⟨38636528931020487522400979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103030743816054633393069277 38636528931020487522400979)
    ·
      refine ⟨57954793396530731283601469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38636528931020487522400979 57954793396530731283601469)
      ·
        refine ⟨21733047523699024231350551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57954793396530731283601469 21733047523699024231350551)
        ·
          refine ⟨32599571285548536347025827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21733047523699024231350551 32599571285548536347025827)
          ·
            refine ⟨48899356928322804520538741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32599571285548536347025827 48899356928322804520538741)
            ·
              refine ⟨4584314712030262923800507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48899356928322804520538741 4584314712030262923800507)
              ·
                refine ⟨6876472068045394385700761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4584314712030262923800507 6876472068045394385700761)
                ·
                  refine ⟨5157354051034045789275571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6876472068045394385700761 5157354051034045789275571)
                  ·
                    refine ⟨7736031076551068683913357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5157354051034045789275571 7736031076551068683913357)
                    ·
                      refine ⟨2901011653706650756467509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7736031076551068683913357 2901011653706650756467509)
                      ·
                        rfl

theorem cell23_5649700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_5649700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649700 prefixEnd_5649700 := by exact prefixLift 5649700
  have htrace : WordTrace (prefixWord ++ tailWord_5649700) baseStart_5649700 baseEnd_5649700 := by
    simpa [prefixWord, tailWord_5649700, baseEnd_5649700] using wordTrace_append hprefix tailTrace_5649700
  have hstable : (prefixWord ++ tailWord_5649700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649700).length < 2 ^ (prefixWord ++ tailWord_5649700).sum := by decide
  have hdescent : baseEnd_5649700 < baseStart_5649700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649718 : List Nat := [5, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5649718 : Nat := 118140960795 + 5649718 * 2 ^ 59
def prefixEnd_5649718 : Nat := 4983230072969 + 3 ^ 40 * 5649718 * 2
def baseEnd_5649718 : Nat := 2901020896358431686042427

theorem tailTrace_5649718 : CollatzResearch.WordTrace tailWord_5649718 prefixEnd_5649718 2901020896358431686042427 := by
  unfold tailWord_5649718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878884009127753491268363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137374762764029370573529205 12878884009127753491268363)
  ·
    refine ⟨19318326013691630236902545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12878884009127753491268363 19318326013691630236902545)
    ·
      refine ⟨14488744510268722677676909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19318326013691630236902545 14488744510268722677676909)
      ·
        refine ⟨5433279191350771004128841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14488744510268722677676909 5433279191350771004128841)
        ·
          refine ⟨4074959393513078253096631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5433279191350771004128841 4074959393513078253096631)
          ·
            refine ⟨6112439090269617379644947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074959393513078253096631 6112439090269617379644947)
            ·
              refine ⟨9168658635404426069467421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112439090269617379644947 9168658635404426069467421)
              ·
                refine ⟨3438246988276659776050283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9168658635404426069467421 3438246988276659776050283)
                ·
                  refine ⟨5157370482414989664075425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438246988276659776050283 5157370482414989664075425)
                  ·
                    refine ⟨3868027861811242248056569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5157370482414989664075425 3868027861811242248056569)
                    ·
                      refine ⟨2901020896358431686042427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868027861811242248056569 2901020896358431686042427)
                      ·
                        rfl

theorem cell23_5649718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5649718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649718 prefixEnd_5649718 := by exact prefixLift 5649718
  have htrace : WordTrace (prefixWord ++ tailWord_5649718) baseStart_5649718 baseEnd_5649718 := by
    simpa [prefixWord, tailWord_5649718, baseEnd_5649718] using wordTrace_append hprefix tailTrace_5649718
  have hstable : (prefixWord ++ tailWord_5649718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649718).length < 2 ^ (prefixWord ++ tailWord_5649718).sum := by decide
  have hdescent : baseEnd_5649718 < baseStart_5649718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649726 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_5649726 : Nat := 118140960795 + 5649726 * 2 ^ 59
def prefixEnd_5649726 : Nat := 4983230072969 + 3 ^ 40 * 5649726 * 2
def baseEnd_5649726 : Nat := 2901025004203667654742389

theorem tailTrace_5649726 : CollatzResearch.WordTrace tailWord_5649726 prefixEnd_5649726 2901025004203667654742389 := by
  unfold tailWord_5649726
  simp only [CollatzResearch.WordTrace]
  refine ⟨25757804491251884153323129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137374957286676715484390021 25757804491251884153323129)
  ·
    refine ⟨19318353368438913114992347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25757804491251884153323129 19318353368438913114992347)
    ·
      refine ⟨28977530052658369672488521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19318353368438913114992347 28977530052658369672488521)
      ·
        refine ⟨21733147539493777254366391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28977530052658369672488521 21733147539493777254366391)
        ·
          refine ⟨32599721309240665881549587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21733147539493777254366391 32599721309240665881549587)
          ·
            refine ⟨48899581963860998822324381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32599721309240665881549587 48899581963860998822324381)
            ·
              refine ⟨18337343236447874558371643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48899581963860998822324381 18337343236447874558371643)
              ·
                refine ⟨27506014854671811837557465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18337343236447874558371643 27506014854671811837557465)
                ·
                  refine ⟨20629511141003858878168099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27506014854671811837557465 20629511141003858878168099)
                  ·
                    refine ⟨30944266711505788317252149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20629511141003858878168099 30944266711505788317252149)
                    ·
                      refine ⟨2901025004203667654742389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30944266711505788317252149 2901025004203667654742389)
                      ·
                        rfl

theorem cell23_5649726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_5649726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649726 prefixEnd_5649726 := by exact prefixLift 5649726
  have htrace : WordTrace (prefixWord ++ tailWord_5649726) baseStart_5649726 baseEnd_5649726 := by
    simpa [prefixWord, tailWord_5649726, baseEnd_5649726] using wordTrace_append hprefix tailTrace_5649726
  have hstable : (prefixWord ++ tailWord_5649726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649726).length < 2 ^ (prefixWord ++ tailWord_5649726).sum := by decide
  have hdescent : baseEnd_5649726 < baseStart_5649726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649759 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 6, 5]
def baseStart_5649759 : Nat := 118140960795 + 5649759 * 2 ^ 59
def prefixEnd_5649759 : Nat := 4983230072969 + 3 ^ 40 * 5649759 * 2
def baseEnd_5649759 : Nat := 967013983021755341876579

theorem tailTrace_5649759 : CollatzResearch.WordTrace tailWord_5649759 prefixEnd_5649759 967013983021755341876579 := by
  unfold tailWord_5649759
  simp only [CollatzResearch.WordTrace]
  refine ⟨206063639538895519862536331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137375759692597013241690887 206063639538895519862536331)
  ·
    refine ⟨309095459308343279793804497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206063639538895519862536331 309095459308343279793804497)
    ·
      refine ⟨231821594481257459845353373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309095459308343279793804497 231821594481257459845353373)
      ·
        refine ⟨86933097930471547442007515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231821594481257459845353373 86933097930471547442007515)
        ·
          refine ⟨130399646895707321163011273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86933097930471547442007515 130399646895707321163011273)
          ·
            refine ⟨97799735171780490872258455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130399646895707321163011273 97799735171780490872258455)
            ·
              refine ⟨146699602757670736308387683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97799735171780490872258455 146699602757670736308387683)
              ·
                refine ⟨220049404136506104462581525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146699602757670736308387683 220049404136506104462581525)
                ·
                  refine ⟨10314815818898723646683509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220049404136506104462581525 10314815818898723646683509)
                  ·
                    refine ⟨967013983021755341876579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10314815818898723646683509 967013983021755341876579)
                    ·
                      rfl

theorem cell23_5649759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_5649759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649759 prefixEnd_5649759 := by exact prefixLift 5649759
  have htrace : WordTrace (prefixWord ++ tailWord_5649759) baseStart_5649759 baseEnd_5649759 := by
    simpa [prefixWord, tailWord_5649759, baseEnd_5649759] using wordTrace_append hprefix tailTrace_5649759
  have hstable : (prefixWord ++ tailWord_5649759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649759).length < 2 ^ (prefixWord ++ tailWord_5649759).sum := by decide
  have hdescent : baseEnd_5649759 < baseStart_5649759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649776 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 2, 5]
def baseStart_5649776 : Nat := 118140960795 + 5649776 * 2 ^ 59
def prefixEnd_5649776 : Nat := 4983230072969 + 3 ^ 40 * 5649776 * 2
def baseEnd_5649776 : Nat := 967016892745464153039053

theorem tailTrace_5649776 : CollatzResearch.WordTrace tailWord_5649776 prefixEnd_5649776 967016892745464153039053 := by
  unfold tailWord_5649776
  simp only [CollatzResearch.WordTrace]
  refine ⟨103032129789916965882952591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137376173053222621177270121 103032129789916965882952591)
  ·
    refine ⟨154548194684875448824428887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103032129789916965882952591 154548194684875448824428887)
    ·
      refine ⟨231822292027313173236643331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154548194684875448824428887 231822292027313173236643331)
      ·
        refine ⟨347733438040969759854964997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231822292027313173236643331 347733438040969759854964997)
        ·
          refine ⟨65200019632681829972805937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347733438040969759854964997 65200019632681829972805937)
          ·
            refine ⟨48900014724511372479604453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65200019632681829972805937 48900014724511372479604453)
            ·
              refine ⟨9168752760845882339925835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48900014724511372479604453 9168752760845882339925835)
              ·
                refine ⟨13753129141268823509888753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9168752760845882339925835 13753129141268823509888753)
                ·
                  refine ⟨10314846855951617632416565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13753129141268823509888753 10314846855951617632416565)
                  ·
                    refine ⟨967016892745464153039053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10314846855951617632416565 967016892745464153039053)
                    ·
                      rfl

theorem cell23_5649776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_5649776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649776 prefixEnd_5649776 := by exact prefixLift 5649776
  have htrace : WordTrace (prefixWord ++ tailWord_5649776) baseStart_5649776 baseEnd_5649776 := by
    simpa [prefixWord, tailWord_5649776, baseEnd_5649776] using wordTrace_append hprefix tailTrace_5649776
  have hstable : (prefixWord ++ tailWord_5649776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649776).length < 2 ^ (prefixWord ++ tailWord_5649776).sum := by decide
  have hdescent : baseEnd_5649776 < baseStart_5649776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649809 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_5649809 : Nat := 118140960795 + 5649809 * 2 ^ 59
def prefixEnd_5649809 : Nat := 4983230072969 + 3 ^ 40 * 5649809 * 2
def baseEnd_5649809 : Nat := 2901067623097990830004507

theorem tailTrace_5649809 : CollatzResearch.WordTrace tailWord_5649809 prefixEnd_5649809 2901067623097990830004507 := by
  unfold tailWord_5649809
  simp only [CollatzResearch.WordTrace]
  refine ⟨206065463188714378401856481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137376975459142918934570987 206065463188714378401856481)
  ·
    refine ⟨154549097391535783801392361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206065463188714378401856481 154549097391535783801392361)
    ·
      refine ⟨115911823043651837851044271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154549097391535783801392361 115911823043651837851044271)
      ·
        refine ⟨173867734565477756776566407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115911823043651837851044271 173867734565477756776566407)
        ·
          refine ⟨260801601848216635164849611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173867734565477756776566407 260801601848216635164849611)
          ·
            refine ⟨391202402772324952747274417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260801601848216635164849611 391202402772324952747274417)
            ·
              refine ⟨293401802079243714560455813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391202402772324952747274417 293401802079243714560455813)
              ·
                refine ⟨55012837889858196480085465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293401802079243714560455813 55012837889858196480085465)
                ·
                  refine ⟨41259628417393647360064099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55012837889858196480085465 41259628417393647360064099)
                  ·
                    refine ⟨61889442626090471040096149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41259628417393647360064099 61889442626090471040096149)
                    ·
                      refine ⟨2901067623097990830004507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61889442626090471040096149 2901067623097990830004507)
                      ·
                        rfl

theorem cell23_5649809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_5649809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649809 prefixEnd_5649809 := by exact prefixLift 5649809
  have htrace : WordTrace (prefixWord ++ tailWord_5649809) baseStart_5649809 baseEnd_5649809 := by
    simpa [prefixWord, tailWord_5649809, baseEnd_5649809] using wordTrace_append hprefix tailTrace_5649809
  have hstable : (prefixWord ++ tailWord_5649809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649809).length < 2 ^ (prefixWord ++ tailWord_5649809).sum := by decide
  have hdescent : baseEnd_5649809 < baseStart_5649809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649823 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 3, 4]
def baseStart_5649823 : Nat := 118140960795 + 5649823 * 2 ^ 59
def prefixEnd_5649823 : Nat := 4983230072969 + 3 ^ 40 * 5649823 * 2
def baseEnd_5649823 : Nat := 967024937275717925076481

theorem tailTrace_5649823 : CollatzResearch.WordTrace tailWord_5649823 prefixEnd_5649823 967024937275717925076481 := by
  unfold tailWord_5649823
  simp only [CollatzResearch.WordTrace]
  refine ⟨206065973810663658792866123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137377315873775772528577415 206065973810663658792866123)
  ·
    refine ⟨309098960715995488189299185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206065973810663658792866123 309098960715995488189299185)
    ·
      refine ⟨231824220536996616141974389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309098960715995488189299185 231824220536996616141974389)
      ·
        refine ⟨21733520675343432763310099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231824220536996616141974389 21733520675343432763310099)
        ·
          refine ⟨32600281013015149144965149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21733520675343432763310099 32600281013015149144965149)
          ·
            refine ⟨12225105379880680929361931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32600281013015149144965149 12225105379880680929361931)
            ·
              refine ⟨18337658069821021394042897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12225105379880680929361931 18337658069821021394042897)
              ·
                refine ⟨13753243552365766045532173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18337658069821021394042897 13753243552365766045532173)
                ·
                  refine ⟨5157466332137162267074565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13753243552365766045532173 5157466332137162267074565)
                  ·
                    refine ⟨967024937275717925076481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157466332137162267074565 967024937275717925076481)
                    ·
                      rfl

theorem cell23_5649823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 4].length) (baseStart_5649823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649823 prefixEnd_5649823 := by exact prefixLift 5649823
  have htrace : WordTrace (prefixWord ++ tailWord_5649823) baseStart_5649823 baseEnd_5649823 := by
    simpa [prefixWord, tailWord_5649823, baseEnd_5649823] using wordTrace_append hprefix tailTrace_5649823
  have hstable : (prefixWord ++ tailWord_5649823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649823).length < 2 ^ (prefixWord ++ tailWord_5649823).sum := by decide
  have hdescent : baseEnd_5649823 < baseStart_5649823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649839 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 6]
def baseStart_5649839 : Nat := 118140960795 + 5649839 * 2 ^ 59
def prefixEnd_5649839 : Nat := 4983230072969 + 3 ^ 40 * 5649839 * 2
def baseEnd_5649839 : Nat := 2901083027517625712629369

theorem tailTrace_5649839 : CollatzResearch.WordTrace tailWord_5649839 prefixEnd_5649839 2901083027517625712629369 := by
  unfold tailWord_5649839
  simp only [CollatzResearch.WordTrace]
  refine ⟨206066557378605693525448571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137377704919070462350299047 206066557378605693525448571)
  ·
    refine ⟨309099836067908540288172857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206066557378605693525448571 309099836067908540288172857)
    ·
      refine ⟨231824877050931405216129643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309099836067908540288172857 231824877050931405216129643)
      ·
        refine ⟨347737315576397107824194465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231824877050931405216129643 347737315576397107824194465)
        ·
          refine ⟨260802986682297830868145849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347737315576397107824194465 260802986682297830868145849)
          ·
            refine ⟨195602240011723373151109387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260802986682297830868145849 195602240011723373151109387)
            ·
              refine ⟨293403360017585059726664081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195602240011723373151109387 293403360017585059726664081)
              ·
                refine ⟨220052520013188794794998061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293403360017585059726664081 220052520013188794794998061)
                ·
                  refine ⟨82519695004945798048124273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220052520013188794794998061 82519695004945798048124273)
                  ·
                    refine ⟨61889771253709348536093205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82519695004945798048124273 61889771253709348536093205)
                    ·
                      refine ⟨2901083027517625712629369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61889771253709348536093205 2901083027517625712629369)
                      ·
                        rfl

theorem cell23_5649839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_5649839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649839 prefixEnd_5649839 := by exact prefixLift 5649839
  have htrace : WordTrace (prefixWord ++ tailWord_5649839) baseStart_5649839 baseEnd_5649839 := by
    simpa [prefixWord, tailWord_5649839, baseEnd_5649839] using wordTrace_append hprefix tailTrace_5649839
  have hstable : (prefixWord ++ tailWord_5649839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649839).length < 2 ^ (prefixWord ++ tailWord_5649839).sum := by decide
  have hdescent : baseEnd_5649839 < baseStart_5649839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649896 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 3, 6]
def baseStart_5649896 : Nat := 118140960795 + 5649896 * 2 ^ 59
def prefixEnd_5649896 : Nat := 4983230072969 + 3 ^ 40 * 5649896 * 2
def baseEnd_5649896 : Nat := 967037431971643996538869

theorem tailTrace_5649896 : CollatzResearch.WordTrace tailWord_5649896 prefixEnd_5649896 967037431971643996538869 := by
  unfold tailWord_5649896
  simp only [CollatzResearch.WordTrace]
  refine ⟨103034318169699596130136771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137379090892932794840182361 103034318169699596130136771)
  ·
    refine ⟨154551477254549394195205157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103034318169699596130136771 154551477254549394195205157)
    ·
      refine ⟨28978401985228011411600967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154551477254549394195205157 28978401985228011411600967)
      ·
        refine ⟨43467602977842017117401451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28978401985228011411600967 43467602977842017117401451)
        ·
          refine ⟨65201404466763025676102177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43467602977842017117401451 65201404466763025676102177)
          ·
            refine ⟨48901053350072269257076633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65201404466763025676102177 48901053350072269257076633)
            ·
              refine ⟨36675790012554201942807475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48901053350072269257076633 36675790012554201942807475)
              ·
                refine ⟨55013685018831302914211213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36675790012554201942807475 55013685018831302914211213)
                ·
                  refine ⟨20630131882061738592829205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55013685018831302914211213 20630131882061738592829205)
                  ·
                    refine ⟨967037431971643996538869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20630131882061738592829205 967037431971643996538869)
                    ·
                      rfl

theorem cell23_5649896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_5649896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649896 prefixEnd_5649896 := by exact prefixLift 5649896
  have htrace : WordTrace (prefixWord ++ tailWord_5649896) baseStart_5649896 baseEnd_5649896 := by
    simpa [prefixWord, tailWord_5649896, baseEnd_5649896] using wordTrace_append hprefix tailTrace_5649896
  have hstable : (prefixWord ++ tailWord_5649896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649896).length < 2 ^ (prefixWord ++ tailWord_5649896).sum := by decide
  have hdescent : baseEnd_5649896 < baseStart_5649896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649903 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 4]
def baseStart_5649903 : Nat := 118140960795 + 5649903 * 2 ^ 59
def prefixEnd_5649903 : Nat := 4983230072969 + 3 ^ 40 * 5649903 * 2
def baseEnd_5649903 : Nat := 2901115890279513462229075

theorem tailTrace_5649903 : CollatzResearch.WordTrace tailWord_5649903 prefixEnd_5649903 2901115890279513462229075 := by
  unfold tailWord_5649903
  simp only [CollatzResearch.WordTrace]
  refine ⟨206068891650373832455778363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137379261100249221637185575 206068891650373832455778363)
  ·
    refine ⟨309103337475560748683667545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206068891650373832455778363 309103337475560748683667545)
    ·
      refine ⟨231827503106670561512750659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309103337475560748683667545 231827503106670561512750659)
      ·
        refine ⟨347741254660005842269125989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231827503106670561512750659 347741254660005842269125989)
        ·
          refine ⟨65201485248751095425461123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347741254660005842269125989 65201485248751095425461123)
          ·
            refine ⟨97802227873126643138191685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65201485248751095425461123 97802227873126643138191685)
            ·
              refine ⟨18337917726211245588410941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97802227873126643138191685 18337917726211245588410941)
              ·
                refine ⟨6876719147329217095654103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18337917726211245588410941 6876719147329217095654103)
                ·
                  refine ⟨10315078720993825643481155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6876719147329217095654103 10315078720993825643481155)
                  ·
                    refine ⟨15472618081490738465221733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10315078720993825643481155 15472618081490738465221733)
                    ·
                      refine ⟨2901115890279513462229075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15472618081490738465221733 2901115890279513462229075)
                      ·
                        rfl

theorem cell23_5649903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 4].length) (baseStart_5649903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649903 prefixEnd_5649903 := by exact prefixLift 5649903
  have htrace : WordTrace (prefixWord ++ tailWord_5649903) baseStart_5649903 baseEnd_5649903 := by
    simpa [prefixWord, tailWord_5649903, baseEnd_5649903] using wordTrace_append hprefix tailTrace_5649903
  have hstable : (prefixWord ++ tailWord_5649903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649903).length < 2 ^ (prefixWord ++ tailWord_5649903).sum := by decide
  have hdescent : baseEnd_5649903 < baseStart_5649903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649913 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 2, 4]
def baseStart_5649913 : Nat := 118140960795 + 5649913 * 2 ^ 59
def prefixEnd_5649913 : Nat := 4983230072969 + 3 ^ 40 * 5649913 * 2
def baseEnd_5649913 : Nat := 967040341695352807701343

theorem tailTrace_5649913 : CollatzResearch.WordTrace tailWord_5649913 prefixEnd_5649913 967040341695352807701343 := by
  unfold tailWord_5649913
  simp only [CollatzResearch.WordTrace]
  refine ⟨206069256380337604163642393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137379504253558402775761595 206069256380337604163642393)
  ·
    refine ⟨154551942285253203122731795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206069256380337604163642393 154551942285253203122731795)
    ·
      refine ⟨231827913427879804684097693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154551942285253203122731795 231827913427879804684097693)
      ·
        refine ⟨86935467535454926756536635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231827913427879804684097693 86935467535454926756536635)
        ·
          refine ⟨130403201303182390134804953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86935467535454926756536635 130403201303182390134804953)
          ·
            refine ⟨97802400977386792601103715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130403201303182390134804953 97802400977386792601103715)
            ·
              refine ⟨146703601466080188901655573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97802400977386792601103715 146703601466080188901655573)
              ·
                refine ⟨6876731318722508854765105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146703601466080188901655573 6876731318722508854765105)
                ·
                  refine ⟨5157548489041881641073829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6876731318722508854765105 5157548489041881641073829)
                  ·
                    refine ⟨967040341695352807701343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157548489041881641073829 967040341695352807701343)
                    ·
                      rfl

theorem cell23_5649913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 4].length) (baseStart_5649913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649913 prefixEnd_5649913 := by exact prefixLift 5649913
  have htrace : WordTrace (prefixWord ++ tailWord_5649913) baseStart_5649913 baseEnd_5649913 := by
    simpa [prefixWord, tailWord_5649913, baseEnd_5649913] using wordTrace_append hprefix tailTrace_5649913
  have hstable : (prefixWord ++ tailWord_5649913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649913).length < 2 ^ (prefixWord ++ tailWord_5649913).sum := by decide
  have hdescent : baseEnd_5649913 < baseStart_5649913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649916 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_5649916 : Nat := 118140960795 + 5649916 * 2 ^ 59
def prefixEnd_5649916 : Nat := 4983230072969 + 3 ^ 40 * 5649916 * 2
def baseEnd_5649916 : Nat := 2901122565528021911366515

theorem tailTrace_5649916 : CollatzResearch.WordTrace tailWord_5649916 prefixEnd_5649916 2901122565528021911366515 := by
  unfold tailWord_5649916
  simp only [CollatzResearch.WordTrace]
  refine ⟨103034682899663367838000801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137379577199551157117334401 103034682899663367838000801)
  ·
    refine ⟨77276012174747525878500601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103034682899663367838000801 77276012174747525878500601)
    ·
      refine ⟨57957009131060644408875451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77276012174747525878500601 57957009131060644408875451)
      ·
        refine ⟨86935513696590966613313177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57957009131060644408875451 86935513696590966613313177)
        ·
          refine ⟨65201635272443224959984883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86935513696590966613313177 65201635272443224959984883)
          ·
            refine ⟨97802452908664837439977325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65201635272443224959984883 97802452908664837439977325)
            ·
              refine ⟨36675919840749314039991497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97802452908664837439977325 36675919840749314039991497)
              ·
                refine ⟨27506939880561985529993623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36675919840749314039991497 27506939880561985529993623)
                ·
                  refine ⟨41260409820842978294990435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27506939880561985529993623 41260409820842978294990435)
                  ·
                    refine ⟨61890614731264467442485653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41260409820842978294990435 61890614731264467442485653)
                    ·
                      refine ⟨2901122565528021911366515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61890614731264467442485653 2901122565528021911366515)
                      ·
                        rfl

theorem cell23_5649916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_5649916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649916 prefixEnd_5649916 := by exact prefixLift 5649916
  have htrace : WordTrace (prefixWord ++ tailWord_5649916) baseStart_5649916 baseEnd_5649916 := by
    simpa [prefixWord, tailWord_5649916, baseEnd_5649916] using wordTrace_append hprefix tailTrace_5649916
  have hstable : (prefixWord ++ tailWord_5649916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649916).length < 2 ^ (prefixWord ++ tailWord_5649916).sum := by decide
  have hdescent : baseEnd_5649916 < baseStart_5649916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649930 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_5649930 : Nat := 118140960795 + 5649930 * 2 ^ 59
def prefixEnd_5649930 : Nat := 4983230072969 + 3 ^ 40 * 5649930 * 2
def baseEnd_5649930 : Nat := 967043251419061618863817

theorem tailTrace_5649930 : CollatzResearch.WordTrace tailWord_5649930 prefixEnd_5649930 967043251419061618863817 := by
  unfold tailWord_5649930
  simp only [CollatzResearch.WordTrace]
  refine ⟨51517469105319004016752811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137379917614184010711340829 51517469105319004016752811)
  ·
    refine ⟨77276203657978506025129217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51517469105319004016752811 77276203657978506025129217)
    ·
      refine ⟨57957152743483879518846913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77276203657978506025129217 57957152743483879518846913)
      ·
        refine ⟨43467864557612909639135185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57957152743483879518846913 43467864557612909639135185)
        ·
          refine ⟨32600898418209682229351389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43467864557612909639135185 32600898418209682229351389)
          ·
            refine ⟨12225336906828630836006771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32600898418209682229351389 12225336906828630836006771)
            ·
              refine ⟨18338005360242946254010157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12225336906828630836006771 18338005360242946254010157)
              ·
                refine ⟨6876752010091104845253809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18338005360242946254010157 6876752010091104845253809)
                ·
                  refine ⟨5157564007568328633940357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6876752010091104845253809 5157564007568328633940357)
                  ·
                    refine ⟨967043251419061618863817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157564007568328633940357 967043251419061618863817)
                    ·
                      rfl

theorem cell23_5649930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_5649930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649930 prefixEnd_5649930 := by exact prefixLift 5649930
  have htrace : WordTrace (prefixWord ++ tailWord_5649930) baseStart_5649930 baseEnd_5649930 := by
    simpa [prefixWord, tailWord_5649930, baseEnd_5649930] using wordTrace_append hprefix tailTrace_5649930
  have hstable : (prefixWord ++ tailWord_5649930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649930).length < 2 ^ (prefixWord ++ tailWord_5649930).sum := by decide
  have hdescent : baseEnd_5649930 < baseStart_5649930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649936 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 3]
def baseStart_5649936 : Nat := 118140960795 + 5649936 * 2 ^ 59
def prefixEnd_5649936 : Nat := 4983230072969 + 3 ^ 40 * 5649936 * 2
def baseEnd_5649936 : Nat := 2901132835141111833116423

theorem tailTrace_5649936 : CollatzResearch.WordTrace tailWord_5649936 prefixEnd_5649936 2901132835141111833116423 := by
  unfold tailWord_5649936
  simp only [CollatzResearch.WordTrace]
  refine ⟨103035047629627139545864831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137380063506169519394486441 103035047629627139545864831)
  ·
    refine ⟨154552571444440709318797247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103035047629627139545864831 154552571444440709318797247)
    ·
      refine ⟨231828857166661063978195871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154552571444440709318797247 231828857166661063978195871)
      ·
        refine ⟨347743285749991595967293807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231828857166661063978195871 347743285749991595967293807)
        ·
          refine ⟨521614928624987393950940711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347743285749991595967293807 521614928624987393950940711)
          ·
            refine ⟨782422392937481090926411067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521614928624987393950940711 782422392937481090926411067)
            ·
              refine ⟨1173633589406221636389616601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782422392937481090926411067 1173633589406221636389616601)
              ·
                refine ⟨880225192054666227292212451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173633589406221636389616601 880225192054666227292212451)
                ·
                  refine ⟨1320337788081999340938318677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880225192054666227292212451 1320337788081999340938318677)
                  ·
                    refine ⟨7736354227042964888310461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1320337788081999340938318677 7736354227042964888310461)
                    ·
                      refine ⟨2901132835141111833116423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7736354227042964888310461 2901132835141111833116423)
                      ·
                        rfl

theorem cell23_5649936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_5649936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649936 prefixEnd_5649936 := by exact prefixLift 5649936
  have htrace : WordTrace (prefixWord ++ tailWord_5649936) baseStart_5649936 baseEnd_5649936 := by
    simpa [prefixWord, tailWord_5649936, baseEnd_5649936] using wordTrace_append hprefix tailTrace_5649936
  have hstable : (prefixWord ++ tailWord_5649936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649936).length < 2 ^ (prefixWord ++ tailWord_5649936).sum := by decide
  have hdescent : baseEnd_5649936 < baseStart_5649936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649953 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_5649953 : Nat := 118140960795 + 5649953 * 2 ^ 59
def prefixEnd_5649953 : Nat := 4983230072969 + 3 ^ 40 * 5649953 * 2
def baseEnd_5649953 : Nat := 2901141564312238266603845

theorem tailTrace_5649953 : CollatzResearch.WordTrace tailWord_5649953 prefixEnd_5649953 2901141564312238266603845 := by
  unfold tailWord_5649953
  simp only [CollatzResearch.WordTrace]
  refine ⟨206070715300192690995098513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137380476866795127330065675 206070715300192690995098513)
  ·
    refine ⟨154553036475144518246323885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206070715300192690995098513 154553036475144518246323885)
    ·
      refine ⟨57957388678179194342371457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154553036475144518246323885 57957388678179194342371457)
      ·
        refine ⟨43468041508634395756778593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57957388678179194342371457 43468041508634395756778593)
        ·
          refine ⟨32601031131475796817583945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43468041508634395756778593 32601031131475796817583945)
          ·
            refine ⟨24450773348606847613187959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32601031131475796817583945 24450773348606847613187959)
            ·
              refine ⟨36676160022910271419781939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24450773348606847613187959 36676160022910271419781939)
              ·
                refine ⟨55014240034365407129672909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36676160022910271419781939 55014240034365407129672909)
                ·
                  refine ⟨20630340012887027673627341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55014240034365407129672909 20630340012887027673627341)
                  ·
                    refine ⟨7736377504832635377610253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20630340012887027673627341 7736377504832635377610253)
                    ·
                      refine ⟨2901141564312238266603845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7736377504832635377610253 2901141564312238266603845)
                      ·
                        rfl

theorem cell23_5649953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_5649953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649953 prefixEnd_5649953 := by exact prefixLift 5649953
  have htrace : WordTrace (prefixWord ++ tailWord_5649953) baseStart_5649953 baseEnd_5649953 := by
    simpa [prefixWord, tailWord_5649953, baseEnd_5649953] using wordTrace_append hprefix tailTrace_5649953
  have hstable : (prefixWord ++ tailWord_5649953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649953).length < 2 ^ (prefixWord ++ tailWord_5649953).sum := by decide
  have hdescent : baseEnd_5649953 < baseStart_5649953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5649971 : List Nat := [1, 1, 1, 2, 4, 5, 2, 2, 1, 2, 2]
def baseStart_5649971 : Nat := 118140960795 + 5649971 * 2 ^ 59
def prefixEnd_5649971 : Nat := 4983230072969 + 3 ^ 40 * 5649971 * 2
def baseEnd_5649971 : Nat := 2901150806964019196178763

theorem tailTrace_5649971 : CollatzResearch.WordTrace tailWord_5649971 prefixEnd_5649971 2901150806964019196178763 := by
  unfold tailWord_5649971
  simp only [CollatzResearch.WordTrace]
  refine ⟨206071371814127480069253767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137380914542751653379502511 206071371814127480069253767)
  ·
    refine ⟨309107057721191220103880651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206071371814127480069253767 309107057721191220103880651)
    ·
      refine ⟨463660586581786830155820977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309107057721191220103880651 463660586581786830155820977)
      ·
        refine ⟨347745439936340122616865733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463660586581786830155820977 347745439936340122616865733)
        ·
          refine ⟨65202269988063772990662325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347745439936340122616865733 65202269988063772990662325)
          ·
            refine ⟨6112712811380978717874593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65202269988063772990662325 6112712811380978717874593)
            ·
              refine ⟨4584534608535734038405945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6112712811380978717874593 4584534608535734038405945)
              ·
                refine ⟨3438400956401800528804459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4584534608535734038405945 3438400956401800528804459)
                ·
                  refine ⟨5157601434602700793206689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438400956401800528804459 5157601434602700793206689)
                  ·
                    refine ⟨3868201075952025594905017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5157601434602700793206689 3868201075952025594905017)
                    ·
                      refine ⟨2901150806964019196178763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868201075952025594905017 2901150806964019196178763)
                      ·
                        rfl

theorem cell23_5649971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 2, 2].length) (baseStart_5649971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5649971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5649971 prefixEnd_5649971 := by exact prefixLift 5649971
  have htrace : WordTrace (prefixWord ++ tailWord_5649971) baseStart_5649971 baseEnd_5649971 := by
    simpa [prefixWord, tailWord_5649971, baseEnd_5649971] using wordTrace_append hprefix tailTrace_5649971
  have hstable : (prefixWord ++ tailWord_5649971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5649971).length < 2 ^ (prefixWord ++ tailWord_5649971).sum := by decide
  have hdescent : baseEnd_5649971 < baseStart_5649971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5649971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650016 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 11]
def baseStart_5650016 : Nat := 118140960795 + 5650016 * 2 ^ 59
def prefixEnd_5650016 : Nat := 4983230072969 + 3 ^ 40 * 5650016 * 2
def baseEnd_5650016 : Nat := 322352657065941280012895

theorem tailTrace_5650016 : CollatzResearch.WordTrace tailWord_5650016 prefixEnd_5650016 322352657065941280012895 := by
  unfold tailWord_5650016
  simp only [CollatzResearch.WordTrace]
  refine ⟨103036506549482226377320951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137382008732642968503094601 103036506549482226377320951)
  ·
    refine ⟨154554759824223339565981427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103036506549482226377320951 154554759824223339565981427)
    ·
      refine ⟨231832139736335009348972141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154554759824223339565981427 231832139736335009348972141)
      ·
        refine ⟨86937052401125628505864553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231832139736335009348972141 86937052401125628505864553)
        ·
          refine ⟨65202789300844221379398415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86937052401125628505864553 65202789300844221379398415)
          ·
            refine ⟨97804183951266332069097623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65202789300844221379398415 97804183951266332069097623)
            ·
              refine ⟨146706275926899498103646435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97804183951266332069097623 146706275926899498103646435)
              ·
                refine ⟨220059413890349247155469653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146706275926899498103646435 220059413890349247155469653)
                ·
                  refine ⟨322352657065941280012895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 220059413890349247155469653 322352657065941280012895)
                  ·
                    rfl

theorem cell23_5650016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 11].length) (baseStart_5650016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650016 prefixEnd_5650016 := by exact prefixLift 5650016
  have htrace : WordTrace (prefixWord ++ tailWord_5650016) baseStart_5650016 baseEnd_5650016 := by
    simpa [prefixWord, tailWord_5650016, baseEnd_5650016] using wordTrace_append hprefix tailTrace_5650016
  have hstable : (prefixWord ++ tailWord_5650016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650016).length < 2 ^ (prefixWord ++ tailWord_5650016).sum := by decide
  have hdescent : baseEnd_5650016 < baseStart_5650016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650023 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_5650023 : Nat := 118140960795 + 5650023 * 2 ^ 59
def prefixEnd_5650023 : Nat := 4983230072969 + 3 ^ 40 * 5650023 * 2
def baseEnd_5650023 : Nat := 2901177507958052992728523

theorem tailTrace_5650023 : CollatzResearch.WordTrace tailWord_5650023 prefixEnd_5650023 2901177507958052992728523 := by
  unfold tailWord_5650023
  simp only [CollatzResearch.WordTrace]
  refine ⟨206073268409939092950146723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137382178939959395300097815 206073268409939092950146723)
  ·
    refine ⟨309109902614908639425220085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206073268409939092950146723 309109902614908639425220085)
    ·
      refine ⟨28979053370147684946114383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 309109902614908639425220085 28979053370147684946114383)
      ·
        refine ⟨43468580055221527419171575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28979053370147684946114383 43468580055221527419171575)
        ·
          refine ⟨65202870082832291128757363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43468580055221527419171575 65202870082832291128757363)
          ·
            refine ⟨97804305124248436693136045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65202870082832291128757363 97804305124248436693136045)
            ·
              refine ⟨36676614421593163759926017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97804305124248436693136045 36676614421593163759926017)
              ·
                refine ⟨27507460816194872819944513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36676614421593163759926017 27507460816194872819944513)
                ·
                  refine ⟨20630595612146154614958385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27507460816194872819944513 20630595612146154614958385)
                  ·
                    refine ⟨15472946709109615961218789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20630595612146154614958385 15472946709109615961218789)
                    ·
                      refine ⟨2901177507958052992728523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15472946709109615961218789 2901177507958052992728523)
                      ·
                        rfl

theorem cell23_5650023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_5650023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650023 prefixEnd_5650023 := by exact prefixLift 5650023
  have htrace : WordTrace (prefixWord ++ tailWord_5650023) baseStart_5650023 baseEnd_5650023 := by
    simpa [prefixWord, tailWord_5650023, baseEnd_5650023] using wordTrace_append hprefix tailTrace_5650023
  have hstable : (prefixWord ++ tailWord_5650023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650023).length < 2 ^ (prefixWord ++ tailWord_5650023).sum := by decide
  have hdescent : baseEnd_5650023 < baseStart_5650023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650043 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 3]
def baseStart_5650043 : Nat := 118140960795 + 5650043 * 2 ^ 59
def prefixEnd_5650043 : Nat := 4983230072969 + 3 ^ 40 * 5650043 * 2
def baseEnd_5650043 : Nat := 2901187777571142914478431

theorem tailTrace_5650043 : CollatzResearch.WordTrace tailWord_5650043 prefixEnd_5650043 2901187777571142914478431 := by
  unfold tailWord_5650043
  simp only [CollatzResearch.WordTrace]
  refine ⟨206073997869866636365874783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137382665246577757577249855 206073997869866636365874783)
  ·
    refine ⟨309110996804799954548812175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206073997869866636365874783 309110996804799954548812175)
    ·
      refine ⟨463666495207199931823218263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309110996804799954548812175 463666495207199931823218263)
      ·
        refine ⟨695499742810799897734827395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463666495207199931823218263 695499742810799897734827395)
        ·
          refine ⟨1043249614216199846602241093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695499742810799897734827395 1043249614216199846602241093)
          ·
            refine ⟨195609302665537471237920205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1043249614216199846602241093 195609302665537471237920205)
            ·
              refine ⟨73353488499576551714220077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195609302665537471237920205 73353488499576551714220077)
              ·
                refine ⟨27507558187341206892832529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73353488499576551714220077 27507558187341206892832529)
                ·
                  refine ⟨20630668640505905169624397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27507558187341206892832529 20630668640505905169624397)
                  ·
                    refine ⟨7736500740189714438609149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20630668640505905169624397 7736500740189714438609149)
                    ·
                      refine ⟨2901187777571142914478431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7736500740189714438609149 2901187777571142914478431)
                      ·
                        rfl

theorem cell23_5650043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 3].length) (baseStart_5650043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650043 prefixEnd_5650043 := by exact prefixLift 5650043
  have htrace : WordTrace (prefixWord ++ tailWord_5650043) baseStart_5650043 baseEnd_5650043 := by
    simpa [prefixWord, tailWord_5650043, baseEnd_5650043] using wordTrace_append hprefix tailTrace_5650043
  have hstable : (prefixWord ++ tailWord_5650043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650043).length < 2 ^ (prefixWord ++ tailWord_5650043).sum := by decide
  have hdescent : baseEnd_5650043 < baseStart_5650043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650080 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 2, 5]
def baseStart_5650080 : Nat := 118140960795 + 5650080 * 2 ^ 59
def prefixEnd_5650080 : Nat := 4983230072969 + 3 ^ 40 * 5650080 * 2
def baseEnd_5650080 : Nat := 967068925451786423238587

theorem tailTrace_5650080 : CollatzResearch.WordTrace tailWord_5650080 prefixEnd_5650080 967068925451786423238587 := by
  unfold tailWord_5650080
  simp only [CollatzResearch.WordTrace]
  refine ⟨103037673685366295842485847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137383564913821727789981129 103037673685366295842485847)
  ·
    refine ⟨154556510528049443763728771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103037673685366295842485847 154556510528049443763728771)
    ·
      refine ⟨231834765792074165645593157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154556510528049443763728771 231834765792074165645593157)
      ·
        refine ⟨43469018586013906058548717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231834765792074165645593157 43469018586013906058548717)
        ·
          refine ⟨16300881969755214771955769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43469018586013906058548717 16300881969755214771955769)
          ·
            refine ⟨12225661477316411078966827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16300881969755214771955769 12225661477316411078966827)
            ·
              refine ⟨18338492215974616618450241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12225661477316411078966827 18338492215974616618450241)
              ·
                refine ⟨13753869161980962463837681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18338492215974616618450241 13753869161980962463837681)
                ·
                  refine ⟨10315401871485721847878261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13753869161980962463837681 10315401871485721847878261)
                  ·
                    refine ⟨967068925451786423238587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10315401871485721847878261 967068925451786423238587)
                    ·
                      rfl

theorem cell23_5650080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_5650080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650080 prefixEnd_5650080 := by exact prefixLift 5650080
  have htrace : WordTrace (prefixWord ++ tailWord_5650080) baseStart_5650080 baseEnd_5650080 := by
    simpa [prefixWord, tailWord_5650080, baseEnd_5650080] using wordTrace_append hprefix tailTrace_5650080
  have hstable : (prefixWord ++ tailWord_5650080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650080).length < 2 ^ (prefixWord ++ tailWord_5650080).sum := by decide
  have hdescent : baseEnd_5650080 < baseStart_5650080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650143 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 6]
def baseStart_5650143 : Nat := 118140960795 + 5650143 * 2 ^ 59
def prefixEnd_5650143 : Nat := 4983230072969 + 3 ^ 40 * 5650143 * 2
def baseEnd_5650143 : Nat := 2901239125636592523227971

theorem tailTrace_5650143 : CollatzResearch.WordTrace tailWord_5650143 prefixEnd_5650143 2901239125636592523227971 := by
  unfold tailWord_5650143
  simp only [CollatzResearch.WordTrace]
  refine ⟨206077645169504353444515083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137385096779669568963010055 206077645169504353444515083)
  ·
    refine ⟨309116467754256530166772625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206077645169504353444515083 309116467754256530166772625)
    ·
      refine ⟨231837350815692397625079469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309116467754256530166772625 231837350815692397625079469)
      ·
        refine ⟨86939006555884649109404801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231837350815692397625079469 86939006555884649109404801)
        ·
          refine ⟨65204254916913486832053601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86939006555884649109404801 65204254916913486832053601)
          ·
            refine ⟨48903191187685115124040201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65204254916913486832053601 48903191187685115124040201)
            ·
              refine ⟨36677393390763836343030151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48903191187685115124040201 36677393390763836343030151)
              ·
                refine ⟨55016090086145754514545227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36677393390763836343030151 55016090086145754514545227)
                ·
                  refine ⟨82524135129218631771817841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55016090086145754514545227 82524135129218631771817841)
                  ·
                    refine ⟨61893101346913973828863381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82524135129218631771817841 61893101346913973828863381)
                    ·
                      refine ⟨2901239125636592523227971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61893101346913973828863381 2901239125636592523227971)
                      ·
                        rfl

theorem cell23_5650143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_5650143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650143 prefixEnd_5650143 := by exact prefixLift 5650143
  have htrace : WordTrace (prefixWord ++ tailWord_5650143) baseStart_5650143 baseEnd_5650143 := by
    simpa [prefixWord, tailWord_5650143, baseEnd_5650143] using wordTrace_append hprefix tailTrace_5650143
  have hstable : (prefixWord ++ tailWord_5650143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650143).length < 2 ^ (prefixWord ++ tailWord_5650143).sum := by decide
  have hdescent : baseEnd_5650143 < baseStart_5650143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650144 : List Nat := [2, 1, 1, 3, 1, 2, 6, 2, 1, 4]
def baseStart_5650144 : Nat := 118140960795 + 5650144 * 2 ^ 59
def prefixEnd_5650144 : Nat := 4983230072969 + 3 ^ 40 * 5650144 * 2
def baseEnd_5650144 : Nat := 967079879705749006438489

theorem tailTrace_5650144 : CollatzResearch.WordTrace tailWord_5650144 prefixEnd_5650144 967079879705749006438489 := by
  unfold tailWord_5650144
  simp only [CollatzResearch.WordTrace]
  refine ⟨103038840821250365307650743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137385121095000487076867657 103038840821250365307650743)
  ·
    refine ⟨154558261231875547961476115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103038840821250365307650743 154558261231875547961476115)
    ·
      refine ⟨231837391847813321942214173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154558261231875547961476115 231837391847813321942214173)
      ·
        refine ⟨86939021942929995728330315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231837391847813321942214173 86939021942929995728330315)
        ·
          refine ⟨130408532914394993592495473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86939021942929995728330315 130408532914394993592495473)
          ·
            refine ⟨97806399685796245194371605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130408532914394993592495473 97806399685796245194371605)
            ·
              refine ⟨4584674985271698993486169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97806399685796245194371605 4584674985271698993486169)
              ·
                refine ⟨3438506238953774245114627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4584674985271698993486169 3438506238953774245114627)
                ·
                  refine ⟨5157759358430661367671941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438506238953774245114627 5157759358430661367671941)
                  ·
                    refine ⟨967079879705749006438489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157759358430661367671941 967079879705749006438489)
                    ·
                      rfl

theorem cell23_5650144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 4].length) (baseStart_5650144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650144 prefixEnd_5650144 := by exact prefixLift 5650144
  have htrace : WordTrace (prefixWord ++ tailWord_5650144) baseStart_5650144 baseEnd_5650144 := by
    simpa [prefixWord, tailWord_5650144, baseEnd_5650144] using wordTrace_append hprefix tailTrace_5650144
  have hstable : (prefixWord ++ tailWord_5650144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650144).length < 2 ^ (prefixWord ++ tailWord_5650144).sum := by decide
  have hdescent : baseEnd_5650144 < baseStart_5650144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650170 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_5650170 : Nat := 118140960795 + 5650170 * 2 ^ 59
def prefixEnd_5650170 : Nat := 4983230072969 + 3 ^ 40 * 5650170 * 2
def baseEnd_5650170 : Nat := 967084329871421305863449

theorem tailTrace_5650170 : CollatzResearch.WordTrace tailWord_5650170 prefixEnd_5650170 967084329871421305863449 := by
  unfold tailWord_5650170
  simp only [CollatzResearch.WordTrace]
  refine ⟨51519657485101634263936991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137385753293604358037165309 51519657485101634263936991)
  ·
    refine ⟨77279486227652451395905487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51519657485101634263936991 77279486227652451395905487)
    ·
      refine ⟨115919229341478677093858231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77279486227652451395905487 115919229341478677093858231)
      ·
        refine ⟨173878844012218015640787347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115919229341478677093858231 173878844012218015640787347)
        ·
          refine ⟨260818266018327023461181021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173878844012218015640787347 260818266018327023461181021)
          ·
            refine ⟨97806849756872633797942883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260818266018327023461181021 97806849756872633797942883)
            ·
              refine ⟨146710274635308950696914325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97806849756872633797942883 146710274635308950696914325)
              ·
                refine ⟨6877044123530107063917859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146710274635308950696914325 6877044123530107063917859)
                ·
                  refine ⟨10315566185295160595876789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877044123530107063917859 10315566185295160595876789)
                  ·
                    refine ⟨967084329871421305863449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10315566185295160595876789 967084329871421305863449)
                    ·
                      rfl

theorem cell23_5650170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_5650170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650170 prefixEnd_5650170 := by exact prefixLift 5650170
  have htrace : WordTrace (prefixWord ++ tailWord_5650170) baseStart_5650170 baseEnd_5650170 := by
    simpa [prefixWord, tailWord_5650170, baseEnd_5650170] using wordTrace_append hprefix tailTrace_5650170
  have hstable : (prefixWord ++ tailWord_5650170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650170).length < 2 ^ (prefixWord ++ tailWord_5650170).sum := by decide
  have hdescent : baseEnd_5650170 < baseStart_5650170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650187 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 1, 5]
def baseStart_5650187 : Nat := 118140960795 + 5650187 * 2 ^ 59
def prefixEnd_5650187 : Nat := 4983230072969 + 3 ^ 40 * 5650187 * 2
def baseEnd_5650187 : Nat := 967087239595130117025923

theorem tailTrace_5650187 : CollatzResearch.WordTrace tailWord_5650187 prefixEnd_5650187 967087239595130117025923 := by
  unfold tailWord_5650187
  simp only [CollatzResearch.WordTrace]
  refine ⟨206079249981344948959116815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137386166654229965972744543 206079249981344948959116815)
  ·
    refine ⟨309118874972017423438675223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206079249981344948959116815 309118874972017423438675223)
    ·
      refine ⟨463678312458026135158012835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309118874972017423438675223 463678312458026135158012835)
      ·
        refine ⟨695517468687039202737019253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463678312458026135158012835 695517468687039202737019253)
        ·
          refine ⟨65204762689409925256595555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 695517468687039202737019253 65204762689409925256595555)
          ·
            refine ⟨97807144034114887884893333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65204762689409925256595555 97807144034114887884893333)
            ·
              refine ⟨4584709876599135369604375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97807144034114887884893333 4584709876599135369604375)
              ·
                refine ⟨6877064814898703054406563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4584709876599135369604375 6877064814898703054406563)
                ·
                  refine ⟨10315597222348054581609845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877064814898703054406563 10315597222348054581609845)
                  ·
                    refine ⟨967087239595130117025923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10315597222348054581609845 967087239595130117025923)
                    ·
                      rfl

theorem cell23_5650187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 5].length) (baseStart_5650187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650187 prefixEnd_5650187 := by exact prefixLift 5650187
  have htrace : WordTrace (prefixWord ++ tailWord_5650187) baseStart_5650187 baseEnd_5650187 := by
    simpa [prefixWord, tailWord_5650187, baseEnd_5650187] using wordTrace_append hprefix tailTrace_5650187
  have hstable : (prefixWord ++ tailWord_5650187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650187).length < 2 ^ (prefixWord ++ tailWord_5650187).sum := by decide
  have hdescent : baseEnd_5650187 < baseStart_5650187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650203 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 6]
def baseStart_5650203 : Nat := 118140960795 + 5650203 * 2 ^ 59
def prefixEnd_5650203 : Nat := 4983230072969 + 3 ^ 40 * 5650203 * 2
def baseEnd_5650203 : Nat := 2901269934475862288477695

theorem tailTrace_5650203 : CollatzResearch.WordTrace tailWord_5650203 prefixEnd_5650203 2901269934475862288477695 := by
  unfold tailWord_5650203
  simp only [CollatzResearch.WordTrace]
  refine ⟨206079833549286983691699263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137386555699524655794466175 206079833549286983691699263)
  ·
    refine ⟨309119750323930475537548895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206079833549286983691699263 309119750323930475537548895)
    ·
      refine ⟨463679625485895713306323343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309119750323930475537548895 463679625485895713306323343)
      ·
        refine ⟨695519438228843569959485015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463679625485895713306323343 695519438228843569959485015)
        ·
          refine ⟨1043279157343265354939227523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695519438228843569959485015 1043279157343265354939227523)
          ·
            refine ⟨1564918736014898032408841285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043279157343265354939227523 1564918736014898032408841285)
            ·
              refine ⟨293422263002793381076657741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1564918736014898032408841285 293422263002793381076657741)
              ·
                refine ⟨110033348626047517903746653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293422263002793381076657741 110033348626047517903746653)
                ·
                  refine ⟨41262505734767819213904995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110033348626047517903746653 41262505734767819213904995)
                  ·
                    refine ⟨61893758602151728820857493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41262505734767819213904995 61893758602151728820857493)
                    ·
                      refine ⟨2901269934475862288477695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61893758602151728820857493 2901269934475862288477695)
                      ·
                        rfl

theorem cell23_5650203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_5650203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650203 prefixEnd_5650203 := by exact prefixLift 5650203
  have htrace : WordTrace (prefixWord ++ tailWord_5650203) baseStart_5650203 baseEnd_5650203 := by
    simpa [prefixWord, tailWord_5650203, baseEnd_5650203] using wordTrace_append hprefix tailTrace_5650203
  have hstable : (prefixWord ++ tailWord_5650203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650203).length < 2 ^ (prefixWord ++ tailWord_5650203).sum := by decide
  have hdescent : baseEnd_5650203 < baseStart_5650203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650220 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_5650220 : Nat := 118140960795 + 5650220 * 2 ^ 59
def prefixEnd_5650220 : Nat := 4983230072969 + 3 ^ 40 * 5650220 * 2
def baseEnd_5650220 : Nat := 2901278663646988721965117

theorem tailTrace_5650220 : CollatzResearch.WordTrace tailWord_5650220 prefixEnd_5650220 2901278663646988721965117 := by
  unfold tailWord_5650220
  simp only [CollatzResearch.WordTrace]
  refine ⟨103040226795112697797534057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137386969060150263730045409 103040226795112697797534057)
  ·
    refine ⟨77280170096334523348150543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103040226795112697797534057 77280170096334523348150543)
    ·
      refine ⟨115920255144501785022225815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77280170096334523348150543 115920255144501785022225815)
      ·
        refine ⟨173880382716752677533338723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115920255144501785022225815 173880382716752677533338723)
        ·
          refine ⟨260820574075129016300008085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173880382716752677533338723 260820574075129016300008085)
          ·
            refine ⟨12225964409771672639062879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 260820574075129016300008085 12225964409771672639062879)
            ·
              refine ⟨18338946614657508958594319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12225964409771672639062879 18338946614657508958594319)
              ·
                refine ⟨27508419921986263437891479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18338946614657508958594319 27508419921986263437891479)
                ·
                  refine ⟨41262629882979395156837219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27508419921986263437891479 41262629882979395156837219)
                  ·
                    refine ⟨61893944824469092735255829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41262629882979395156837219 61893944824469092735255829)
                    ·
                      refine ⟨2901278663646988721965117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61893944824469092735255829 2901278663646988721965117)
                      ·
                        rfl

theorem cell23_5650220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_5650220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650220 prefixEnd_5650220 := by exact prefixLift 5650220
  have htrace : WordTrace (prefixWord ++ tailWord_5650220) baseStart_5650220 baseEnd_5650220 := by
    simpa [prefixWord, tailWord_5650220, baseEnd_5650220] using wordTrace_append hprefix tailTrace_5650220
  have hstable : (prefixWord ++ tailWord_5650220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650220).length < 2 ^ (prefixWord ++ tailWord_5650220).sum := by decide
  have hdescent : baseEnd_5650220 < baseStart_5650220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650223 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 7]
def baseStart_5650223 : Nat := 118140960795 + 5650223 * 2 ^ 59
def prefixEnd_5650223 : Nat := 4983230072969 + 3 ^ 40 * 5650223 * 2
def baseEnd_5650223 : Nat := 2901280204088952210227603

theorem tailTrace_5650223 : CollatzResearch.WordTrace tailWord_5650223 prefixEnd_5650223 2901280204088952210227603 := by
  unfold tailWord_5650223
  simp only [CollatzResearch.WordTrace]
  refine ⟨206080563009214527107427323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137387042006143018071618215 206080563009214527107427323)
  ·
    refine ⟨309120844513821790661140985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206080563009214527107427323 309120844513821790661140985)
    ·
      refine ⟨231840633385366342995855739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309120844513821790661140985 231840633385366342995855739)
      ·
        refine ⟨347760950078049514493783609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231840633385366342995855739 347760950078049514493783609)
        ·
          refine ⟨260820712558537135870337707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347760950078049514493783609 260820712558537135870337707)
          ·
            refine ⟨391231068837805703805506561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260820712558537135870337707 391231068837805703805506561)
            ·
              refine ⟨293423301628354277854129921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391231068837805703805506561 293423301628354277854129921)
              ·
                refine ⟨220067476221265708390597441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293423301628354277854129921 220067476221265708390597441)
                ·
                  refine ⟨165050607165949281292948081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220067476221265708390597441 165050607165949281292948081)
                  ·
                    refine ⟨123787955374461960969711061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 165050607165949281292948081 123787955374461960969711061)
                    ·
                      refine ⟨2901280204088952210227603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123787955374461960969711061 2901280204088952210227603)
                      ·
                        rfl

theorem cell23_5650223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_5650223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650223 prefixEnd_5650223 := by exact prefixLift 5650223
  have htrace : WordTrace (prefixWord ++ tailWord_5650223) baseStart_5650223 baseEnd_5650223 := by
    simpa [prefixWord, tailWord_5650223, baseEnd_5650223] using wordTrace_append hprefix tailTrace_5650223
  have hstable : (prefixWord ++ tailWord_5650223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650223).length < 2 ^ (prefixWord ++ tailWord_5650223).sum := by decide
  have hdescent : baseEnd_5650223 < baseStart_5650223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650268 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_5650268 : Nat := 118140960795 + 5650268 * 2 ^ 59
def prefixEnd_5650268 : Nat := 4983230072969 + 3 ^ 40 * 5650268 * 2
def baseEnd_5650268 : Nat := 967101103572801511388299

theorem tailTrace_5650268 : CollatzResearch.WordTrace tailWord_5650268 prefixEnd_5650268 967101103572801511388299 := by
  unfold tailWord_5650268
  simp only [CollatzResearch.WordTrace]
  refine ⟨103041102147025749896407729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137388136196034333195210305 103041102147025749896407729)
  ·
    refine ⟨77280826610269312422305797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103041102147025749896407729 77280826610269312422305797)
    ·
      refine ⟨14490154989425496079182337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77280826610269312422305797 14490154989425496079182337)
      ·
        refine ⟨10867616242069122059386753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14490154989425496079182337 10867616242069122059386753)
        ·
          refine ⟨8150712181551841544540065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10867616242069122059386753 8150712181551841544540065)
          ·
            refine ⟨6113034136163881158405049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8150712181551841544540065 6113034136163881158405049)
            ·
              refine ⟨4584775602122910868803787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6113034136163881158405049 4584775602122910868803787)
              ·
                refine ⟨6877163403184366303205681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4584775602122910868803787 6877163403184366303205681)
                ·
                  refine ⟨5157872552388274727404261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6877163403184366303205681 5157872552388274727404261)
                  ·
                    refine ⟨967101103572801511388299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5157872552388274727404261 967101103572801511388299)
                    ·
                      rfl

theorem cell23_5650268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_5650268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650268 prefixEnd_5650268 := by exact prefixLift 5650268
  have htrace : WordTrace (prefixWord ++ tailWord_5650268) baseStart_5650268 baseEnd_5650268 := by
    simpa [prefixWord, tailWord_5650268, baseEnd_5650268] using wordTrace_append hprefix tailTrace_5650268
  have hstable : (prefixWord ++ tailWord_5650268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650268).length < 2 ^ (prefixWord ++ tailWord_5650268).sum := by decide
  have hdescent : baseEnd_5650268 < baseStart_5650268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650284 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 3, 3, 2]
def baseStart_5650284 : Nat := 118140960795 + 5650284 * 2 ^ 59
def prefixEnd_5650284 : Nat := 4983230072969 + 3 ^ 40 * 5650284 * 2
def baseEnd_5650284 : Nat := 2901311526408876471564823

theorem tailTrace_5650284 : CollatzResearch.WordTrace tailWord_5650284 prefixEnd_5650284 2901311526408876471564823 := by
  unfold tailWord_5650284
  simp only [CollatzResearch.WordTrace]
  refine ⟨103041393930996767262698953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137388525241329023016931937 103041393930996767262698953)
  ·
    refine ⟨77281045448247575447024215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103041393930996767262698953 77281045448247575447024215)
    ·
      refine ⟨115921568172371363170536323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77281045448247575447024215 115921568172371363170536323)
      ·
        refine ⟨173882352258557044755804485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115921568172371363170536323 173882352258557044755804485)
        ·
          refine ⟨32602941048479445891713341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173882352258557044755804485 32602941048479445891713341)
          ·
            refine ⟨12226102893179792209392503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32602941048479445891713341 12226102893179792209392503)
            ·
              refine ⟨18339154339769688314088755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12226102893179792209392503 18339154339769688314088755)
              ·
                refine ⟨27508731509654532471133133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18339154339769688314088755 27508731509654532471133133)
                ·
                  refine ⟨10315774316120449676674925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27508731509654532471133133 10315774316120449676674925)
                  ·
                    refine ⟨3868415368545168628753097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10315774316120449676674925 3868415368545168628753097)
                    ·
                      refine ⟨2901311526408876471564823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868415368545168628753097 2901311526408876471564823)
                      ·
                        rfl

theorem cell23_5650284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_5650284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650284 prefixEnd_5650284 := by exact prefixLift 5650284
  have htrace : WordTrace (prefixWord ++ tailWord_5650284) baseStart_5650284 baseEnd_5650284 := by
    simpa [prefixWord, tailWord_5650284, baseEnd_5650284] using wordTrace_append hprefix tailTrace_5650284
  have hstable : (prefixWord ++ tailWord_5650284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650284).length < 2 ^ (prefixWord ++ tailWord_5650284).sum := by decide
  have hdescent : baseEnd_5650284 < baseStart_5650284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650290 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_5650290 : Nat := 118140960795 + 5650290 * 2 ^ 59
def prefixEnd_5650290 : Nat := 4983230072969 + 3 ^ 40 * 5650290 * 2
def baseEnd_5650290 : Nat := 967104869097601149363265

theorem tailTrace_5650290 : CollatzResearch.WordTrace tailWord_5650290 prefixEnd_5650290 967104869097601149363265 := by
  unfold tailWord_5650290
  simp only [CollatzResearch.WordTrace]
  refine ⟨51520751674992949387529081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137388671133314531700077549 51520751674992949387529081)
  ·
    refine ⟨38640563756244712040646811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51520751674992949387529081 38640563756244712040646811)
    ·
      refine ⟨57960845634367068060970217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38640563756244712040646811 57960845634367068060970217)
      ·
        refine ⟨43470634225775301045727663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57960845634367068060970217 43470634225775301045727663)
        ·
          refine ⟨65205951338662951568591495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43470634225775301045727663 65205951338662951568591495)
          ·
            refine ⟨97808927007994427352887243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65205951338662951568591495 97808927007994427352887243)
            ·
              refine ⟨146713390511991641029330865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97808927007994427352887243 146713390511991641029330865)
              ·
                refine ⟨110035042883993730771998149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146713390511991641029330865 110035042883993730771998149)
                ·
                  refine ⟨20631570540748824519749653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110035042883993730771998149 20631570540748824519749653)
                  ·
                    refine ⟨967104869097601149363265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20631570540748824519749653 967104869097601149363265)
                    ·
                      rfl

theorem cell23_5650290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_5650290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650290 prefixEnd_5650290 := by exact prefixLift 5650290
  have htrace : WordTrace (prefixWord ++ tailWord_5650290) baseStart_5650290 baseEnd_5650290 := by
    simpa [prefixWord, tailWord_5650290, baseEnd_5650290] using wordTrace_append hprefix tailTrace_5650290
  have hstable : (prefixWord ++ tailWord_5650290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650290).length < 2 ^ (prefixWord ++ tailWord_5650290).sum := by decide
  have hdescent : baseEnd_5650290 < baseStart_5650290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650327 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_5650327 : Nat := 118140960795 + 5650327 * 2 ^ 59
def prefixEnd_5650327 : Nat := 4983230072969 + 3 ^ 40 * 5650327 * 2
def baseEnd_5650327 : Nat := 2901333606077019803327125

theorem tailTrace_5650327 : CollatzResearch.WordTrace tailWord_5650327 prefixEnd_5650327 2901333606077019803327125 := by
  unfold tailWord_5650327
  simp only [CollatzResearch.WordTrace]
  refine ⟨206084356200837752869213235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137389570800558501912808823 206084356200837752869213235)
  ·
    refine ⟨309126534301256629303819853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206084356200837752869213235 309126534301256629303819853)
    ·
      refine ⟨115922450362971235988932445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309126534301256629303819853 115922450362971235988932445)
      ·
        refine ⟨43470918886114213495849667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115922450362971235988932445 43470918886114213495849667)
        ·
          refine ⟨65206378329171320243774501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43470918886114213495849667 65206378329171320243774501)
          ·
            refine ⟨12226195936719622545707719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65206378329171320243774501 12226195936719622545707719)
            ·
              refine ⟨18339293905079433818561579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12226195936719622545707719 18339293905079433818561579)
              ·
                refine ⟨27508940857619150727842369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18339293905079433818561579 27508940857619150727842369)
                ·
                  refine ⟨20631705643214363045881777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27508940857619150727842369 20631705643214363045881777)
                  ·
                    refine ⟨15473779232410772284411333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20631705643214363045881777 15473779232410772284411333)
                    ·
                      refine ⟨2901333606077019803327125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15473779232410772284411333 2901333606077019803327125)
                      ·
                        rfl

theorem cell23_5650327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_5650327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650327 prefixEnd_5650327 := by exact prefixLift 5650327
  have htrace : WordTrace (prefixWord ++ tailWord_5650327) baseStart_5650327 baseEnd_5650327 := by
    simpa [prefixWord, tailWord_5650327, baseEnd_5650327] using wordTrace_append hprefix tailTrace_5650327
  have hstable : (prefixWord ++ tailWord_5650327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650327).length < 2 ^ (prefixWord ++ tailWord_5650327).sum := by decide
  have hdescent : baseEnd_5650327 < baseStart_5650327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650481 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 2, 3, 2]
def baseStart_5650481 : Nat := 118140960795 + 5650481 * 2 ^ 59
def prefixEnd_5650481 : Nat := 4983230072969 + 3 ^ 40 * 5650481 * 2
def baseEnd_5650481 : Nat := 2901412682097812200801417

theorem tailTrace_5650481 : CollatzResearch.WordTrace tailWord_5650481 prefixEnd_5650481 2901412682097812200801417 := by
  unfold tailWord_5650481
  simp only [CollatzResearch.WordTrace]
  refine ⟨206089973042279837170319297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137393315361519891446879531 206089973042279837170319297)
  ·
    refine ⟨154567479781709877877739473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206089973042279837170319297 154567479781709877877739473)
    ·
      refine ⟨115925609836282408408304605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154567479781709877877739473 115925609836282408408304605)
      ·
        refine ⟨43472103688605903153114227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115925609836282408408304605 43472103688605903153114227)
        ·
          refine ⟨65208155532908854729671341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43472103688605903153114227 65208155532908854729671341)
          ·
            refine ⟨24453058324840820523626753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65208155532908854729671341 24453058324840820523626753)
            ·
              refine ⟨18339793743630615392720065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24453058324840820523626753 18339793743630615392720065)
              ·
                refine ⟨13754845307722961544540049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18339793743630615392720065 13754845307722961544540049)
                ·
                  refine ⟨10316133980792221158405037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13754845307722961544540049 10316133980792221158405037)
                  ·
                    refine ⟨3868550242797082934401889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10316133980792221158405037 3868550242797082934401889)
                    ·
                      refine ⟨2901412682097812200801417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868550242797082934401889 2901412682097812200801417)
                      ·
                        rfl

theorem cell23_5650481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_5650481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650481 prefixEnd_5650481 := by exact prefixLift 5650481
  have htrace : WordTrace (prefixWord ++ tailWord_5650481) baseStart_5650481 baseEnd_5650481 := by
    simpa [prefixWord, tailWord_5650481, baseEnd_5650481] using wordTrace_append hprefix tailTrace_5650481
  have hstable : (prefixWord ++ tailWord_5650481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650481).length < 2 ^ (prefixWord ++ tailWord_5650481).sum := by decide
  have hdescent : baseEnd_5650481 < baseStart_5650481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650507 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 4]
def baseStart_5650507 : Nat := 118140960795 + 5650507 * 2 ^ 59
def prefixEnd_5650507 : Nat := 4983230072969 + 3 ^ 40 * 5650507 * 2
def baseEnd_5650507 : Nat := 2901426032594829099076297

theorem tailTrace_5650507 : CollatzResearch.WordTrace tailWord_5650507 prefixEnd_5650507 2901426032594829099076297 := by
  unfold tailWord_5650507
  simp only [CollatzResearch.WordTrace]
  refine ⟨206090921340185643610765775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137393947560123762407177183 206090921340185643610765775)
  ·
    refine ⟨309136382010278465416148663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206090921340185643610765775 309136382010278465416148663)
    ·
      refine ⟨463704573015417698124222995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309136382010278465416148663 463704573015417698124222995)
      ·
        refine ⟨695556859523126547186334493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463704573015417698124222995 695556859523126547186334493)
        ·
          refine ⟨260833822321172455194875435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695556859523126547186334493 260833822321172455194875435)
          ·
            refine ⟨391250733481758682792313153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260833822321172455194875435 391250733481758682792313153)
            ·
              refine ⟨293438050111319012094234865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391250733481758682792313153 293438050111319012094234865)
              ·
                refine ⟨220078537583489259070676149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293438050111319012094234865 220078537583489259070676149)
                ·
                  refine ⟨20632362898452118037875889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220078537583489259070676149 20632362898452118037875889)
                  ·
                    refine ⟨15474272173839088528406917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20632362898452118037875889 15474272173839088528406917)
                    ·
                      refine ⟨2901426032594829099076297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15474272173839088528406917 2901426032594829099076297)
                      ·
                        rfl

theorem cell23_5650507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 4].length) (baseStart_5650507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650507 prefixEnd_5650507 := by exact prefixLift 5650507
  have htrace : WordTrace (prefixWord ++ tailWord_5650507) baseStart_5650507 baseEnd_5650507 := by
    simpa [prefixWord, tailWord_5650507, baseEnd_5650507] using wordTrace_append hprefix tailTrace_5650507
  have hstable : (prefixWord ++ tailWord_5650507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650507).length < 2 ^ (prefixWord ++ tailWord_5650507).sum := by decide
  have hdescent : baseEnd_5650507 < baseStart_5650507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650511 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 3, 2, 2]
def baseStart_5650511 : Nat := 118140960795 + 5650511 * 2 ^ 59
def prefixEnd_5650511 : Nat := 4983230072969 + 3 ^ 40 * 5650511 * 2
def baseEnd_5650511 : Nat := 2901428086517447083426279

theorem tailTrace_5650511 : CollatzResearch.WordTrace tailWord_5650511 prefixEnd_5650511 2901428086517447083426279 := by
  unfold tailWord_5650511
  simp only [CollatzResearch.WordTrace]
  refine ⟨206091067232171152293911387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137394044821447434862607591 206091067232171152293911387)
  ·
    refine ⟨309136600848256728440867081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206091067232171152293911387 309136600848256728440867081)
    ·
      refine ⟨231852450636192546330650311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309136600848256728440867081 231852450636192546330650311)
      ·
        refine ⟨347778675954288819495975467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231852450636192546330650311 347778675954288819495975467)
        ·
          refine ⟨521668013931433229243963201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347778675954288819495975467 521668013931433229243963201)
          ·
            refine ⟨391251010448574921932972401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521668013931433229243963201 391251010448574921932972401)
            ·
              refine ⟨293438257836431191449729301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391251010448574921932972401 293438257836431191449729301)
              ·
                refine ⟨13754918336082712099206061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 293438257836431191449729301 13754918336082712099206061)
                ·
                  refine ⟨5158094376031017037202273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13754918336082712099206061 5158094376031017037202273)
                  ·
                    refine ⟨3868570782023262777901705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5158094376031017037202273 3868570782023262777901705)
                    ·
                      refine ⟨2901428086517447083426279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868570782023262777901705 2901428086517447083426279)
                      ·
                        rfl

theorem cell23_5650511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 2, 2].length) (baseStart_5650511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650511 prefixEnd_5650511 := by exact prefixLift 5650511
  have htrace : WordTrace (prefixWord ++ tailWord_5650511) baseStart_5650511 baseEnd_5650511 := by
    simpa [prefixWord, tailWord_5650511, baseEnd_5650511] using wordTrace_append hprefix tailTrace_5650511
  have hstable : (prefixWord ++ tailWord_5650511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650511).length < 2 ^ (prefixWord ++ tailWord_5650511).sum := by decide
  have hdescent : baseEnd_5650511 < baseStart_5650511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650525 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5650525 : Nat := 118140960795 + 5650525 * 2 ^ 59
def prefixEnd_5650525 : Nat := 4983230072969 + 3 ^ 40 * 5650525 * 2
def baseEnd_5650525 : Nat := 967145091748870009550405

theorem tailTrace_5650525 : CollatzResearch.WordTrace tailWord_5650525 prefixEnd_5650525 967145091748870009550405 := by
  unfold tailWord_5650525
  simp only [CollatzResearch.WordTrace]
  refine ⟨206091577854120432684921029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137394385236080288456614019 206091577854120432684921029)
  ·
    refine ⟨38642170847647581128422693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206091577854120432684921029 38642170847647581128422693)
    ·
      refine ⟨7245407033933921461579255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38642170847647581128422693 7245407033933921461579255)
      ·
        refine ⟨10868110550900882192368883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7245407033933921461579255 10868110550900882192368883)
        ·
          refine ⟨16302165826351323288553325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10868110550900882192368883 16302165826351323288553325)
          ·
            refine ⟨6113312184881746233207497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16302165826351323288553325 6113312184881746233207497)
            ·
              refine ⟨4584984138661309674905623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6113312184881746233207497 4584984138661309674905623)
              ·
                refine ⟨6877476207991964512358435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4584984138661309674905623 6877476207991964512358435)
                ·
                  refine ⟨10316214311987946768537653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877476207991964512358435 10316214311987946768537653)
                  ·
                    refine ⟨967145091748870009550405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10316214311987946768537653 967145091748870009550405)
                    ·
                      rfl

theorem cell23_5650525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5650525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650525 prefixEnd_5650525 := by exact prefixLift 5650525
  have htrace : WordTrace (prefixWord ++ tailWord_5650525) baseStart_5650525 baseEnd_5650525 := by
    simpa [prefixWord, tailWord_5650525, baseEnd_5650525] using wordTrace_append hprefix tailTrace_5650525
  have hstable : (prefixWord ++ tailWord_5650525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650525).length < 2 ^ (prefixWord ++ tailWord_5650525).sum := by decide
  have hdescent : baseEnd_5650525 < baseStart_5650525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650528 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 1, 1, 4]
def baseStart_5650528 : Nat := 118140960795 + 5650528 * 2 ^ 59
def prefixEnd_5650528 : Nat := 4983230072969 + 3 ^ 40 * 5650528 * 2
def baseEnd_5650528 : Nat := 2901436815688573516913701

theorem tailTrace_5650528 : CollatzResearch.WordTrace tailWord_5650528 prefixEnd_5650528 2901436815688573516913701 := by
  unfold tailWord_5650528
  simp only [CollatzResearch.WordTrace]
  refine ⟨103045843636554782098640119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137394458182073042798186825 103045843636554782098640119)
  ·
    refine ⟨154568765454832173147960179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103045843636554782098640119 154568765454832173147960179)
    ·
      refine ⟨231853148182248259721940269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154568765454832173147960179 231853148182248259721940269)
      ·
        refine ⟨86944930568343097395727601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231853148182248259721940269 86944930568343097395727601)
        ·
          refine ⟨65208697926257323046795701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86944930568343097395727601 65208697926257323046795701)
          ·
            refine ⟨6113315430586624035637097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65208697926257323046795701 6113315430586624035637097)
            ·
              refine ⟨4584986572939968026727823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6113315430586624035637097 4584986572939968026727823)
              ·
                refine ⟨6877479859409952040091735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4584986572939968026727823 6877479859409952040091735)
                ·
                  refine ⟨10316219789114928060137603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877479859409952040091735 10316219789114928060137603)
                  ·
                    refine ⟨15474329683672392090206405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10316219789114928060137603 15474329683672392090206405)
                    ·
                      refine ⟨2901436815688573516913701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15474329683672392090206405 2901436815688573516913701)
                      ·
                        rfl

theorem cell23_5650528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_5650528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650528 prefixEnd_5650528 := by exact prefixLift 5650528
  have htrace : WordTrace (prefixWord ++ tailWord_5650528) baseStart_5650528 baseEnd_5650528 := by
    simpa [prefixWord, tailWord_5650528, baseEnd_5650528] using wordTrace_append hprefix tailTrace_5650528
  have hstable : (prefixWord ++ tailWord_5650528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650528).length < 2 ^ (prefixWord ++ tailWord_5650528).sum := by decide
  have hdescent : baseEnd_5650528 < baseStart_5650528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650588 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_5650588 : Nat := 118140960795 + 5650588 * 2 ^ 59
def prefixEnd_5650588 : Nat := 4983230072969 + 3 ^ 40 * 5650588 * 2
def baseEnd_5650588 : Nat := 2901467624527843282163425

theorem tailTrace_5650588 : CollatzResearch.WordTrace tailWord_5650588 prefixEnd_5650588 2901467624527843282163425 := by
  unfold tailWord_5650588
  simp only [CollatzResearch.WordTrace]
  refine ⟨103046937826446097222232209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137395917101928129629642945 103046937826446097222232209)
  ·
    refine ⟨77285203369834572916674157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103046937826446097222232209 77285203369834572916674157)
    ·
      refine ⟨28981951263687964843752809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77285203369834572916674157 28981951263687964843752809)
      ·
        refine ⟨21736463447765973632814607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28981951263687964843752809 21736463447765973632814607)
        ·
          refine ⟨32604695171648960449221911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21736463447765973632814607 32604695171648960449221911)
          ·
            refine ⟨48907042757473440673832867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32604695171648960449221911 48907042757473440673832867)
            ·
              refine ⟨73360564136210161010749301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48907042757473440673832867 73360564136210161010749301)
              ·
                refine ⟨6877552887769702594757747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73360564136210161010749301 6877552887769702594757747)
                ·
                  refine ⟨10316329331654553892136621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877552887769702594757747 10316329331654553892136621)
                  ·
                    refine ⟨3868623499370457709551233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10316329331654553892136621 3868623499370457709551233)
                    ·
                      refine ⟨2901467624527843282163425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868623499370457709551233 2901467624527843282163425)
                      ·
                        rfl

theorem cell23_5650588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_5650588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650588 prefixEnd_5650588 := by exact prefixLift 5650588
  have htrace : WordTrace (prefixWord ++ tailWord_5650588) baseStart_5650588 baseEnd_5650588 := by
    simpa [prefixWord, tailWord_5650588, baseEnd_5650588] using wordTrace_append hprefix tailTrace_5650588
  have hstable : (prefixWord ++ tailWord_5650588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650588).length < 2 ^ (prefixWord ++ tailWord_5650588).sum := by decide
  have hdescent : baseEnd_5650588 < baseStart_5650588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650622 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_5650622 : Nat := 118140960795 + 5650622 * 2 ^ 59
def prefixEnd_5650622 : Nat := 4983230072969 + 3 ^ 40 * 5650622 * 2
def baseEnd_5650622 : Nat := 2901485082870096149138269

theorem tailTrace_5650622 : CollatzResearch.WordTrace tailWord_5650622 prefixEnd_5650622 2901485082870096149138269 := by
  unfold tailWord_5650622
  simp only [CollatzResearch.WordTrace]
  refine ⟨25761889466846127281400265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137396743823179345500801413 25761889466846127281400265)
  ·
    refine ⟨19321417100134595461050199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25761889466846127281400265 19321417100134595461050199)
    ·
      refine ⟨28982125650201893191575299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19321417100134595461050199 28982125650201893191575299)
      ·
        refine ⟨43473188475302839787362949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28982125650201893191575299 43473188475302839787362949)
        ·
          refine ⟨8151222839119282460130553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43473188475302839787362949 8151222839119282460130553)
          ·
            refine ⟨6113417129339461845097915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8151222839119282460130553 6113417129339461845097915)
            ·
              refine ⟨9170125694009192767646873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113417129339461845097915 9170125694009192767646873)
              ·
                refine ⟨6877594270506894575735155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9170125694009192767646873 6877594270506894575735155)
                ·
                  refine ⟨10316391405760341863602733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877594270506894575735155 10316391405760341863602733)
                  ·
                    refine ⟨3868646777160128198851025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10316391405760341863602733 3868646777160128198851025)
                    ·
                      refine ⟨2901485082870096149138269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868646777160128198851025 2901485082870096149138269)
                      ·
                        rfl

theorem cell23_5650622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_5650622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650622 prefixEnd_5650622 := by exact prefixLift 5650622
  have htrace : WordTrace (prefixWord ++ tailWord_5650622) baseStart_5650622 baseEnd_5650622 := by
    simpa [prefixWord, tailWord_5650622, baseEnd_5650622] using wordTrace_append hprefix tailTrace_5650622
  have hstable : (prefixWord ++ tailWord_5650622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650622).length < 2 ^ (prefixWord ++ tailWord_5650622).sum := by decide
  have hdescent : baseEnd_5650622 < baseStart_5650622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650691 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 1, 6, 2]
def baseStart_5650691 : Nat := 118140960795 + 5650691 * 2 ^ 59
def prefixEnd_5650691 : Nat := 4983230072969 + 3 ^ 40 * 5650691 * 2
def baseEnd_5650691 : Nat := 2901520513035256379175451

theorem tailTrace_5650691 : CollatzResearch.WordTrace tailWord_5650691 prefixEnd_5650691 2901520513035256379175451 := by
  unfold tailWord_5650691
  simp only [CollatzResearch.WordTrace]
  refine ⟨206097632371519043035463927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137398421581012695356975951 206097632371519043035463927)
  ·
    refine ⟨309146448557278564553195891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206097632371519043035463927 309146448557278564553195891)
    ·
      refine ⟨463719672835917846829793837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309146448557278564553195891 463719672835917846829793837)
      ·
        refine ⟨173894877313469192561172689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 463719672835917846829793837 173894877313469192561172689)
        ·
          refine ⟨130421157985101894420879517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173894877313469192561172689 130421157985101894420879517)
          ·
            refine ⟨48907934244413210407829819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130421157985101894420879517 48907934244413210407829819)
            ·
              refine ⟨73361901366619815611744729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48907934244413210407829819 73361901366619815611744729)
              ·
                refine ⟨55021426024964861708808547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73361901366619815611744729 55021426024964861708808547)
                ·
                  refine ⟨82532139037447292563212821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55021426024964861708808547 82532139037447292563212821)
                  ·
                    refine ⟨3868694017380341838900601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82532139037447292563212821 3868694017380341838900601)
                    ·
                      refine ⟨2901520513035256379175451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868694017380341838900601 2901520513035256379175451)
                      ·
                        rfl

theorem cell23_5650691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_5650691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650691 prefixEnd_5650691 := by exact prefixLift 5650691
  have htrace : WordTrace (prefixWord ++ tailWord_5650691) baseStart_5650691 baseEnd_5650691 := by
    simpa [prefixWord, tailWord_5650691, baseEnd_5650691] using wordTrace_append hprefix tailTrace_5650691
  have hstable : (prefixWord ++ tailWord_5650691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650691).length < 2 ^ (prefixWord ++ tailWord_5650691).sum := by decide
  have hdescent : baseEnd_5650691 < baseStart_5650691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650741 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_5650741 : Nat := 118140960795 + 5650741 * 2 ^ 59
def prefixEnd_5650741 : Nat := 4983230072969 + 3 ^ 40 * 5650741 * 2
def baseEnd_5650741 : Nat := 2901546187067981183550221

theorem tailTrace_5650741 : CollatzResearch.WordTrace tailWord_5650741 prefixEnd_5650741 2901546187067981183550221 := by
  unfold tailWord_5650741
  simp only [CollatzResearch.WordTrace]
  refine ⟨206099456021337901574784077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137399637347558601049856051 206099456021337901574784077)
  ·
    refine ⟨77287296008001713090544029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206099456021337901574784077 77287296008001713090544029)
    ·
      refine ⟨28982736003000642408954011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77287296008001713090544029 28982736003000642408954011)
      ·
        refine ⟨43474104004500963613431017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28982736003000642408954011 43474104004500963613431017)
        ·
          refine ⟨32605578003375722710073263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43474104004500963613431017 32605578003375722710073263)
          ·
            refine ⟨48908367005063584065109895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32605578003375722710073263 48908367005063584065109895)
            ·
              refine ⟨73362550507595376097664843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48908367005063584065109895 73362550507595376097664843)
              ·
                refine ⟨110043825761393064146497265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73362550507595376097664843 110043825761393064146497265)
                ·
                  refine ⟨82532869321044798109872949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110043825761393064146497265 82532869321044798109872949)
                  ·
                    refine ⟨7737456498847949822800589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82532869321044798109872949 7737456498847949822800589)
                    ·
                      refine ⟨2901546187067981183550221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7737456498847949822800589 2901546187067981183550221)
                      ·
                        rfl

theorem cell23_5650741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_5650741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650741 prefixEnd_5650741 := by exact prefixLift 5650741
  have htrace : WordTrace (prefixWord ++ tailWord_5650741) baseStart_5650741 baseEnd_5650741 := by
    simpa [prefixWord, tailWord_5650741, baseEnd_5650741] using wordTrace_append hprefix tailTrace_5650741
  have hstable : (prefixWord ++ tailWord_5650741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650741).length < 2 ^ (prefixWord ++ tailWord_5650741).sum := by decide
  have hdescent : baseEnd_5650741 < baseStart_5650741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650768 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 4, 3, 2]
def baseStart_5650768 : Nat := 118140960795 + 5650768 * 2 ^ 59
def prefixEnd_5650768 : Nat := 4983230072969 + 3 ^ 40 * 5650768 * 2
def baseEnd_5650768 : Nat := 2901560051045652577912597

theorem tailTrace_5650768 : CollatzResearch.WordTrace tailWord_5650768 prefixEnd_5650768 2901560051045652577912597 := by
  unfold tailWord_5650768
  simp only [CollatzResearch.WordTrace]
  refine ⟨103050220396120042593008479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137400293861493390124011305 103050220396120042593008479)
  ·
    refine ⟨154575330594180063889512719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103050220396120042593008479 154575330594180063889512719)
    ·
      refine ⟨231862995891270095834269079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154575330594180063889512719 231862995891270095834269079)
      ·
        refine ⟨347794493836905143751403619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231862995891270095834269079 347794493836905143751403619)
        ·
          refine ⟨521691740755357715627105429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347794493836905143751403619 521691740755357715627105429)
          ·
            refine ⟨24454300347907392920020567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 521691740755357715627105429 24454300347907392920020567)
            ·
              refine ⟨36681450521861089380030851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24454300347907392920020567 36681450521861089380030851)
              ·
                refine ⟨55022175782791634070046277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36681450521861089380030851 55022175782791634070046277)
                ·
                  refine ⟨10316657959273431388133677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55022175782791634070046277 10316657959273431388133677)
                  ·
                    refine ⟨3868746734727536770550129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10316657959273431388133677 3868746734727536770550129)
                    ·
                      refine ⟨2901560051045652577912597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868746734727536770550129 2901560051045652577912597)
                      ·
                        rfl

theorem cell23_5650768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 3, 2].length) (baseStart_5650768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650768 prefixEnd_5650768 := by exact prefixLift 5650768
  have htrace : WordTrace (prefixWord ++ tailWord_5650768) baseStart_5650768 baseEnd_5650768 := by
    simpa [prefixWord, tailWord_5650768, baseEnd_5650768] using wordTrace_append hprefix tailTrace_5650768
  have hstable : (prefixWord ++ tailWord_5650768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650768).length < 2 ^ (prefixWord ++ tailWord_5650768).sum := by decide
  have hdescent : baseEnd_5650768 < baseStart_5650768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650811 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 4]
def baseStart_5650811 : Nat := 118140960795 + 5650811 * 2 ^ 59
def prefixEnd_5650811 : Nat := 4983230072969 + 3 ^ 40 * 5650811 * 2
def baseEnd_5650811 : Nat := 2901582130713795909674899

theorem tailTrace_5650811 : CollatzResearch.WordTrace tailWord_5650811 prefixEnd_5650811 2901582130713795909674899 := by
  unfold tailWord_5650811
  simp only [CollatzResearch.WordTrace]
  refine ⟨206102009131084303529832287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137401339420722869019888191 206102009131084303529832287)
  ·
    refine ⟨309153013696626455294748431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206102009131084303529832287 309153013696626455294748431)
    ·
      refine ⟨463729520544939682942122647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309153013696626455294748431 463729520544939682942122647)
      ·
        refine ⟨695594280817409524413183971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463729520544939682942122647 695594280817409524413183971)
        ·
          refine ⟨1043391421226114286619775957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695594280817409524413183971 1043391421226114286619775957)
          ·
            refine ⟨24454486434987053592650999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1043391421226114286619775957 24454486434987053592650999)
            ·
              refine ⟨36681729652480580388976499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24454486434987053592650999 36681729652480580388976499)
              ·
                refine ⟨55022594478720870583464749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36681729652480580388976499 55022594478720870583464749)
                ·
                  refine ⟨20633472929520326468799281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55022594478720870583464749 20633472929520326468799281)
                  ·
                    refine ⟨15475104697140244851599461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20633472929520326468799281 15475104697140244851599461)
                    ·
                      refine ⟨2901582130713795909674899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15475104697140244851599461 2901582130713795909674899)
                      ·
                        rfl

theorem cell23_5650811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 4].length) (baseStart_5650811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650811 prefixEnd_5650811 := by exact prefixLift 5650811
  have htrace : WordTrace (prefixWord ++ tailWord_5650811) baseStart_5650811 baseEnd_5650811 := by
    simpa [prefixWord, tailWord_5650811, baseEnd_5650811] using wordTrace_append hprefix tailTrace_5650811
  have hstable : (prefixWord ++ tailWord_5650811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650811).length < 2 ^ (prefixWord ++ tailWord_5650811).sum := by decide
  have hdescent : baseEnd_5650811 < baseStart_5650811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650825 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 2, 4]
def baseStart_5650825 : Nat := 118140960795 + 5650825 * 2 ^ 59
def prefixEnd_5650825 : Nat := 4983230072969 + 3 ^ 40 * 5650825 * 2
def baseEnd_5650825 : Nat := 967196439814319618299945

theorem tailTrace_5650825 : CollatzResearch.WordTrace tailWord_5650825 prefixEnd_5650825 967196439814319618299945 := by
  unfold tailWord_5650825
  simp only [CollatzResearch.WordTrace]
  refine ⟨206102519753033583920841929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137401679835355722613894619 206102519753033583920841929)
  ·
    refine ⟨154576889814775187940631447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206102519753033583920841929 154576889814775187940631447)
    ·
      refine ⟨231865334722162781910947171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154576889814775187940631447 231865334722162781910947171)
      ·
        refine ⟨347798002083244172866420757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231865334722162781910947171 347798002083244172866420757)
        ·
          refine ⟨16303031347652070603113473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 347798002083244172866420757 16303031347652070603113473)
          ·
            refine ⟨12227273510739052952335105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16303031347652070603113473 12227273510739052952335105)
            ·
              refine ⟨9170455133054289714251329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12227273510739052952335105 9170455133054289714251329)
              ·
                refine ⟨6877841349790717285688497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9170455133054289714251329 6877841349790717285688497)
                ·
                  refine ⟨5158381012343037964266373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6877841349790717285688497 5158381012343037964266373)
                  ·
                    refine ⟨967196439814319618299945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5158381012343037964266373 967196439814319618299945)
                    ·
                      rfl

theorem cell23_5650825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 4].length) (baseStart_5650825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650825 prefixEnd_5650825 := by exact prefixLift 5650825
  have htrace : WordTrace (prefixWord ++ tailWord_5650825) baseStart_5650825 baseEnd_5650825 := by
    simpa [prefixWord, tailWord_5650825, baseEnd_5650825] using wordTrace_append hprefix tailTrace_5650825
  have hstable : (prefixWord ++ tailWord_5650825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650825).length < 2 ^ (prefixWord ++ tailWord_5650825).sum := by decide
  have hdescent : baseEnd_5650825 < baseStart_5650825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650845 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_5650845 : Nat := 118140960795 + 5650845 * 2 ^ 59
def prefixEnd_5650845 : Nat := 4983230072969 + 3 ^ 40 * 5650845 * 2
def baseEnd_5650845 : Nat := 2901599589056048776649743

theorem tailTrace_5650845 : CollatzResearch.WordTrace tailWord_5650845 prefixEnd_5650845 2901599589056048776649743 := by
  unfold tailWord_5650845
  simp only [CollatzResearch.WordTrace]
  refine ⟨206103249212961127336569989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137402166141974084891046659 206103249212961127336569989)
  ·
    refine ⟨38644359227430211375606873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206103249212961127336569989 38644359227430211375606873)
    ·
      refine ⟨28983269420572658531705155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38644359227430211375606873 28983269420572658531705155)
      ·
        refine ⟨43474904130858987797557733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28983269420572658531705155 43474904130858987797557733)
        ·
          refine ⟨8151544524536060212042075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43474904130858987797557733 8151544524536060212042075)
          ·
            refine ⟨12227316786804090318063113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151544524536060212042075 12227316786804090318063113)
            ·
              refine ⟨9170487590103067738547335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12227316786804090318063113 9170487590103067738547335)
              ·
                refine ⟨13755731385154601607821003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9170487590103067738547335 13755731385154601607821003)
                ·
                  refine ⟨20633597077731902411731505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13755731385154601607821003 20633597077731902411731505)
                  ·
                    refine ⟨15475197808298926808798629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20633597077731902411731505 15475197808298926808798629)
                    ·
                      refine ⟨2901599589056048776649743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15475197808298926808798629 2901599589056048776649743)
                      ·
                        rfl

theorem cell23_5650845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_5650845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650845 prefixEnd_5650845 := by exact prefixLift 5650845
  have htrace : WordTrace (prefixWord ++ tailWord_5650845) baseStart_5650845 baseEnd_5650845 := by
    simpa [prefixWord, tailWord_5650845, baseEnd_5650845] using wordTrace_append hprefix tailTrace_5650845
  have hstable : (prefixWord ++ tailWord_5650845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650845).length < 2 ^ (prefixWord ++ tailWord_5650845).sum := by decide
  have hdescent : baseEnd_5650845 < baseStart_5650845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650848 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 3]
def baseStart_5650848 : Nat := 118140960795 + 5650848 * 2 ^ 59
def prefixEnd_5650848 : Nat := 4983230072969 + 3 ^ 40 * 5650848 * 2
def baseEnd_5650848 : Nat := 2901601129498012264912229

theorem tailTrace_5650848 : CollatzResearch.WordTrace tailWord_5650848 prefixEnd_5650848 2901601129498012264912229 := by
  unfold tailWord_5650848
  simp only [CollatzResearch.WordTrace]
  refine ⟨103051679315975129424464599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137402239087966839232619465 103051679315975129424464599)
  ·
    refine ⟨154577518973962694136696899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103051679315975129424464599 154577518973962694136696899)
    ·
      refine ⟨231866278460944041205045349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154577518973962694136696899 231866278460944041205045349)
      ·
        refine ⟨43474927211427007725946003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231866278460944041205045349 43474927211427007725946003)
        ·
          refine ⟨65212390817140511588919005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43474927211427007725946003 65212390817140511588919005)
          ·
            refine ⟨24454646556427691845844627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65212390817140511588919005 24454646556427691845844627)
            ·
              refine ⟨36681969834641537768766941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24454646556427691845844627 36681969834641537768766941)
              ·
                refine ⟨13755738687990576663287603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36681969834641537768766941 13755738687990576663287603)
                ·
                  refine ⟨20633608031985864994931405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13755738687990576663287603 20633608031985864994931405)
                  ·
                    refine ⟨7737603011994699373099277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20633608031985864994931405 7737603011994699373099277)
                    ·
                      refine ⟨2901601129498012264912229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7737603011994699373099277 2901601129498012264912229)
                      ·
                        rfl

theorem cell23_5650848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_5650848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650848 prefixEnd_5650848 := by exact prefixLift 5650848
  have htrace : WordTrace (prefixWord ++ tailWord_5650848) baseStart_5650848 baseEnd_5650848 := by
    simpa [prefixWord, tailWord_5650848, baseEnd_5650848] using wordTrace_append hprefix tailTrace_5650848
  have hstable : (prefixWord ++ tailWord_5650848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650848).length < 2 ^ (prefixWord ++ tailWord_5650848).sum := by decide
  have hdescent : baseEnd_5650848 < baseStart_5650848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650849 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5650849 : Nat := 118140960795 + 5650849 * 2 ^ 59
def prefixEnd_5650849 : Nat := 4983230072969 + 3 ^ 40 * 5650849 * 2
def baseEnd_5650849 : Nat := 2901601642978666760999725

theorem tailTrace_5650849 : CollatzResearch.WordTrace tailWord_5650849 prefixEnd_5650849 2901601642978666760999725 := by
  unfold tailWord_5650849
  simp only [CollatzResearch.WordTrace]
  refine ⟨206103395104946636019715601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137402263403297757346477067 206103395104946636019715601)
  ·
    refine ⟨154577546328709977014786701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206103395104946636019715601 154577546328709977014786701)
    ·
      refine ⟨57966579873266241380545013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154577546328709977014786701 57966579873266241380545013)
      ·
        refine ⟨5434366863118710129426095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57966579873266241380545013 5434366863118710129426095)
        ·
          refine ⟨8151550294678065194139143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434366863118710129426095 8151550294678065194139143)
          ·
            refine ⟨12227325442017097791208715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151550294678065194139143 12227325442017097791208715)
            ·
              refine ⟨18340988163025646686813073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12227325442017097791208715 18340988163025646686813073)
              ·
                refine ⟨13755741122269235015109805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18340988163025646686813073 13755741122269235015109805)
                ·
                  refine ⟨5158402920850963130666177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13755741122269235015109805 5158402920850963130666177)
                  ·
                    refine ⟨3868802190638222347999633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5158402920850963130666177 3868802190638222347999633)
                    ·
                      refine ⟨2901601642978666760999725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868802190638222347999633 2901601642978666760999725)
                      ·
                        rfl

theorem cell23_5650849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5650849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650849 prefixEnd_5650849 := by exact prefixLift 5650849
  have htrace : WordTrace (prefixWord ++ tailWord_5650849) baseStart_5650849 baseEnd_5650849 := by
    simpa [prefixWord, tailWord_5650849, baseEnd_5650849] using wordTrace_append hprefix tailTrace_5650849
  have hstable : (prefixWord ++ tailWord_5650849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650849).length < 2 ^ (prefixWord ++ tailWord_5650849).sum := by decide
  have hdescent : baseEnd_5650849 < baseStart_5650849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650869 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_5650869 : Nat := 118140960795 + 5650869 * 2 ^ 59
def prefixEnd_5650869 : Nat := 4983230072969 + 3 ^ 40 * 5650869 * 2
def baseEnd_5650869 : Nat := 2901611912591756682749633

theorem tailTrace_5650869 : CollatzResearch.WordTrace tailWord_5650869 prefixEnd_5650869 2901611912591756682749633 := by
  unfold tailWord_5650869
  simp only [CollatzResearch.WordTrace]
  refine ⟨206104124564874179435443661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137402749709916119623629107 206104124564874179435443661)
  ·
    refine ⟨77289046711827817288291373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206104124564874179435443661 77289046711827817288291373)
    ·
      refine ⟨28983392516935431483109265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77289046711827817288291373 28983392516935431483109265)
      ·
        refine ⟨21737544387701573612331949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28983392516935431483109265 21737544387701573612331949)
        ·
          refine ⟨8151579145388090104624481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21737544387701573612331949 8151579145388090104624481)
          ·
            refine ⟨6113684359041067578468361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8151579145388090104624481 6113684359041067578468361)
            ·
              refine ⟨4585263269280800683851271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6113684359041067578468361 4585263269280800683851271)
              ·
                refine ⟨6877894903921201025776907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4585263269280800683851271 6877894903921201025776907)
                ·
                  refine ⟨10316842355881801538665361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877894903921201025776907 10316842355881801538665361)
                  ·
                    refine ⟨7737631766911351153999021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10316842355881801538665361 7737631766911351153999021)
                    ·
                      refine ⟨2901611912591756682749633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7737631766911351153999021 2901611912591756682749633)
                      ·
                        rfl

theorem cell23_5650869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_5650869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650869 prefixEnd_5650869 := by exact prefixLift 5650869
  have htrace : WordTrace (prefixWord ++ tailWord_5650869) baseStart_5650869 baseEnd_5650869 := by
    simpa [prefixWord, tailWord_5650869, baseEnd_5650869] using wordTrace_append hprefix tailTrace_5650869
  have hstable : (prefixWord ++ tailWord_5650869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650869).length < 2 ^ (prefixWord ++ tailWord_5650869).sum := by decide
  have hdescent : baseEnd_5650869 < baseStart_5650869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650891 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 5]
def baseStart_5650891 : Nat := 118140960795 + 5650891 * 2 ^ 59
def prefixEnd_5650891 : Nat := 4983230072969 + 3 ^ 40 * 5650891 * 2
def baseEnd_5650891 : Nat := 2901623209166155596674531

theorem tailTrace_5650891 : CollatzResearch.WordTrace tailWord_5650891 prefixEnd_5650891 2901623209166155596674531 := by
  unfold tailWord_5650891
  simp only [CollatzResearch.WordTrace]
  refine ⟨206104926970794477192744527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137403284647196318128496351 206104926970794477192744527)
  ·
    refine ⟨309157390456191715789116791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206104926970794477192744527 309157390456191715789116791)
    ·
      refine ⟨463736085684287573683675187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309157390456191715789116791 463736085684287573683675187)
      ·
        refine ⟨695604128526431360525512781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463736085684287573683675187 695604128526431360525512781)
        ·
          refine ⟨260851548197411760197067293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695604128526431360525512781 260851548197411760197067293)
          ·
            refine ⟨97819330574029410073900235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260851548197411760197067293 97819330574029410073900235)
            ·
              refine ⟨146728995861044115110850353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97819330574029410073900235 146728995861044115110850353)
              ·
                refine ⟨110046746895783086333137765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146728995861044115110850353 110046746895783086333137765)
                ·
                  refine ⟨20633765042959328687463331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110046746895783086333137765 20633765042959328687463331)
                  ·
                    refine ⟨30950647564438993031194997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20633765042959328687463331 30950647564438993031194997)
                    ·
                      refine ⟨2901623209166155596674531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30950647564438993031194997 2901623209166155596674531)
                      ·
                        rfl

theorem cell23_5650891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_5650891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650891 prefixEnd_5650891 := by exact prefixLift 5650891
  have htrace : WordTrace (prefixWord ++ tailWord_5650891) baseStart_5650891 baseEnd_5650891 := by
    simpa [prefixWord, tailWord_5650891, baseEnd_5650891] using wordTrace_append hprefix tailTrace_5650891
  have hstable : (prefixWord ++ tailWord_5650891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650891).length < 2 ^ (prefixWord ++ tailWord_5650891).sum := by decide
  have hdescent : baseEnd_5650891 < baseStart_5650891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650922 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_5650922 : Nat := 118140960795 + 5650922 * 2 ^ 59
def prefixEnd_5650922 : Nat := 4983230072969 + 3 ^ 40 * 5650922 * 2
def baseEnd_5650922 : Nat := 2901639127066444975386889

theorem tailTrace_5650922 : CollatzResearch.WordTrace tailWord_5650922 prefixEnd_5650922 2901639127066444975386889 := by
  unfold tailWord_5650922
  simp only [CollatzResearch.WordTrace]
  refine ⟨51526514408420542371780755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137404038422454779658082013 51526514408420542371780755)
  ·
    refine ⟨77289771612630813557671133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51526514408420542371780755 77289771612630813557671133)
    ·
      refine ⟨28983664354736555084126675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77289771612630813557671133 28983664354736555084126675)
      ·
        refine ⟨43475496532104832626190013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28983664354736555084126675 43475496532104832626190013)
        ·
          refine ⟨16303311199539312234821255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43475496532104832626190013 16303311199539312234821255)
          ·
            refine ⟨24454966799308968352231883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16303311199539312234821255 24454966799308968352231883)
            ·
              refine ⟨36682450198963452528347825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24454966799308968352231883 36682450198963452528347825)
              ·
                refine ⟨27511837649222589396260869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36682450198963452528347825 27511837649222589396260869)
                ·
                  refine ⟨5158469559229235511798913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27511837649222589396260869 5158469559229235511798913)
                  ·
                    refine ⟨3868852169421926633849185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5158469559229235511798913 3868852169421926633849185)
                    ·
                      refine ⟨2901639127066444975386889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868852169421926633849185 2901639127066444975386889)
                      ·
                        rfl

theorem cell23_5650922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_5650922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650922 prefixEnd_5650922 := by exact prefixLift 5650922
  have htrace : WordTrace (prefixWord ++ tailWord_5650922) baseStart_5650922 baseEnd_5650922 := by
    simpa [prefixWord, tailWord_5650922, baseEnd_5650922] using wordTrace_append hprefix tailTrace_5650922
  have hstable : (prefixWord ++ tailWord_5650922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650922).length < 2 ^ (prefixWord ++ tailWord_5650922).sum := by decide
  have hdescent : baseEnd_5650922 < baseStart_5650922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650925 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5650925 : Nat := 118140960795 + 5650925 * 2 ^ 59
def prefixEnd_5650925 : Nat := 4983230072969 + 3 ^ 40 * 5650925 * 2
def baseEnd_5650925 : Nat := 2901640667508408463649375

theorem tailTrace_5650925 : CollatzResearch.WordTrace tailWord_5650925 prefixEnd_5650925 2901640667508408463649375 := by
  unfold tailWord_5650925
  simp only [CollatzResearch.WordTrace]
  refine ⟨206106167052671300999482229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137404111368447533999654819 206106167052671300999482229)
  ·
    refine ⟨19322453161187934468701459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206106167052671300999482229 19322453161187934468701459)
    ·
      refine ⟨28983679741781901703052189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19322453161187934468701459 28983679741781901703052189)
      ·
        refine ⟨10868879903168213138644571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28983679741781901703052189 10868879903168213138644571)
        ·
          refine ⟨16303319854752319707966857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10868879903168213138644571 16303319854752319707966857)
          ·
            refine ⟨12227489891064239780975143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16303319854752319707966857 12227489891064239780975143)
            ·
              refine ⟨18341234836596359671462715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12227489891064239780975143 18341234836596359671462715)
              ·
                refine ⟨27511852254894539507194073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18341234836596359671462715 27511852254894539507194073)
                ·
                  refine ⟨20633889191170904630395555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27511852254894539507194073 20633889191170904630395555)
                  ·
                    refine ⟨30950833786756356945593333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20633889191170904630395555 30950833786756356945593333)
                    ·
                      refine ⟨2901640667508408463649375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30950833786756356945593333 2901640667508408463649375)
                      ·
                        rfl

theorem cell23_5650925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5650925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650925 prefixEnd_5650925 := by exact prefixLift 5650925
  have htrace : WordTrace (prefixWord ++ tailWord_5650925) baseStart_5650925 baseEnd_5650925 := by
    simpa [prefixWord, tailWord_5650925, baseEnd_5650925] using wordTrace_append hprefix tailTrace_5650925
  have hstable : (prefixWord ++ tailWord_5650925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650925).length < 2 ^ (prefixWord ++ tailWord_5650925).sum := by decide
  have hdescent : baseEnd_5650925 < baseStart_5650925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650938 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_5650938 : Nat := 118140960795 + 5650938 * 2 ^ 59
def prefixEnd_5650938 : Nat := 4983230072969 + 3 ^ 40 * 5650938 * 2
def baseEnd_5650938 : Nat := 2901647342756916912786815

theorem tailTrace_5650938 : CollatzResearch.WordTrace tailWord_5650938 prefixEnd_5650938 2901647342756916912786815 := by
  unfold tailWord_5650938
  simp only [CollatzResearch.WordTrace]
  refine ⟨51526660300406051054926367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137404427467749469479803645 51526660300406051054926367)
  ·
    refine ⟨77289990450609076582389551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51526660300406051054926367 77289990450609076582389551)
    ·
      refine ⟨115934985675913614873584327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77289990450609076582389551 115934985675913614873584327)
      ·
        refine ⟨173902478513870422310376491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115934985675913614873584327 173902478513870422310376491)
        ·
          refine ⟨260853717770805633465564737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173902478513870422310376491 260853717770805633465564737)
          ·
            refine ⟨195640288328104225099173553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260853717770805633465564737 195640288328104225099173553)
            ·
              refine ⟨146730216246078168824380165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195640288328104225099173553 146730216246078168824380165)
              ·
                refine ⟨27511915546139656654571281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146730216246078168824380165 27511915546139656654571281)
                ·
                  refine ⟨20633936659604742490928461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27511915546139656654571281 20633936659604742490928461)
                  ·
                    refine ⟨7737726247351778434098173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20633936659604742490928461 7737726247351778434098173)
                    ·
                      refine ⟨2901647342756916912786815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7737726247351778434098173 2901647342756916912786815)
                      ·
                        rfl

theorem cell23_5650938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_5650938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650938 prefixEnd_5650938 := by exact prefixLift 5650938
  have htrace : WordTrace (prefixWord ++ tailWord_5650938) baseStart_5650938 baseEnd_5650938 := by
    simpa [prefixWord, tailWord_5650938, baseEnd_5650938] using wordTrace_append hprefix tailTrace_5650938
  have hstable : (prefixWord ++ tailWord_5650938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650938).length < 2 ^ (prefixWord ++ tailWord_5650938).sum := by decide
  have hdescent : baseEnd_5650938 < baseStart_5650938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650945 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 7]
def baseStart_5650945 : Nat := 118140960795 + 5650945 * 2 ^ 59
def prefixEnd_5650945 : Nat := 4983230072969 + 3 ^ 40 * 5650945 * 2
def baseEnd_5650945 : Nat := 322405659680166487266587

theorem tailTrace_5650945 : CollatzResearch.WordTrace tailWord_5650945 prefixEnd_5650945 322405659680166487266587 := by
  unfold tailWord_5650945
  simp only [CollatzResearch.WordTrace]
  refine ⟨206106896512598844415210289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137404597675065896276806859 206106896512598844415210289)
  ·
    refine ⟨154580172384449133311407717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206106896512598844415210289 154580172384449133311407717)
    ·
      refine ⟨28983782322084212495888947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154580172384449133311407717 28983782322084212495888947)
      ·
        refine ⟨43475673483126318743833421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28983782322084212495888947 43475673483126318743833421)
        ·
          refine ⟨16303377556172369528937533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43475673483126318743833421 16303377556172369528937533)
          ·
            refine ⟨6113766583564638573351575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16303377556172369528937533 6113766583564638573351575)
            ·
              refine ⟨9170649875346957860027363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113766583564638573351575 9170649875346957860027363)
              ·
                refine ⟨13755974813020436790041045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9170649875346957860027363 13755974813020436790041045)
                ·
                  refine ⟨322405659680166487266587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13755974813020436790041045 322405659680166487266587)
                  ·
                    rfl

theorem cell23_5650945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 7].length) (baseStart_5650945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650945 prefixEnd_5650945 := by exact prefixLift 5650945
  have htrace : WordTrace (prefixWord ++ tailWord_5650945) baseStart_5650945 baseEnd_5650945 := by
    simpa [prefixWord, tailWord_5650945, baseEnd_5650945] using wordTrace_append hprefix tailTrace_5650945
  have hstable : (prefixWord ++ tailWord_5650945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650945).length < 2 ^ (prefixWord ++ tailWord_5650945).sum := by decide
  have hdescent : baseEnd_5650945 < baseStart_5650945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650950 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_5650950 : Nat := 118140960795 + 5650950 * 2 ^ 59
def prefixEnd_5650950 : Nat := 4983230072969 + 3 ^ 40 * 5650950 * 2
def baseEnd_5650950 : Nat := 2901653504524770865836761

theorem tailTrace_5650950 : CollatzResearch.WordTrace tailWord_5650950 prefixEnd_5650950 2901653504524770865836761 := by
  unfold tailWord_5650950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6440846214924397820910697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137404719251720486846094869 6440846214924397820910697)
  ·
    refine ⟨4830634661193298365683023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6440846214924397820910697 4830634661193298365683023)
    ·
      refine ⟨7245951991789947548524535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830634661193298365683023 7245951991789947548524535)
      ·
        refine ⟨10868927987684921322786803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7245951991789947548524535 10868927987684921322786803)
        ·
          refine ⟨16303391981527381984180205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10868927987684921322786803 16303391981527381984180205)
          ·
            refine ⟨6113771993072768244067577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16303391981527381984180205 6113771993072768244067577)
            ·
              refine ⟨4585328994804576183050683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6113771993072768244067577 4585328994804576183050683)
              ·
                refine ⟨6877993492206864274576025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4585328994804576183050683 6877993492206864274576025)
                ·
                  refine ⟨5158495119155148205932019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6877993492206864274576025 5158495119155148205932019)
                  ·
                    refine ⟨7737742678732722308898029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5158495119155148205932019 7737742678732722308898029)
                    ·
                      refine ⟨2901653504524770865836761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7737742678732722308898029 2901653504524770865836761)
                      ·
                        rfl

theorem cell23_5650950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_5650950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650950 prefixEnd_5650950 := by exact prefixLift 5650950
  have htrace : WordTrace (prefixWord ++ tailWord_5650950) baseStart_5650950 baseEnd_5650950 := by
    simpa [prefixWord, tailWord_5650950, baseEnd_5650950] using wordTrace_append hprefix tailTrace_5650950
  have hstable : (prefixWord ++ tailWord_5650950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650950).length < 2 ^ (prefixWord ++ tailWord_5650950).sum := by decide
  have hdescent : baseEnd_5650950 < baseStart_5650950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650956 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 2, 2, 2]
def baseStart_5650956 : Nat := 118140960795 + 5650956 * 2 ^ 59
def prefixEnd_5650956 : Nat := 4983230072969 + 3 ^ 40 * 5650956 * 2
def baseEnd_5650956 : Nat := 2901656585408697842361733

theorem tailTrace_5650956 : CollatzResearch.WordTrace tailWord_5650956 prefixEnd_5650956 2901656585408697842361733 := by
  unfold tailWord_5650956
  simp only [CollatzResearch.WordTrace]
  refine ⟨103053648857779496646930361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137404865143705995529240481 103053648857779496646930361)
  ·
    refine ⟨77290236643334622485197771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103053648857779496646930361 77290236643334622485197771)
    ·
      refine ⟨115935354965001933727796657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77290236643334622485197771 115935354965001933727796657)
      ·
        refine ⟨86951516223751450295847493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115935354965001933727796657 86951516223751450295847493)
        ·
          refine ⟨16303409291953396930471405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86951516223751450295847493 16303409291953396930471405)
          ·
            refine ⟨6113778484482523848926777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16303409291953396930471405 6113778484482523848926777)
            ·
              refine ⟨4585333863361892886695083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6113778484482523848926777 4585333863361892886695083)
              ·
                refine ⟨6878000795042839330042625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4585333863361892886695083 6878000795042839330042625)
                ·
                  refine ⟨5158500596282129497531969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6878000795042839330042625 5158500596282129497531969)
                  ·
                    refine ⟨3868875447211597123148977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5158500596282129497531969 3868875447211597123148977)
                    ·
                      refine ⟨2901656585408697842361733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868875447211597123148977 2901656585408697842361733)
                      ·
                        rfl

theorem cell23_5650956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_5650956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650956 prefixEnd_5650956 := by exact prefixLift 5650956
  have htrace : WordTrace (prefixWord ++ tailWord_5650956) baseStart_5650956 baseEnd_5650956 := by
    simpa [prefixWord, tailWord_5650956, baseEnd_5650956] using wordTrace_append hprefix tailTrace_5650956
  have hstable : (prefixWord ++ tailWord_5650956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650956).length < 2 ^ (prefixWord ++ tailWord_5650956).sum := by decide
  have hdescent : baseEnd_5650956 < baseStart_5650956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5650995 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 2, 4, 2]
def baseStart_5650995 : Nat := 118140960795 + 5650995 * 2 ^ 59
def prefixEnd_5650995 : Nat := 4983230072969 + 3 ^ 40 * 5650995 * 2
def baseEnd_5650995 : Nat := 2901676611154223189774053

theorem tailTrace_5650995 : CollatzResearch.WordTrace tailWord_5650995 prefixEnd_5650995 2901676611154223189774053 := by
  unfold tailWord_5650995
  simp only [CollatzResearch.WordTrace]
  refine ⟨206108720162417702954530439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137405813441611801969686959 206108720162417702954530439)
  ·
    refine ⟨309163080243626554431795659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206108720162417702954530439 309163080243626554431795659)
    ·
      refine ⟨463744620365439831647693489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309163080243626554431795659 463744620365439831647693489)
      ·
        refine ⟨347808465274079873735770117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463744620365439831647693489 347808465274079873735770117)
        ·
          refine ⟨65214087238889976325456897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347808465274079873735770117 65214087238889976325456897)
          ·
            refine ⟨48910565429167482244092673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65214087238889976325456897 48910565429167482244092673)
            ·
              refine ⟨36682924071875611683069505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48910565429167482244092673 36682924071875611683069505)
              ·
                refine ⟨27512193053906708762302129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36682924071875611683069505 27512193053906708762302129)
                ·
                  refine ⟨20634144790430031571726597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27512193053906708762302129 20634144790430031571726597)
                  ·
                    refine ⟨3868902148205630919698737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20634144790430031571726597 3868902148205630919698737)
                    ·
                      refine ⟨2901676611154223189774053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868902148205630919698737 2901676611154223189774053)
                      ·
                        rfl

theorem cell23_5650995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 4, 2].length) (baseStart_5650995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5650995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5650995 prefixEnd_5650995 := by exact prefixLift 5650995
  have htrace : WordTrace (prefixWord ++ tailWord_5650995) baseStart_5650995 baseEnd_5650995 := by
    simpa [prefixWord, tailWord_5650995, baseEnd_5650995] using wordTrace_append hprefix tailTrace_5650995
  have hstable : (prefixWord ++ tailWord_5650995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5650995).length < 2 ^ (prefixWord ++ tailWord_5650995).sum := by decide
  have hdescent : baseEnd_5650995 < baseStart_5650995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5650995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651095 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 6, 4]
def baseStart_5651095 : Nat := 118140960795 + 5651095 * 2 ^ 59
def prefixEnd_5651095 : Nat := 4983230072969 + 3 ^ 40 * 5651095 * 2
def baseEnd_5651095 : Nat := 967242653073224266174531

theorem tailTrace_5651095 : CollatzResearch.WordTrace tailWord_5651095 prefixEnd_5651095 967242653073224266174531 := by
  unfold tailWord_5651095
  simp only [CollatzResearch.WordTrace]
  refine ⟨206112367462055420033170739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137408244974703613355447159 206112367462055420033170739)
  ·
    refine ⟨309168551193083130049756109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206112367462055420033170739 309168551193083130049756109)
    ·
      refine ⟨115938206697406173768658541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309168551193083130049756109 115938206697406173768658541)
      ·
        refine ⟨43476827511527315163246953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115938206697406173768658541 43476827511527315163246953)
        ·
          refine ⟨32607620633645486372435215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43476827511527315163246953 32607620633645486372435215)
          ·
            refine ⟨48911430950468229558652823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32607620633645486372435215 48911430950468229558652823)
            ·
              refine ⟨73367146425702344337979235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48911430950468229558652823 73367146425702344337979235)
              ·
                refine ⟨110050719638553516506968853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73367146425702344337979235 110050719638553516506968853)
                ·
                  refine ⟨5158627483057196086264165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110050719638553516506968853 5158627483057196086264165)
                  ·
                    refine ⟨967242653073224266174531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5158627483057196086264165 967242653073224266174531)
                    ·
                      rfl

theorem cell23_5651095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_5651095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651095 prefixEnd_5651095 := by exact prefixLift 5651095
  have htrace : WordTrace (prefixWord ++ tailWord_5651095) baseStart_5651095 baseEnd_5651095 := by
    simpa [prefixWord, tailWord_5651095, baseEnd_5651095] using wordTrace_append hprefix tailTrace_5651095
  have hstable : (prefixWord ++ tailWord_5651095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651095).length < 2 ^ (prefixWord ++ tailWord_5651095).sum := by decide
  have hdescent : baseEnd_5651095 < baseStart_5651095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651119 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 3, 2, 2]
def baseStart_5651119 : Nat := 118140960795 + 5651119 * 2 ^ 59
def prefixEnd_5651119 : Nat := 4983230072969 + 3 ^ 40 * 5651119 * 2
def baseEnd_5651119 : Nat := 2901740282755380704623483

theorem tailTrace_5651119 : CollatzResearch.WordTrace tailWord_5651119 prefixEnd_5651119 2901740282755380704623483 := by
  unfold tailWord_5651119
  simp only [CollatzResearch.WordTrace]
  refine ⟨206113242813968472132044411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137408828542645648088029607 206113242813968472132044411)
  ·
    refine ⟨309169864220952708198066617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206113242813968472132044411 309169864220952708198066617)
    ·
      refine ⟨231877398165714531148549963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309169864220952708198066617 231877398165714531148549963)
      ·
        refine ⟨347816097248571796722824945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231877398165714531148549963 347816097248571796722824945)
        ·
          refine ⟨260862072936428847542118709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347816097248571796722824945 260862072936428847542118709)
          ·
            refine ⟨24455819337790204457073629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260862072936428847542118709 24455819337790204457073629)
            ·
              refine ⟨9170932251671326671402611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24455819337790204457073629 9170932251671326671402611)
              ·
                refine ⟨13756398377506990007103917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9170932251671326671402611 13756398377506990007103917)
                ·
                  refine ⟨5158649391565121252663969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13756398377506990007103917 5158649391565121252663969)
                  ·
                    refine ⟨3868987043673840939497977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5158649391565121252663969 3868987043673840939497977)
                    ·
                      refine ⟨2901740282755380704623483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3868987043673840939497977 2901740282755380704623483)
                      ·
                        rfl

theorem cell23_5651119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 2, 2].length) (baseStart_5651119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651119 prefixEnd_5651119 := by exact prefixLift 5651119
  have htrace : WordTrace (prefixWord ++ tailWord_5651119) baseStart_5651119 baseEnd_5651119 := by
    simpa [prefixWord, tailWord_5651119, baseEnd_5651119] using wordTrace_append hprefix tailTrace_5651119
  have hstable : (prefixWord ++ tailWord_5651119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651119).length < 2 ^ (prefixWord ++ tailWord_5651119).sum := by decide
  have hdescent : baseEnd_5651119 < baseStart_5651119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651125 : List Nat := [1, 3, 3, 3, 1, 1, 1, 10]
def baseStart_5651125 : Nat := 118140960795 + 5651125 * 2 ^ 59
def prefixEnd_5651125 : Nat := 4983230072969 + 3 ^ 40 * 5651125 * 2
def baseEnd_5651125 : Nat := 107471976431085469672165

theorem tailTrace_5651125 : CollatzResearch.WordTrace tailWord_5651125 prefixEnd_5651125 107471976431085469672165 := by
  unfold tailWord_5651125
  simp only [CollatzResearch.WordTrace]
  refine ⟨206113461651946735156762829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137408974434631156771175219 206113461651946735156762829)
  ·
    refine ⟨77292548119480025683786061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206113461651946735156762829 77292548119480025683786061)
    ·
      refine ⟨28984705544805009631419773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77292548119480025683786061 28984705544805009631419773)
      ·
        refine ⟨10869264579301878611782415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28984705544805009631419773 10869264579301878611782415)
        ·
          refine ⟨16303896868952817917673623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10869264579301878611782415 16303896868952817917673623)
          ·
            refine ⟨24455845303429226876510435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16303896868952817917673623 24455845303429226876510435)
            ·
              refine ⟨36683767955143840314765653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24455845303429226876510435 36683767955143840314765653)
              ·
                refine ⟨107471976431085469672165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36683767955143840314765653 107471976431085469672165)
                ·
                  rfl

theorem cell23_5651125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 10].length) (baseStart_5651125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651125 prefixEnd_5651125 := by exact prefixLift 5651125
  have htrace : WordTrace (prefixWord ++ tailWord_5651125) baseStart_5651125 baseEnd_5651125 := by
    simpa [prefixWord, tailWord_5651125, baseEnd_5651125] using wordTrace_append hprefix tailTrace_5651125
  have hstable : (prefixWord ++ tailWord_5651125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651125).length < 2 ^ (prefixWord ++ tailWord_5651125).sum := by decide
  have hdescent : baseEnd_5651125 < baseStart_5651125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651156 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5651156 : Nat := 118140960795 + 5651156 * 2 ^ 59
def prefixEnd_5651156 : Nat := 4983230072969 + 3 ^ 40 * 5651156 * 2
def baseEnd_5651156 : Nat := 2901759281539597059860813

theorem tailTrace_5651156 : CollatzResearch.WordTrace tailWord_5651156 prefixEnd_5651156 2901759281539597059860813 := by
  unfold tailWord_5651156
  simp only [CollatzResearch.WordTrace]
  refine ⟨103057296157417213725570661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137409728209889618300760881 103057296157417213725570661)
  ·
    refine ⟨19323243029515727573544499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103057296157417213725570661 19323243029515727573544499)
    ·
      refine ⟨28984864544273591360316749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19323243029515727573544499 28984864544273591360316749)
      ·
        refine ⟨10869324204102596760118781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28984864544273591360316749 10869324204102596760118781)
        ·
          refine ⟨4075996576538473785044543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10869324204102596760118781 4075996576538473785044543)
          ·
            refine ⟨6113994864807710677566815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075996576538473785044543 6113994864807710677566815)
            ·
              refine ⟨9170992297211566016350223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113994864807710677566815 9170992297211566016350223)
              ·
                refine ⟨13756488445817349024525335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9170992297211566016350223 13756488445817349024525335)
                ·
                  refine ⟨20634732668726023536788003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13756488445817349024525335 20634732668726023536788003)
                  ·
                    refine ⟨30952099003089035305182005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20634732668726023536788003 30952099003089035305182005)
                    ·
                      refine ⟨2901759281539597059860813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30952099003089035305182005 2901759281539597059860813)
                      ·
                        rfl

theorem cell23_5651156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5651156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651156 prefixEnd_5651156 := by exact prefixLift 5651156
  have htrace : WordTrace (prefixWord ++ tailWord_5651156) baseStart_5651156 baseEnd_5651156 := by
    simpa [prefixWord, tailWord_5651156, baseEnd_5651156] using wordTrace_append hprefix tailTrace_5651156
  have hstable : (prefixWord ++ tailWord_5651156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651156).length < 2 ^ (prefixWord ++ tailWord_5651156).sum := by decide
  have hdescent : baseEnd_5651156 < baseStart_5651156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651169 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_5651169 : Nat := 118140960795 + 5651169 * 2 ^ 59
def prefixEnd_5651169 : Nat := 4983230072969 + 3 ^ 40 * 5651169 * 2
def baseEnd_5651169 : Nat := 2901765956788105508998253

theorem tailTrace_5651169 : CollatzResearch.WordTrace tailWord_5651169 prefixEnd_5651169 2901765956788105508998253 := by
  unfold tailWord_5651169
  simp only [CollatzResearch.WordTrace]
  refine ⟨206115066463787330671364561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137410044309191553780909707 206115066463787330671364561)
  ·
    refine ⟨154586299847840498003523421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206115066463787330671364561 154586299847840498003523421)
    ·
      refine ⟨57969862442940186751321283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154586299847840498003523421 57969862442940186751321283)
      ·
        refine ⟨86954793664410280126981925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57969862442940186751321283 86954793664410280126981925)
        ·
          refine ⟨16304023812076927523809111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86954793664410280126981925 16304023812076927523809111)
          ·
            refine ⟨24456035718115391285713667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16304023812076927523809111 24456035718115391285713667)
            ·
              refine ⟨36684053577173086928570501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24456035718115391285713667 36684053577173086928570501)
              ·
                refine ⟨6878260045719953799106969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36684053577173086928570501 6878260045719953799106969)
                ·
                  refine ⟨5158695034289965349330227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6878260045719953799106969 5158695034289965349330227)
                  ·
                    refine ⟨7738042551434948023995341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5158695034289965349330227 7738042551434948023995341)
                    ·
                      refine ⟨2901765956788105508998253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7738042551434948023995341 2901765956788105508998253)
                      ·
                        rfl

theorem cell23_5651169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_5651169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651169 prefixEnd_5651169 := by exact prefixLift 5651169
  have htrace : WordTrace (prefixWord ++ tailWord_5651169) baseStart_5651169 baseEnd_5651169 := by
    simpa [prefixWord, tailWord_5651169, baseEnd_5651169] using wordTrace_append hprefix tailTrace_5651169
  have hstable : (prefixWord ++ tailWord_5651169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651169).length < 2 ^ (prefixWord ++ tailWord_5651169).sum := by decide
  have hdescent : baseEnd_5651169 < baseStart_5651169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651185 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 2, 6]
def baseStart_5651185 : Nat := 118140960795 + 5651185 * 2 ^ 59
def prefixEnd_5651185 : Nat := 4983230072969 + 3 ^ 40 * 5651185 * 2
def baseEnd_5651185 : Nat := 967258057492859148799393

theorem tailTrace_5651185 : CollatzResearch.WordTrace tailWord_5651185 prefixEnd_5651185 967258057492859148799393 := by
  unfold tailWord_5651185
  simp only [CollatzResearch.WordTrace]
  refine ⟨206115650031729365403947009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137410433354486243602631339 206115650031729365403947009)
  ·
    refine ⟨154586737523797024052960257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206115650031729365403947009 154586737523797024052960257)
    ·
      refine ⟨115940053142847768039720193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154586737523797024052960257 115940053142847768039720193)
      ·
        refine ⟨86955039857135826029790145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115940053142847768039720193 86955039857135826029790145)
        ·
          refine ⟨65216279892851869522342609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86955039857135826029790145 65216279892851869522342609)
          ·
            refine ⟨48912209919638902141756957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65216279892851869522342609 48912209919638902141756957)
            ·
              refine ⟨18342078719864588303158859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48912209919638902141756957 18342078719864588303158859)
              ·
                refine ⟨27513118079796882454738289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18342078719864588303158859 27513118079796882454738289)
                ·
                  refine ⟨20634838559847661841053717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27513118079796882454738289 20634838559847661841053717)
                  ·
                    refine ⟨967258057492859148799393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20634838559847661841053717 967258057492859148799393)
                    ·
                      rfl

theorem cell23_5651185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_5651185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651185 prefixEnd_5651185 := by exact prefixLift 5651185
  have htrace : WordTrace (prefixWord ++ tailWord_5651185) baseStart_5651185 baseEnd_5651185 := by
    simpa [prefixWord, tailWord_5651185, baseEnd_5651185] using wordTrace_append hprefix tailTrace_5651185
  have hstable : (prefixWord ++ tailWord_5651185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651185).length < 2 ^ (prefixWord ++ tailWord_5651185).sum := by decide
  have hdescent : baseEnd_5651185 < baseStart_5651185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651232 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 7]
def baseStart_5651232 : Nat := 118140960795 + 5651232 * 2 ^ 59
def prefixEnd_5651232 : Nat := 4983230072969 + 3 ^ 40 * 5651232 * 2
def baseEnd_5651232 : Nat := 322422034007704306945607

theorem tailTrace_5651232 : CollatzResearch.WordTrace tailWord_5651232 prefixEnd_5651232 322422034007704306945607 := by
  unfold tailWord_5651232
  simp only [CollatzResearch.WordTrace]
  refine ⟨103058682131279546215453975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137411576175039394953938633 103058682131279546215453975)
  ·
    refine ⟨154588023196919319323180963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103058682131279546215453975 154588023196919319323180963)
    ·
      refine ⟨231882034795378978984771445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154588023196919319323180963 231882034795378978984771445)
      ·
        refine ⟨21738940762066779279822323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231882034795378978984771445 21738940762066779279822323)
        ·
          refine ⟨32608411143100168919733485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21738940762066779279822323 32608411143100168919733485)
          ·
            refine ⟨12228154178662563344900057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32608411143100168919733485 12228154178662563344900057)
            ·
              refine ⟨9171115633996922508675043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12228154178662563344900057 9171115633996922508675043)
              ·
                refine ⟨13756673450995383763012565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9171115633996922508675043 13756673450995383763012565)
                ·
                  refine ⟨322422034007704306945607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13756673450995383763012565 322422034007704306945607)
                  ·
                    rfl

theorem cell23_5651232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 7].length) (baseStart_5651232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651232 prefixEnd_5651232 := by exact prefixLift 5651232
  have htrace : WordTrace (prefixWord ++ tailWord_5651232) baseStart_5651232 baseEnd_5651232 := by
    simpa [prefixWord, tailWord_5651232, baseEnd_5651232] using wordTrace_append hprefix tailTrace_5651232
  have hstable : (prefixWord ++ tailWord_5651232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651232).length < 2 ^ (prefixWord ++ tailWord_5651232).sum := by decide
  have hdescent : baseEnd_5651232 < baseStart_5651232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651350 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5651350 : Nat := 118140960795 + 5651350 * 2 ^ 59
def prefixEnd_5651350 : Nat := 4983230072969 + 3 ^ 40 * 5651350 * 2
def baseEnd_5651350 : Nat := 2901858896786569300834921

theorem tailTrace_5651350 : CollatzResearch.WordTrace tailWord_5651350 prefixEnd_5651350 2901858896786569300834921 := by
  unfold tailWord_5651350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12882604254758224911481469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137414445384087732389135669 12882604254758224911481469)
  ·
    refine ⟨4830976595534334341805551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12882604254758224911481469 4830976595534334341805551)
    ·
      refine ⟨7246464893301501512708327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830976595534334341805551 7246464893301501512708327)
      ·
        refine ⟨10869697339952252269062491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7246464893301501512708327 10869697339952252269062491)
        ·
          refine ⟨16304546009928378403593737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10869697339952252269062491 16304546009928378403593737)
          ·
            refine ⟨12228409507446283802695303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16304546009928378403593737 12228409507446283802695303)
            ·
              refine ⟨18342614261169425704042955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12228409507446283802695303 18342614261169425704042955)
              ·
                refine ⟨27513921391754138556064433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18342614261169425704042955 27513921391754138556064433)
                ·
                  refine ⟨20635441043815603917048325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27513921391754138556064433 20635441043815603917048325)
                  ·
                    refine ⟨3869145195715425734446561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20635441043815603917048325 3869145195715425734446561)
                    ·
                      refine ⟨2901858896786569300834921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869145195715425734446561 2901858896786569300834921)
                      ·
                        rfl

theorem cell23_5651350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5651350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651350 prefixEnd_5651350 := by exact prefixLift 5651350
  have htrace : WordTrace (prefixWord ++ tailWord_5651350) baseStart_5651350 baseEnd_5651350 := by
    simpa [prefixWord, tailWord_5651350, baseEnd_5651350] using wordTrace_append hprefix tailTrace_5651350
  have hstable : (prefixWord ++ tailWord_5651350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651350).length < 2 ^ (prefixWord ++ tailWord_5651350).sum := by decide
  have hdescent : baseEnd_5651350 < baseStart_5651350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651355 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 10]
def baseStart_5651355 : Nat := 118140960795 + 5651355 * 2 ^ 59
def prefixEnd_5651355 : Nat := 4983230072969 + 3 ^ 40 * 5651355 * 2
def baseEnd_5651355 : Nat := 2901861464189841781272397

theorem tailTrace_5651355 : CollatzResearch.WordTrace tailWord_5651355 prefixEnd_5651355 2901861464189841781272397 := by
  unfold tailWord_5651355
  simp only [CollatzResearch.WordTrace]
  refine ⟨206121850441113484437635519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137414566960742322958423679 206121850441113484437635519)
  ·
    refine ⟨309182775661670226656453279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206121850441113484437635519 309182775661670226656453279)
    ·
      refine ⟨463774163492505339984679919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309182775661670226656453279 463774163492505339984679919)
      ·
        refine ⟨695661245238758009977019879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463774163492505339984679919 695661245238758009977019879)
        ·
          refine ⟨1043491867858137014965529819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695661245238758009977019879 1043491867858137014965529819)
          ·
            refine ⟨1565237801787205522448294729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043491867858137014965529819 1565237801787205522448294729)
            ·
              refine ⟨1173928351340404141836221047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1565237801787205522448294729 1173928351340404141836221047)
              ·
                refine ⟨1760892527010606212754331571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173928351340404141836221047 1760892527010606212754331571)
                ·
                  refine ⟨2641338790515909319131497357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760892527010606212754331571 2641338790515909319131497357)
                  ·
                    refine ⟨990502046443465994674311509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2641338790515909319131497357 990502046443465994674311509)
                    ·
                      refine ⟨2901861464189841781272397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 990502046443465994674311509 2901861464189841781272397)
                      ·
                        rfl

theorem cell23_5651355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_5651355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651355 prefixEnd_5651355 := by exact prefixLift 5651355
  have htrace : WordTrace (prefixWord ++ tailWord_5651355) baseStart_5651355 baseEnd_5651355 := by
    simpa [prefixWord, tailWord_5651355, baseEnd_5651355] using wordTrace_append hprefix tailTrace_5651355
  have hstable : (prefixWord ++ tailWord_5651355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651355).length < 2 ^ (prefixWord ++ tailWord_5651355).sum := by decide
  have hdescent : baseEnd_5651355 < baseStart_5651355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651402 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_5651402 : Nat := 118140960795 + 5651402 * 2 ^ 59
def prefixEnd_5651402 : Nat := 4983230072969 + 3 ^ 40 * 5651402 * 2
def baseEnd_5651402 : Nat := 2901885597780603097384681

theorem tailTrace_5651402 : CollatzResearch.WordTrace tailWord_5651402 prefixEnd_5651402 2901885597780603097384681 := by
  unfold tailWord_5651402
  simp only [CollatzResearch.WordTrace]
  refine ⟨51530891167985802866149115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137415709781295474309730973 51530891167985802866149115)
  ·
    refine ⟨77296336751978704299223673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51530891167985802866149115 77296336751978704299223673)
    ·
      refine ⟨57972252563984028224417755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77296336751978704299223673 57972252563984028224417755)
      ·
        refine ⟨86958378845976042336626633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57972252563984028224417755 86958378845976042336626633)
        ·
          refine ⟨65218784134482031752469975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86958378845976042336626633 65218784134482031752469975)
          ·
            refine ⟨97828176201723047628704963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65218784134482031752469975 97828176201723047628704963)
            ·
              refine ⟨146742264302584571443057445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97828176201723047628704963 146742264302584571443057445)
              ·
                refine ⟨27514174556734607145573271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146742264302584571443057445 27514174556734607145573271)
                ·
                  refine ⟨41271261835101910718359907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27514174556734607145573271 41271261835101910718359907)
                  ·
                    refine ⟨61906892752652866077539861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41271261835101910718359907 61906892752652866077539861)
                    ·
                      refine ⟨2901885597780603097384681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61906892752652866077539861 2901885597780603097384681)
                      ·
                        rfl

theorem cell23_5651402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_5651402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651402 prefixEnd_5651402 := by exact prefixLift 5651402
  have htrace : WordTrace (prefixWord ++ tailWord_5651402) baseStart_5651402 baseEnd_5651402 := by
    simpa [prefixWord, tailWord_5651402, baseEnd_5651402] using wordTrace_append hprefix tailTrace_5651402
  have hstable : (prefixWord ++ tailWord_5651402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651402).length < 2 ^ (prefixWord ++ tailWord_5651402).sum := by decide
  have hdescent : baseEnd_5651402 < baseStart_5651402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651444 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5651444 : Nat := 118140960795 + 5651444 * 2 ^ 59
def prefixEnd_5651444 : Nat := 4983230072969 + 3 ^ 40 * 5651444 * 2
def baseEnd_5651444 : Nat := 2901907163968091933059489

theorem tailTrace_5651444 : CollatzResearch.WordTrace tailWord_5651444 prefixEnd_5651444 2901907163968091933059489 := by
  unfold tailWord_5651444
  simp only [CollatzResearch.WordTrace]
  refine ⟨103062548268895526318812693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137416731025194035091750257 103062548268895526318812693)
  ·
    refine ⟨4831056950104477796194345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103062548268895526318812693 4831056950104477796194345)
    ·
      refine ⟨3623292712578358347145759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4831056950104477796194345 3623292712578358347145759)
      ·
        refine ⟨5434939068867537520718639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3623292712578358347145759 5434939068867537520718639)
        ·
          refine ⟨8152408603301306281077959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434939068867537520718639 8152408603301306281077959)
          ·
            refine ⟨12228612904951959421616939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8152408603301306281077959 12228612904951959421616939)
            ·
              refine ⟨18342919357427939132425409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12228612904951959421616939 18342919357427939132425409)
              ·
                refine ⟨13757189518070954349319057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18342919357427939132425409 13757189518070954349319057)
                ·
                  refine ⟨10317892138553215761989293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13757189518070954349319057 10317892138553215761989293)
                  ·
                    refine ⟨3869209551957455910745985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10317892138553215761989293 3869209551957455910745985)
                    ·
                      refine ⟨2901907163968091933059489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869209551957455910745985 2901907163968091933059489)
                      ·
                        rfl

theorem cell23_5651444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5651444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651444 prefixEnd_5651444 := by exact prefixLift 5651444
  have htrace : WordTrace (prefixWord ++ tailWord_5651444) baseStart_5651444 baseEnd_5651444 := by
    simpa [prefixWord, tailWord_5651444, baseEnd_5651444] using wordTrace_append hprefix tailTrace_5651444
  have hstable : (prefixWord ++ tailWord_5651444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651444).length < 2 ^ (prefixWord ++ tailWord_5651444).sum := by decide
  have hdescent : baseEnd_5651444 < baseStart_5651444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651457 : List Nat := [1, 2, 4, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_5651457 : Nat := 118140960795 + 5651457 * 2 ^ 59
def prefixEnd_5651457 : Nat := 4983230072969 + 3 ^ 40 * 5651457 * 2
def baseEnd_5651457 : Nat := 2901913839216600382196929

theorem tailTrace_5651457 : CollatzResearch.WordTrace tailWord_5651457 prefixEnd_5651457 2901913839216600382196929 := by
  unfold tailWord_5651457
  simp only [CollatzResearch.WordTrace]
  refine ⟨206125570686743955857848625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137417047124495970571899083 206125570686743955857848625)
  ·
    refine ⟨154594178015057966893386469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206125570686743955857848625 154594178015057966893386469)
    ·
      refine ⟨28986408377823368792509963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154594178015057966893386469 28986408377823368792509963)
      ·
        refine ⟨43479612566735053188764945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28986408377823368792509963 43479612566735053188764945)
        ·
          refine ⟨32609709425051289891573709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43479612566735053188764945 32609709425051289891573709)
          ·
            refine ⟨12228641034394233709340141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32609709425051289891573709 12228641034394233709340141)
            ·
              refine ⟨4585740387897837641002553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12228641034394233709340141 4585740387897837641002553)
              ·
                refine ⟨3439305290923378230751915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4585740387897837641002553 3439305290923378230751915)
                ·
                  refine ⟨5158957936385067346127873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439305290923378230751915 5158957936385067346127873)
                  ·
                    refine ⟨3869218452288800509595905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5158957936385067346127873 3869218452288800509595905)
                    ·
                      refine ⟨2901913839216600382196929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869218452288800509595905 2901913839216600382196929)
                      ·
                        rfl

theorem cell23_5651457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_5651457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651457 prefixEnd_5651457 := by exact prefixLift 5651457
  have htrace : WordTrace (prefixWord ++ tailWord_5651457) baseStart_5651457 baseEnd_5651457 := by
    simpa [prefixWord, tailWord_5651457, baseEnd_5651457] using wordTrace_append hprefix tailTrace_5651457
  have hstable : (prefixWord ++ tailWord_5651457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651457).length < 2 ^ (prefixWord ++ tailWord_5651457).sum := by decide
  have hdescent : baseEnd_5651457 < baseStart_5651457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651474 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5651474 : Nat := 118140960795 + 5651474 * 2 ^ 59
def prefixEnd_5651474 : Nat := 4983230072969 + 3 ^ 40 * 5651474 * 2
def baseEnd_5651474 : Nat := 2901922568387726815684351

theorem tailTrace_5651474 : CollatzResearch.WordTrace tailWord_5651474 prefixEnd_5651474 2901922568387726815684351 := by
  unfold tailWord_5651474
  simp only [CollatzResearch.WordTrace]
  refine ⟨51531547681920591940304369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137417460485121578507478317 51531547681920591940304369)
  ·
    refine ⟨38648660761440443955228277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51531547681920591940304369 38648660761440443955228277)
    ·
      refine ⟨3623311946385041620802651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38648660761440443955228277 3623311946385041620802651)
      ·
        refine ⟨5434967919577562431203977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3623311946385041620802651 5434967919577562431203977)
        ·
          refine ⟨4076225939683171823402983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5434967919577562431203977 4076225939683171823402983)
          ·
            refine ⟨6114338909524757735104475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4076225939683171823402983 6114338909524757735104475)
            ·
              refine ⟨9171508364287136602656713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6114338909524757735104475 9171508364287136602656713)
              ·
                refine ⟨6878631273215352451992535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9171508364287136602656713 6878631273215352451992535)
                ·
                  refine ⟨10317946909823028677988803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6878631273215352451992535 10317946909823028677988803)
                  ·
                    refine ⟨15476920364734543016983205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10317946909823028677988803 15476920364734543016983205)
                    ·
                      refine ⟨2901922568387726815684351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15476920364734543016983205 2901922568387726815684351)
                      ·
                        rfl

theorem cell23_5651474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5651474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651474 prefixEnd_5651474 := by exact prefixLift 5651474
  have htrace : WordTrace (prefixWord ++ tailWord_5651474) baseStart_5651474 baseEnd_5651474 := by
    simpa [prefixWord, tailWord_5651474, baseEnd_5651474] using wordTrace_append hprefix tailTrace_5651474
  have hstable : (prefixWord ++ tailWord_5651474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651474).length < 2 ^ (prefixWord ++ tailWord_5651474).sum := by decide
  have hdescent : baseEnd_5651474 < baseStart_5651474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651509 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_5651509 : Nat := 118140960795 + 5651509 * 2 ^ 59
def prefixEnd_5651509 : Nat := 4983230072969 + 3 ^ 40 * 5651509 * 2
def baseEnd_5651509 : Nat := 2901940540210634178746689

theorem tailTrace_5651509 : CollatzResearch.WordTrace tailWord_5651509 prefixEnd_5651509 2901940540210634178746689 := by
  unfold tailWord_5651509
  simp only [CollatzResearch.WordTrace]
  refine ⟨206127467282555568738741581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137418311521703712492494387 206127467282555568738741581)
  ·
    refine ⟨77297800230958338277028093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206127467282555568738741581 77297800230958338277028093)
    ·
      refine ⟨28986675086609376853885535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77297800230958338277028093 28986675086609376853885535)
      ·
        refine ⟨43480012629914065280828303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28986675086609376853885535 43480012629914065280828303)
        ·
          refine ⟨65220018944871097921242455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43480012629914065280828303 65220018944871097921242455)
          ·
            refine ⟨97830028417306646881863683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65220018944871097921242455 97830028417306646881863683)
            ·
              refine ⟨146745042625959970322795525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97830028417306646881863683 146745042625959970322795525)
              ·
                refine ⟨27514695492367494435524161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146745042625959970322795525 27514695492367494435524161)
                ·
                  refine ⟨20636021619275620826643121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27514695492367494435524161 20636021619275620826643121)
                  ·
                    refine ⟨15477016214456715619982341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20636021619275620826643121 15477016214456715619982341)
                    ·
                      refine ⟨2901940540210634178746689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15477016214456715619982341 2901940540210634178746689)
                      ·
                        rfl

theorem cell23_5651509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_5651509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651509 prefixEnd_5651509 := by exact prefixLift 5651509
  have htrace : WordTrace (prefixWord ++ tailWord_5651509) baseStart_5651509 baseEnd_5651509 := by
    simpa [prefixWord, tailWord_5651509, baseEnd_5651509] using wordTrace_append hprefix tailTrace_5651509
  have hstable : (prefixWord ++ tailWord_5651509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651509).length < 2 ^ (prefixWord ++ tailWord_5651509).sum := by decide
  have hdescent : baseEnd_5651509 < baseStart_5651509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651623 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5651623 : Nat := 118140960795 + 5651623 * 2 ^ 59
def prefixEnd_5651623 : Nat := 4983230072969 + 3 ^ 40 * 5651623 * 2
def baseEnd_5651623 : Nat := 2901999077005246732721165

theorem tailTrace_5651623 : CollatzResearch.WordTrace tailWord_5651623 prefixEnd_5651623 2901999077005246732721165 := by
  unfold tailWord_5651623
  simp only [CollatzResearch.WordTrace]
  refine ⟨206131625204142566208391523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137421083469428377472261015 206131625204142566208391523)
  ·
    refine ⟨309197437806213849312587285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206131625204142566208391523 309197437806213849312587285)
    ·
      refine ⟨14493629897166274186527529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 309197437806213849312587285 14493629897166274186527529)
      ·
        refine ⟨10870222422874705639895647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14493629897166274186527529 10870222422874705639895647)
        ·
          refine ⟨16305333634312058459843471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10870222422874705639895647 16305333634312058459843471)
          ·
            refine ⟨24458000451468087689765207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16305333634312058459843471 24458000451468087689765207)
            ·
              refine ⟨36687000677202131534647811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24458000451468087689765207 36687000677202131534647811)
              ·
                refine ⟨55030501015803197301971717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36687000677202131534647811 55030501015803197301971717)
                ·
                  refine ⟨10318218940463099494119697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55030501015803197301971717 10318218940463099494119697)
                  ·
                    refine ⟨7738664205347324620589773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10318218940463099494119697 7738664205347324620589773)
                    ·
                      refine ⟨2901999077005246732721165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7738664205347324620589773 2901999077005246732721165)
                      ·
                        rfl

theorem cell23_5651623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5651623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651623 prefixEnd_5651623 := by exact prefixLift 5651623
  have htrace : WordTrace (prefixWord ++ tailWord_5651623) baseStart_5651623 baseEnd_5651623 := by
    simpa [prefixWord, tailWord_5651623, baseEnd_5651623] using wordTrace_append hprefix tailTrace_5651623
  have hstable : (prefixWord ++ tailWord_5651623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651623).length < 2 ^ (prefixWord ++ tailWord_5651623).sum := by decide
  have hdescent : baseEnd_5651623 < baseStart_5651623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651654 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5651654 : Nat := 118140960795 + 5651654 * 2 ^ 59
def prefixEnd_5651654 : Nat := 4983230072969 + 3 ^ 40 * 5651654 * 2
def baseEnd_5651654 : Nat := 2902014994905536111433523

theorem tailTrace_5651654 : CollatzResearch.WordTrace tailWord_5651654 prefixEnd_5651654 2902014994905536111433523 := by
  unfold tailWord_5651654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441648620844695578211563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137421837244686839001846677 6441648620844695578211563)
  ·
    refine ⟨9662472931267043367317345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6441648620844695578211563 9662472931267043367317345)
    ·
      refine ⟨7246854698450282525488009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9662472931267043367317345 7246854698450282525488009)
      ·
        refine ⟨5435141023837711894116007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7246854698450282525488009 5435141023837711894116007)
        ·
          refine ⟨8152711535756567841174011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5435141023837711894116007 8152711535756567841174011)
          ·
            refine ⟨12229067303634851761761017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8152711535756567841174011 12229067303634851761761017)
            ·
              refine ⟨9171800477726138821320763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12229067303634851761761017 9171800477726138821320763)
              ·
                refine ⟨13757700716589208231981145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9171800477726138821320763 13757700716589208231981145)
                ·
                  refine ⟨10318275537441906173985859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13757700716589208231981145 10318275537441906173985859)
                  ·
                    refine ⟨15477413306162859260978789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10318275537441906173985859 15477413306162859260978789)
                    ·
                      refine ⟨2902014994905536111433523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15477413306162859260978789 2902014994905536111433523)
                      ·
                        rfl

theorem cell23_5651654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5651654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651654 prefixEnd_5651654 := by exact prefixLift 5651654
  have htrace : WordTrace (prefixWord ++ tailWord_5651654) baseStart_5651654 baseEnd_5651654 := by
    simpa [prefixWord, tailWord_5651654, baseEnd_5651654] using wordTrace_append hprefix tailTrace_5651654
  have hstable : (prefixWord ++ tailWord_5651654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651654).length < 2 ^ (prefixWord ++ tailWord_5651654).sum := by decide
  have hdescent : baseEnd_5651654 < baseStart_5651654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651693 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5651693 : Nat := 118140960795 + 5651693 * 2 ^ 59
def prefixEnd_5651693 : Nat := 4983230072969 + 3 ^ 40 * 5651693 * 2
def baseEnd_5651693 : Nat := 2902035020651061458845843

theorem tailTrace_5651693 : CollatzResearch.WordTrace tailWord_5651693 prefixEnd_5651693 2902035020651061458845843 := by
  unfold tailWord_5651693
  simp only [CollatzResearch.WordTrace]
  refine ⟨206134178313888968163439733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137422785542592645442293155 206134178313888968163439733)
  ·
    refine ⟨19325079216927090765322475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206134178313888968163439733 19325079216927090765322475)
    ·
      refine ⟨28987618825390636147983713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19325079216927090765322475 28987618825390636147983713)
      ·
        refine ⟨21740714119042977110987785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28987618825390636147983713 21740714119042977110987785)
        ·
          refine ⟨16305535589282232833240839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21740714119042977110987785 16305535589282232833240839)
          ·
            refine ⟨24458303383923349249861259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16305535589282232833240839 24458303383923349249861259)
            ·
              refine ⟨36687455075885023874791889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24458303383923349249861259 36687455075885023874791889)
              ·
                refine ⟨27515591306913767906093917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36687455075885023874791889 27515591306913767906093917)
                ·
                  refine ⟨10318346740092662964785219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27515591306913767906093917 10318346740092662964785219)
                  ·
                    refine ⟨15477520110138994447177829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10318346740092662964785219 15477520110138994447177829)
                    ·
                      refine ⟨2902035020651061458845843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15477520110138994447177829 2902035020651061458845843)
                      ·
                        rfl

theorem cell23_5651693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5651693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651693 prefixEnd_5651693 := by exact prefixLift 5651693
  have htrace : WordTrace (prefixWord ++ tailWord_5651693) baseStart_5651693 baseEnd_5651693 := by
    simpa [prefixWord, tailWord_5651693, baseEnd_5651693] using wordTrace_append hprefix tailTrace_5651693
  have hstable : (prefixWord ++ tailWord_5651693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651693).length < 2 ^ (prefixWord ++ tailWord_5651693).sum := by decide
  have hdescent : baseEnd_5651693 < baseStart_5651693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651713 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_5651713 : Nat := 118140960795 + 5651713 * 2 ^ 59
def prefixEnd_5651713 : Nat := 4983230072969 + 3 ^ 40 * 5651713 * 2
def baseEnd_5651713 : Nat := 2902045290264151380595751

theorem tailTrace_5651713 : CollatzResearch.WordTrace tailWord_5651713 prefixEnd_5651713 2902045290264151380595751 := by
  unfold tailWord_5651713
  simp only [CollatzResearch.WordTrace]
  refine ⟨206134907773816511579167793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137423271849211007719445195 206134907773816511579167793)
  ·
    refine ⟨154601180830362383684375845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206134907773816511579167793 154601180830362383684375845)
    ·
      refine ⟨28987721405692946940820471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154601180830362383684375845 28987721405692946940820471)
      ·
        refine ⟨43481582108539420411230707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28987721405692946940820471 43481582108539420411230707)
        ·
          refine ⟨65222373162809130616846061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43481582108539420411230707 65222373162809130616846061)
          ·
            refine ⟨24458389936053423981317273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65222373162809130616846061 24458389936053423981317273)
            ·
              refine ⟨18343792452040067985987955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24458389936053423981317273 18343792452040067985987955)
              ·
                refine ⟨27515688678060101978981933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18343792452040067985987955 27515688678060101978981933)
                ·
                  refine ⟨10318383254272538242118225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27515688678060101978981933 10318383254272538242118225)
                  ·
                    refine ⟨7738787440704403681588669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10318383254272538242118225 7738787440704403681588669)
                    ·
                      refine ⟨2902045290264151380595751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7738787440704403681588669 2902045290264151380595751)
                      ·
                        rfl

theorem cell23_5651713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_5651713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651713 prefixEnd_5651713 := by exact prefixLift 5651713
  have htrace : WordTrace (prefixWord ++ tailWord_5651713) baseStart_5651713 baseEnd_5651713 := by
    simpa [prefixWord, tailWord_5651713, baseEnd_5651713] using wordTrace_append hprefix tailTrace_5651713
  have hstable : (prefixWord ++ tailWord_5651713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651713).length < 2 ^ (prefixWord ++ tailWord_5651713).sum := by decide
  have hdescent : baseEnd_5651713 < baseStart_5651713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651714 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_5651714 : Nat := 118140960795 + 5651714 * 2 ^ 59
def prefixEnd_5651714 : Nat := 4983230072969 + 3 ^ 40 * 5651714 * 2
def baseEnd_5651714 : Nat := 2902045803744805876683247

theorem tailTrace_5651714 : CollatzResearch.WordTrace tailWord_5651714 prefixEnd_5651714 2902045803744805876683247 := by
  unfold tailWord_5651714
  simp only [CollatzResearch.WordTrace]
  refine ⟨51533736061703222187488549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137423296164541925833302797 51533736061703222187488549)
  ·
    refine ⟨9662575511569354160154103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51533736061703222187488549 9662575511569354160154103)
    ·
      refine ⟨14493863267354031240231155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9662575511569354160154103 14493863267354031240231155)
      ·
        refine ⟨21740794901031046860346733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14493863267354031240231155 21740794901031046860346733)
        ·
          refine ⟨8152798087886642572630025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21740794901031046860346733 8152798087886642572630025)
          ·
            refine ⟨6114598565914981929472519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8152798087886642572630025 6114598565914981929472519)
            ·
              refine ⟨9171897848872472894208779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6114598565914981929472519 9171897848872472894208779)
              ·
                refine ⟨13757846773308709341313169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9171897848872472894208779 13757846773308709341313169)
                ·
                  refine ⟨10318385079981532005984877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13757846773308709341313169 10318385079981532005984877)
                  ·
                    refine ⟨3869394404993074502244329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10318385079981532005984877 3869394404993074502244329)
                    ·
                      refine ⟨2902045803744805876683247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869394404993074502244329 2902045803744805876683247)
                      ·
                        rfl

theorem cell23_5651714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_5651714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651714 prefixEnd_5651714 := by exact prefixLift 5651714
  have htrace : WordTrace (prefixWord ++ tailWord_5651714) baseStart_5651714 baseEnd_5651714 := by
    simpa [prefixWord, tailWord_5651714, baseEnd_5651714] using wordTrace_append hprefix tailTrace_5651714
  have hstable : (prefixWord ++ tailWord_5651714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651714).length < 2 ^ (prefixWord ++ tailWord_5651714).sum := by decide
  have hdescent : baseEnd_5651714 < baseStart_5651714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651757 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_5651757 : Nat := 118140960795 + 5651757 * 2 ^ 59
def prefixEnd_5651757 : Nat := 4983230072969 + 3 ^ 40 * 5651757 * 2
def baseEnd_5651757 : Nat := 2902067883412949208445549

theorem tailTrace_5651757 : CollatzResearch.WordTrace tailWord_5651757 prefixEnd_5651757 2902067883412949208445549 := by
  unfold tailWord_5651757
  simp only [CollatzResearch.WordTrace]
  refine ⟨206136512585657107093769525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137424341723771404729179683 206136512585657107093769525)
  ·
    refine ⟨19325298054905353790040893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206136512585657107093769525 19325298054905353790040893)
    ·
      refine ⟨7246986770589507671265335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19325298054905353790040893 7246986770589507671265335)
      ·
        refine ⟨10870480155884261506898003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7246986770589507671265335 10870480155884261506898003)
        ·
          refine ⟨16305720233826392260347005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10870480155884261506898003 16305720233826392260347005)
          ·
            refine ⟨6114645087684897097630127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16305720233826392260347005 6114645087684897097630127)
            ·
              refine ⟨9171967631527345646445191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6114645087684897097630127 9171967631527345646445191)
              ·
                refine ⟨13757951447291018469667787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9171967631527345646445191 13757951447291018469667787)
                ·
                  refine ⟨20636927170936527704501681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13757951447291018469667787 20636927170936527704501681)
                  ·
                    refine ⟨15477695378202395778376261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20636927170936527704501681 15477695378202395778376261)
                    ·
                      refine ⟨2902067883412949208445549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15477695378202395778376261 2902067883412949208445549)
                      ·
                        rfl

theorem cell23_5651757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_5651757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651757 prefixEnd_5651757 := by exact prefixLift 5651757
  have htrace : WordTrace (prefixWord ++ tailWord_5651757) baseStart_5651757 baseEnd_5651757 := by
    simpa [prefixWord, tailWord_5651757, baseEnd_5651757] using wordTrace_append hprefix tailTrace_5651757
  have hstable : (prefixWord ++ tailWord_5651757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651757).length < 2 ^ (prefixWord ++ tailWord_5651757).sum := by decide
  have hdescent : baseEnd_5651757 < baseStart_5651757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651800 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 4, 2, 2]
def baseStart_5651800 : Nat := 118140960795 + 5651800 * 2 ^ 59
def prefixEnd_5651800 : Nat := 4983230072969 + 3 ^ 40 * 5651800 * 2
def baseEnd_5651800 : Nat := 2902089963081092540207851

theorem tailTrace_5651800 : CollatzResearch.WordTrace tailWord_5651800 prefixEnd_5651800 2902089963081092540207851 := by
  unfold tailWord_5651800
  simp only [CollatzResearch.WordTrace]
  refine ⟨103069040462250662718792427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137425387283000883625056569 103069040462250662718792427)
  ·
    refine ⟨154603560693375994078188641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103069040462250662718792427 154603560693375994078188641)
    ·
      refine ⟨115952670520031995558641481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154603560693375994078188641 115952670520031995558641481)
      ·
        refine ⟨86964502890023996668981111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115952670520031995558641481 86964502890023996668981111)
        ·
          refine ⟨130446754335035995003471667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86964502890023996668981111 130446754335035995003471667)
          ·
            refine ⟨195670131502553992505207501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130446754335035995003471667 195670131502553992505207501)
            ·
              refine ⟨73376299313457747189452813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195670131502553992505207501 73376299313457747189452813)
              ·
                refine ⟨27516112242546655196044805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73376299313457747189452813 27516112242546655196044805)
                ·
                  refine ⟨5159271045477497849258401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27516112242546655196044805 5159271045477497849258401)
                  ·
                    refine ⟨3869453284108123386943801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5159271045477497849258401 3869453284108123386943801)
                    ·
                      refine ⟨2902089963081092540207851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869453284108123386943801 2902089963081092540207851)
                      ·
                        rfl

theorem cell23_5651800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_5651800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651800 prefixEnd_5651800 := by exact prefixLift 5651800
  have htrace : WordTrace (prefixWord ++ tailWord_5651800) baseStart_5651800 baseEnd_5651800 := by
    simpa [prefixWord, tailWord_5651800, baseEnd_5651800] using wordTrace_append hprefix tailTrace_5651800
  have hstable : (prefixWord ++ tailWord_5651800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651800).length < 2 ^ (prefixWord ++ tailWord_5651800).sum := by decide
  have hdescent : baseEnd_5651800 < baseStart_5651800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651838 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5651838 : Nat := 118140960795 + 5651838 * 2 ^ 59
def prefixEnd_5651838 : Nat := 4983230072969 + 3 ^ 40 * 5651838 * 2
def baseEnd_5651838 : Nat := 2902109475345963391532677

theorem tailTrace_5651838 : CollatzResearch.WordTrace tailWord_5651838 prefixEnd_5651838 2902109475345963391532677 := by
  unfold tailWord_5651838
  simp only [CollatzResearch.WordTrace]
  refine ⟨25767433362295457240933521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137426311265575771951645445 25767433362295457240933521)
  ·
    refine ⟨19325575021721592930700141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25767433362295457240933521 19325575021721592930700141)
    ·
      refine ⟨7247090633145597349012553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19325575021721592930700141 7247090633145597349012553)
      ·
        refine ⟨5435317974859198011759415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7247090633145597349012553 5435317974859198011759415)
        ·
          refine ⟨8152976962288797017639123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5435317974859198011759415 8152976962288797017639123)
          ·
            refine ⟨12229465443433195526458685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8152976962288797017639123 12229465443433195526458685)
            ·
              refine ⟨4586049541287448322422007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12229465443433195526458685 4586049541287448322422007)
              ·
                refine ⟨6879074311931172483633011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586049541287448322422007 6879074311931172483633011)
                ·
                  refine ⟨10318611467896758725449517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6879074311931172483633011 10318611467896758725449517)
                  ·
                    refine ⟨3869479300461284522043569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10318611467896758725449517 3869479300461284522043569)
                    ·
                      refine ⟨2902109475345963391532677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869479300461284522043569 2902109475345963391532677)
                      ·
                        rfl

theorem cell23_5651838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5651838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651838 prefixEnd_5651838 := by exact prefixLift 5651838
  have htrace : WordTrace (prefixWord ++ tailWord_5651838) baseStart_5651838 baseEnd_5651838 := by
    simpa [prefixWord, tailWord_5651838, baseEnd_5651838] using wordTrace_append hprefix tailTrace_5651838
  have hstable : (prefixWord ++ tailWord_5651838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651838).length < 2 ^ (prefixWord ++ tailWord_5651838).sum := by decide
  have hdescent : baseEnd_5651838 < baseStart_5651838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5651960 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 1, 5]
def baseStart_5651960 : Nat := 118140960795 + 5651960 * 2 ^ 59
def prefixEnd_5651960 : Nat := 4983230072969 + 3 ^ 40 * 5651960 * 2
def baseEnd_5651960 : Nat := 967390706661937304735705

theorem tailTrace_5651960 : CollatzResearch.WordTrace tailWord_5651960 prefixEnd_5651960 967390706661937304735705 := by
  unfold tailWord_5651960
  simp only [CollatzResearch.WordTrace]
  refine ⟨103071958301960836381704667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137429277735947781842272889 103071958301960836381704667)
  ·
    refine ⟨154607937452941254572557001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103071958301960836381704667 154607937452941254572557001)
    ·
      refine ⟨115955953089705940929417751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154607937452941254572557001 115955953089705940929417751)
      ·
        refine ⟨173933929634558911394126627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115955953089705940929417751 173933929634558911394126627)
        ·
          refine ⟨260900894451838367091189941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173933929634558911394126627 260900894451838367091189941)
          ·
            refine ⟨24459458854859846914799057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260900894451838367091189941 24459458854859846914799057)
            ·
              refine ⟨18344594141144885186099293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24459458854859846914799057 18344594141144885186099293)
              ·
                refine ⟨6879222802929331944787235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18344594141144885186099293 6879222802929331944787235)
                ·
                  refine ⟨10318834204393997917180853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6879222802929331944787235 10318834204393997917180853)
                  ·
                    refine ⟨967390706661937304735705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10318834204393997917180853 967390706661937304735705)
                    ·
                      rfl

theorem cell23_5651960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_5651960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5651960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5651960 prefixEnd_5651960 := by exact prefixLift 5651960
  have htrace : WordTrace (prefixWord ++ tailWord_5651960) baseStart_5651960 baseEnd_5651960 := by
    simpa [prefixWord, tailWord_5651960, baseEnd_5651960] using wordTrace_append hprefix tailTrace_5651960
  have hstable : (prefixWord ++ tailWord_5651960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5651960).length < 2 ^ (prefixWord ++ tailWord_5651960).sum := by decide
  have hdescent : baseEnd_5651960 < baseStart_5651960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5651960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652031 : List Nat := [1, 1, 2, 2, 3, 4, 1, 4, 1, 2, 2]
def baseStart_5652031 : Nat := 118140960795 + 5652031 * 2 ^ 59
def prefixEnd_5652031 : Nat := 4983230072969 + 3 ^ 40 * 5652031 * 2
def baseEnd_5652031 : Nat := 2902208577112281136419289

theorem tailTrace_5652031 : CollatzResearch.WordTrace tailWord_5652031 prefixEnd_5652031 2902208577112281136419289 := by
  unfold tailWord_5652031
  simp only [CollatzResearch.WordTrace]
  refine ⟨206146506186664451889243947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137431004124442967926162631 206146506186664451889243947)
  ·
    refine ⟨309219759279996677833865921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206146506186664451889243947 309219759279996677833865921)
    ·
      refine ⟨231914819459997508375399441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309219759279996677833865921 231914819459997508375399441)
      ·
        refine ⟨173936114594998131281549581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231914819459997508375399441 173936114594998131281549581)
        ·
          refine ⟨65226042973124299230581093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173936114594998131281549581 65226042973124299230581093)
          ·
            refine ⟨12229883057460806105733955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65226042973124299230581093 12229883057460806105733955)
            ·
              refine ⟨18344824586191209158600933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12229883057460806105733955 18344824586191209158600933)
              ·
                refine ⟨3439654609910851717237675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18344824586191209158600933 3439654609910851717237675)
                ·
                  refine ⟨5159481914866277575856513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439654609910851717237675 5159481914866277575856513)
                  ·
                    refine ⟨3869611436149708181892385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5159481914866277575856513 3869611436149708181892385)
                    ·
                      refine ⟨2902208577112281136419289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869611436149708181892385 2902208577112281136419289)
                      ·
                        rfl

theorem cell23_5652031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_5652031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652031 prefixEnd_5652031 := by exact prefixLift 5652031
  have htrace : WordTrace (prefixWord ++ tailWord_5652031) baseStart_5652031 baseEnd_5652031 := by
    simpa [prefixWord, tailWord_5652031, baseEnd_5652031] using wordTrace_append hprefix tailTrace_5652031
  have hstable : (prefixWord ++ tailWord_5652031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652031).length < 2 ^ (prefixWord ++ tailWord_5652031).sum := by decide
  have hdescent : baseEnd_5652031 < baseStart_5652031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652043 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 5]
def baseStart_5652043 : Nat := 118140960795 + 5652043 * 2 ^ 59
def prefixEnd_5652043 : Nat := 4983230072969 + 3 ^ 40 * 5652043 * 2
def baseEnd_5652043 : Nat := 2902214738880135089469233

theorem tailTrace_5652043 : CollatzResearch.WordTrace tailWord_5652043 prefixEnd_5652043 2902214738880135089469233 := by
  unfold tailWord_5652043
  simp only [CollatzResearch.WordTrace]
  refine ⟨206146943862620977938680783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137431295908413985292453855 206146943862620977938680783)
  ·
    refine ⟨309220415793931466908021175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206146943862620977938680783 309220415793931466908021175)
    ·
      refine ⟨463830623690897200362031763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309220415793931466908021175 463830623690897200362031763)
      ·
        refine ⟨695745935536345800543047645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463830623690897200362031763 695745935536345800543047645)
        ·
          refine ⟨260904725826129675203642867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695745935536345800543047645 260904725826129675203642867)
          ·
            refine ⟨391357088739194512805464301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260904725826129675203642867 391357088739194512805464301)
            ·
              refine ⟨146758908277197942302049113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 391357088739194512805464301 146758908277197942302049113)
              ·
                refine ⟨110069181207898456726536835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146758908277197942302049113 110069181207898456726536835)
                ·
                  refine ⟨165103771811847685089805253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110069181207898456726536835 165103771811847685089805253)
                  ·
                    refine ⟨30956957214721440954338485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165103771811847685089805253 30956957214721440954338485)
                    ·
                      refine ⟨2902214738880135089469233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30956957214721440954338485 2902214738880135089469233)
                      ·
                        rfl

theorem cell23_5652043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_5652043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652043 prefixEnd_5652043 := by exact prefixLift 5652043
  have htrace : WordTrace (prefixWord ++ tailWord_5652043) baseStart_5652043 baseEnd_5652043 := by
    simpa [prefixWord, tailWord_5652043, baseEnd_5652043] using wordTrace_append hprefix tailTrace_5652043
  have hstable : (prefixWord ++ tailWord_5652043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652043).length < 2 ^ (prefixWord ++ tailWord_5652043).sum := by decide
  have hdescent : baseEnd_5652043 < baseStart_5652043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652080 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 2, 6]
def baseStart_5652080 : Nat := 118140960795 + 5652080 * 2 ^ 59
def prefixEnd_5652080 : Nat := 4983230072969 + 3 ^ 40 * 5652080 * 2
def baseEnd_5652080 : Nat := 967411245888117148235521

theorem tailTrace_5652080 : CollatzResearch.WordTrace tailWord_5652080 prefixEnd_5652080 967411245888117148235521 := by
  unfold tailWord_5652080
  simp only [CollatzResearch.WordTrace]
  refine ⟨103074146681743466628888847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137432195575657955505185129 103074146681743466628888847)
  ·
    refine ⟨154611220022615199943333271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103074146681743466628888847 154611220022615199943333271)
    ·
      refine ⟨231916830033922799914999907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154611220022615199943333271 231916830033922799914999907)
      ·
        refine ⟨347875245050884199872499861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231916830033922799914999907 347875245050884199872499861)
        ·
          refine ⟨16306652111760196869023431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 347875245050884199872499861 16306652111760196869023431)
          ·
            refine ⟨24459978167640295303535147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16306652111760196869023431 24459978167640295303535147)
            ·
              refine ⟨36689967251460442955302721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24459978167640295303535147 36689967251460442955302721)
              ·
                refine ⟨27517475438595332216477041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36689967251460442955302721 27517475438595332216477041)
                ·
                  refine ⟨20638106578946499162357781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27517475438595332216477041 20638106578946499162357781)
                  ·
                    refine ⟨967411245888117148235521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20638106578946499162357781 967411245888117148235521)
                    ·
                      rfl

theorem cell23_5652080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_5652080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652080 prefixEnd_5652080 := by exact prefixLift 5652080
  have htrace : WordTrace (prefixWord ++ tailWord_5652080) baseStart_5652080 baseEnd_5652080 := by
    simpa [prefixWord, tailWord_5652080, baseEnd_5652080] using wordTrace_append hprefix tailTrace_5652080
  have hstable : (prefixWord ++ tailWord_5652080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652080).length < 2 ^ (prefixWord ++ tailWord_5652080).sum := by decide
  have hdescent : baseEnd_5652080 < baseStart_5652080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652090 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_5652090 : Nat := 118140960795 + 5652090 * 2 ^ 59
def prefixEnd_5652090 : Nat := 4983230072969 + 3 ^ 40 * 5652090 * 2
def baseEnd_5652090 : Nat := 2902238872470896405581517

theorem tailTrace_5652090 : CollatzResearch.WordTrace tailWord_5652090 prefixEnd_5652090 2902238872470896405581517 := by
  unfold tailWord_5652090
  simp only [CollatzResearch.WordTrace]
  refine ⟨51537164523362676241410431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137432438728967136643761149 51537164523362676241410431)
  ·
    refine ⟨77305746785044014362115647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51537164523362676241410431 77305746785044014362115647)
    ·
      refine ⟨115958620177566021543173471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77305746785044014362115647 115958620177566021543173471)
      ·
        refine ⟨173937930266349032314760207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115958620177566021543173471 173937930266349032314760207)
        ·
          refine ⟨260906895399523548472140311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173937930266349032314760207 260906895399523548472140311)
          ·
            refine ⟨391360343099285322708210467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260906895399523548472140311 391360343099285322708210467)
            ·
              refine ⟨587040514648927984062315701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391360343099285322708210467 587040514648927984062315701)
              ·
                refine ⟨55035048248336998505842097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 587040514648927984062315701 55035048248336998505842097)
                ·
                  refine ⟨41276286186252748879381573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55035048248336998505842097 41276286186252748879381573)
                  ·
                    refine ⟨7739303659922390414884045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41276286186252748879381573 7739303659922390414884045)
                    ·
                      refine ⟨2902238872470896405581517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7739303659922390414884045 2902238872470896405581517)
                      ·
                        rfl

theorem cell23_5652090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_5652090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652090 prefixEnd_5652090 := by exact prefixLift 5652090
  have htrace : WordTrace (prefixWord ++ tailWord_5652090) baseStart_5652090 baseEnd_5652090 := by
    simpa [prefixWord, tailWord_5652090, baseEnd_5652090] using wordTrace_append hprefix tailTrace_5652090
  have hstable : (prefixWord ++ tailWord_5652090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652090).length < 2 ^ (prefixWord ++ tailWord_5652090).sum := by decide
  have hdescent : baseEnd_5652090 < baseStart_5652090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652147 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 2, 5, 2]
def baseStart_5652147 : Nat := 118140960795 + 5652147 * 2 ^ 59
def prefixEnd_5652147 : Nat := 4983230072969 + 3 ^ 40 * 5652147 * 2
def baseEnd_5652147 : Nat := 2902268140868202682568755

theorem tailTrace_5652147 : CollatzResearch.WordTrace tailWord_5652147 prefixEnd_5652147 2902268140868202682568755 := by
  unfold tailWord_5652147
  simp only [CollatzResearch.WordTrace]
  refine ⟨206150737054244203700466695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137433824702829469133644463 206150737054244203700466695)
  ·
    refine ⟨309226105581366305550700043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206150737054244203700466695 309226105581366305550700043)
    ·
      refine ⟨463839158372049458326050065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309226105581366305550700043 463839158372049458326050065)
      ·
        refine ⟨347879368779037093744537549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463839158372049458326050065 347879368779037093744537549)
        ·
          refine ⟨130454763292138910154201581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347879368779037093744537549 130454763292138910154201581)
          ·
            refine ⟨48920536234552091307825593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130454763292138910154201581 48920536234552091307825593)
            ·
              refine ⟨36690402175914068480869195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48920536234552091307825593 36690402175914068480869195)
              ·
                refine ⟨55035603263871102721303793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36690402175914068480869195 55035603263871102721303793)
                ·
                  refine ⟨41276702447903327040977845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55035603263871102721303793 41276702447903327040977845)
                  ·
                    refine ⟨3869690854490936910091673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41276702447903327040977845 3869690854490936910091673)
                    ·
                      refine ⟨2902268140868202682568755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869690854490936910091673 2902268140868202682568755)
                      ·
                        rfl

theorem cell23_5652147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 5, 2].length) (baseStart_5652147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652147 prefixEnd_5652147 := by exact prefixLift 5652147
  have htrace : WordTrace (prefixWord ++ tailWord_5652147) baseStart_5652147 baseEnd_5652147 := by
    simpa [prefixWord, tailWord_5652147, baseEnd_5652147] using wordTrace_append hprefix tailTrace_5652147
  have hstable : (prefixWord ++ tailWord_5652147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652147).length < 2 ^ (prefixWord ++ tailWord_5652147).sum := by decide
  have hdescent : baseEnd_5652147 < baseStart_5652147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652177 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_5652177 : Nat := 118140960795 + 5652177 * 2 ^ 59
def prefixEnd_5652177 : Nat := 4983230072969 + 3 ^ 40 * 5652177 * 2
def baseEnd_5652177 : Nat := 2902283545287837565193617

theorem tailTrace_5652177 : CollatzResearch.WordTrace tailWord_5652177 prefixEnd_5652177 2902283545287837565193617 := by
  unfold tailWord_5652177
  simp only [CollatzResearch.WordTrace]
  refine ⟨206151831244135518824058785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137434554162757012549372523 206151831244135518824058785)
  ·
    refine ⟨154613873433101639118044089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206151831244135518824058785 154613873433101639118044089)
    ·
      refine ⟨115960405074826229338533067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154613873433101639118044089 115960405074826229338533067)
      ·
        refine ⟨173940607612239344007799601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115960405074826229338533067 173940607612239344007799601)
        ·
          refine ⟨130455455709179508005849701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173940607612239344007799601 130455455709179508005849701)
          ·
            refine ⟨24460397945471157751096819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130455455709179508005849701 24460397945471157751096819)
            ·
              refine ⟨36690596918206736626645229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24460397945471157751096819 36690596918206736626645229)
              ·
                refine ⟨13758973844327526234991961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36690596918206736626645229 13758973844327526234991961)
                ·
                  refine ⟨10319230383245644676243971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13758973844327526234991961 10319230383245644676243971)
                  ·
                    refine ⟨15478845574868467014365957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10319230383245644676243971 15478845574868467014365957)
                    ·
                      refine ⟨2902283545287837565193617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15478845574868467014365957 2902283545287837565193617)
                      ·
                        rfl

theorem cell23_5652177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_5652177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652177 prefixEnd_5652177 := by exact prefixLift 5652177
  have htrace : WordTrace (prefixWord ++ tailWord_5652177) baseStart_5652177 baseEnd_5652177 := by
    simpa [prefixWord, tailWord_5652177, baseEnd_5652177] using wordTrace_append hprefix tailTrace_5652177
  have hstable : (prefixWord ++ tailWord_5652177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652177).length < 2 ^ (prefixWord ++ tailWord_5652177).sum := by decide
  have hdescent : baseEnd_5652177 < baseStart_5652177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652261 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_5652261 : Nat := 118140960795 + 5652261 * 2 ^ 59
def prefixEnd_5652261 : Nat := 4983230072969 + 3 ^ 40 * 5652261 * 2
def baseEnd_5652261 : Nat := 2902326677662815236543231

theorem tailTrace_5652261 : CollatzResearch.WordTrace tailWord_5652261 prefixEnd_5652261 2902326677662815236543231 := by
  unfold tailWord_5652261
  simp only [CollatzResearch.WordTrace]
  refine ⟨206154894975831201170116637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137436596650554134113411091 206154894975831201170116637)
  ·
    refine ⟨77308085615936700438793739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206154894975831201170116637 77308085615936700438793739)
    ·
      refine ⟨115962128423905050658190609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77308085615936700438793739 115962128423905050658190609)
      ·
        refine ⟨86971596317928787993642957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115962128423905050658190609 86971596317928787993642957)
        ·
          refine ⟨32614348619223295497616109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86971596317928787993642957 32614348619223295497616109)
          ·
            refine ⟨12230380732208735811606041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32614348619223295497616109 12230380732208735811606041)
            ·
              refine ⟨9172785549156551858704531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12230380732208735811606041 9172785549156551858704531)
              ·
                refine ⟨13759178323734827788056797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9172785549156551858704531 13759178323734827788056797)
                ·
                  refine ⟨5159691871400560420521299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13759178323734827788056797 5159691871400560420521299)
                  ·
                    refine ⟨7739537807100840630781949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5159691871400560420521299 7739537807100840630781949)
                    ·
                      refine ⟨2902326677662815236543231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7739537807100840630781949 2902326677662815236543231)
                      ·
                        rfl

theorem cell23_5652261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_5652261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652261 prefixEnd_5652261 := by exact prefixLift 5652261
  have htrace : WordTrace (prefixWord ++ tailWord_5652261) baseStart_5652261 baseEnd_5652261 := by
    simpa [prefixWord, tailWord_5652261, baseEnd_5652261] using wordTrace_append hprefix tailTrace_5652261
  have hstable : (prefixWord ++ tailWord_5652261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652261).length < 2 ^ (prefixWord ++ tailWord_5652261).sum := by decide
  have hdescent : baseEnd_5652261 < baseStart_5652261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652278 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_5652278 : Nat := 118140960795 + 5652278 * 2 ^ 59
def prefixEnd_5652278 : Nat := 4983230072969 + 3 ^ 40 * 5652278 * 2
def baseEnd_5652278 : Nat := 2902335406833941670030653

theorem tailTrace_5652278 : CollatzResearch.WordTrace tailWord_5652278 prefixEnd_5652278 2902335406833941670030653 := by
  unfold tailWord_5652278
  simp only [CollatzResearch.WordTrace]
  refine ⟨12884719688548100817092843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137437010011179742048990325 12884719688548100817092843)
  ·
    refine ⟨19327079532822151225639265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12884719688548100817092843 19327079532822151225639265)
    ·
      refine ⟨14495309649616613419229449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19327079532822151225639265 14495309649616613419229449)
      ·
        refine ⟨10871482237212460064422087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14495309649616613419229449 10871482237212460064422087)
        ·
          refine ⟨16307223355818690096633131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10871482237212460064422087 16307223355818690096633131)
          ·
            refine ⟨24460835033728035144949697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16307223355818690096633131 24460835033728035144949697)
            ·
              refine ⟨18345626275296026358712273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24460835033728035144949697 18345626275296026358712273)
              ·
                refine ⟨13759219706472019769034205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18345626275296026358712273 13759219706472019769034205)
                ·
                  refine ⟨5159707389927007413387827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13759219706472019769034205 5159707389927007413387827)
                  ·
                    refine ⟨7739561084890511120081741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5159707389927007413387827 7739561084890511120081741)
                    ·
                      refine ⟨2902335406833941670030653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7739561084890511120081741 2902335406833941670030653)
                      ·
                        rfl

theorem cell23_5652278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_5652278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652278 prefixEnd_5652278 := by exact prefixLift 5652278
  have htrace : WordTrace (prefixWord ++ tailWord_5652278) baseStart_5652278 baseEnd_5652278 := by
    simpa [prefixWord, tailWord_5652278, baseEnd_5652278] using wordTrace_append hprefix tailTrace_5652278
  have hstable : (prefixWord ++ tailWord_5652278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652278).length < 2 ^ (prefixWord ++ tailWord_5652278).sum := by decide
  have hdescent : baseEnd_5652278 < baseStart_5652278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652284 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_5652284 : Nat := 118140960795 + 5652284 * 2 ^ 59
def prefixEnd_5652284 : Nat := 4983230072969 + 3 ^ 40 * 5652284 * 2
def baseEnd_5652284 : Nat := 2902338487717868646555625

theorem tailTrace_5652284 : CollatzResearch.WordTrace tailWord_5652284 prefixEnd_5652284 2902338487717868646555625 := by
  unfold tailWord_5652284
  simp only [CollatzResearch.WordTrace]
  refine ⟨103077866927373938049101953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137437155903165250732135937 103077866927373938049101953)
  ·
    refine ⟨77308400195530453536826465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103077866927373938049101953 77308400195530453536826465)
    ·
      refine ⟨57981300146647840152619849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77308400195530453536826465 57981300146647840152619849)
      ·
        refine ⟨43485975109985880114464887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57981300146647840152619849 43485975109985880114464887)
        ·
          refine ⟨65228962664978820171697331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43485975109985880114464887 65228962664978820171697331)
          ·
            refine ⟨97843443997468230257545997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65228962664978820171697331 97843443997468230257545997)
            ·
              refine ⟨36691291499050586346579749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97843443997468230257545997 36691291499050586346579749)
              ·
                refine ⟨6879617156071984939983703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36691291499050586346579749 6879617156071984939983703)
                ·
                  refine ⟨10319425734107977409975555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6879617156071984939983703 10319425734107977409975555)
                  ·
                    refine ⟨15479138601161966114963333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10319425734107977409975555 15479138601161966114963333)
                    ·
                      refine ⟨2902338487717868646555625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15479138601161966114963333 2902338487717868646555625)
                      ·
                        rfl

theorem cell23_5652284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_5652284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652284 prefixEnd_5652284 := by exact prefixLift 5652284
  have htrace : WordTrace (prefixWord ++ tailWord_5652284) baseStart_5652284 baseEnd_5652284 := by
    simpa [prefixWord, tailWord_5652284, baseEnd_5652284] using wordTrace_append hprefix tailTrace_5652284
  have hstable : (prefixWord ++ tailWord_5652284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652284).length < 2 ^ (prefixWord ++ tailWord_5652284).sum := by decide
  have hdescent : baseEnd_5652284 < baseStart_5652284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652297 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_5652297 : Nat := 118140960795 + 5652297 * 2 ^ 59
def prefixEnd_5652297 : Nat := 4983230072969 + 3 ^ 40 * 5652297 * 2
def baseEnd_5652297 : Nat := 2902345162966377095693065

theorem tailTrace_5652297 : CollatzResearch.WordTrace tailWord_5652297 prefixEnd_5652297 2902345162966377095693065 := by
  unfold tailWord_5652297
  simp only [CollatzResearch.WordTrace]
  refine ⟨206156208003700779318427145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137437472002467186212284763 206156208003700779318427145)
  ·
    refine ⟨154617156002775584488820359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206156208003700779318427145 154617156002775584488820359)
    ·
      refine ⟨231925734004163376733230539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154617156002775584488820359 231925734004163376733230539)
      ·
        refine ⟨347888601006245065099845809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231925734004163376733230539 347888601006245065099845809)
        ·
          refine ⟨260916450754683798824884357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347888601006245065099845809 260916450754683798824884357)
          ·
            refine ⟨48921834516503212279665817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260916450754683798824884357 48921834516503212279665817)
            ·
              refine ⟨36691375887377409209749363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48921834516503212279665817 36691375887377409209749363)
              ·
                refine ⟨55037063831066113814624045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36691375887377409209749363 55037063831066113814624045)
                ·
                  refine ⟨20638898936649792680484017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55037063831066113814624045 20638898936649792680484017)
                  ·
                    refine ⟨15479174202487344510363013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20638898936649792680484017 15479174202487344510363013)
                    ·
                      refine ⟨2902345162966377095693065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15479174202487344510363013 2902345162966377095693065)
                      ·
                        rfl

theorem cell23_5652297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_5652297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652297 prefixEnd_5652297 := by exact prefixLift 5652297
  have htrace : WordTrace (prefixWord ++ tailWord_5652297) baseStart_5652297 baseEnd_5652297 := by
    simpa [prefixWord, tailWord_5652297, baseEnd_5652297] using wordTrace_append hprefix tailTrace_5652297
  have hstable : (prefixWord ++ tailWord_5652297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652297).length < 2 ^ (prefixWord ++ tailWord_5652297).sum := by decide
  have hdescent : baseEnd_5652297 < baseStart_5652297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652324 : List Nat := [2, 3, 1, 1, 5, 1, 2, 8]
def baseStart_5652324 : Nat := 118140960795 + 5652324 * 2 ^ 59
def prefixEnd_5652324 : Nat := 4983230072969 + 3 ^ 40 * 5652324 * 2
def baseEnd_5652324 : Nat := 107494778775705499631683

theorem tailTrace_5652324 : CollatzResearch.WordTrace tailWord_5652324 prefixEnd_5652324 107494778775705499631683 := by
  unfold tailWord_5652324
  simp only [CollatzResearch.WordTrace]
  refine ⟨103078596387301481464830013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137438128516401975286440017 103078596387301481464830013)
  ·
    refine ⟨38654473645238055549311255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103078596387301481464830013 38654473645238055549311255)
    ·
      refine ⟨57981710467857083323966883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38654473645238055549311255 57981710467857083323966883)
      ·
        refine ⟨86972565701785624985950325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57981710467857083323966883 86972565701785624985950325)
        ·
          refine ⟨8153678034542402342432843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86972565701785624985950325 8153678034542402342432843)
          ·
            refine ⟨12230517051813603513649265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8153678034542402342432843 12230517051813603513649265)
            ·
              refine ⟨9172887788860202635236949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12230517051813603513649265 9172887788860202635236949)
              ·
                refine ⟨107494778775705499631683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9172887788860202635236949 107494778775705499631683)
                ·
                  rfl

theorem cell23_5652324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 8].length) (baseStart_5652324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652324 prefixEnd_5652324 := by exact prefixLift 5652324
  have htrace : WordTrace (prefixWord ++ tailWord_5652324) baseStart_5652324 baseEnd_5652324 := by
    simpa [prefixWord, tailWord_5652324, baseEnd_5652324] using wordTrace_append hprefix tailTrace_5652324
  have hstable : (prefixWord ++ tailWord_5652324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652324).length < 2 ^ (prefixWord ++ tailWord_5652324).sum := by decide
  have hdescent : baseEnd_5652324 < baseStart_5652324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652327 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_5652327 : Nat := 118140960795 + 5652327 * 2 ^ 59
def prefixEnd_5652327 : Nat := 4983230072969 + 3 ^ 40 * 5652327 * 2
def baseEnd_5652327 : Nat := 2902360567386011978317927

theorem tailTrace_5652327 : CollatzResearch.WordTrace tailWord_5652327 prefixEnd_5652327 2902360567386011978317927 := by
  unfold tailWord_5652327
  simp only [CollatzResearch.WordTrace]
  refine ⟨206157302193592094442019235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137438201462394729628012823 206157302193592094442019235)
  ·
    refine ⟨309235953290388141663028853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206157302193592094442019235 309235953290388141663028853)
    ·
      refine ⟨28990870620973888280908955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 309235953290388141663028853 28990870620973888280908955)
      ·
        refine ⟨43486305931460832421363433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28990870620973888280908955 43486305931460832421363433)
        ·
          refine ⟨32614729448595624316022575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43486305931460832421363433 32614729448595624316022575)
          ·
            refine ⟨48922094172893436474033863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32614729448595624316022575 48922094172893436474033863)
            ·
              refine ⟨73383141259340154711050795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48922094172893436474033863 73383141259340154711050795)
              ·
                refine ⟨110074711889010232066576193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73383141259340154711050795 110074711889010232066576193)
                ·
                  refine ⟨82556033916757674049932145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110074711889010232066576193 82556033916757674049932145)
                  ·
                    refine ⟨61917025437568255537449109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82556033916757674049932145 61917025437568255537449109)
                    ·
                      refine ⟨2902360567386011978317927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61917025437568255537449109 2902360567386011978317927)
                      ·
                        rfl

theorem cell23_5652327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_5652327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652327 prefixEnd_5652327 := by exact prefixLift 5652327
  have htrace : WordTrace (prefixWord ++ tailWord_5652327) baseStart_5652327 baseEnd_5652327 := by
    simpa [prefixWord, tailWord_5652327, baseEnd_5652327] using wordTrace_append hprefix tailTrace_5652327
  have hstable : (prefixWord ++ tailWord_5652327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652327).length < 2 ^ (prefixWord ++ tailWord_5652327).sum := by decide
  have hdescent : baseEnd_5652327 < baseStart_5652327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652377 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_5652377 : Nat := 118140960795 + 5652377 * 2 ^ 59
def prefixEnd_5652377 : Nat := 4983230072969 + 3 ^ 40 * 5652377 * 2
def baseEnd_5652377 : Nat := 2902386241418736782692697

theorem tailTrace_5652377 : CollatzResearch.WordTrace tailWord_5652377 prefixEnd_5652377 2902386241418736782692697 := by
  unfold tailWord_5652377
  simp only [CollatzResearch.WordTrace]
  refine ⟨206159125843410952981339385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137439417228940635320892923 206159125843410952981339385)
  ·
    refine ⟨154619344382558214736004539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206159125843410952981339385 154619344382558214736004539)
    ·
      refine ⟨231929016573837322104006809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154619344382558214736004539 231929016573837322104006809)
      ·
        refine ⟨173946762430377991578005107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231929016573837322104006809 173946762430377991578005107)
        ·
          refine ⟨260920143645566987367007661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173946762430377991578005107 260920143645566987367007661)
          ·
            refine ⟨97845053867087620262627873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260920143645566987367007661 97845053867087620262627873)
            ·
              refine ⟨73383790400315715196970905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97845053867087620262627873 73383790400315715196970905)
              ·
                refine ⟨55037842800236786397728179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73383790400315715196970905 55037842800236786397728179)
                ·
                  refine ⟨82556764200355179596592269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55037842800236786397728179 82556764200355179596592269)
                  ·
                    refine ⟨30958786575133192348722101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82556764200355179596592269 30958786575133192348722101)
                    ·
                      refine ⟨2902386241418736782692697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30958786575133192348722101 2902386241418736782692697)
                      ·
                        rfl

theorem cell23_5652377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_5652377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652377 prefixEnd_5652377 := by exact prefixLift 5652377
  have htrace : WordTrace (prefixWord ++ tailWord_5652377) baseStart_5652377 baseEnd_5652377 := by
    simpa [prefixWord, tailWord_5652377, baseEnd_5652377] using wordTrace_append hprefix tailTrace_5652377
  have hstable : (prefixWord ++ tailWord_5652377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652377).length < 2 ^ (prefixWord ++ tailWord_5652377).sum := by decide
  have hdescent : baseEnd_5652377 < baseStart_5652377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652407 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_5652407 : Nat := 118140960795 + 5652407 * 2 ^ 59
def prefixEnd_5652407 : Nat := 4983230072969 + 3 ^ 40 * 5652407 * 2
def baseEnd_5652407 : Nat := 2902401645838371665317559

theorem tailTrace_5652407 : CollatzResearch.WordTrace tailWord_5652407 prefixEnd_5652407 2902401645838371665317559 := by
  unfold tailWord_5652407
  simp only [CollatzResearch.WordTrace]
  refine ⟨206160220033302268104931475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137440146688868178736620983 206160220033302268104931475)
  ·
    refine ⟨309240330049953402157397213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206160220033302268104931475 309240330049953402157397213)
    ·
      refine ⟨115965123768732525809023955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309240330049953402157397213 115965123768732525809023955)
      ·
        refine ⟨173947685653098788713535933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115965123768732525809023955 173947685653098788713535933)
        ·
          refine ⟨65230382119912045767575975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173947685653098788713535933 65230382119912045767575975)
          ·
            refine ⟨97845573179868068651363963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65230382119912045767575975 97845573179868068651363963)
            ·
              refine ⟨146768359769802102977045945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97845573179868068651363963 146768359769802102977045945)
              ·
                refine ⟨110076269827351577232784459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146768359769802102977045945 110076269827351577232784459)
                ·
                  refine ⟨165114404741027365849176689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110076269827351577232784459 165114404741027365849176689)
                  ·
                    refine ⟨123835803555770524386882517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 165114404741027365849176689 123835803555770524386882517)
                    ·
                      refine ⟨2902401645838371665317559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123835803555770524386882517 2902401645838371665317559)
                      ·
                        rfl

theorem cell23_5652407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_5652407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652407 prefixEnd_5652407 := by exact prefixLift 5652407
  have htrace : WordTrace (prefixWord ++ tailWord_5652407) baseStart_5652407 baseEnd_5652407 := by
    simpa [prefixWord, tailWord_5652407, baseEnd_5652407] using wordTrace_append hprefix tailTrace_5652407
  have hstable : (prefixWord ++ tailWord_5652407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652407).length < 2 ^ (prefixWord ++ tailWord_5652407).sum := by decide
  have hdescent : baseEnd_5652407 < baseStart_5652407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652442 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2]
def baseStart_5652442 : Nat := 118140960795 + 5652442 * 2 ^ 59
def prefixEnd_5652442 : Nat := 4983230072969 + 3 ^ 40 * 5652442 * 2
def baseEnd_5652442 : Nat := 2902419617661279028379899

theorem tailTrace_5652442 : CollatzResearch.WordTrace tailWord_5652442 prefixEnd_5652442 2902419617661279028379899 := by
  unfold tailWord_5652442
  simp only [CollatzResearch.WordTrace]
  refine ⟨51540374147043867270613895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137440997725450312721637053 51540374147043867270613895)
  ·
    refine ⟨77310561220565800905920843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51540374147043867270613895 77310561220565800905920843)
    ·
      refine ⟨115965841830848701358881265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77310561220565800905920843 115965841830848701358881265)
      ·
        refine ⟨86974381373136526019160949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115965841830848701358881265 86974381373136526019160949)
        ·
          refine ⟨8153848253731549314296339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86974381373136526019160949 8153848253731549314296339)
          ·
            refine ⟨12230772380597323971444509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8153848253731549314296339 12230772380597323971444509)
            ·
              refine ⟨4586539642723996489291691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12230772380597323971444509 4586539642723996489291691)
              ·
                refine ⟨6879809464085994733937537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586539642723996489291691 6879809464085994733937537)
                ·
                  refine ⟨5159857098064496050453153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6879809464085994733937537 5159857098064496050453153)
                  ·
                    refine ⟨3869892823548372037839865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5159857098064496050453153 3869892823548372037839865)
                    ·
                      refine ⟨2902419617661279028379899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869892823548372037839865 2902419617661279028379899)
                      ·
                        rfl

theorem cell23_5652442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_5652442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652442 prefixEnd_5652442 := by exact prefixLift 5652442
  have htrace : WordTrace (prefixWord ++ tailWord_5652442) baseStart_5652442 baseEnd_5652442 := by
    simpa [prefixWord, tailWord_5652442, baseEnd_5652442] using wordTrace_append hprefix tailTrace_5652442
  have hstable : (prefixWord ++ tailWord_5652442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652442).length < 2 ^ (prefixWord ++ tailWord_5652442).sum := by decide
  have hdescent : baseEnd_5652442 < baseStart_5652442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652464 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_5652464 : Nat := 118140960795 + 5652464 * 2 ^ 59
def prefixEnd_5652464 : Nat := 4983230072969 + 3 ^ 40 * 5652464 * 2
def baseEnd_5652464 : Nat := 2902430914235677942304797

theorem tailTrace_5652464 : CollatzResearch.WordTrace tailWord_5652464 prefixEnd_5652464 2902430914235677942304797 := by
  unfold tailWord_5652464
  simp only [CollatzResearch.WordTrace]
  refine ⟨103081149497047883419878223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137441532662730511226504297 103081149497047883419878223)
  ·
    refine ⟨154621724245571825129817335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103081149497047883419878223 154621724245571825129817335)
    ·
      refine ⟨231932586368357737694726003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154621724245571825129817335 231932586368357737694726003)
      ·
        refine ⟨347898879552536606542089005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231932586368357737694726003 347898879552536606542089005)
        ·
          refine ⟨130462079832201227453283377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347898879552536606542089005 130462079832201227453283377)
          ·
            refine ⟨97846559874150920589962533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130462079832201227453283377 97846559874150920589962533)
            ·
              refine ⟨18346229976403297610617975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97846559874150920589962533 18346229976403297610617975)
              ·
                refine ⟨27519344964604946415926963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18346229976403297610617975 27519344964604946415926963)
                ·
                  refine ⟨41279017446907419623890445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27519344964604946415926963 41279017446907419623890445)
                  ·
                    refine ⟨15479631542590282358958917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41279017446907419623890445 15479631542590282358958917)
                    ·
                      refine ⟨2902430914235677942304797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15479631542590282358958917 2902430914235677942304797)
                      ·
                        rfl

theorem cell23_5652464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_5652464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652464 prefixEnd_5652464 := by exact prefixLift 5652464
  have htrace : WordTrace (prefixWord ++ tailWord_5652464) baseStart_5652464 baseEnd_5652464 := by
    simpa [prefixWord, tailWord_5652464, baseEnd_5652464] using wordTrace_append hprefix tailTrace_5652464
  have hstable : (prefixWord ++ tailWord_5652464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652464).length < 2 ^ (prefixWord ++ tailWord_5652464).sum := by decide
  have hdescent : baseEnd_5652464 < baseStart_5652464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652465 : List Nat := [1, 2, 2, 2, 6, 1, 1, 3, 5]
def baseStart_5652465 : Nat := 118140960795 + 5652465 * 2 ^ 59
def prefixEnd_5652465 : Nat := 4983230072969 + 3 ^ 40 * 5652465 * 2
def baseEnd_5652465 : Nat := 322492380857370270932477

theorem tailTrace_5652465 : CollatzResearch.WordTrace tailWord_5652465 prefixEnd_5652465 322492380857370270932477 := by
  unfold tailWord_5652465
  simp only [CollatzResearch.WordTrace]
  refine ⟨206162335467092144010542849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137441556978061429340361899 206162335467092144010542849)
  ·
    refine ⟨154621751600319108007907137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206162335467092144010542849 154621751600319108007907137)
    ·
      refine ⟨115966313700239331005930353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154621751600319108007907137 115966313700239331005930353)
      ·
        refine ⟨86974735275179498254447765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115966313700239331005930353 86974735275179498254447765)
        ·
          refine ⟨4076940716024038980677239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86974735275179498254447765 4076940716024038980677239)
          ·
            refine ⟨6115411074036058471015859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4076940716024038980677239 6115411074036058471015859)
            ·
              refine ⟨9173116611054087706523789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6115411074036058471015859 9173116611054087706523789)
              ·
                refine ⟨3439918729145282889946421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9173116611054087706523789 3439918729145282889946421)
                ·
                  refine ⟨322492380857370270932477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3439918729145282889946421 322492380857370270932477)
                  ·
                    rfl

theorem cell23_5652465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 5].length) (baseStart_5652465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652465 prefixEnd_5652465 := by exact prefixLift 5652465
  have htrace : WordTrace (prefixWord ++ tailWord_5652465) baseStart_5652465 baseEnd_5652465 := by
    simpa [prefixWord, tailWord_5652465, baseEnd_5652465] using wordTrace_append hprefix tailTrace_5652465
  have hstable : (prefixWord ++ tailWord_5652465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652465).length < 2 ^ (prefixWord ++ tailWord_5652465).sum := by decide
  have hdescent : baseEnd_5652465 < baseStart_5652465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652478 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_5652478 : Nat := 118140960795 + 5652478 * 2 ^ 59
def prefixEnd_5652478 : Nat := 4983230072969 + 3 ^ 40 * 5652478 * 2
def baseEnd_5652478 : Nat := 967479367654946962509911

theorem tailTrace_5652478 : CollatzResearch.WordTrace tailWord_5652478 prefixEnd_5652478 967479367654946962509911 := by
  unfold tailWord_5652478
  simp only [CollatzResearch.WordTrace]
  refine ⟨25770351202005630903845761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137441873077363364820510725 25770351202005630903845761)
  ·
    refine ⟨19327763401504223177884321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25770351202005630903845761 19327763401504223177884321)
    ·
      refine ⟨14495822551128167383413241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19327763401504223177884321 14495822551128167383413241)
      ·
        refine ⟨10871866913346125537559931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14495822551128167383413241 10871866913346125537559931)
        ·
          refine ⟨16307800370019188306339897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10871866913346125537559931 16307800370019188306339897)
          ·
            refine ⟨12230850277514391229754923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16307800370019188306339897 12230850277514391229754923)
            ·
              refine ⟨18346275416271586844632385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12230850277514391229754923 18346275416271586844632385)
              ·
                refine ⟨13759706562203690133474289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18346275416271586844632385 13759706562203690133474289)
                ·
                  refine ⟨10319779921652767600105717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13759706562203690133474289 10319779921652767600105717)
                  ·
                    refine ⟨967479367654946962509911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10319779921652767600105717 967479367654946962509911)
                    ·
                      rfl

theorem cell23_5652478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_5652478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652478 prefixEnd_5652478 := by exact prefixLift 5652478
  have htrace : WordTrace (prefixWord ++ tailWord_5652478) baseStart_5652478 baseEnd_5652478 := by
    simpa [prefixWord, tailWord_5652478, baseEnd_5652478] using wordTrace_append hprefix tailTrace_5652478
  have hstable : (prefixWord ++ tailWord_5652478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652478).length < 2 ^ (prefixWord ++ tailWord_5652478).sum := by decide
  have hdescent : baseEnd_5652478 < baseStart_5652478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652481 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_5652481 : Nat := 118140960795 + 5652481 * 2 ^ 59
def prefixEnd_5652481 : Nat := 4983230072969 + 3 ^ 40 * 5652481 * 2
def baseEnd_5652481 : Nat := 2902439643406804375792219

theorem tailTrace_5652481 : CollatzResearch.WordTrace tailWord_5652481 prefixEnd_5652481 2902439643406804375792219 := by
  unfold tailWord_5652481
  simp only [CollatzResearch.WordTrace]
  refine ⟨206162919035034178743125297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137441946023356119162083531 206162919035034178743125297)
  ·
    refine ⟨154622189276275634057343973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206162919035034178743125297 154622189276275634057343973)
    ·
      refine ⟨28991660489301681385751995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154622189276275634057343973 28991660489301681385751995)
      ·
        refine ⟨43487490733952522078627993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28991660489301681385751995 43487490733952522078627993)
        ·
          refine ⟨32615618050464391558970995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43487490733952522078627993 32615618050464391558970995)
          ·
            refine ⟨48923427075696587338456493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32615618050464391558970995 48923427075696587338456493)
            ·
              refine ⟨18346285153386220251921185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48923427075696587338456493 18346285153386220251921185)
              ·
                refine ⟨13759713865039665188940889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18346285153386220251921185 13759713865039665188940889)
                ·
                  refine ⟨10319785398779748891705667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13759713865039665188940889 10319785398779748891705667)
                  ·
                    refine ⟨15479678098169623337558501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10319785398779748891705667 15479678098169623337558501)
                    ·
                      refine ⟨2902439643406804375792219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15479678098169623337558501 2902439643406804375792219)
                      ·
                        rfl

theorem cell23_5652481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_5652481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652481 prefixEnd_5652481 := by exact prefixLift 5652481
  have htrace : WordTrace (prefixWord ++ tailWord_5652481) baseStart_5652481 baseEnd_5652481 := by
    simpa [prefixWord, tailWord_5652481, baseEnd_5652481] using wordTrace_append hprefix tailTrace_5652481
  have hstable : (prefixWord ++ tailWord_5652481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652481).length < 2 ^ (prefixWord ++ tailWord_5652481).sum := by decide
  have hdescent : baseEnd_5652481 < baseStart_5652481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652493 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5652493 : Nat := 118140960795 + 5652493 * 2 ^ 59
def prefixEnd_5652493 : Nat := 4983230072969 + 3 ^ 40 * 5652493 * 2
def baseEnd_5652493 : Nat := 2902445805174658328842165

theorem tailTrace_5652493 : CollatzResearch.WordTrace tailWord_5652493 prefixEnd_5652493 2902445805174658328842165 := by
  unfold tailWord_5652493
  simp only [CollatzResearch.WordTrace]
  refine ⟨206163356710990704792562133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137442237807327136528374755 206163356710990704792562133)
  ·
    refine ⟨4831953672913844643575675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 206163356710990704792562133 4831953672913844643575675)
    ·
      refine ⟨7247930509370766965363513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4831953672913844643575675 7247930509370766965363513)
      ·
        refine ⟨5435947882028075224022635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7247930509370766965363513 5435947882028075224022635)
        ·
          refine ⟨8153921823042112836033953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5435947882028075224022635 8153921823042112836033953)
          ·
            refine ⟨6115441367281584627025465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8153921823042112836033953 6115441367281584627025465)
            ·
              refine ⟨4586581025461188470269099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6115441367281584627025465 4586581025461188470269099)
              ·
                refine ⟨6879871538191782705403649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586581025461188470269099 6879871538191782705403649)
                ·
                  refine ⟨5159903653643837029052737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6879871538191782705403649 5159903653643837029052737)
                  ·
                    refine ⟨3869927740232877771789553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5159903653643837029052737 3869927740232877771789553)
                    ·
                      refine ⟨2902445805174658328842165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3869927740232877771789553 2902445805174658328842165)
                      ·
                        rfl

theorem cell23_5652493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5652493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652493 prefixEnd_5652493 := by exact prefixLift 5652493
  have htrace : WordTrace (prefixWord ++ tailWord_5652493) baseStart_5652493 baseEnd_5652493 := by
    simpa [prefixWord, tailWord_5652493, baseEnd_5652493] using wordTrace_append hprefix tailTrace_5652493
  have hstable : (prefixWord ++ tailWord_5652493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652493).length < 2 ^ (prefixWord ++ tailWord_5652493).sum := by decide
  have hdescent : baseEnd_5652493 < baseStart_5652493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652542 : List Nat := [4, 2, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_5652542 : Nat := 118140960795 + 5652542 * 2 ^ 59
def prefixEnd_5652542 : Nat := 4983230072969 + 3 ^ 40 * 5652542 * 2
def baseEnd_5652542 : Nat := 967490321908909545709813

theorem tailTrace_5652542 : CollatzResearch.WordTrace tailWord_5652542 prefixEnd_5652542 967490321908909545709813 := by
  unfold tailWord_5652542
  simp only [CollatzResearch.WordTrace]
  refine ⟨25770642985976648270136985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137443429258542124107397253 25770642985976648270136985)
  ·
    refine ⟨19327982239482486202602739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25770642985976648270136985 19327982239482486202602739)
    ·
      refine ⟨28991973359223729303904109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19327982239482486202602739 28991973359223729303904109)
      ·
        refine ⟨10871990009708898488964041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28991973359223729303904109 10871990009708898488964041)
        ·
          refine ⟨8153992507281673866723031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10871990009708898488964041 8153992507281673866723031)
          ·
            refine ⟨12230988760922510800084547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8153992507281673866723031 12230988760922510800084547)
            ·
              refine ⟨18346483141383766200126821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12230988760922510800084547 18346483141383766200126821)
              ·
                refine ⟨3439965589009456162523779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18346483141383766200126821 3439965589009456162523779)
                ·
                  refine ⟨5159948383514184243785669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439965589009456162523779 5159948383514184243785669)
                  ·
                    refine ⟨967490321908909545709813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5159948383514184243785669 967490321908909545709813)
                    ·
                      rfl

theorem cell23_5652542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_5652542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652542 prefixEnd_5652542 := by exact prefixLift 5652542
  have htrace : WordTrace (prefixWord ++ tailWord_5652542) baseStart_5652542 baseEnd_5652542 := by
    simpa [prefixWord, tailWord_5652542, baseEnd_5652542] using wordTrace_append hprefix tailTrace_5652542
  have hstable : (prefixWord ++ tailWord_5652542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652542).length < 2 ^ (prefixWord ++ tailWord_5652542).sum := by decide
  have hdescent : baseEnd_5652542 < baseStart_5652542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652581 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 1, 6]
def baseStart_5652581 : Nat := 118140960795 + 5652581 * 2 ^ 59
def prefixEnd_5652581 : Nat := 4983230072969 + 3 ^ 40 * 5652581 * 2
def baseEnd_5652581 : Nat := 967496997157417994847253

theorem tailTrace_5652581 : CollatzResearch.WordTrace tailWord_5652581 prefixEnd_5652581 967496997157417994847253 := by
  unfold tailWord_5652581
  simp only [CollatzResearch.WordTrace]
  refine ⟨206166566334671895821765597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137444377556447930547843731 206166566334671895821765597)
  ·
    refine ⟨77312462375501960933162099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206166566334671895821765597 77312462375501960933162099)
    ·
      refine ⟨115968693563252941399743149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77312462375501960933162099 115968693563252941399743149)
      ·
        refine ⟨43488260086219853024903681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115968693563252941399743149 43488260086219853024903681)
        ·
          refine ⟨32616195064664889768677761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43488260086219853024903681 32616195064664889768677761)
          ·
            refine ⟨24462146298498667326508321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32616195064664889768677761 24462146298498667326508321)
            ·
              refine ⟨18346609723874000494881241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24462146298498667326508321 18346609723874000494881241)
              ·
                refine ⟨13759957292905500371160931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18346609723874000494881241 13759957292905500371160931)
                ·
                  refine ⟨20639935939358250556741397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13759957292905500371160931 20639935939358250556741397)
                  ·
                    refine ⟨967496997157417994847253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20639935939358250556741397 967496997157417994847253)
                    ·
                      rfl

theorem cell23_5652581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_5652581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652581 prefixEnd_5652581 := by exact prefixLift 5652581
  have htrace : WordTrace (prefixWord ++ tailWord_5652581) baseStart_5652581 baseEnd_5652581 := by
    simpa [prefixWord, tailWord_5652581, baseEnd_5652581] using wordTrace_append hprefix tailTrace_5652581
  have hstable : (prefixWord ++ tailWord_5652581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652581).length < 2 ^ (prefixWord ++ tailWord_5652581).sum := by decide
  have hdescent : baseEnd_5652581 < baseStart_5652581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652588 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_5652588 : Nat := 118140960795 + 5652588 * 2 ^ 59
def prefixEnd_5652588 : Nat := 4983230072969 + 3 ^ 40 * 5652588 * 2
def baseEnd_5652588 : Nat := 2902494585836835457154227

theorem tailTrace_5652588 : CollatzResearch.WordTrace tailWord_5652588 prefixEnd_5652588 2902494585836835457154227 := by
  unfold tailWord_5652588
  simp only [CollatzResearch.WordTrace]
  refine ⟨103083410822823268008635209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137444547763764357344846945 103083410822823268008635209)
  ·
    refine ⟨77312558117117451006476407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103083410822823268008635209 77312558117117451006476407)
    ·
      refine ⟨115968837175676176509714611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77312558117117451006476407 115968837175676176509714611)
      ·
        refine ⟨173953255763514264764571917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115968837175676176509714611 173953255763514264764571917)
        ·
          refine ⟨65232470911317849286714469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173953255763514264764571917 65232470911317849286714469)
          ·
            refine ⟨12231088295872096741258963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65232470911317849286714469 12231088295872096741258963)
            ·
              refine ⟨18346632443808145111888445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12231088295872096741258963 18346632443808145111888445)
              ·
                refine ⟨6879987166428054416958167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18346632443808145111888445 6879987166428054416958167)
                ·
                  refine ⟨10319980749642081625437251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6879987166428054416958167 10319980749642081625437251)
                  ·
                    refine ⟨15479971124463122438155877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10319980749642081625437251 15479971124463122438155877)
                    ·
                      refine ⟨2902494585836835457154227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15479971124463122438155877 2902494585836835457154227)
                      ·
                        rfl

theorem cell23_5652588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_5652588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652588 prefixEnd_5652588 := by exact prefixLift 5652588
  have htrace : WordTrace (prefixWord ++ tailWord_5652588) baseStart_5652588 baseEnd_5652588 := by
    simpa [prefixWord, tailWord_5652588, baseEnd_5652588] using wordTrace_append hprefix tailTrace_5652588
  have hstable : (prefixWord ++ tailWord_5652588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652588).length < 2 ^ (prefixWord ++ tailWord_5652588).sum := by decide
  have hdescent : baseEnd_5652588 < baseStart_5652588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652605 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_5652605 : Nat := 118140960795 + 5652605 * 2 ^ 59
def prefixEnd_5652605 : Nat := 4983230072969 + 3 ^ 40 * 5652605 * 2
def baseEnd_5652605 : Nat := 2902503315007961890641649

theorem tailTrace_5652605 : CollatzResearch.WordTrace tailWord_5652605 prefixEnd_5652605 2902503315007961890641649 := by
  unfold tailWord_5652605
  simp only [CollatzResearch.WordTrace]
  refine ⟨206167441686584947920639269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137444961124389965280426179 206167441686584947920639269)
  ·
    refine ⟨38656395316234677735119863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206167441686584947920639269 38656395316234677735119863)
    ·
      refine ⟨57984592974352016602679795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38656395316234677735119863 57984592974352016602679795)
      ·
        refine ⟨86976889461528024904019693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57984592974352016602679795 86976889461528024904019693)
        ·
          refine ⟨32616333548073009339007385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86976889461528024904019693 32616333548073009339007385)
          ·
            refine ⟨24462250161054757004255539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32616333548073009339007385 24462250161054757004255539)
            ·
              refine ⟨36693375241582135506383309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24462250161054757004255539 36693375241582135506383309)
              ·
                refine ⟨13760015715593300814893741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36693375241582135506383309 13760015715593300814893741)
                ·
                  refine ⟨5160005893347487805585153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13760015715593300814893741 5160005893347487805585153)
                  ·
                    refine ⟨3870004420010615854188865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160005893347487805585153 3870004420010615854188865)
                    ·
                      refine ⟨2902503315007961890641649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870004420010615854188865 2902503315007961890641649)
                      ·
                        rfl

theorem cell23_5652605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_5652605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652605 prefixEnd_5652605 := by exact prefixLift 5652605
  have htrace : WordTrace (prefixWord ++ tailWord_5652605) baseStart_5652605 baseEnd_5652605 := by
    simpa [prefixWord, tailWord_5652605, baseEnd_5652605] using wordTrace_append hprefix tailTrace_5652605
  have hstable : (prefixWord ++ tailWord_5652605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652605).length < 2 ^ (prefixWord ++ tailWord_5652605).sum := by decide
  have hdescent : baseEnd_5652605 < baseStart_5652605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652618 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_5652618 : Nat := 118140960795 + 5652618 * 2 ^ 59
def prefixEnd_5652618 : Nat := 4983230072969 + 3 ^ 40 * 5652618 * 2
def baseEnd_5652618 : Nat := 2902509990256470339779089

theorem tailTrace_5652618 : CollatzResearch.WordTrace tailWord_5652618 prefixEnd_5652618 2902509990256470339779089 := by
  unfold tailWord_5652618
  simp only [CollatzResearch.WordTrace]
  refine ⟨51541978958884462785215627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137445277223691900760575005 51541978958884462785215627)
  ·
    refine ⟨77312968438326694177823441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51541978958884462785215627 77312968438326694177823441)
    ·
      refine ⟨57984726328745020633367581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77312968438326694177823441 57984726328745020633367581)
      ·
        refine ⟨21744272373279382737512843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57984726328745020633367581 21744272373279382737512843)
        ·
          refine ⟨32616408559919074106269265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21744272373279382737512843 32616408559919074106269265)
          ·
            refine ⟨24462306419939305579701949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32616408559919074106269265 24462306419939305579701949)
            ·
              refine ⟨9173364907477239592388231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24462306419939305579701949 9173364907477239592388231)
              ·
                refine ⟨13760047361215859388582347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9173364907477239592388231 13760047361215859388582347)
                ·
                  refine ⟨20640071041823789082873521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13760047361215859388582347 20640071041823789082873521)
                  ·
                    refine ⟨15480053281367841812155141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20640071041823789082873521 15480053281367841812155141)
                    ·
                      refine ⟨2902509990256470339779089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15480053281367841812155141 2902509990256470339779089)
                      ·
                        rfl

theorem cell23_5652618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_5652618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652618 prefixEnd_5652618 := by exact prefixLift 5652618
  have htrace : WordTrace (prefixWord ++ tailWord_5652618) baseStart_5652618 baseEnd_5652618 := by
    simpa [prefixWord, tailWord_5652618, baseEnd_5652618] using wordTrace_append hprefix tailTrace_5652618
  have hstable : (prefixWord ++ tailWord_5652618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652618).length < 2 ^ (prefixWord ++ tailWord_5652618).sum := by decide
  have hdescent : baseEnd_5652618 < baseStart_5652618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652639 : List Nat := [1, 1, 2, 6, 1, 1, 3, 3, 1, 2, 2]
def baseStart_5652639 : Nat := 118140960795 + 5652639 * 2 ^ 59
def prefixEnd_5652639 : Nat := 4983230072969 + 3 ^ 40 * 5652639 * 2
def baseEnd_5652639 : Nat := 2902520773350214757616493

theorem tailTrace_5652639 : CollatzResearch.WordTrace tailWord_5652639 prefixEnd_5652639 2902520773350214757616493 := by
  unfold tailWord_5652639
  simp only [CollatzResearch.WordTrace]
  refine ⟨206168681768461771727376971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137445787845641181151584647 206168681768461771727376971)
  ·
    refine ⟨309253022652692657591065457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206168681768461771727376971 309253022652692657591065457)
    ·
      refine ⟨231939766989519493193299093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309253022652692657591065457 231939766989519493193299093)
      ·
        refine ⟨10872176577633726243435895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 231939766989519493193299093 10872176577633726243435895)
        ·
          refine ⟨16308264866450589365153843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10872176577633726243435895 16308264866450589365153843)
          ·
            refine ⟨24462397299675884047730765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16308264866450589365153843 24462397299675884047730765)
            ·
              refine ⟨9173398987378456517899037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24462397299675884047730765 9173398987378456517899037)
              ·
                refine ⟨3440024620266921194212139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9173398987378456517899037 3440024620266921194212139)
                ·
                  refine ⟨5160036930400381791318209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440024620266921194212139 5160036930400381791318209)
                  ·
                    refine ⟨3870027697800286343488657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160036930400381791318209 3870027697800286343488657)
                    ·
                      refine ⟨2902520773350214757616493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870027697800286343488657 2902520773350214757616493)
                      ·
                        rfl

theorem cell23_5652639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_5652639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652639 prefixEnd_5652639 := by exact prefixLift 5652639
  have htrace : WordTrace (prefixWord ++ tailWord_5652639) baseStart_5652639 baseEnd_5652639 := by
    simpa [prefixWord, tailWord_5652639, baseEnd_5652639] using wordTrace_append hprefix tailTrace_5652639
  have hstable : (prefixWord ++ tailWord_5652639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652639).length < 2 ^ (prefixWord ++ tailWord_5652639).sum := by decide
  have hdescent : baseEnd_5652639 < baseStart_5652639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652672 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 2, 1, 3]
def baseStart_5652672 : Nat := 118140960795 + 5652672 * 2 ^ 59
def prefixEnd_5652672 : Nat := 4983230072969 + 3 ^ 40 * 5652672 * 2
def baseEnd_5652672 : Nat := 2902537718211813128503841

theorem tailTrace_5652672 : CollatzResearch.WordTrace tailWord_5652672 prefixEnd_5652672 2902537718211813128503841 := by
  unfold tailWord_5652672
  simp only [CollatzResearch.WordTrace]
  refine ⟨103084942688671109181664135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137446590251561478908885513 103084942688671109181664135)
  ·
    refine ⟨154627414033006663772496203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103084942688671109181664135 154627414033006663772496203)
    ·
      refine ⟨231941121049509995658744305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154627414033006663772496203 231941121049509995658744305)
      ·
        refine ⟨173955840787132496744058229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231941121049509995658744305 173955840787132496744058229)
        ·
          refine ⟨16308360073793671569755459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173955840787132496744058229 16308360073793671569755459)
          ·
            refine ⟨24462540110690507354633189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16308360073793671569755459 24462540110690507354633189)
            ·
              refine ⟨4586726270754470128993723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24462540110690507354633189 4586726270754470128993723)
              ·
                refine ⟨6880089406131705193490585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586726270754470128993723 6880089406131705193490585)
                ·
                  refine ⟨5160067054598778895117939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6880089406131705193490585 5160067054598778895117939)
                  ·
                    refine ⟨7740100581898168342676909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5160067054598778895117939 7740100581898168342676909)
                    ·
                      refine ⟨2902537718211813128503841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7740100581898168342676909 2902537718211813128503841)
                      ·
                        rfl

theorem cell23_5652672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_5652672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652672 prefixEnd_5652672 := by exact prefixLift 5652672
  have htrace : WordTrace (prefixWord ++ tailWord_5652672) baseStart_5652672 baseEnd_5652672 := by
    simpa [prefixWord, tailWord_5652672, baseEnd_5652672] using wordTrace_append hprefix tailTrace_5652672
  have hstable : (prefixWord ++ tailWord_5652672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652672).length < 2 ^ (prefixWord ++ tailWord_5652672).sum := by decide
  have hdescent : baseEnd_5652672 < baseStart_5652672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652681 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 3]
def baseStart_5652681 : Nat := 118140960795 + 5652681 * 2 ^ 59
def prefixEnd_5652681 : Nat := 4983230072969 + 3 ^ 40 * 5652681 * 2
def baseEnd_5652681 : Nat := 2902542339537703593291299

theorem tailTrace_5652681 : CollatzResearch.WordTrace tailWord_5652681 prefixEnd_5652681 2902542339537703593291299 := by
  unfold tailWord_5652681
  simp only [CollatzResearch.WordTrace]
  refine ⟨206170213634309612900405897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137446809089539741933603931 206170213634309612900405897)
  ·
    refine ⟨154627660225732209675304423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206170213634309612900405897 154627660225732209675304423)
    ·
      refine ⟨231941490338598314512956635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154627660225732209675304423 231941490338598314512956635)
      ·
        refine ⟨347912235507897471769434953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231941490338598314512956635 347912235507897471769434953)
        ·
          refine ⟨260934176630923103827076215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347912235507897471769434953 260934176630923103827076215)
          ·
            refine ⟨391401264946384655740614323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260934176630923103827076215 391401264946384655740614323)
            ·
              refine ⟨587101897419576983610921485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391401264946384655740614323 587101897419576983610921485)
              ·
                refine ⟨220163211532341368854095557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587101897419576983610921485 220163211532341368854095557)
                ·
                  refine ⟨41280602162314006660142917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220163211532341368854095557 41280602162314006660142917)
                  ·
                    refine ⟨7740112905433876248776797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41280602162314006660142917 7740112905433876248776797)
                    ·
                      refine ⟨2902542339537703593291299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7740112905433876248776797 2902542339537703593291299)
                      ·
                        rfl

theorem cell23_5652681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_5652681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652681 prefixEnd_5652681 := by exact prefixLift 5652681
  have htrace : WordTrace (prefixWord ++ tailWord_5652681) baseStart_5652681 baseEnd_5652681 := by
    simpa [prefixWord, tailWord_5652681, baseEnd_5652681] using wordTrace_append hprefix tailTrace_5652681
  have hstable : (prefixWord ++ tailWord_5652681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652681).length < 2 ^ (prefixWord ++ tailWord_5652681).sum := by decide
  have hdescent : baseEnd_5652681 < baseStart_5652681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652712 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_5652712 : Nat := 118140960795 + 5652712 * 2 ^ 59
def prefixEnd_5652712 : Nat := 4983230072969 + 3 ^ 40 * 5652712 * 2
def baseEnd_5652712 : Nat := 2902558257437992972003657

theorem tailTrace_5652712 : CollatzResearch.WordTrace tailWord_5652712 prefixEnd_5652712 2902558257437992972003657 := by
  unfold tailWord_5652712
  simp only [CollatzResearch.WordTrace]
  refine ⟨103085672148598652597392195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137447562864798203463189593 103085672148598652597392195)
  ·
    refine ⟨154628508222897978896088293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103085672148598652597392195 154628508222897978896088293)
    ·
      refine ⟨28992845291793371043016555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154628508222897978896088293 28992845291793371043016555)
      ·
        refine ⟨43489267937690056564524833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28992845291793371043016555 43489267937690056564524833)
        ·
          refine ⟨32616950953267542423393625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43489267937690056564524833 32616950953267542423393625)
          ·
            refine ⟨24462713214950656817545219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32616950953267542423393625 24462713214950656817545219)
            ·
              refine ⟨36694069822425985226317829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24462713214950656817545219 36694069822425985226317829)
              ·
                refine ⟨6880138091704872229934593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36694069822425985226317829 6880138091704872229934593)
                ·
                  refine ⟨5160103568778654172450945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6880138091704872229934593 5160103568778654172450945)
                  ·
                    refine ⟨3870077676583990629338209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160103568778654172450945 3870077676583990629338209)
                    ·
                      refine ⟨2902558257437992972003657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870077676583990629338209 2902558257437992972003657)
                      ·
                        rfl

theorem cell23_5652712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_5652712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652712 prefixEnd_5652712 := by exact prefixLift 5652712
  have htrace : WordTrace (prefixWord ++ tailWord_5652712) baseStart_5652712 baseEnd_5652712 := by
    simpa [prefixWord, tailWord_5652712, baseEnd_5652712] using wordTrace_append hprefix tailTrace_5652712
  have hstable : (prefixWord ++ tailWord_5652712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652712).length < 2 ^ (prefixWord ++ tailWord_5652712).sum := by decide
  have hdescent : baseEnd_5652712 < baseStart_5652712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652741 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_5652741 : Nat := 118140960795 + 5652741 * 2 ^ 59
def prefixEnd_5652741 : Nat := 4983230072969 + 3 ^ 40 * 5652741 * 2
def baseEnd_5652741 : Nat := 2902573148376973358541023

theorem tailTrace_5652741 : CollatzResearch.WordTrace tailWord_5652741 prefixEnd_5652741 2902573148376973358541023 := by
  unfold tailWord_5652741
  simp only [CollatzResearch.WordTrace]
  refine ⟨206172402014092243147590077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137448268009394828765060051 206172402014092243147590077)
  ·
    refine ⟨77314650755284591180346279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206172402014092243147590077 77314650755284591180346279)
    ·
      refine ⟨115971976132926886770519419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77314650755284591180346279 115971976132926886770519419)
      ·
        refine ⟨173957964199390330155779129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115971976132926886770519419 173957964199390330155779129)
        ·
          refine ⟨130468473149542747616834347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173957964199390330155779129 130468473149542747616834347)
          ·
            refine ⟨195702709724314121425251521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130468473149542747616834347 195702709724314121425251521)
            ·
              refine ⟨146777032293235591068938641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195702709724314121425251521 146777032293235591068938641)
              ·
                refine ⟨110082774219926693301703981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146777032293235591068938641 110082774219926693301703981)
                ·
                  refine ⟨41281040332472509988138993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110082774219926693301703981 41281040332472509988138993)
                  ·
                    refine ⟨30960780249354382491104245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41281040332472509988138993 30960780249354382491104245)
                    ·
                      refine ⟨2902573148376973358541023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30960780249354382491104245 2902573148376973358541023)
                      ·
                        rfl

theorem cell23_5652741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_5652741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652741 prefixEnd_5652741 := by exact prefixLift 5652741
  have htrace : WordTrace (prefixWord ++ tailWord_5652741) baseStart_5652741 baseEnd_5652741 := by
    simpa [prefixWord, tailWord_5652741, baseEnd_5652741] using wordTrace_append hprefix tailTrace_5652741
  have hstable : (prefixWord ++ tailWord_5652741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652741).length < 2 ^ (prefixWord ++ tailWord_5652741).sum := by decide
  have hdescent : baseEnd_5652741 < baseStart_5652741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652811 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 8]
def baseStart_5652811 : Nat := 118140960795 + 5652811 * 2 ^ 59
def prefixEnd_5652811 : Nat := 4983230072969 + 3 ^ 40 * 5652811 * 2
def baseEnd_5652811 : Nat := 2902609092022788084665701

theorem tailTrace_5652811 : CollatzResearch.WordTrace tailWord_5652811 prefixEnd_5652811 2902609092022788084665701 := by
  unfold tailWord_5652811
  simp only [CollatzResearch.WordTrace]
  refine ⟨206174955123838645102638287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137449970082559096735092191 206174955123838645102638287)
  ·
    refine ⟨309262432685757967653957431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206174955123838645102638287 309262432685757967653957431)
    ·
      refine ⟨463893649028636951480936147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309262432685757967653957431 463893649028636951480936147)
      ·
        refine ⟨695840473542955427221404221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463893649028636951480936147 695840473542955427221404221)
        ·
          refine ⟨260940177578608285208026583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 695840473542955427221404221 260940177578608285208026583)
          ·
            refine ⟨391410266367912427812039875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260940177578608285208026583 391410266367912427812039875)
            ·
              refine ⟨587115399551868641718059813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391410266367912427812039875 587115399551868641718059813)
              ·
                refine ⟨110084137415975370322136215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 587115399551868641718059813 110084137415975370322136215)
                ·
                  refine ⟨165126206123963055483204323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110084137415975370322136215 165126206123963055483204323)
                  ·
                    refine ⟨247689309185944583224806485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165126206123963055483204323 247689309185944583224806485)
                    ·
                      refine ⟨2902609092022788084665701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 247689309185944583224806485 2902609092022788084665701)
                      ·
                        rfl

theorem cell23_5652811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_5652811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652811 prefixEnd_5652811 := by exact prefixLift 5652811
  have htrace : WordTrace (prefixWord ++ tailWord_5652811) baseStart_5652811 baseEnd_5652811 := by
    simpa [prefixWord, tailWord_5652811, baseEnd_5652811] using wordTrace_append hprefix tailTrace_5652811
  have hstable : (prefixWord ++ tailWord_5652811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652811).length < 2 ^ (prefixWord ++ tailWord_5652811).sum := by decide
  have hdescent : baseEnd_5652811 < baseStart_5652811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652842 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 6]
def baseStart_5652842 : Nat := 118140960795 + 5652842 * 2 ^ 59
def prefixEnd_5652842 : Nat := 4983230072969 + 3 ^ 40 * 5652842 * 2
def baseEnd_5652842 : Nat := 322513889991453051486451

theorem tailTrace_5652842 : CollatzResearch.WordTrace tailWord_5652842 prefixEnd_5652842 322513889991453051486451 := by
  unfold tailWord_5652842
  simp only [CollatzResearch.WordTrace]
  refine ⟨51544021446681584349254195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137450723857817558264677853 51544021446681584349254195)
  ·
    refine ⟨77316032170022376523881293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51544021446681584349254195 77316032170022376523881293)
    ·
      refine ⟨28993512063758391196455485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77316032170022376523881293 28993512063758391196455485)
      ·
        refine ⟨10872567023909396698670807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28993512063758391196455485 10872567023909396698670807)
        ·
          refine ⟨16308850535864095048006211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10872567023909396698670807 16308850535864095048006211)
          ·
            refine ⟨24463275803796142572009317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16308850535864095048006211 24463275803796142572009317)
            ·
              refine ⟨4586864213211776732251747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24463275803796142572009317 4586864213211776732251747)
              ·
                refine ⟨6880296319817665098377621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586864213211776732251747 6880296319817665098377621)
                ·
                  refine ⟨322513889991453051486451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6880296319817665098377621 322513889991453051486451)
                  ·
                    rfl

theorem cell23_5652842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_5652842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652842 prefixEnd_5652842 := by exact prefixLift 5652842
  have htrace : WordTrace (prefixWord ++ tailWord_5652842) baseStart_5652842 baseEnd_5652842 := by
    simpa [prefixWord, tailWord_5652842, baseEnd_5652842] using wordTrace_append hprefix tailTrace_5652842
  have hstable : (prefixWord ++ tailWord_5652842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652842).length < 2 ^ (prefixWord ++ tailWord_5652842).sum := by decide
  have hdescent : baseEnd_5652842 < baseStart_5652842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652872 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 1, 5]
def baseStart_5652872 : Nat := 118140960795 + 5652872 * 2 ^ 59
def prefixEnd_5652872 : Nat := 4983230072969 + 3 ^ 40 * 5652872 * 2
def baseEnd_5652872 : Nat := 967546804780904115334307

theorem tailTrace_5652872 : CollatzResearch.WordTrace tailWord_5652872 prefixEnd_5652872 967546804780904115334307 := by
  unfold tailWord_5652872
  simp only [CollatzResearch.WordTrace]
  refine ⟨103088589988308826260304435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137451453317745101680405913 103088589988308826260304435)
  ·
    refine ⟨154632884982463239390456653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103088589988308826260304435 154632884982463239390456653)
    ·
      refine ⟨57987331868423714771421245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154632884982463239390456653 57987331868423714771421245)
      ·
        refine ⟨21745249450658893039282967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57987331868423714771421245 21745249450658893039282967)
        ·
          refine ⟨32617874175988339558924451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21745249450658893039282967 32617874175988339558924451)
          ·
            refine ⟨48926811263982509338386677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32617874175988339558924451 48926811263982509338386677)
            ·
              refine ⟨4586888555998360250473751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48926811263982509338386677 4586888555998360250473751)
              ·
                refine ⟨6880332833997540375710627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586888555998360250473751 6880332833997540375710627)
                ·
                  refine ⟨10320499250996310563565941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6880332833997540375710627 10320499250996310563565941)
                  ·
                    refine ⟨967546804780904115334307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10320499250996310563565941 967546804780904115334307)
                    ·
                      rfl

theorem cell23_5652872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_5652872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652872 prefixEnd_5652872 := by exact prefixLift 5652872
  have htrace : WordTrace (prefixWord ++ tailWord_5652872) baseStart_5652872 baseEnd_5652872 := by
    simpa [prefixWord, tailWord_5652872, baseEnd_5652872] using wordTrace_append hprefix tailTrace_5652872
  have hstable : (prefixWord ++ tailWord_5652872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652872).length < 2 ^ (prefixWord ++ tailWord_5652872).sum := by decide
  have hdescent : baseEnd_5652872 < baseStart_5652872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652895 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 3]
def baseStart_5652895 : Nat := 118140960795 + 5652895 * 2 ^ 59
def prefixEnd_5652895 : Nat := 4983230072969 + 3 ^ 40 * 5652895 * 2
def baseEnd_5652895 : Nat := 2902652224397765756015315

theorem tailTrace_5652895 : CollatzResearch.WordTrace tailWord_5652895 prefixEnd_5652895 2902652224397765756015315 := by
  unfold tailWord_5652895
  simp only [CollatzResearch.WordTrace]
  refine ⟨206178018855534327448696139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137452012570356218299130759 206178018855534327448696139)
  ·
    refine ⟨309267028283301491173044209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206178018855534327448696139 309267028283301491173044209)
    ·
      refine ⟨231950271212476118379783157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309267028283301491173044209 231950271212476118379783157)
      ·
        refine ⟨21745337926169636098104671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231950271212476118379783157 21745337926169636098104671)
        ·
          refine ⟨32618006889254454147157007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21745337926169636098104671 32618006889254454147157007)
          ·
            refine ⟨48927010333881681220735511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32618006889254454147157007 48927010333881681220735511)
            ·
              refine ⟨73390515500822521831103267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48927010333881681220735511 73390515500822521831103267)
              ·
                refine ⟨110085773251233782746654901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73390515500822521831103267 110085773251233782746654901)
                ·
                  refine ⟨10320541242303167132498897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110085773251233782746654901 10320541242303167132498897)
                  ·
                    refine ⟨7740405931727375349374173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10320541242303167132498897 7740405931727375349374173)
                    ·
                      refine ⟨2902652224397765756015315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7740405931727375349374173 2902652224397765756015315)
                      ·
                        rfl

theorem cell23_5652895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_5652895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652895 prefixEnd_5652895 := by exact prefixLift 5652895
  have htrace : WordTrace (prefixWord ++ tailWord_5652895) baseStart_5652895 baseEnd_5652895 := by
    simpa [prefixWord, tailWord_5652895, baseEnd_5652895] using wordTrace_append hprefix tailTrace_5652895
  have hstable : (prefixWord ++ tailWord_5652895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652895).length < 2 ^ (prefixWord ++ tailWord_5652895).sum := by decide
  have hdescent : baseEnd_5652895 < baseStart_5652895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5652926 : List Nat := [4, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_5652926 : Nat := 118140960795 + 5652926 * 2 ^ 59
def prefixEnd_5652926 : Nat := 4983230072969 + 3 ^ 40 * 5652926 * 2
def baseEnd_5652926 : Nat := 2902668142298055134727673

theorem tailTrace_5652926 : CollatzResearch.WordTrace tailWord_5652926 prefixEnd_5652926 2902668142298055134727673 := by
  unfold tailWord_5652926
  simp only [CollatzResearch.WordTrace]
  refine ⟨25772393689802752467884329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137452766345614679828716421 25772393689802752467884329)
  ·
    refine ⟨19329295267352064350913247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25772393689802752467884329 19329295267352064350913247)
    ·
      refine ⟨28993942901028096526369871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19329295267352064350913247 28993942901028096526369871)
      ·
        refine ⟨43490914351542144789554807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28993942901028096526369871 43490914351542144789554807)
        ·
          refine ⟨65236371527313217184332211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43490914351542144789554807 65236371527313217184332211)
          ·
            refine ⟨97854557290969825776498317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65236371527313217184332211 97854557290969825776498317)
            ·
              refine ⟨36695458984113684666186869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97854557290969825776498317 36695458984113684666186869)
              ·
                refine ⟨3440199279760657937455019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36695458984113684666186869 3440199279760657937455019)
                ·
                  refine ⟨5160298919640986906182529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440199279760657937455019 5160298919640986906182529)
                  ·
                    refine ⟨3870224189730740179636897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160298919640986906182529 3870224189730740179636897)
                    ·
                      refine ⟨2902668142298055134727673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870224189730740179636897 2902668142298055134727673)
                      ·
                        rfl

theorem cell23_5652926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_5652926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5652926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5652926 prefixEnd_5652926 := by exact prefixLift 5652926
  have htrace : WordTrace (prefixWord ++ tailWord_5652926) baseStart_5652926 baseEnd_5652926 := by
    simpa [prefixWord, tailWord_5652926, baseEnd_5652926] using wordTrace_append hprefix tailTrace_5652926
  have hstable : (prefixWord ++ tailWord_5652926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5652926).length < 2 ^ (prefixWord ++ tailWord_5652926).sum := by decide
  have hdescent : baseEnd_5652926 < baseStart_5652926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5652926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653016 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 2, 2, 2]
def baseStart_5653016 : Nat := 118140960795 + 5653016 * 2 ^ 59
def prefixEnd_5653016 : Nat := 4983230072969 + 3 ^ 40 * 5653016 * 2
def baseEnd_5653016 : Nat := 2902714355556959782602259

theorem tailTrace_5653016 : CollatzResearch.WordTrace tailWord_5653016 prefixEnd_5653016 2902714355556959782602259 := by
  unfold tailWord_5653016
  simp only [CollatzResearch.WordTrace]
  refine ⟨103091216044047982556925451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137454954725397310075900601 103091216044047982556925451)
  ·
    refine ⟨154636824066071973835388177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103091216044047982556925451 154636824066071973835388177)
    ·
      refine ⟨115977618049553980376541133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154636824066071973835388177 115977618049553980376541133)
      ·
        refine ⟨43491606768582742641202925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115977618049553980376541133 43491606768582742641202925)
        ·
          refine ⟨16309352538218528490451097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43491606768582742641202925 16309352538218528490451097)
          ·
            refine ⟨12232014403663896367838323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16309352538218528490451097 12232014403663896367838323)
            ·
              refine ⟨18348021605495844551757485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12232014403663896367838323 18348021605495844551757485)
              ·
                refine ⟨6880508102060941706909057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18348021605495844551757485 6880508102060941706909057)
                ·
                  refine ⟨5160381076545706280181793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6880508102060941706909057 5160381076545706280181793)
                  ·
                    refine ⟨3870285807409279710136345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160381076545706280181793 3870285807409279710136345)
                    ·
                      refine ⟨2902714355556959782602259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870285807409279710136345 2902714355556959782602259)
                      ·
                        rfl

theorem cell23_5653016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_5653016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653016 prefixEnd_5653016 := by exact prefixLift 5653016
  have htrace : WordTrace (prefixWord ++ tailWord_5653016) baseStart_5653016 baseEnd_5653016 := by
    simpa [prefixWord, tailWord_5653016, baseEnd_5653016] using wordTrace_append hprefix tailTrace_5653016
  have hstable : (prefixWord ++ tailWord_5653016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653016).length < 2 ^ (prefixWord ++ tailWord_5653016).sum := by decide
  have hdescent : baseEnd_5653016 < baseStart_5653016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653037 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5653037 : Nat := 118140960795 + 5653037 * 2 ^ 59
def prefixEnd_5653037 : Nat := 4983230072969 + 3 ^ 40 * 5653037 * 2
def baseEnd_5653037 : Nat := 2902725138650704200439663

theorem tailTrace_5653037 : CollatzResearch.WordTrace tailWord_5653037 prefixEnd_5653037 2902725138650704200439663 := by
  unfold tailWord_5653037
  simp only [CollatzResearch.WordTrace]
  refine ⟨206183198021019885700365365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137455465347346590466910243 206183198021019885700365365)
  ·
    refine ⟨19329674814470614284409253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206183198021019885700365365 19329674814470614284409253)
    ·
      refine ⟨3624314027713240178326735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19329674814470614284409253 3624314027713240178326735)
      ·
        refine ⟨5436471041569860267490103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624314027713240178326735 5436471041569860267490103)
        ·
          refine ⟨8154706562354790401235155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436471041569860267490103 8154706562354790401235155)
          ·
            refine ⟨12232059843532185601852733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8154706562354790401235155 12232059843532185601852733)
            ·
              refine ⟨4587022441324569600694775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12232059843532185601852733 4587022441324569600694775)
              ·
                refine ⟨6880533661986854401042163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587022441324569600694775 6880533661986854401042163)
                ·
                  refine ⟨10320800492980281601563245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6880533661986854401042163 10320800492980281601563245)
                  ·
                    refine ⟨3870300184867605600586217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10320800492980281601563245 3870300184867605600586217)
                    ·
                      refine ⟨2902725138650704200439663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870300184867605600586217 2902725138650704200439663)
                      ·
                        rfl

theorem cell23_5653037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5653037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653037 prefixEnd_5653037 := by exact prefixLift 5653037
  have htrace : WordTrace (prefixWord ++ tailWord_5653037) baseStart_5653037 baseEnd_5653037 := by
    simpa [prefixWord, tailWord_5653037, baseEnd_5653037] using wordTrace_append hprefix tailTrace_5653037
  have hstable : (prefixWord ++ tailWord_5653037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653037).length < 2 ^ (prefixWord ++ tailWord_5653037).sum := by decide
  have hdescent : baseEnd_5653037 < baseStart_5653037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653045 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_5653045 : Nat := 118140960795 + 5653045 * 2 ^ 59
def prefixEnd_5653045 : Nat := 4983230072969 + 3 ^ 40 * 5653045 * 2
def baseEnd_5653045 : Nat := 2902729246495940169139625

theorem tailTrace_5653045 : CollatzResearch.WordTrace tailWord_5653045 prefixEnd_5653045 2902729246495940169139625 := by
  unfold tailWord_5653045
  simp only [CollatzResearch.WordTrace]
  refine ⟨206183489804990903066656589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137455659869993935377771059 206183489804990903066656589)
  ·
    refine ⟨77318808676871588649996221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206183489804990903066656589 77318808676871588649996221)
    ·
      refine ⟨28994553253826845743748583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77318808676871588649996221 28994553253826845743748583)
      ·
        refine ⟨43491829880740268615622875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28994553253826845743748583 43491829880740268615622875)
        ·
          refine ⟨65237744821110402923434313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43491829880740268615622875 65237744821110402923434313)
          ·
            refine ⟨48928308615832802192575735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65237744821110402923434313 48928308615832802192575735)
            ·
              refine ⟨73392462923749203288863603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48928308615832802192575735 73392462923749203288863603)
              ·
                refine ⟨110088694385623804933295405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73392462923749203288863603 110088694385623804933295405)
                ·
                  refine ⟨41283260394608926849985777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110088694385623804933295405 41283260394608926849985777)
                  ·
                    refine ⟨30962445295956695137489333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41283260394608926849985777 30962445295956695137489333)
                    ·
                      refine ⟨2902729246495940169139625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30962445295956695137489333 2902729246495940169139625)
                      ·
                        rfl

theorem cell23_5653045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_5653045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653045 prefixEnd_5653045 := by exact prefixLift 5653045
  have htrace : WordTrace (prefixWord ++ tailWord_5653045) baseStart_5653045 baseEnd_5653045 := by
    simpa [prefixWord, tailWord_5653045, baseEnd_5653045] using wordTrace_append hprefix tailTrace_5653045
  have hstable : (prefixWord ++ tailWord_5653045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653045).length < 2 ^ (prefixWord ++ tailWord_5653045).sum := by decide
  have hdescent : baseEnd_5653045 < baseStart_5653045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653052 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_5653052 : Nat := 118140960795 + 5653052 * 2 ^ 59
def prefixEnd_5653052 : Nat := 4983230072969 + 3 ^ 40 * 5653052 * 2
def baseEnd_5653052 : Nat := 967577613620173880584031

theorem tailTrace_5653052 : CollatzResearch.WordTrace tailWord_5653052 prefixEnd_5653052 967577613620173880584031 := by
  unfold tailWord_5653052
  simp only [CollatzResearch.WordTrace]
  refine ⟨103091872557982771631080705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137455830077310362174774273 103091872557982771631080705)
  ·
    refine ⟨77318904418487078723310529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103091872557982771631080705 77318904418487078723310529)
    ·
      refine ⟨57989178313865309042482897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77318904418487078723310529 57989178313865309042482897)
      ·
        refine ⟨43491883735398981781862173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57989178313865309042482897 43491883735398981781862173)
        ·
          refine ⟨16309456400774618168198315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43491883735398981781862173 16309456400774618168198315)
          ·
            refine ⟨24464184601161927252297473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16309456400774618168198315 24464184601161927252297473)
            ·
              refine ⟨18348138450871445439223105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24464184601161927252297473 18348138450871445439223105)
              ·
                refine ⟨13761103838153584079417329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18348138450871445439223105 13761103838153584079417329)
                ·
                  refine ⟨10320827878615188059562997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13761103838153584079417329 10320827878615188059562997)
                  ·
                    refine ⟨967577613620173880584031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10320827878615188059562997 967577613620173880584031)
                    ·
                      rfl

theorem cell23_5653052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_5653052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653052 prefixEnd_5653052 := by exact prefixLift 5653052
  have htrace : WordTrace (prefixWord ++ tailWord_5653052) baseStart_5653052 baseEnd_5653052 := by
    simpa [prefixWord, tailWord_5653052, baseEnd_5653052] using wordTrace_append hprefix tailTrace_5653052
  have hstable : (prefixWord ++ tailWord_5653052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653052).length < 2 ^ (prefixWord ++ tailWord_5653052).sum := by decide
  have hdescent : baseEnd_5653052 < baseStart_5653052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653089 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_5653089 : Nat := 118140960795 + 5653089 * 2 ^ 59
def prefixEnd_5653089 : Nat := 4983230072969 + 3 ^ 40 * 5653089 * 2
def baseEnd_5653089 : Nat := 2902751839644737996989423

theorem tailTrace_5653089 : CollatzResearch.WordTrace tailWord_5653089 prefixEnd_5653089 2902751839644737996989423 := by
  unfold tailWord_5653089
  simp only [CollatzResearch.WordTrace]
  refine ⟨206185094616831498581258321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137456729744554332387505547 206185094616831498581258321)
  ·
    refine ⟨154638820962623623935943741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206185094616831498581258321 154638820962623623935943741)
    ·
      refine ⟨57989557860983858975978903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154638820962623623935943741 57989557860983858975978903)
      ·
        refine ⟨86984336791475788463968355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57989557860983858975978903 86984336791475788463968355)
        ·
          refine ⟨130476505187213682695952533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86984336791475788463968355 130476505187213682695952533)
          ·
            refine ⟨6116086180650641376372775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130476505187213682695952533 6116086180650641376372775)
            ·
              refine ⟨9174129270975962064559163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6116086180650641376372775 9174129270975962064559163)
              ·
                refine ⟨13761193906463943096838745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9174129270975962064559163 13761193906463943096838745)
                ·
                  refine ⟨10320895429847957322629059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13761193906463943096838745 10320895429847957322629059)
                  ·
                    refine ⟨15481343144771935983943589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10320895429847957322629059 15481343144771935983943589)
                    ·
                      refine ⟨2902751839644737996989423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15481343144771935983943589 2902751839644737996989423)
                      ·
                        rfl

theorem cell23_5653089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_5653089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653089 prefixEnd_5653089 := by exact prefixLift 5653089
  have htrace : WordTrace (prefixWord ++ tailWord_5653089) baseStart_5653089 baseEnd_5653089 := by
    simpa [prefixWord, tailWord_5653089, baseEnd_5653089] using wordTrace_append hprefix tailTrace_5653089
  have hstable : (prefixWord ++ tailWord_5653089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653089).length < 2 ^ (prefixWord ++ tailWord_5653089).sum := by decide
  have hdescent : baseEnd_5653089 < baseStart_5653089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653092 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_5653092 : Nat := 118140960795 + 5653092 * 2 ^ 59
def prefixEnd_5653092 : Nat := 4983230072969 + 3 ^ 40 * 5653092 * 2
def baseEnd_5653092 : Nat := 2902753380086701485251909

theorem tailTrace_5653092 : CollatzResearch.WordTrace tailWord_5653092 prefixEnd_5653092 2902753380086701485251909 := by
  unfold tailWord_5653092
  simp only [CollatzResearch.WordTrace]
  refine ⟨103092602017910315046808765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137456802690547086729078353 103092602017910315046808765)
  ·
    refine ⟨38659725756716368142553287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103092602017910315046808765 38659725756716368142553287)
    ·
      refine ⟨57989588635074552213829931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38659725756716368142553287 57989588635074552213829931)
      ·
        refine ⟨86984382952611828320744897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57989588635074552213829931 86984382952611828320744897)
        ·
          refine ⟨65238287214458871240558673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86984382952611828320744897 65238287214458871240558673)
          ·
            refine ⟨48928715410844153430419005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65238287214458871240558673 48928715410844153430419005)
            ·
              refine ⟨18348268279066557536407127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48928715410844153430419005 18348268279066557536407127)
              ·
                refine ⟨27522402418599836304610691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18348268279066557536407127 27522402418599836304610691)
                ·
                  refine ⟨41283603627899754456916037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27522402418599836304610691 41283603627899754456916037)
                  ·
                    refine ⟨7740675680231203960671757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41283603627899754456916037 7740675680231203960671757)
                    ·
                      refine ⟨2902753380086701485251909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7740675680231203960671757 2902753380086701485251909)
                      ·
                        rfl

theorem cell23_5653092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_5653092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653092 prefixEnd_5653092 := by exact prefixLift 5653092
  have htrace : WordTrace (prefixWord ++ tailWord_5653092) baseStart_5653092 baseEnd_5653092 := by
    simpa [prefixWord, tailWord_5653092, baseEnd_5653092] using wordTrace_append hprefix tailTrace_5653092
  have hstable : (prefixWord ++ tailWord_5653092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653092).length < 2 ^ (prefixWord ++ tailWord_5653092).sum := by decide
  have hdescent : baseEnd_5653092 < baseStart_5653092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653095 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 8]
def baseStart_5653095 : Nat := 118140960795 + 5653095 * 2 ^ 59
def prefixEnd_5653095 : Nat := 4983230072969 + 3 ^ 40 * 5653095 * 2
def baseEnd_5653095 : Nat := 322528324503184997057155

theorem tailTrace_5653095 : CollatzResearch.WordTrace tailWord_5653095 prefixEnd_5653095 322528324503184997057155 := by
  unfold tailWord_5653095
  simp only [CollatzResearch.WordTrace]
  refine ⟨206185313454809761605976739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137456875636539841070651159 206185313454809761605976739)
  ·
    refine ⟨309277970182214642408965109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206185313454809761605976739 309277970182214642408965109)
    ·
      refine ⟨28994809704582622725840479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 309277970182214642408965109 28994809704582622725840479)
      ·
        refine ⟨43492214556873934088760719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28994809704582622725840479 43492214556873934088760719)
        ·
          refine ⟨65238321835310901133141079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43492214556873934088760719 65238321835310901133141079)
          ·
            refine ⟨97857482752966351699711619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65238321835310901133141079 97857482752966351699711619)
            ·
              refine ⟨146786224129449527549567429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97857482752966351699711619 146786224129449527549567429)
              ·
                refine ⟨27522417024271786415543893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146786224129449527549567429 27522417024271786415543893)
                ·
                  refine ⟨322528324503184997057155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27522417024271786415543893 322528324503184997057155)
                  ·
                    rfl

theorem cell23_5653095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 8].length) (baseStart_5653095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653095 prefixEnd_5653095 := by exact prefixLift 5653095
  have htrace : WordTrace (prefixWord ++ tailWord_5653095) baseStart_5653095 baseEnd_5653095 := by
    simpa [prefixWord, tailWord_5653095, baseEnd_5653095] using wordTrace_append hprefix tailTrace_5653095
  have hstable : (prefixWord ++ tailWord_5653095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653095).length < 2 ^ (prefixWord ++ tailWord_5653095).sum := by decide
  have hdescent : baseEnd_5653095 < baseStart_5653095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653102 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5653102 : Nat := 118140960795 + 5653102 * 2 ^ 59
def prefixEnd_5653102 : Nat := 4983230072969 + 3 ^ 40 * 5653102 * 2
def baseEnd_5653102 : Nat := 2902758514893246446126863

theorem tailTrace_5653102 : CollatzResearch.WordTrace tailWord_5653102 prefixEnd_5653102 2902758514893246446126863 := by
  unfold tailWord_5653102
  simp only [CollatzResearch.WordTrace]
  refine ⟨25773196095723050225185195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137457045843856267867654373 25773196095723050225185195)
  ·
    refine ⟨38659794143584575337777793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25773196095723050225185195 38659794143584575337777793)
    ·
      refine ⟨28994845607688431503333345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38659794143584575337777793 28994845607688431503333345)
      ·
        refine ⟨21746134205766323627500009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28994845607688431503333345 21746134205766323627500009)
        ·
          refine ⟨16309600654324742720625007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21746134205766323627500009 16309600654324742720625007)
          ·
            refine ⟨24464400981487114080937511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16309600654324742720625007 24464400981487114080937511)
            ·
              refine ⟨36696601472230671121406267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24464400981487114080937511 36696601472230671121406267)
              ·
                refine ⟨55044902208346006682109401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36696601472230671121406267 55044902208346006682109401)
                ·
                  refine ⟨41283676656259505011582051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55044902208346006682109401 41283676656259505011582051)
                  ·
                    refine ⟨61925514984389257517373077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41283676656259505011582051 61925514984389257517373077)
                    ·
                      refine ⟨2902758514893246446126863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61925514984389257517373077 2902758514893246446126863)
                      ·
                        rfl

theorem cell23_5653102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5653102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653102 prefixEnd_5653102 := by exact prefixLift 5653102
  have htrace : WordTrace (prefixWord ++ tailWord_5653102) baseStart_5653102 baseEnd_5653102 := by
    simpa [prefixWord, tailWord_5653102, baseEnd_5653102] using wordTrace_append hprefix tailTrace_5653102
  have hstable : (prefixWord ++ tailWord_5653102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653102).length < 2 ^ (prefixWord ++ tailWord_5653102).sum := by decide
  have hdescent : baseEnd_5653102 < baseStart_5653102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653149 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_5653149 : Nat := 118140960795 + 5653149 * 2 ^ 59
def prefixEnd_5653149 : Nat := 4983230072969 + 3 ^ 40 * 5653149 * 2
def baseEnd_5653149 : Nat := 2902782648484007762239147

theorem tailTrace_5653149 : CollatzResearch.WordTrace tailWord_5653149 prefixEnd_5653149 2902782648484007762239147 := by
  unfold tailWord_5653149
  simp only [CollatzResearch.WordTrace]
  refine ⟨206187282996614128828442501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137458188664409419218961667 206187282996614128828442501)
  ·
    refine ⟨38660115561865149155332969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206187282996614128828442501 38660115561865149155332969)
    ·
      refine ⟨28995086671398861866499727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38660115561865149155332969 28995086671398861866499727)
      ·
        refine ⟨43492630007098292799749591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28995086671398861866499727 43492630007098292799749591)
        ·
          refine ⟨65238945010647439199624387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43492630007098292799749591 65238945010647439199624387)
          ·
            refine ⟨97858417515971158799436581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65238945010647439199624387 97858417515971158799436581)
            ·
              refine ⟨18348453284244592274894359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97858417515971158799436581 18348453284244592274894359)
              ·
                refine ⟨27522679926366888412341539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18348453284244592274894359 27522679926366888412341539)
                ·
                  refine ⟨41284019889550332618512309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27522679926366888412341539 41284019889550332618512309)
                  ·
                    refine ⟨3870376864645343682985529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41284019889550332618512309 3870376864645343682985529)
                    ·
                      refine ⟨2902782648484007762239147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870376864645343682985529 2902782648484007762239147)
                      ·
                        rfl

theorem cell23_5653149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_5653149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653149 prefixEnd_5653149 := by exact prefixLift 5653149
  have htrace : WordTrace (prefixWord ++ tailWord_5653149) baseStart_5653149 baseEnd_5653149 := by
    simpa [prefixWord, tailWord_5653149, baseEnd_5653149] using wordTrace_append hprefix tailTrace_5653149
  have hstable : (prefixWord ++ tailWord_5653149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653149).length < 2 ^ (prefixWord ++ tailWord_5653149).sum := by decide
  have hdescent : baseEnd_5653149 < baseStart_5653149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653173 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_5653173 : Nat := 118140960795 + 5653173 * 2 ^ 59
def prefixEnd_5653173 : Nat := 4983230072969 + 3 ^ 40 * 5653173 * 2
def baseEnd_5653173 : Nat := 2902794972019715668339037

theorem tailTrace_5653173 : CollatzResearch.WordTrace tailWord_5653173 prefixEnd_5653173 2902794972019715668339037 := by
  unfold tailWord_5653173
  simp only [CollatzResearch.WordTrace]
  refine ⟨206188158348527180927316173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137458772232351453951544115 206188158348527180927316173)
  ·
    refine ⟨77320559380697692847743565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206188158348527180927316173 77320559380697692847743565)
    ·
      refine ⟨28995209767761634817903837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77320559380697692847743565 28995209767761634817903837)
      ·
        refine ⟨10873203662910613056713939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28995209767761634817903837 10873203662910613056713939)
        ·
          refine ⟨16309805494365919585070909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10873203662910613056713939 16309805494365919585070909)
          ·
            refine ⟨6116177060387219844401591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16309805494365919585070909 6116177060387219844401591)
            ·
              refine ⟨9174265590580829766602387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6116177060387219844401591 9174265590580829766602387)
              ·
                refine ⟨13761398385871244649903581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9174265590580829766602387 13761398385871244649903581)
                ·
                  refine ⟨5160524394701716743713843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13761398385871244649903581 5160524394701716743713843)
                  ·
                    refine ⟨7740786592052575115570765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5160524394701716743713843 7740786592052575115570765)
                    ·
                      refine ⟨2902794972019715668339037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7740786592052575115570765 2902794972019715668339037)
                      ·
                        rfl

theorem cell23_5653173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_5653173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653173 prefixEnd_5653173 := by exact prefixLift 5653173
  have htrace : WordTrace (prefixWord ++ tailWord_5653173) baseStart_5653173 baseEnd_5653173 := by
    simpa [prefixWord, tailWord_5653173, baseEnd_5653173] using wordTrace_append hprefix tailTrace_5653173
  have hstable : (prefixWord ++ tailWord_5653173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653173).length < 2 ^ (prefixWord ++ tailWord_5653173).sum := by decide
  have hdescent : baseEnd_5653173 < baseStart_5653173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653192 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_5653192 : Nat := 118140960795 + 5653192 * 2 ^ 59
def prefixEnd_5653192 : Nat := 4983230072969 + 3 ^ 40 * 5653192 * 2
def baseEnd_5653192 : Nat := 2902804728152151094001449

theorem tailTrace_5653192 : CollatzResearch.WordTrace tailWord_5653192 prefixEnd_5653192 2902804728152151094001449 := by
  unfold tailWord_5653192
  simp only [CollatzResearch.WordTrace]
  refine ⟨103094425667729173586128915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137459234223638898114838553 103094425667729173586128915)
  ·
    refine ⟨154641638501593760379193373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103094425667729173586128915 154641638501593760379193373)
    ·
      refine ⟨57990614438097660142197515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154641638501593760379193373 57990614438097660142197515)
      ·
        refine ⟨86985921657146490213296273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57990614438097660142197515 86985921657146490213296273)
        ·
          refine ⟨65239441242859867659972205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86985921657146490213296273 65239441242859867659972205)
          ·
            refine ⟨24464790466072450372489577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65239441242859867659972205 24464790466072450372489577)
            ·
              refine ⟨18348592849554337779367183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24464790466072450372489577 18348592849554337779367183)
              ·
                refine ⟨27522889274331506669050775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18348592849554337779367183 27522889274331506669050775)
                ·
                  refine ⟨41284333911497260003576163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27522889274331506669050775 41284333911497260003576163)
                  ·
                    refine ⟨61926500867245890005364245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41284333911497260003576163 61926500867245890005364245)
                    ·
                      refine ⟨2902804728152151094001449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61926500867245890005364245 2902804728152151094001449)
                      ·
                        rfl

theorem cell23_5653192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_5653192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653192 prefixEnd_5653192 := by exact prefixLift 5653192
  have htrace : WordTrace (prefixWord ++ tailWord_5653192) baseStart_5653192 baseEnd_5653192 := by
    simpa [prefixWord, tailWord_5653192, baseEnd_5653192] using wordTrace_append hprefix tailTrace_5653192
  have hstable : (prefixWord ++ tailWord_5653192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653192).length < 2 ^ (prefixWord ++ tailWord_5653192).sum := by decide
  have hdescent : baseEnd_5653192 < baseStart_5653192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653196 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5653196 : Nat := 118140960795 + 5653196 * 2 ^ 59
def prefixEnd_5653196 : Nat := 4983230072969 + 3 ^ 40 * 5653196 * 2
def baseEnd_5653196 : Nat := 2902806782074769078351431

theorem tailTrace_5653196 : CollatzResearch.WordTrace tailWord_5653196 prefixEnd_5653196 2902806782074769078351431 := by
  unfold tailWord_5653196
  simp only [CollatzResearch.WordTrace]
  refine ⟨103094498613721927927701721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137459331484962570570268961 103094498613721927927701721)
  ·
    refine ⟨77320873960291445945776291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103094498613721927927701721 77320873960291445945776291)
    ·
      refine ⟨115981310940437168918664437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77320873960291445945776291 115981310940437168918664437)
      ·
        refine ⟨10873247900665984586124791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115981310940437168918664437 10873247900665984586124791)
        ·
          refine ⟨16309871850998976879187187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10873247900665984586124791 16309871850998976879187187)
          ·
            refine ⟨24464807776498465318780781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16309871850998976879187187 24464807776498465318780781)
            ·
              refine ⟨9174302916186924494542793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24464807776498465318780781 9174302916186924494542793)
              ·
                refine ⟨6880727187140193370907095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9174302916186924494542793 6880727187140193370907095)
                ·
                  refine ⟨10321090780710290056360643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6880727187140193370907095 10321090780710290056360643)
                  ·
                    refine ⟨15481636171065435084540965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10321090780710290056360643 15481636171065435084540965)
                    ·
                      refine ⟨2902806782074769078351431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15481636171065435084540965 2902806782074769078351431)
                      ·
                        rfl

theorem cell23_5653196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5653196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653196 prefixEnd_5653196 := by exact prefixLift 5653196
  have htrace : WordTrace (prefixWord ++ tailWord_5653196) baseStart_5653196 baseEnd_5653196 := by
    simpa [prefixWord, tailWord_5653196, baseEnd_5653196] using wordTrace_append hprefix tailTrace_5653196
  have hstable : (prefixWord ++ tailWord_5653196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653196).length < 2 ^ (prefixWord ++ tailWord_5653196).sum := by decide
  have hdescent : baseEnd_5653196 < baseStart_5653196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653229 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_5653229 : Nat := 118140960795 + 5653229 * 2 ^ 59
def prefixEnd_5653229 : Nat := 4983230072969 + 3 ^ 40 * 5653229 * 2
def baseEnd_5653229 : Nat := 2902823726936367449238779

theorem tailTrace_5653229 : CollatzResearch.WordTrace tailWord_5653229 prefixEnd_5653229 2902823726936367449238779 := by
  unfold tailWord_5653229
  simp only [CollatzResearch.WordTrace]
  refine ⟨206190200836324302491354741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137460133890882868327569827 206190200836324302491354741)
  ·
    refine ⟨19330331328405403358564507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206190200836324302491354741 19330331328405403358564507)
    ·
      refine ⟨28995496992608105037846761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19330331328405403358564507 28995496992608105037846761)
      ·
        refine ⟨21746622744456078778385071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28995496992608105037846761 21746622744456078778385071)
        ·
          refine ⟨32619934116684118167577607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21746622744456078778385071 32619934116684118167577607)
          ·
            refine ⟨48929901175026177251366411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32619934116684118167577607 48929901175026177251366411)
            ·
              refine ⟨73394851762539265877049617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48929901175026177251366411 73394851762539265877049617)
              ·
                refine ⟨55046138821904449407787213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73394851762539265877049617 55046138821904449407787213)
                ·
                  refine ⟨20642302058214168527920205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55046138821904449407787213 20642302058214168527920205)
                  ·
                    refine ⟨7740863271830313197970077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20642302058214168527920205 7740863271830313197970077)
                    ·
                      refine ⟨2902823726936367449238779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7740863271830313197970077 2902823726936367449238779)
                      ·
                        rfl

theorem cell23_5653229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_5653229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653229 prefixEnd_5653229 := by exact prefixLift 5653229
  have htrace : WordTrace (prefixWord ++ tailWord_5653229) baseStart_5653229 baseEnd_5653229 := by
    simpa [prefixWord, tailWord_5653229, baseEnd_5653229] using wordTrace_append hprefix tailTrace_5653229
  have hstable : (prefixWord ++ tailWord_5653229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653229).length < 2 ^ (prefixWord ++ tailWord_5653229).sum := by decide
  have hdescent : baseEnd_5653229 < baseStart_5653229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653230 : List Nat := [4, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_5653230 : Nat := 118140960795 + 5653230 * 2 ^ 59
def prefixEnd_5653230 : Nat := 4983230072969 + 3 ^ 40 * 5653230 * 2
def baseEnd_5653230 : Nat := 2902824240417021945326275

theorem tailTrace_5653230 : CollatzResearch.WordTrace tailWord_5653230 prefixEnd_5653230 2902824240417021945326275 := by
  unfold tailWord_5653230
  simp only [CollatzResearch.WordTrace]
  refine ⟨25773779663665084957767643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137460158206213786441427429 25773779663665084957767643)
  ·
    refine ⟨38660669495497627436651465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25773779663665084957767643 38660669495497627436651465)
    ·
      refine ⟨28995502121623220577488599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38660669495497627436651465 28995502121623220577488599)
      ·
        refine ⟨43493253182434830866232899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28995502121623220577488599 43493253182434830866232899)
        ·
          refine ⟨65239879773652246299349349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43493253182434830866232899 65239879773652246299349349)
          ·
            refine ⟨12232477457559796181128003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65239879773652246299349349 12232477457559796181128003)
            ·
              refine ⟨18348716186339694271692005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12232477457559796181128003 18348716186339694271692005)
              ·
                refine ⟨3440384284938692675942251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18348716186339694271692005 3440384284938692675942251)
                ·
                  refine ⟨5160576427408039013913377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440384284938692675942251 5160576427408039013913377)
                  ·
                    refine ⟨3870432320556029260435033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160576427408039013913377 3870432320556029260435033)
                    ·
                      refine ⟨2902824240417021945326275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870432320556029260435033 2902824240417021945326275)
                      ·
                        rfl

theorem cell23_5653230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_5653230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653230 prefixEnd_5653230 := by exact prefixLift 5653230
  have htrace : WordTrace (prefixWord ++ tailWord_5653230) baseStart_5653230 baseEnd_5653230 := by
    simpa [prefixWord, tailWord_5653230, baseEnd_5653230] using wordTrace_append hprefix tailTrace_5653230
  have hstable : (prefixWord ++ tailWord_5653230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653230).length < 2 ^ (prefixWord ++ tailWord_5653230).sum := by decide
  have hdescent : baseEnd_5653230 < baseStart_5653230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653246 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_5653246 : Nat := 118140960795 + 5653246 * 2 ^ 59
def prefixEnd_5653246 : Nat := 4983230072969 + 3 ^ 40 * 5653246 * 2
def baseEnd_5653246 : Nat := 2902832456107493882726201

theorem tailTrace_5653246 : CollatzResearch.WordTrace tailWord_5653246 prefixEnd_5653246 2902832456107493882726201 := by
  unfold tailWord_5653246
  simp only [CollatzResearch.WordTrace]
  refine ⟨25773852609657839299340449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137460547251508476263149061 25773852609657839299340449)
  ·
    refine ⟨19330389457243379474505337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25773852609657839299340449 19330389457243379474505337)
    ·
      refine ⟨14497792092932534605879003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19330389457243379474505337 14497792092932534605879003)
      ·
        refine ⟨21746688139398801908818505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14497792092932534605879003 21746688139398801908818505)
        ·
          refine ⟨16310016104549101431613879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21746688139398801908818505 16310016104549101431613879)
          ·
            refine ⟨24465024156823652147420819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16310016104549101431613879 24465024156823652147420819)
            ·
              refine ⟨36697536235235478221131229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24465024156823652147420819 36697536235235478221131229)
              ·
                refine ⟨13761576088213304332924211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36697536235235478221131229 13761576088213304332924211)
                ·
                  refine ⟨20642364132319956499386317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13761576088213304332924211 20642364132319956499386317)
                  ·
                    refine ⟨7740886549619983687269869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20642364132319956499386317 7740886549619983687269869)
                    ·
                      refine ⟨2902832456107493882726201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7740886549619983687269869 2902832456107493882726201)
                      ·
                        rfl

theorem cell23_5653246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_5653246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653246 prefixEnd_5653246 := by exact prefixLift 5653246
  have htrace : WordTrace (prefixWord ++ tailWord_5653246) baseStart_5653246 baseEnd_5653246 := by
    simpa [prefixWord, tailWord_5653246, baseEnd_5653246] using wordTrace_append hprefix tailTrace_5653246
  have hstable : (prefixWord ++ tailWord_5653246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653246).length < 2 ^ (prefixWord ++ tailWord_5653246).sum := by decide
  have hdescent : baseEnd_5653246 < baseStart_5653246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653256 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_5653256 : Nat := 118140960795 + 5653256 * 2 ^ 59
def prefixEnd_5653256 : Nat := 4983230072969 + 3 ^ 40 * 5653256 * 2
def baseEnd_5653256 : Nat := 2902837590914038843601155

theorem tailTrace_5653256 : CollatzResearch.WordTrace tailWord_5653256 prefixEnd_5653256 2902837590914038843601155 := by
  unfold tailWord_5653256
  simp only [CollatzResearch.WordTrace]
  refine ⟨103095592803613243051293811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137460790404817657401725081 103095592803613243051293811)
  ·
    refine ⟨154643389205419864576940717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103095592803613243051293811 154643389205419864576940717)
    ·
      refine ⟨57991270952032449216352769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154643389205419864576940717 57991270952032449216352769)
      ·
        refine ⟨43493453214024336912264577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57991270952032449216352769 43493453214024336912264577)
        ·
          refine ⟨32620089910518252684198433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43493453214024336912264577 32620089910518252684198433)
          ·
            refine ⟨24465067432888689513148825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32620089910518252684198433 24465067432888689513148825)
            ·
              refine ⟨18348800574666517134861619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24465067432888689513148825 18348800574666517134861619)
              ·
                refine ⟨27523200861999775702292429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18348800574666517134861619 27523200861999775702292429)
                ·
                  refine ⟨10321200323249915888359661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27523200861999775702292429 10321200323249915888359661)
                  ·
                    refine ⟨3870450121218718458134873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10321200323249915888359661 3870450121218718458134873)
                    ·
                      refine ⟨2902837590914038843601155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870450121218718458134873 2902837590914038843601155)
                      ·
                        rfl

theorem cell23_5653256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_5653256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653256 prefixEnd_5653256 := by exact prefixLift 5653256
  have htrace : WordTrace (prefixWord ++ tailWord_5653256) baseStart_5653256 baseEnd_5653256 := by
    simpa [prefixWord, tailWord_5653256, baseEnd_5653256] using wordTrace_append hprefix tailTrace_5653256
  have hstable : (prefixWord ++ tailWord_5653256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653256).length < 2 ^ (prefixWord ++ tailWord_5653256).sum := by decide
  have hdescent : baseEnd_5653256 < baseStart_5653256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653262 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_5653262 : Nat := 118140960795 + 5653262 * 2 ^ 59
def prefixEnd_5653262 : Nat := 4983230072969 + 3 ^ 40 * 5653262 * 2
def baseEnd_5653262 : Nat := 967613557265988606708709

theorem tailTrace_5653262 : CollatzResearch.WordTrace tailWord_5653262 prefixEnd_5653262 967613557265988606708709 := by
  unfold tailWord_5653262
  simp only [CollatzResearch.WordTrace]
  refine ⟨25773925555650593640913255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137460936296803166084870693 25773925555650593640913255)
  ·
    refine ⟨38660888333475890461369883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25773925555650593640913255 38660888333475890461369883)
    ·
      refine ⟨57991332500213835692054825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38660888333475890461369883 57991332500213835692054825)
      ·
        refine ⟨43493499375160376769041119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57991332500213835692054825 43493499375160376769041119)
        ·
          refine ⟨65240249062740565153561679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43493499375160376769041119 65240249062740565153561679)
          ·
            refine ⟨97860373594110847730342519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65240249062740565153561679 97860373594110847730342519)
            ·
              refine ⟨146790560391166271595513779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97860373594110847730342519 146790560391166271595513779)
              ·
                refine ⟨220185840586749407393270669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146790560391166271595513779 220185840586749407393270669)
                ·
                  refine ⟨82569690220031027772476501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220185840586749407393270669 82569690220031027772476501)
                  ·
                    refine ⟨967613557265988606708709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82569690220031027772476501 967613557265988606708709)
                    ·
                      rfl

theorem cell23_5653262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_5653262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653262 prefixEnd_5653262 := by exact prefixLift 5653262
  have htrace : WordTrace (prefixWord ++ tailWord_5653262) baseStart_5653262 baseEnd_5653262 := by
    simpa [prefixWord, tailWord_5653262, baseEnd_5653262] using wordTrace_append hprefix tailTrace_5653262
  have hstable : (prefixWord ++ tailWord_5653262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653262).length < 2 ^ (prefixWord ++ tailWord_5653262).sum := by decide
  have hdescent : baseEnd_5653262 < baseStart_5653262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653272 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5653272 : Nat := 118140960795 + 5653272 * 2 ^ 59
def prefixEnd_5653272 : Nat := 4983230072969 + 3 ^ 40 * 5653272 * 2
def baseEnd_5653272 : Nat := 2902845806604510781001081

theorem tailTrace_5653272 : CollatzResearch.WordTrace tailWord_5653272 prefixEnd_5653272 2902845806604510781001081 := by
  unfold tailWord_5653272
  simp only [CollatzResearch.WordTrace]
  refine ⟨103095884587584260417585035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137461179450112347223446713 103095884587584260417585035)
  ·
    refine ⟨154643826881376390626377553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103095884587584260417585035 154643826881376390626377553)
    ·
      refine ⟨115982870161032292969783165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154643826881376390626377553 115982870161032292969783165)
      ·
        refine ⟨43493576310387109863668687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115982870161032292969783165 43493576310387109863668687)
        ·
          refine ⟨65240364465580664795503031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43493576310387109863668687 65240364465580664795503031)
          ·
            refine ⟨97860546698370997193254547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65240364465580664795503031 97860546698370997193254547)
            ·
              refine ⟨146790820047556495789881821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97860546698370997193254547 146790820047556495789881821)
              ·
                refine ⟨55046557517833685921205683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146790820047556495789881821 55046557517833685921205683)
                ·
                  refine ⟨82569836276750528881808525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55046557517833685921205683 82569836276750528881808525)
                  ·
                    refine ⟨30963688603781448330678197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82569836276750528881808525 30963688603781448330678197)
                    ·
                      refine ⟨2902845806604510781001081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30963688603781448330678197 2902845806604510781001081)
                      ·
                        rfl

theorem cell23_5653272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5653272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653272 prefixEnd_5653272 := by exact prefixLift 5653272
  have htrace : WordTrace (prefixWord ++ tailWord_5653272) baseStart_5653272 baseEnd_5653272 := by
    simpa [prefixWord, tailWord_5653272, baseEnd_5653272] using wordTrace_append hprefix tailTrace_5653272
  have hstable : (prefixWord ++ tailWord_5653272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653272).length < 2 ^ (prefixWord ++ tailWord_5653272).sum := by decide
  have hdescent : baseEnd_5653272 < baseStart_5653272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653299 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 4]
def baseStart_5653299 : Nat := 118140960795 + 5653299 * 2 ^ 59
def prefixEnd_5653299 : Nat := 4983230072969 + 3 ^ 40 * 5653299 * 2
def baseEnd_5653299 : Nat := 2902859670582182175363457

theorem tailTrace_5653299 : CollatzResearch.WordTrace tailWord_5653299 prefixEnd_5653299 2902859670582182175363457 := by
  unfold tailWord_5653299
  simp only [CollatzResearch.WordTrace]
  refine ⟨206192753946070704446402951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137461835964047136297601967 206192753946070704446402951)
  ·
    refine ⟨309289130919106056669604427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206192753946070704446402951 309289130919106056669604427)
    ·
      refine ⟨463933696378659085004406641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309289130919106056669604427 463933696378659085004406641)
      ·
        refine ⟨347950272283994313753304981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463933696378659085004406641 347950272283994313753304981)
        ·
          refine ⟨16310169013312233457186171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 347950272283994313753304981 16310169013312233457186171)
          ·
            refine ⟨24465253519968350185779257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16310169013312233457186171 24465253519968350185779257)
            ·
              refine ⟨18348940139976262639334443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24465253519968350185779257 18348940139976262639334443)
              ·
                refine ⟨27523410209964393959001665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18348940139976262639334443 27523410209964393959001665)
                ·
                  refine ⟨20642557657473295469251249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27523410209964393959001665 20642557657473295469251249)
                  ·
                    refine ⟨15481918243104971601938437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20642557657473295469251249 15481918243104971601938437)
                    ·
                      refine ⟨2902859670582182175363457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15481918243104971601938437 2902859670582182175363457)
                      ·
                        rfl

theorem cell23_5653299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_5653299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653299 prefixEnd_5653299 := by exact prefixLift 5653299
  have htrace : WordTrace (prefixWord ++ tailWord_5653299) baseStart_5653299 baseEnd_5653299 := by
    simpa [prefixWord, tailWord_5653299, baseEnd_5653299] using wordTrace_append hprefix tailTrace_5653299
  have hstable : (prefixWord ++ tailWord_5653299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653299).length < 2 ^ (prefixWord ++ tailWord_5653299).sum := by decide
  have hdescent : baseEnd_5653299 < baseStart_5653299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653460 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_5653460 : Nat := 118140960795 + 5653460 * 2 ^ 59
def prefixEnd_5653460 : Nat := 4983230072969 + 3 ^ 40 * 5653460 * 2
def baseEnd_5653460 : Nat := 2902942340967556045450217

theorem tailTrace_5653460 : CollatzResearch.WordTrace tailWord_5653460 prefixEnd_5653460 2902942340967556045450217 := by
  unfold tailWord_5653460
  simp only [CollatzResearch.WordTrace]
  refine ⟨103099313049243714471506917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137465750732324952628675889 103099313049243714471506917)
  ·
    refine ⟨19331121196733196463407547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103099313049243714471506917 19331121196733196463407547)
    ·
      refine ⟨28996681795099794695111321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19331121196733196463407547 28996681795099794695111321)
      ·
        refine ⟨21747511346324846021333491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28996681795099794695111321 21747511346324846021333491)
        ·
          refine ⟨32621267019487269032000237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21747511346324846021333491 32621267019487269032000237)
          ·
            refine ⟨12232975132307725887000089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32621267019487269032000237 12232975132307725887000089)
            ·
              refine ⟨9174731349230794415250067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12232975132307725887000089 9174731349230794415250067)
              ·
                refine ⟨13762097023846191622875101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9174731349230794415250067 13762097023846191622875101)
                ·
                  refine ⟨5160786383942321858578163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13762097023846191622875101 5160786383942321858578163)
                  ·
                    refine ⟨7741179575913482787867245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5160786383942321858578163 7741179575913482787867245)
                    ·
                      refine ⟨2902942340967556045450217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7741179575913482787867245 2902942340967556045450217)
                      ·
                        rfl

theorem cell23_5653460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_5653460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653460 prefixEnd_5653460 := by exact prefixLift 5653460
  have htrace : WordTrace (prefixWord ++ tailWord_5653460) baseStart_5653460 baseEnd_5653460 := by
    simpa [prefixWord, tailWord_5653460, baseEnd_5653460] using wordTrace_append hprefix tailTrace_5653460
  have hstable : (prefixWord ++ tailWord_5653460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653460).length < 2 ^ (prefixWord ++ tailWord_5653460).sum := by decide
  have hdescent : baseEnd_5653460 < baseStart_5653460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653494 : List Nat := [5, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_5653494 : Nat := 118140960795 + 5653494 * 2 ^ 59
def prefixEnd_5653494 : Nat := 4983230072969 + 3 ^ 40 * 5653494 * 2
def baseEnd_5653494 : Nat := 2902959799309808912425061

theorem tailTrace_5653494 : CollatzResearch.WordTrace tailWord_5653494 prefixEnd_5653494 2902959799309808912425061 := by
  unfold tailWord_5653494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887491636272765796859471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137466577453576168499834357 12887491636272765796859471)
  ·
    refine ⟨19331237454409148695289207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12887491636272765796859471 19331237454409148695289207)
    ·
      refine ⟨28996856181613723042933811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19331237454409148695289207 28996856181613723042933811)
      ·
        refine ⟨43495284272420584564400717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28996856181613723042933811 43495284272420584564400717)
        ·
          refine ⟨16310731602157719211650269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43495284272420584564400717 16310731602157719211650269)
          ·
            refine ⟨6116524350809144704368851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16310731602157719211650269 6116524350809144704368851)
            ·
              refine ⟨9174786526213717056553277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6116524350809144704368851 9174786526213717056553277)
              ·
                refine ⟨3440544947330143896207479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9174786526213717056553277 3440544947330143896207479)
                ·
                  refine ⟨5160817420995215844311219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440544947330143896207479 5160817420995215844311219)
                  ·
                    refine ⟨7741226131492823766466829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5160817420995215844311219 7741226131492823766466829)
                    ·
                      refine ⟨2902959799309808912425061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7741226131492823766466829 2902959799309808912425061)
                      ·
                        rfl

theorem cell23_5653494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_5653494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653494 prefixEnd_5653494 := by exact prefixLift 5653494
  have htrace : WordTrace (prefixWord ++ tailWord_5653494) baseStart_5653494 baseEnd_5653494 := by
    simpa [prefixWord, tailWord_5653494, baseEnd_5653494] using wordTrace_append hprefix tailTrace_5653494
  have hstable : (prefixWord ++ tailWord_5653494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653494).length < 2 ^ (prefixWord ++ tailWord_5653494).sum := by decide
  have hdescent : baseEnd_5653494 < baseStart_5653494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653527 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 2, 4]
def baseStart_5653527 : Nat := 118140960795 + 5653527 * 2 ^ 59
def prefixEnd_5653527 : Nat := 4983230072969 + 3 ^ 40 * 5653527 * 2
def baseEnd_5653527 : Nat := 967658914723802427770803

theorem tailTrace_5653527 : CollatzResearch.WordTrace tailWord_5653527 prefixEnd_5653527 967658914723802427770803 := by
  unfold tailWord_5653527
  simp only [CollatzResearch.WordTrace]
  refine ⟨206201069789244699385702835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137467379859496466257135223 206201069789244699385702835)
  ·
    refine ⟨309301604683867049078554253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206201069789244699385702835 309301604683867049078554253)
    ·
      refine ⟨115988101756450143404457845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 309301604683867049078554253 115988101756450143404457845)
      ·
        refine ⟨10873884539667200944167923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115988101756450143404457845 10873884539667200944167923)
        ·
          refine ⟨16310826809500801416251885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10873884539667200944167923 16310826809500801416251885)
          ·
            refine ⟨6116560053562800531094457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16310826809500801416251885 6116560053562800531094457)
            ·
              refine ⟨4587420040172100398320843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6116560053562800531094457 4587420040172100398320843)
              ·
                refine ⟨6881130060258150597481265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587420040172100398320843 6881130060258150597481265)
                ·
                  refine ⟨5160847545193612948110949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6881130060258150597481265 5160847545193612948110949)
                  ·
                    refine ⟨967658914723802427770803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5160847545193612948110949 967658914723802427770803)
                    ·
                      rfl

theorem cell23_5653527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_5653527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653527 prefixEnd_5653527 := by exact prefixLift 5653527
  have htrace : WordTrace (prefixWord ++ tailWord_5653527) baseStart_5653527 baseEnd_5653527 := by
    simpa [prefixWord, tailWord_5653527, baseEnd_5653527] using wordTrace_append hprefix tailTrace_5653527
  have hstable : (prefixWord ++ tailWord_5653527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653527).length < 2 ^ (prefixWord ++ tailWord_5653527).sum := by decide
  have hdescent : baseEnd_5653527 < baseStart_5653527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653576 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_5653576 : Nat := 118140960795 + 5653576 * 2 ^ 59
def prefixEnd_5653576 : Nat := 4983230072969 + 3 ^ 40 * 5653576 * 2
def baseEnd_5653576 : Nat := 2903001904723477591599683

theorem tailTrace_5653576 : CollatzResearch.WordTrace tailWord_5653576 prefixEnd_5653576 2903001904723477591599683 := by
  unfold tailWord_5653576
  simp only [CollatzResearch.WordTrace]
  refine ⟨103101428483033590377118291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137468571310711453836157721 103101428483033590377118291)
  ·
    refine ⟨154652142724550385565677437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103101428483033590377118291 154652142724550385565677437)
    ·
      refine ⟨57994553521706394587129039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154652142724550385565677437 57994553521706394587129039)
      ·
        refine ⟨86991830282559591880693559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57994553521706394587129039 86991830282559591880693559)
        ·
          refine ⟨130487745423839387821040339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86991830282559591880693559 130487745423839387821040339)
          ·
            refine ⟨195731618135759081731560509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130487745423839387821040339 195731618135759081731560509)
            ·
              refine ⟨73399356800909655649335191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195731618135759081731560509 73399356800909655649335191)
              ·
                refine ⟨110099035201364483474002787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73399356800909655649335191 110099035201364483474002787)
                ·
                  refine ⟨165148552802046725211004181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110099035201364483474002787 165148552802046725211004181)
                  ·
                    refine ⟨7741338412595940244265821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 165148552802046725211004181 7741338412595940244265821)
                    ·
                      refine ⟨2903001904723477591599683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7741338412595940244265821 2903001904723477591599683)
                      ·
                        rfl

theorem cell23_5653576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_5653576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653576 prefixEnd_5653576 := by exact prefixLift 5653576
  have htrace : WordTrace (prefixWord ++ tailWord_5653576) baseStart_5653576 baseEnd_5653576 := by
    simpa [prefixWord, tailWord_5653576, baseEnd_5653576] using wordTrace_append hprefix tailTrace_5653576
  have hstable : (prefixWord ++ tailWord_5653576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653576).length < 2 ^ (prefixWord ++ tailWord_5653576).sum := by decide
  have hdescent : baseEnd_5653576 < baseStart_5653576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653676 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_5653676 : Nat := 118140960795 + 5653676 * 2 ^ 59
def prefixEnd_5653676 : Nat := 4983230072969 + 3 ^ 40 * 5653676 * 2
def baseEnd_5653676 : Nat := 2903053252788927200349223

theorem tailTrace_5653676 : CollatzResearch.WordTrace tailWord_5653676 prefixEnd_5653676 2903053252788927200349223 := by
  unfold tailWord_5653676
  simp only [CollatzResearch.WordTrace]
  refine ⟨103103252132852448916438441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137471002843803265221917921 103103252132852448916438441)
  ·
    refine ⟨77327439099639336687328831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103103252132852448916438441 77327439099639336687328831)
    ·
      refine ⟨115991158649459005030993247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77327439099639336687328831 115991158649459005030993247)
      ·
        refine ⟨173986737974188507546489871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115991158649459005030993247 173986737974188507546489871)
        ·
          refine ⟨260980106961282761319734807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173986737974188507546489871 260980106961282761319734807)
          ·
            refine ⟨391470160441924141979602211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260980106961282761319734807 391470160441924141979602211)
            ·
              refine ⟨587205240662886212969403317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391470160441924141979602211 587205240662886212969403317)
              ·
                refine ⟨55050491312145582465881561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 587205240662886212969403317 55050491312145582465881561)
                ·
                  refine ⟨41287868484109186849411171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55050491312145582465881561 41287868484109186849411171)
                  ·
                    refine ⟨61931802726163780274116757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41287868484109186849411171 61931802726163780274116757)
                    ·
                      refine ⟨2903053252788927200349223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61931802726163780274116757 2903053252788927200349223)
                      ·
                        rfl

theorem cell23_5653676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_5653676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653676 prefixEnd_5653676 := by exact prefixLift 5653676
  have htrace : WordTrace (prefixWord ++ tailWord_5653676) baseStart_5653676 baseEnd_5653676 := by
    simpa [prefixWord, tailWord_5653676, baseEnd_5653676] using wordTrace_append hprefix tailTrace_5653676
  have hstable : (prefixWord ++ tailWord_5653676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653676).length < 2 ^ (prefixWord ++ tailWord_5653676).sum := by decide
  have hdescent : baseEnd_5653676 < baseStart_5653676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653683 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 3]
def baseStart_5653683 : Nat := 118140960795 + 5653683 * 2 ^ 59
def prefixEnd_5653683 : Nat := 4983230072969 + 3 ^ 40 * 5653683 * 2
def baseEnd_5653683 : Nat := 2903056847153508672961691

theorem tailTrace_5653683 : CollatzResearch.WordTrace tailWord_5653683 prefixEnd_5653683 2903056847153508672961691 := by
  unfold tailWord_5653683
  simp only [CollatzResearch.WordTrace]
  refine ⟨206206759576679538028381703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137471173051119692018921135 206206759576679538028381703)
  ·
    refine ⟨309310139365019307042572555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206206759576679538028381703 309310139365019307042572555)
    ·
      refine ⟨463965209047528960563858833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309310139365019307042572555 463965209047528960563858833)
      ·
        refine ⟨347973906785646720422894125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463965209047528960563858833 347973906785646720422894125)
        ·
          refine ⟨130490215044617520158585297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347973906785646720422894125 130490215044617520158585297)
          ·
            refine ⟨97867661283463140118938973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130490215044617520158585297 97867661283463140118938973)
            ·
              refine ⟨36700372981298677544602115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97867661283463140118938973 36700372981298677544602115)
              ·
                refine ⟨55050559471948016316903173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36700372981298677544602115 55050559471948016316903173)
                ·
                  refine ⟨10321979900990253059419345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55050559471948016316903173 10321979900990253059419345)
                  ·
                    refine ⟨7741484925742689794564509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10321979900990253059419345 7741484925742689794564509)
                    ·
                      refine ⟨2903056847153508672961691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7741484925742689794564509 2903056847153508672961691)
                      ·
                        rfl

theorem cell23_5653683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_5653683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653683 prefixEnd_5653683 := by exact prefixLift 5653683
  have htrace : WordTrace (prefixWord ++ tailWord_5653683) baseStart_5653683 baseEnd_5653683 := by
    simpa [prefixWord, tailWord_5653683, baseEnd_5653683] using wordTrace_append hprefix tailTrace_5653683
  have hstable : (prefixWord ++ tailWord_5653683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653683).length < 2 ^ (prefixWord ++ tailWord_5653683).sum := by decide
  have hdescent : baseEnd_5653683 < baseStart_5653683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653717 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5653717 : Nat := 118140960795 + 5653717 * 2 ^ 59
def prefixEnd_5653717 : Nat := 4983230072969 + 3 ^ 40 * 5653717 * 2
def baseEnd_5653717 : Nat := 2903074305495761539936535

theorem tailTrace_5653717 : CollatzResearch.WordTrace tailWord_5653717 prefixEnd_5653717 2903074305495761539936535 := by
  unfold tailWord_5653717
  simp only [CollatzResearch.WordTrace]
  refine ⟨206207999658556361835119405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137471999772370907890079603 206207999658556361835119405)
  ·
    refine ⟨77327999871958635688169777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206207999658556361835119405 77327999871958635688169777)
    ·
      refine ⟨57995999903968976766127333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77327999871958635688169777 57995999903968976766127333)
      ·
        refine ⟨10874249981994183143648875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57995999903968976766127333 10874249981994183143648875)
        ·
          refine ⟨16311374972991274715473313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10874249981994183143648875 16311374972991274715473313)
          ·
            refine ⟨12233531229743456036604985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16311374972991274715473313 12233531229743456036604985)
            ·
              refine ⟨9175148422307592027453739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12233531229743456036604985 9175148422307592027453739)
              ·
                refine ⟨13762722633461388041180609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9175148422307592027453739 13762722633461388041180609)
                ·
                  refine ⟨10322041975096041030885457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13762722633461388041180609 10322041975096041030885457)
                  ·
                    refine ⟨7741531481322030773164093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10322041975096041030885457 7741531481322030773164093)
                    ·
                      refine ⟨2903074305495761539936535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7741531481322030773164093 2903074305495761539936535)
                      ·
                        rfl

theorem cell23_5653717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5653717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653717 prefixEnd_5653717 := by exact prefixLift 5653717
  have htrace : WordTrace (prefixWord ++ tailWord_5653717) baseStart_5653717 baseEnd_5653717 := by
    simpa [prefixWord, tailWord_5653717, baseEnd_5653717] using wordTrace_append hprefix tailTrace_5653717
  have hstable : (prefixWord ++ tailWord_5653717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653717).length < 2 ^ (prefixWord ++ tailWord_5653717).sum := by decide
  have hdescent : baseEnd_5653717 < baseStart_5653717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653741 : List Nat := [1, 5, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_5653741 : Nat := 118140960795 + 5653741 * 2 ^ 59
def prefixEnd_5653741 : Nat := 4983230072969 + 3 ^ 40 * 5653741 * 2
def baseEnd_5653741 : Nat := 967695543010489815345475

theorem tailTrace_5653741 : CollatzResearch.WordTrace tailWord_5653741 prefixEnd_5653741 967695543010489815345475 := by
  unfold tailWord_5653741
  simp only [CollatzResearch.WordTrace]
  refine ⟨206208875010469413933993077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137472583340312942622662051 206208875010469413933993077)
  ·
    refine ⟨19332082032231507556311851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206208875010469413933993077 19332082032231507556311851)
    ·
      refine ⟨28998123048347261334467777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19332082032231507556311851 28998123048347261334467777)
      ·
        refine ⟨21748592286260446000850833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28998123048347261334467777 21748592286260446000850833)
        ·
          refine ⟨16311444214695334500638125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21748592286260446000850833 16311444214695334500638125)
          ·
            refine ⟨6116791580510750437739297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16311444214695334500638125 6116791580510750437739297)
            ·
              refine ⟨4587593685383062828304473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6116791580510750437739297 4587593685383062828304473)
              ·
                refine ⟨3440695264037297121228355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4587593685383062828304473 3440695264037297121228355)
                ·
                  refine ⟨5161042896055945681842533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440695264037297121228355 5161042896055945681842533)
                  ·
                    refine ⟨967695543010489815345475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5161042896055945681842533 967695543010489815345475)
                    ·
                      rfl

theorem cell23_5653741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_5653741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653741 prefixEnd_5653741 := by exact prefixLift 5653741
  have htrace : WordTrace (prefixWord ++ tailWord_5653741) baseStart_5653741 baseEnd_5653741 := by
    simpa [prefixWord, tailWord_5653741, baseEnd_5653741] using wordTrace_append hprefix tailTrace_5653741
  have hstable : (prefixWord ++ tailWord_5653741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653741).length < 2 ^ (prefixWord ++ tailWord_5653741).sum := by decide
  have hdescent : baseEnd_5653741 < baseStart_5653741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653753 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_5653753 : Nat := 118140960795 + 5653753 * 2 ^ 59
def prefixEnd_5653753 : Nat := 4983230072969 + 3 ^ 40 * 5653753 * 2
def baseEnd_5653753 : Nat := 2903092790799323399086369

theorem tailTrace_5653753 : CollatzResearch.WordTrace tailWord_5653753 prefixEnd_5653753 2903092790799323399086369 := by
  unfold tailWord_5653753
  simp only [CollatzResearch.WordTrace]
  refine ⟨206209312686425939983429913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137472875124283959988953275 206209312686425939983429913)
  ·
    refine ⟨154656984514819454987572435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206209312686425939983429913 154656984514819454987572435)
    ·
      refine ⟨231985476772229182481358653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154656984514819454987572435 231985476772229182481358653)
      ·
        refine ⟨86994553789585943430509495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231985476772229182481358653 86994553789585943430509495)
        ·
          refine ⟨130491830684378915145764243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86994553789585943430509495 130491830684378915145764243)
          ·
            refine ⟨195737746026568372718646365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130491830684378915145764243 195737746026568372718646365)
            ·
              refine ⟨73401654759963139769492387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195737746026568372718646365 73401654759963139769492387)
              ·
                refine ⟨110102482139944709654238581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73401654759963139769492387 110102482139944709654238581)
                ·
                  refine ⟨10322107700619816530084867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110102482139944709654238581 10322107700619816530084867)
                  ·
                    refine ⟨15483161550929724795127301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10322107700619816530084867 15483161550929724795127301)
                    ·
                      refine ⟨2903092790799323399086369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15483161550929724795127301 2903092790799323399086369)
                      ·
                        rfl

theorem cell23_5653753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_5653753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653753 prefixEnd_5653753 := by exact prefixLift 5653753
  have htrace : WordTrace (prefixWord ++ tailWord_5653753) baseStart_5653753 baseEnd_5653753 := by
    simpa [prefixWord, tailWord_5653753, baseEnd_5653753] using wordTrace_append hprefix tailTrace_5653753
  have hstable : (prefixWord ++ tailWord_5653753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653753).length < 2 ^ (prefixWord ++ tailWord_5653753).sum := by decide
  have hdescent : baseEnd_5653753 < baseStart_5653753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653763 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 1, 6]
def baseStart_5653763 : Nat := 118140960795 + 5653763 * 2 ^ 59
def prefixEnd_5653763 : Nat := 4983230072969 + 3 ^ 40 * 5653763 * 2
def baseEnd_5653763 : Nat := 967699308535289453320441

theorem tailTrace_5653763 : CollatzResearch.WordTrace tailWord_5653763 prefixEnd_5653763 967699308535289453320441 := by
  unfold tailWord_5653763
  simp only [CollatzResearch.WordTrace]
  refine ⟨206209677416389711691293943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137473118277593141127529295 206209677416389711691293943)
  ·
    refine ⟨309314516124584567536940915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206209677416389711691293943 309314516124584567536940915)
    ·
      refine ⟨463971774186876851305411373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309314516124584567536940915 463971774186876851305411373)
      ·
        refine ⟨173989415320078819239529265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 463971774186876851305411373 173989415320078819239529265)
        ·
          refine ⟨130492061490059114429646949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173989415320078819239529265 130492061490059114429646949)
          ·
            refine ⟨24467261529386083955558803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130492061490059114429646949 24467261529386083955558803)
            ·
              refine ⟨36700892294079125933338205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24467261529386083955558803 36700892294079125933338205)
              ·
                refine ⟨13762834610279672225001827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36700892294079125933338205 13762834610279672225001827)
                ·
                  refine ⟨20644251915419508337502741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13762834610279672225001827 20644251915419508337502741)
                  ·
                    refine ⟨967699308535289453320441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20644251915419508337502741 967699308535289453320441)
                    ·
                      rfl

theorem cell23_5653763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 6].length) (baseStart_5653763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653763 prefixEnd_5653763 := by exact prefixLift 5653763
  have htrace : WordTrace (prefixWord ++ tailWord_5653763) baseStart_5653763 baseEnd_5653763 := by
    simpa [prefixWord, tailWord_5653763, baseEnd_5653763] using wordTrace_append hprefix tailTrace_5653763
  have hstable : (prefixWord ++ tailWord_5653763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653763).length < 2 ^ (prefixWord ++ tailWord_5653763).sum := by decide
  have hdescent : baseEnd_5653763 < baseStart_5653763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653770 : List Nat := [3, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_5653770 : Nat := 118140960795 + 5653770 * 2 ^ 59
def prefixEnd_5653770 : Nat := 4983230072969 + 3 ^ 40 * 5653770 * 2
def baseEnd_5653770 : Nat := 2903101519970449832573791

theorem tailTrace_5653770 : CollatzResearch.WordTrace tailWord_5653770 prefixEnd_5653770 2903101519970449832573791 := by
  unfold tailWord_5653770
  simp only [CollatzResearch.WordTrace]
  refine ⟨51552483181841087971699691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137473288484909567924532509 51552483181841087971699691)
  ·
    refine ⟨77328724772761631957549537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51552483181841087971699691 77328724772761631957549537)
    ·
      refine ⟨57996543579571223968162153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77328724772761631957549537 57996543579571223968162153)
      ·
        refine ⟨43497407684678417976121615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57996543579571223968162153 43497407684678417976121615)
        ·
          refine ⟨65246111527017626964182423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43497407684678417976121615 65246111527017626964182423)
          ·
            refine ⟨97869167290526440446273635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65246111527017626964182423 97869167290526440446273635)
            ·
              refine ⟨146803750935789660669410453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97869167290526440446273635 146803750935789660669410453)
              ·
                refine ⟨6881425825115140343878615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146803750935789660669410453 6881425825115140343878615)
                ·
                  refine ⟨10322138737672710515817923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6881425825115140343878615 10322138737672710515817923)
                  ·
                    refine ⟨15483208106509065773726885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10322138737672710515817923 15483208106509065773726885)
                    ·
                      refine ⟨2903101519970449832573791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15483208106509065773726885 2903101519970449832573791)
                      ·
                        rfl

theorem cell23_5653770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_5653770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653770 prefixEnd_5653770 := by exact prefixLift 5653770
  have htrace : WordTrace (prefixWord ++ tailWord_5653770) baseStart_5653770 baseEnd_5653770 := by
    simpa [prefixWord, tailWord_5653770, baseEnd_5653770] using wordTrace_append hprefix tailTrace_5653770
  have hstable : (prefixWord ++ tailWord_5653770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653770).length < 2 ^ (prefixWord ++ tailWord_5653770).sum := by decide
  have hdescent : baseEnd_5653770 < baseStart_5653770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653774 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_5653774 : Nat := 118140960795 + 5653774 * 2 ^ 59
def prefixEnd_5653774 : Nat := 4983230072969 + 3 ^ 40 * 5653774 * 2
def baseEnd_5653774 : Nat := 2903103573893067816923773

theorem tailTrace_5653774 : CollatzResearch.WordTrace tailWord_5653774 prefixEnd_5653774 2903103573893067816923773 := by
  unfold tailWord_5653774
  simp only [CollatzResearch.WordTrace]
  refine ⟨25776259827418732571243047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137473385746233240379962917 25776259827418732571243047)
  ·
    refine ⟨38664389741128098856864571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25776259827418732571243047 38664389741128098856864571)
    ·
      refine ⟨57996584611692148285296857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38664389741128098856864571 57996584611692148285296857)
      ·
        refine ⟨43497438458769111213972643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57996584611692148285296857 43497438458769111213972643)
        ·
          refine ⟨65246157688153666820958965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43497438458769111213972643 65246157688153666820958965)
          ·
            refine ⟨6116827283264406264464903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65246157688153666820958965 6116827283264406264464903)
            ·
              refine ⟨9175240924896609396697355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6116827283264406264464903 9175240924896609396697355)
              ·
                refine ⟨13762861387344914095046033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9175240924896609396697355 13762861387344914095046033)
                ·
                  refine ⟨10322146040508685571284525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13762861387344914095046033 10322146040508685571284525)
                  ·
                    refine ⟨3870804765190757089231697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10322146040508685571284525 3870804765190757089231697)
                    ·
                      refine ⟨2903103573893067816923773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870804765190757089231697 2903103573893067816923773)
                      ·
                        rfl

theorem cell23_5653774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_5653774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653774 prefixEnd_5653774 := by exact prefixLift 5653774
  have htrace : WordTrace (prefixWord ++ tailWord_5653774) baseStart_5653774 baseEnd_5653774 := by
    simpa [prefixWord, tailWord_5653774, baseEnd_5653774] using wordTrace_append hprefix tailTrace_5653774
  have hstable : (prefixWord ++ tailWord_5653774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653774).length < 2 ^ (prefixWord ++ tailWord_5653774).sum := by decide
  have hdescent : baseEnd_5653774 < baseStart_5653774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653797 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 2, 4]
def baseStart_5653797 : Nat := 118140960795 + 5653797 * 2 ^ 59
def prefixEnd_5653797 : Nat := 4983230072969 + 3 ^ 40 * 5653797 * 2
def baseEnd_5653797 : Nat := 967705127982707075645389

theorem tailTrace_5653797 : CollatzResearch.WordTrace tailWord_5653797 prefixEnd_5653797 967705127982707075645389 := by
  unfold tailWord_5653797
  simp only [CollatzResearch.WordTrace]
  refine ⟨206210917498266535498031645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137473944998844356998687763 206210917498266535498031645)
  ·
    refine ⟨77329094061849950811761867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206210917498266535498031645 77329094061849950811761867)
    ·
      refine ⟨115993641092774926217642801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77329094061849950811761867 115993641092774926217642801)
      ·
        refine ⟨86995230819581194663232101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115993641092774926217642801 86995230819581194663232101)
        ·
          refine ⟨16311605778671473999356019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86995230819581194663232101 16311605778671473999356019)
          ·
            refine ⟨24467408668007210999034029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16311605778671473999356019 24467408668007210999034029)
            ·
              refine ⟨9175278250502704124637761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24467408668007210999034029 9175278250502704124637761)
              ·
                refine ⟨6881458687877028093478321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9175278250502704124637761 6881458687877028093478321)
                ·
                  refine ⟨5161094015907771070108741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6881458687877028093478321 5161094015907771070108741)
                  ·
                    refine ⟨967705127982707075645389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5161094015907771070108741 967705127982707075645389)
                    ·
                      rfl

theorem cell23_5653797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_5653797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653797 prefixEnd_5653797 := by exact prefixLift 5653797
  have htrace : WordTrace (prefixWord ++ tailWord_5653797) baseStart_5653797 baseEnd_5653797 := by
    simpa [prefixWord, tailWord_5653797, baseEnd_5653797] using wordTrace_append hprefix tailTrace_5653797
  have hstable : (prefixWord ++ tailWord_5653797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653797).length < 2 ^ (prefixWord ++ tailWord_5653797).sum := by decide
  have hdescent : baseEnd_5653797 < baseStart_5653797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653833 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_5653833 : Nat := 118140960795 + 5653833 * 2 ^ 59
def prefixEnd_5653833 : Nat := 4983230072969 + 3 ^ 40 * 5653833 * 2
def baseEnd_5653833 : Nat := 2903133869251683086086001

theorem tailTrace_5653833 : CollatzResearch.WordTrace tailWord_5653833 prefixEnd_5653833 2903133869251683086086001 := by
  unfold tailWord_5653833
  simp only [CollatzResearch.WordTrace]
  refine ⟨206212230526136113646342153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137474820350757409097561435 206212230526136113646342153)
  ·
    refine ⟨154659172894602085234756615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206212230526136113646342153 154659172894602085234756615)
    ·
      refine ⟨231988759341903127852134923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154659172894602085234756615 231988759341903127852134923)
      ·
        refine ⟨347983139012854691778202385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231988759341903127852134923 347983139012854691778202385)
        ·
          refine ⟨260987354259641018833651789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347983139012854691778202385 260987354259641018833651789)
          ·
            refine ⟨97870257847365382062619421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260987354259641018833651789 97870257847365382062619421)
            ·
              refine ⟨36701346692762018273482283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97870257847365382062619421 36701346692762018273482283)
              ·
                refine ⟨55052020039143027410223425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36701346692762018273482283 55052020039143027410223425)
                ·
                  refine ⟨41289015029357270557667569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55052020039143027410223425 41289015029357270557667569)
                  ·
                    refine ⟨30966761272017952918250677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41289015029357270557667569 30966761272017952918250677)
                    ·
                      refine ⟨2903133869251683086086001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30966761272017952918250677 2903133869251683086086001)
                      ·
                        rfl

theorem cell23_5653833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_5653833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653833 prefixEnd_5653833 := by exact prefixLift 5653833
  have htrace : WordTrace (prefixWord ++ tailWord_5653833) baseStart_5653833 baseEnd_5653833 := by
    simpa [prefixWord, tailWord_5653833, baseEnd_5653833] using wordTrace_append hprefix tailTrace_5653833
  have hstable : (prefixWord ++ tailWord_5653833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653833).length < 2 ^ (prefixWord ++ tailWord_5653833).sum := by decide
  have hdescent : baseEnd_5653833 < baseStart_5653833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653883 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 9]
def baseStart_5653883 : Nat := 118140960795 + 5653883 * 2 ^ 59
def prefixEnd_5653883 : Nat := 4983230072969 + 3 ^ 40 * 5653883 * 2
def baseEnd_5653883 : Nat := 322573282587156432273419

theorem tailTrace_5653883 : CollatzResearch.WordTrace tailWord_5653883 prefixEnd_5653883 322573282587156432273419 := by
  unfold tailWord_5653883
  simp only [CollatzResearch.WordTrace]
  refine ⟨206214054175954972185662303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137476036117303314790441535 206214054175954972185662303)
  ·
    refine ⟨309321081263932458278493455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206214054175954972185662303 309321081263932458278493455)
    ·
      refine ⟨463981621895898687417740183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309321081263932458278493455 463981621895898687417740183)
      ·
        refine ⟨695972432843848031126610275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463981621895898687417740183 695972432843848031126610275)
        ·
          refine ⟨1043958649265772046689915413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695972432843848031126610275 1043958649265772046689915413)
          ·
            refine ⟨48935561684333064688589785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1043958649265772046689915413 48935561684333064688589785)
            ·
              refine ⟨36701671263249798516442339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48935561684333064688589785 36701671263249798516442339)
              ·
                refine ⟨55052506894874697774663509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36701671263249798516442339 55052506894874697774663509)
                ·
                  refine ⟨322573282587156432273419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55052506894874697774663509 322573282587156432273419)
                  ·
                    rfl

theorem cell23_5653883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 9].length) (baseStart_5653883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653883 prefixEnd_5653883 := by exact prefixLift 5653883
  have htrace : WordTrace (prefixWord ++ tailWord_5653883) baseStart_5653883 baseEnd_5653883 := by
    simpa [prefixWord, tailWord_5653883, baseEnd_5653883] using wordTrace_append hprefix tailTrace_5653883
  have hstable : (prefixWord ++ tailWord_5653883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653883).length < 2 ^ (prefixWord ++ tailWord_5653883).sum := by decide
  have hdescent : baseEnd_5653883 < baseStart_5653883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653927 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_5653927 : Nat := 118140960795 + 5653927 * 2 ^ 59
def prefixEnd_5653927 : Nat := 4983230072969 + 3 ^ 40 * 5653927 * 2
def baseEnd_5653927 : Nat := 2903182136433205718310569

theorem tailTrace_5653927 : CollatzResearch.WordTrace tailWord_5653927 prefixEnd_5653927 2903182136433205718310569 := by
  unfold tailWord_5653927
  simp only [CollatzResearch.WordTrace]
  refine ⟨206215658987795567700264035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137477105991863711800176023 206215658987795567700264035)
  ·
    refine ⟨309323488481693351550396053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206215658987795567700264035 309323488481693351550396053)
    ·
      refine ⟨14499538522579375853924815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 309323488481693351550396053 14499538522579375853924815)
      ·
        refine ⟨21749307783869063780887223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14499538522579375853924815 21749307783869063780887223)
        ·
          refine ⟨32623961675803595671330835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21749307783869063780887223 32623961675803595671330835)
          ·
            refine ⟨48935942513705393506996253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32623961675803595671330835 48935942513705393506996253)
            ·
              refine ⟨18350978442639522565123595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48935942513705393506996253 18350978442639522565123595)
              ·
                refine ⟨27526467663959283847685393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18350978442639522565123595 27526467663959283847685393)
                ·
                  refine ⟨20644850747969462885764045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27526467663959283847685393 20644850747969462885764045)
                  ·
                    refine ⟨7741819030488548582161517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20644850747969462885764045 7741819030488548582161517)
                    ·
                      refine ⟨2903182136433205718310569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7741819030488548582161517 2903182136433205718310569)
                      ·
                        rfl

theorem cell23_5653927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_5653927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653927 prefixEnd_5653927 := by exact prefixLift 5653927
  have htrace : WordTrace (prefixWord ++ tailWord_5653927) baseStart_5653927 baseEnd_5653927 := by
    simpa [prefixWord, tailWord_5653927, baseEnd_5653927] using wordTrace_append hprefix tailTrace_5653927
  have hstable : (prefixWord ++ tailWord_5653927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653927).length < 2 ^ (prefixWord ++ tailWord_5653927).sum := by decide
  have hdescent : baseEnd_5653927 < baseStart_5653927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653937 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 2, 5, 2]
def baseStart_5653937 : Nat := 118140960795 + 5653937 * 2 ^ 59
def prefixEnd_5653937 : Nat := 4983230072969 + 3 ^ 40 * 5653937 * 2
def baseEnd_5653937 : Nat := 2903187271239750679185523

theorem tailTrace_5653937 : CollatzResearch.WordTrace tailWord_5653937 prefixEnd_5653937 2903187271239750679185523 := by
  unfold tailWord_5653937
  simp only [CollatzResearch.WordTrace]
  refine ⟨206216023717759339408128065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137477349145172892938752043 206216023717759339408128065)
  ·
    refine ⟨154662017788319504556096049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206216023717759339408128065 154662017788319504556096049)
    ·
      refine ⟨115996513341239628417072037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154662017788319504556096049 115996513341239628417072037)
      ·
        refine ⟨21749346251482430328201007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115996513341239628417072037 21749346251482430328201007)
        ·
          refine ⟨32624019377223645492301511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21749346251482430328201007 32624019377223645492301511)
          ·
            refine ⟨48936029065835468238452267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32624019377223645492301511 48936029065835468238452267)
            ·
              refine ⟨73404043598753202357678401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48936029065835468238452267 73404043598753202357678401)
              ·
                refine ⟨55053032699064901768258801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73404043598753202357678401 55053032699064901768258801)
                ·
                  refine ⟨41289774524298676326194101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55053032699064901768258801 41289774524298676326194101)
                  ·
                    refine ⟨3870916361653000905580697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41289774524298676326194101 3870916361653000905580697)
                    ·
                      refine ⟨2903187271239750679185523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870916361653000905580697 2903187271239750679185523)
                      ·
                        rfl

theorem cell23_5653937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_5653937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653937 prefixEnd_5653937 := by exact prefixLift 5653937
  have htrace : WordTrace (prefixWord ++ tailWord_5653937) baseStart_5653937 baseEnd_5653937 := by
    simpa [prefixWord, tailWord_5653937, baseEnd_5653937] using wordTrace_append hprefix tailTrace_5653937
  have hstable : (prefixWord ++ tailWord_5653937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653937).length < 2 ^ (prefixWord ++ tailWord_5653937).sum := by decide
  have hdescent : baseEnd_5653937 < baseStart_5653937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653967 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 2, 4, 2]
def baseStart_5653967 : Nat := 118140960795 + 5653967 * 2 ^ 59
def prefixEnd_5653967 : Nat := 4983230072969 + 3 ^ 40 * 5653967 * 2
def baseEnd_5653967 : Nat := 2903202675659385561810385

theorem tailTrace_5653967 : CollatzResearch.WordTrace tailWord_5653967 prefixEnd_5653967 2903202675659385561810385 := by
  unfold tailWord_5653967
  simp only [CollatzResearch.WordTrace]
  refine ⟨206217117907650654531720155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137478078605100436354480103 206217117907650654531720155)
  ·
    refine ⟨309325676861475981797580233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206217117907650654531720155 309325676861475981797580233)
    ·
      refine ⟨231994257646106986348185175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309325676861475981797580233 231994257646106986348185175)
      ·
        refine ⟨347991386469160479522277763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231994257646106986348185175 347991386469160479522277763)
        ·
          refine ⟨521987079703740719283416645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347991386469160479522277763 521987079703740719283416645)
          ·
            refine ⟨97872577444451384865640621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 521987079703740719283416645 97872577444451384865640621)
            ·
              refine ⟨36702216541669269324615233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97872577444451384865640621 36702216541669269324615233)
              ·
                refine ⟨27526662406251951993461425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36702216541669269324615233 27526662406251951993461425)
                ·
                  refine ⟨20644996804688963995096069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27526662406251951993461425 20644996804688963995096069)
                  ·
                    refine ⟨3870936900879180749080513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20644996804688963995096069 3870936900879180749080513)
                    ·
                      refine ⟨2903202675659385561810385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870936900879180749080513 2903202675659385561810385)
                      ·
                        rfl

theorem cell23_5653967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 4, 2].length) (baseStart_5653967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653967 prefixEnd_5653967 := by exact prefixLift 5653967
  have htrace : WordTrace (prefixWord ++ tailWord_5653967) baseStart_5653967 baseEnd_5653967 := by
    simpa [prefixWord, tailWord_5653967, baseEnd_5653967] using wordTrace_append hprefix tailTrace_5653967
  have hstable : (prefixWord ++ tailWord_5653967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653967).length < 2 ^ (prefixWord ++ tailWord_5653967).sum := by decide
  have hdescent : baseEnd_5653967 < baseStart_5653967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653977 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 3, 4]
def baseStart_5653977 : Nat := 118140960795 + 5653977 * 2 ^ 59
def prefixEnd_5653977 : Nat := 4983230072969 + 3 ^ 40 * 5653977 * 2
def baseEnd_5653977 : Nat := 967735936821976840895113

theorem tailTrace_5653977 : CollatzResearch.WordTrace tailWord_5653977 prefixEnd_5653977 967735936821976840895113 := by
  unfold tailWord_5653977
  simp only [CollatzResearch.WordTrace]
  refine ⟨206217482637614426239584185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137478321758409617493056123 206217482637614426239584185)
  ·
    refine ⟨154663111978210819679688139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206217482637614426239584185 154663111978210819679688139)
    ·
      refine ⟨231994667967316229519532209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154663111978210819679688139 231994667967316229519532209)
      ·
        refine ⟨173996000975487172139649157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231994667967316229519532209 173996000975487172139649157)
        ·
          refine ⟨32624250182903844776184217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173996000975487172139649157 32624250182903844776184217)
          ·
            refine ⟨24468187637177883582138163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32624250182903844776184217 24468187637177883582138163)
            ·
              refine ⟨36702281455766825373207245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24468187637177883582138163 36702281455766825373207245)
              ·
                refine ⟨13763355545912559514952717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36702281455766825373207245 13763355545912559514952717)
                ·
                  refine ⟨5161258329717209818107269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13763355545912559514952717 5161258329717209818107269)
                  ·
                    refine ⟨967735936821976840895113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5161258329717209818107269 967735936821976840895113)
                    ·
                      rfl

theorem cell23_5653977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 4].length) (baseStart_5653977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653977 prefixEnd_5653977 := by exact prefixLift 5653977
  have htrace : WordTrace (prefixWord ++ tailWord_5653977) baseStart_5653977 baseEnd_5653977 := by
    simpa [prefixWord, tailWord_5653977, baseEnd_5653977] using wordTrace_append hprefix tailTrace_5653977
  have hstable : (prefixWord ++ tailWord_5653977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653977).length < 2 ^ (prefixWord ++ tailWord_5653977).sum := by decide
  have hdescent : baseEnd_5653977 < baseStart_5653977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5653987 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 3]
def baseStart_5653987 : Nat := 118140960795 + 5653987 * 2 ^ 59
def prefixEnd_5653987 : Nat := 4983230072969 + 3 ^ 40 * 5653987 * 2
def baseEnd_5653987 : Nat := 2903212945272475483560293

theorem tailTrace_5653987 : CollatzResearch.WordTrace tailWord_5653987 prefixEnd_5653987 2903212945272475483560293 := by
  unfold tailWord_5653987
  simp only [CollatzResearch.WordTrace]
  refine ⟨206217847367578197947448215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137478564911718798631632143 206217847367578197947448215)
  ·
    refine ⟨309326771051367296921172323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206217847367578197947448215 309326771051367296921172323)
    ·
      refine ⟨463990156577050945381758485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309326771051367296921172323 463990156577050945381758485)
      ·
        refine ⟨21749538589549263064769929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 463990156577050945381758485 21749538589549263064769929)
        ·
          refine ⟨16312153942161947298577447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21749538589549263064769929 16312153942161947298577447)
          ·
            refine ⟨24468230913242920947866171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16312153942161947298577447 24468230913242920947866171)
            ·
              refine ⟨36702346369864381421799257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24468230913242920947866171 36702346369864381421799257)
              ·
                refine ⟨27526759777398286066349443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36702346369864381421799257 27526759777398286066349443)
                ·
                  refine ⟨41290139666097429099524165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27526759777398286066349443 41290139666097429099524165)
                  ·
                    refine ⟨7741901187393267956160781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41290139666097429099524165 7741901187393267956160781)
                    ·
                      refine ⟨2903212945272475483560293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7741901187393267956160781 2903212945272475483560293)
                      ·
                        rfl

theorem cell23_5653987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_5653987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5653987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5653987 prefixEnd_5653987 := by exact prefixLift 5653987
  have htrace : WordTrace (prefixWord ++ tailWord_5653987) baseStart_5653987 baseEnd_5653987 := by
    simpa [prefixWord, tailWord_5653987, baseEnd_5653987] using wordTrace_append hprefix tailTrace_5653987
  have hstable : (prefixWord ++ tailWord_5653987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5653987).length < 2 ^ (prefixWord ++ tailWord_5653987).sum := by decide
  have hdescent : baseEnd_5653987 < baseStart_5653987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5653987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654028 : List Nat := [2, 2, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_5654028 : Nat := 118140960795 + 5654028 * 2 ^ 59
def prefixEnd_5654028 : Nat := 4983230072969 + 3 ^ 40 * 5654028 * 2
def baseEnd_5654028 : Nat := 967744665993103274382535

theorem tailTrace_5654028 : CollatzResearch.WordTrace tailWord_5654028 prefixEnd_5654028 967744665993103274382535 := by
  unfold tailWord_5654028
  simp only [CollatzResearch.WordTrace]
  refine ⟨103109671380214830974845369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137479561840286441299793825 103109671380214830974845369)
  ·
    refine ⟨77332253535161123231134027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103109671380214830974845369 77332253535161123231134027)
    ·
      refine ⟨115998380302741684846701041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77332253535161123231134027 115998380302741684846701041)
      ·
        refine ⟨86998785227056263635025781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115998380302741684846701041 86998785227056263635025781)
        ·
          refine ⟨8156136115036524715783667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86998785227056263635025781 8156136115036524715783667)
          ·
            refine ⟨12234204172554787073675501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156136115036524715783667 12234204172554787073675501)
            ·
              refine ⟨4587826564708045152628313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12234204172554787073675501 4587826564708045152628313)
              ·
                refine ⟨3440869923531033864471235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4587826564708045152628313 3440869923531033864471235)
                ·
                  refine ⟨5161304885296550796706853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440869923531033864471235 5161304885296550796706853)
                  ·
                    refine ⟨967744665993103274382535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5161304885296550796706853 967744665993103274382535)
                    ·
                      rfl

theorem cell23_5654028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_5654028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654028 prefixEnd_5654028 := by exact prefixLift 5654028
  have htrace : WordTrace (prefixWord ++ tailWord_5654028) baseStart_5654028 baseEnd_5654028 := by
    simpa [prefixWord, tailWord_5654028, baseEnd_5654028] using wordTrace_append hprefix tailTrace_5654028
  have hstable : (prefixWord ++ tailWord_5654028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654028).length < 2 ^ (prefixWord ++ tailWord_5654028).sum := by decide
  have hdescent : baseEnd_5654028 < baseStart_5654028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654044 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_5654044 : Nat := 118140960795 + 5654044 * 2 ^ 59
def prefixEnd_5654044 : Nat := 4983230072969 + 3 ^ 40 * 5654044 * 2
def baseEnd_5654044 : Nat := 2903242213669781760547531

theorem tailTrace_5654044 : CollatzResearch.WordTrace tailWord_5654044 prefixEnd_5654044 2903242213669781760547531 := by
  unfold tailWord_5654044
  simp only [CollatzResearch.WordTrace]
  refine ⟨103109963164185848341136593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137479950885581131121515457 103109963164185848341136593)
  ·
    refine ⟨77332472373139386255852445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103109963164185848341136593 77332472373139386255852445)
    ·
      refine ⟨28999677139927269845944667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77332472373139386255852445 28999677139927269845944667)
      ·
        refine ⟨43499515709890904768917001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28999677139927269845944667 43499515709890904768917001)
        ·
          refine ⟨32624636782418178576687751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43499515709890904768917001 32624636782418178576687751)
          ·
            refine ⟨48936955173627267865031627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32624636782418178576687751 48936955173627267865031627)
            ·
              refine ⟨73405432760440901797547441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48936955173627267865031627 73405432760440901797547441)
              ·
                refine ⟨55054074570330676348160581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73405432760440901797547441 55054074570330676348160581)
                ·
                  refine ⟨10322638981937001815280109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55054074570330676348160581 10322638981937001815280109)
                  ·
                    refine ⟨3870989618226375680730041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10322638981937001815280109 3870989618226375680730041)
                    ·
                      refine ⟨2903242213669781760547531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3870989618226375680730041 2903242213669781760547531)
                      ·
                        rfl

theorem cell23_5654044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_5654044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654044 prefixEnd_5654044 := by exact prefixLift 5654044
  have htrace : WordTrace (prefixWord ++ tailWord_5654044) baseStart_5654044 baseEnd_5654044 := by
    simpa [prefixWord, tailWord_5654044, baseEnd_5654044] using wordTrace_append hprefix tailTrace_5654044
  have hstable : (prefixWord ++ tailWord_5654044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654044).length < 2 ^ (prefixWord ++ tailWord_5654044).sum := by decide
  have hdescent : baseEnd_5654044 < baseStart_5654044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654060 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_5654060 : Nat := 118140960795 + 5654060 * 2 ^ 59
def prefixEnd_5654060 : Nat := 4983230072969 + 3 ^ 40 * 5654060 * 2
def baseEnd_5654060 : Nat := 2903250429360253697947457

theorem tailTrace_5654060 : CollatzResearch.WordTrace tailWord_5654060 prefixEnd_5654060 2903250429360253697947457 := by
  unfold tailWord_5654060
  simp only [CollatzResearch.WordTrace]
  refine ⟨103110254948156865707427817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137480339930875820943237089 103110254948156865707427817)
  ·
    refine ⟨77332691211117649280570863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103110254948156865707427817 77332691211117649280570863)
    ·
      refine ⟨115999036816676473920856295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77332691211117649280570863 115999036816676473920856295)
      ·
        refine ⟨173998555225014710881284443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115999036816676473920856295 173998555225014710881284443)
        ·
          refine ⟨260997832837522066321926665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173998555225014710881284443 260997832837522066321926665)
          ·
            refine ⟨195748374628141549741444999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260997832837522066321926665 195748374628141549741444999)
            ·
              refine ⟨293622561942212324612167499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195748374628141549741444999 293622561942212324612167499)
              ·
                refine ⟨440433842913318486918251249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293622561942212324612167499 440433842913318486918251249)
                ·
                  refine ⟨330325382184988865188688437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440433842913318486918251249 330325382184988865188688437)
                  ·
                    refine ⟨30968004579842706111439541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 330325382184988865188688437 30968004579842706111439541)
                    ·
                      refine ⟨2903250429360253697947457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30968004579842706111439541 2903250429360253697947457)
                      ·
                        rfl

theorem cell23_5654060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_5654060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654060 prefixEnd_5654060 := by exact prefixLift 5654060
  have htrace : WordTrace (prefixWord ++ tailWord_5654060) baseStart_5654060 baseEnd_5654060 := by
    simpa [prefixWord, tailWord_5654060, baseEnd_5654060] using wordTrace_append hprefix tailTrace_5654060
  have hstable : (prefixWord ++ tailWord_5654060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654060).length < 2 ^ (prefixWord ++ tailWord_5654060).sum := by decide
  have hdescent : baseEnd_5654060 < baseStart_5654060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654067 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 1, 6]
def baseStart_5654067 : Nat := 118140960795 + 5654067 * 2 ^ 59
def prefixEnd_5654067 : Nat := 4983230072969 + 3 ^ 40 * 5654067 * 2
def baseEnd_5654067 : Nat := 967751341241611723519975

theorem tailTrace_5654067 : CollatzResearch.WordTrace tailWord_5654067 prefixEnd_5654067 967751341241611723519975 := by
  unfold tailWord_5654067
  simp only [CollatzResearch.WordTrace]
  refine ⟨206220765207288371610360455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137480510138192247740240303 206220765207288371610360455)
  ·
    refine ⟨309331147810932557415540683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206220765207288371610360455 309331147810932557415540683)
    ·
      refine ⟨463996721716398836123311025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309331147810932557415540683 463996721716398836123311025)
      ·
        refine ⟨347997541287299127092483269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 463996721716398836123311025 347997541287299127092483269)
        ·
          refine ⟨65249538991368586329840613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 347997541287299127092483269 65249538991368586329840613)
          ·
            refine ⟨12234288560881609936845115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65249538991368586329840613 12234288560881609936845115)
            ·
              refine ⟨18351432841322414905267673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12234288560881609936845115 18351432841322414905267673)
              ·
                refine ⟨13763574630991811178950755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18351432841322414905267673 13763574630991811178950755)
                ·
                  refine ⟨20645361946487716768426133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13763574630991811178950755 20645361946487716768426133)
                  ·
                    refine ⟨967751341241611723519975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20645361946487716768426133 967751341241611723519975)
                    ·
                      rfl

theorem cell23_5654067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 6].length) (baseStart_5654067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654067 prefixEnd_5654067 := by exact prefixLift 5654067
  have htrace : WordTrace (prefixWord ++ tailWord_5654067) baseStart_5654067 baseEnd_5654067 := by
    simpa [prefixWord, tailWord_5654067, baseEnd_5654067] using wordTrace_append hprefix tailTrace_5654067
  have hstable : (prefixWord ++ tailWord_5654067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654067).length < 2 ^ (prefixWord ++ tailWord_5654067).sum := by decide
  have hdescent : baseEnd_5654067 < baseStart_5654067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654108 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_5654108 : Nat := 118140960795 + 5654108 * 2 ^ 59
def prefixEnd_5654108 : Nat := 4983230072969 + 3 ^ 40 * 5654108 * 2
def baseEnd_5654108 : Nat := 2903275076431669510147237

theorem tailTrace_5654108 : CollatzResearch.WordTrace tailWord_5654108 prefixEnd_5654108 2903275076431669510147237 := by
  unfold tailWord_5654108
  simp only [CollatzResearch.WordTrace]
  refine ⟨103111130300069917806301489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137481507066759890408401985 103111130300069917806301489)
  ·
    refine ⟨77333347725052438354726117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103111130300069917806301489 77333347725052438354726117)
    ·
      refine ⟨14500002698447332191511147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77333347725052438354726117 14500002698447332191511147)
      ·
        refine ⟨21750004047670998287266721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14500002698447332191511147 21750004047670998287266721)
        ·
          refine ⟨16312503035753248715450041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21750004047670998287266721 16312503035753248715450041)
          ·
            refine ⟨12234377276814936536587531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16312503035753248715450041 12234377276814936536587531)
            ·
              refine ⟨18351565915222404804881297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12234377276814936536587531 18351565915222404804881297)
              ·
                refine ⟨13763674436416803603660973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18351565915222404804881297 13763674436416803603660973)
                ·
                  refine ⟨5161377913656301351372865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13763674436416803603660973 5161377913656301351372865)
                  ·
                    refine ⟨3871033435242226013529649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5161377913656301351372865 3871033435242226013529649)
                    ·
                      refine ⟨2903275076431669510147237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871033435242226013529649 2903275076431669510147237)
                      ·
                        rfl

theorem cell23_5654108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_5654108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654108 prefixEnd_5654108 := by exact prefixLift 5654108
  have htrace : WordTrace (prefixWord ++ tailWord_5654108) baseStart_5654108 baseEnd_5654108 := by
    simpa [prefixWord, tailWord_5654108, baseEnd_5654108] using wordTrace_append hprefix tailTrace_5654108
  have hstable : (prefixWord ++ tailWord_5654108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654108).length < 2 ^ (prefixWord ++ tailWord_5654108).sum := by decide
  have hdescent : baseEnd_5654108 < baseStart_5654108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654124 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_5654124 : Nat := 118140960795 + 5654124 * 2 ^ 59
def prefixEnd_5654124 : Nat := 4983230072969 + 3 ^ 40 * 5654124 * 2
def baseEnd_5654124 : Nat := 2903283292122141447547163

theorem tailTrace_5654124 : CollatzResearch.WordTrace tailWord_5654124 prefixEnd_5654124 2903283292122141447547163 := by
  unfold tailWord_5654124
  simp only [CollatzResearch.WordTrace]
  refine ⟨103111422084040935172592713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137481896112054580230123617 103111422084040935172592713)
  ·
    refine ⟨77333566563030701379444535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103111422084040935172592713 77333566563030701379444535)
    ·
      refine ⟨116000349844546052069166803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77333566563030701379444535 116000349844546052069166803)
      ·
        refine ⟨174000524766819078103750205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116000349844546052069166803 174000524766819078103750205)
        ·
          refine ⟨65250196787557154288906327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174000524766819078103750205 65250196787557154288906327)
          ·
            refine ⟨97875295181335731433359491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65250196787557154288906327 97875295181335731433359491)
            ·
              refine ⟨146812942772003597150039237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97875295181335731433359491 146812942772003597150039237)
              ·
                refine ⟨27527426769750674465632357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146812942772003597150039237 27527426769750674465632357)
                ·
                  refine ⟨5161392519328251462306067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27527426769750674465632357 5161392519328251462306067)
                  ·
                    refine ⟨7742088778992377193459101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5161392519328251462306067 7742088778992377193459101)
                    ·
                      refine ⟨2903283292122141447547163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7742088778992377193459101 2903283292122141447547163)
                      ·
                        rfl

theorem cell23_5654124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_5654124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654124 prefixEnd_5654124 := by exact prefixLift 5654124
  have htrace : WordTrace (prefixWord ++ tailWord_5654124) baseStart_5654124 baseEnd_5654124 := by
    simpa [prefixWord, tailWord_5654124, baseEnd_5654124] using wordTrace_append hprefix tailTrace_5654124
  have hstable : (prefixWord ++ tailWord_5654124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654124).length < 2 ^ (prefixWord ++ tailWord_5654124).sum := by decide
  have hdescent : baseEnd_5654124 < baseStart_5654124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654125 : List Nat := [1, 5, 1, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_5654125 : Nat := 118140960795 + 5654125 * 2 ^ 59
def prefixEnd_5654125 : Nat := 4983230072969 + 3 ^ 40 * 5654125 * 2
def baseEnd_5654125 : Nat := 2903283805602795943634659

theorem tailTrace_5654125 : CollatzResearch.WordTrace tailWord_5654125 prefixEnd_5654125 2903283805602795943634659 := by
  unfold tailWord_5654125
  simp only [CollatzResearch.WordTrace]
  refine ⟨206222880641078247515971829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137481920427385498343981219 206222880641078247515971829)
  ·
    refine ⟨19333395060101085704622359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206222880641078247515971829 19333395060101085704622359)
    ·
      refine ⟨29000092590151628556933539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19333395060101085704622359 29000092590151628556933539)
      ·
        refine ⟨43500138885227442835400309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29000092590151628556933539 43500138885227442835400309)
        ·
          refine ⟨4078138020490072765818779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43500138885227442835400309 4078138020490072765818779)
          ·
            refine ⟨6117207030735109148728169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078138020490072765818779 6117207030735109148728169)
            ·
              refine ⟨4587905273051331861546127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6117207030735109148728169 4587905273051331861546127)
              ·
                refine ⟨6881857909576997792319191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587905273051331861546127 6881857909576997792319191)
                ·
                  refine ⟨10322786864365496688478787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6881857909576997792319191 10322786864365496688478787)
                  ·
                    refine ⟨15484180296548245032718181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10322786864365496688478787 15484180296548245032718181)
                    ·
                      refine ⟨2903283805602795943634659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15484180296548245032718181 2903283805602795943634659)
                      ·
                        rfl

theorem cell23_5654125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_5654125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654125 prefixEnd_5654125 := by exact prefixLift 5654125
  have htrace : WordTrace (prefixWord ++ tailWord_5654125) baseStart_5654125 baseEnd_5654125 := by
    simpa [prefixWord, tailWord_5654125, baseEnd_5654125] using wordTrace_append hprefix tailTrace_5654125
  have hstable : (prefixWord ++ tailWord_5654125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654125).length < 2 ^ (prefixWord ++ tailWord_5654125).sum := by decide
  have hdescent : baseEnd_5654125 < baseStart_5654125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654128 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 1, 2, 3]
def baseStart_5654128 : Nat := 118140960795 + 5654128 * 2 ^ 59
def prefixEnd_5654128 : Nat := 4983230072969 + 3 ^ 40 * 5654128 * 2
def baseEnd_5654128 : Nat := 2903285346044759431897145

theorem tailTrace_5654128 : CollatzResearch.WordTrace tailWord_5654128 prefixEnd_5654128 2903285346044759431897145 := by
  unfold tailWord_5654128
  simp only [CollatzResearch.WordTrace]
  refine ⟨103111495030033689514165519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137481993373378252685554025 103111495030033689514165519)
  ·
    refine ⟨154667242545050534271248279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103111495030033689514165519 154667242545050534271248279)
    ·
      refine ⟨232000863817575801406872419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154667242545050534271248279 232000863817575801406872419)
      ·
        refine ⟨348001295726363702110308629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232000863817575801406872419 348001295726363702110308629)
        ·
          refine ⟨16312560737173298536420717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 348001295726363702110308629 16312560737173298536420717)
          ·
            refine ⟨6117210276439986951157769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16312560737173298536420717 6117210276439986951157769)
            ·
              refine ⟨4587907707329990213368327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6117210276439986951157769 4587907707329990213368327)
              ·
                refine ⟨6881861560994985320052491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587907707329990213368327 6881861560994985320052491)
                ·
                  refine ⟨10322792341492477980078737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6881861560994985320052491 10322792341492477980078737)
                  ·
                    refine ⟨7742094256119358485059053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10322792341492477980078737 7742094256119358485059053)
                    ·
                      refine ⟨2903285346044759431897145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7742094256119358485059053 2903285346044759431897145)
                      ·
                        rfl

theorem cell23_5654128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 2, 3].length) (baseStart_5654128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654128 prefixEnd_5654128 := by exact prefixLift 5654128
  have htrace : WordTrace (prefixWord ++ tailWord_5654128) baseStart_5654128 baseEnd_5654128 := by
    simpa [prefixWord, tailWord_5654128, baseEnd_5654128] using wordTrace_append hprefix tailTrace_5654128
  have hstable : (prefixWord ++ tailWord_5654128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654128).length < 2 ^ (prefixWord ++ tailWord_5654128).sum := by decide
  have hdescent : baseEnd_5654128 < baseStart_5654128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654141 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_5654141 : Nat := 118140960795 + 5654141 * 2 ^ 59
def prefixEnd_5654141 : Nat := 4983230072969 + 3 ^ 40 * 5654141 * 2
def baseEnd_5654141 : Nat := 2903292021293267881034585

theorem tailTrace_5654141 : CollatzResearch.WordTrace tailWord_5654141 prefixEnd_5654141 2903292021293267881034585 := by
  unfold tailWord_5654141
  simp only [CollatzResearch.WordTrace]
  refine ⟨206223464209020282248554277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137482309472680188165702851 206223464209020282248554277)
  ·
    refine ⟨38666899539191302921603927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206223464209020282248554277 38666899539191302921603927)
    ·
      refine ⟨58000349308786954382405891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38666899539191302921603927 58000349308786954382405891)
      ·
        refine ⟨87000523963180431573608837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58000349308786954382405891 87000523963180431573608837)
        ·
          refine ⟨16312598243096330920051657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87000523963180431573608837 16312598243096330920051657)
          ·
            refine ⟨12234448682322248190038743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16312598243096330920051657 12234448682322248190038743)
            ·
              refine ⟨18351673023483372285058115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12234448682322248190038743 18351673023483372285058115)
              ·
                refine ⟨27527509535225058427587173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18351673023483372285058115 27527509535225058427587173)
                ·
                  refine ⟨5161408037854698455172595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27527509535225058427587173 5161408037854698455172595)
                  ·
                    refine ⟨7742112056782047682758893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5161408037854698455172595 7742112056782047682758893)
                    ·
                      refine ⟨2903292021293267881034585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7742112056782047682758893 2903292021293267881034585)
                      ·
                        rfl

theorem cell23_5654141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_5654141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654141 prefixEnd_5654141 := by exact prefixLift 5654141
  have htrace : WordTrace (prefixWord ++ tailWord_5654141) baseStart_5654141 baseEnd_5654141 := by
    simpa [prefixWord, tailWord_5654141, baseEnd_5654141] using wordTrace_append hprefix tailTrace_5654141
  have hstable : (prefixWord ++ tailWord_5654141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654141).length < 2 ^ (prefixWord ++ tailWord_5654141).sum := by decide
  have hdescent : baseEnd_5654141 < baseStart_5654141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654168 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 1, 3, 2]
def baseStart_5654168 : Nat := 118140960795 + 5654168 * 2 ^ 59
def prefixEnd_5654168 : Nat := 4983230072969 + 3 ^ 40 * 5654168 * 2
def baseEnd_5654168 : Nat := 2903305885270939275396961

theorem tailTrace_5654168 : CollatzResearch.WordTrace tailWord_5654168 prefixEnd_5654168 2903305885270939275396961 := by
  unfold tailWord_5654168
  simp only [CollatzResearch.WordTrace]
  refine ⟨103112224489961232929893579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137482965986614977239858105 103112224489961232929893579)
  ·
    refine ⟨154668336734941849394840369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103112224489961232929893579 154668336734941849394840369)
    ·
      refine ⟨116001252551206387046130277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154668336734941849394840369 116001252551206387046130277)
      ·
        refine ⟨21750234853351197571149427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116001252551206387046130277 21750234853351197571149427)
        ·
          refine ⟨32625352280026796356724141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21750234853351197571149427 32625352280026796356724141)
          ·
            refine ⟨12234507105010048633771553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32625352280026796356724141 12234507105010048633771553)
            ·
              refine ⟨9175880328757536475328665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12234507105010048633771553 9175880328757536475328665)
              ·
                refine ⟨6881910246568152356496499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9175880328757536475328665 6881910246568152356496499)
                ·
                  refine ⟨10322865369852228534744749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6881910246568152356496499 10322865369852228534744749)
                  ·
                    refine ⟨3871074513694585700529281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10322865369852228534744749 3871074513694585700529281)
                    ·
                      refine ⟨2903305885270939275396961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871074513694585700529281 2903305885270939275396961)
                      ·
                        rfl

theorem cell23_5654168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_5654168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654168 prefixEnd_5654168 := by exact prefixLift 5654168
  have htrace : WordTrace (prefixWord ++ tailWord_5654168) baseStart_5654168 baseEnd_5654168 := by
    simpa [prefixWord, tailWord_5654168, baseEnd_5654168] using wordTrace_append hprefix tailTrace_5654168
  have hstable : (prefixWord ++ tailWord_5654168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654168).length < 2 ^ (prefixWord ++ tailWord_5654168).sum := by decide
  have hdescent : baseEnd_5654168 < baseStart_5654168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654181 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 4, 2, 2]
def baseStart_5654181 : Nat := 118140960795 + 5654181 * 2 ^ 59
def prefixEnd_5654181 : Nat := 4983230072969 + 3 ^ 40 * 5654181 * 2
def baseEnd_5654181 : Nat := 2903312560519447724534401

theorem tailTrace_5654181 : CollatzResearch.WordTrace tailWord_5654181 prefixEnd_5654181 2903312560519447724534401 := by
  unfold tailWord_5654181
  simp only [CollatzResearch.WordTrace]
  refine ⟨206224923128875369080010397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137483282085916912720006931 206224923128875369080010397)
  ·
    refine ⟨77334346173328263405003899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206224923128875369080010397 77334346173328263405003899)
    ·
      refine ⟨116001519259992395107505849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77334346173328263405003899 116001519259992395107505849)
      ·
        refine ⟨87001139444994296330629387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116001519259992395107505849 87001139444994296330629387)
        ·
          refine ⟨130501709167491444495944081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87001139444994296330629387 130501709167491444495944081)
          ·
            refine ⟨97876281875618583371958061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130501709167491444495944081 97876281875618583371958061)
            ·
              refine ⟨36703605703356968764484273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97876281875618583371958061 36703605703356968764484273)
              ·
                refine ⟨27527704277517726573363205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36703605703356968764484273 27527704277517726573363205)
                ·
                  refine ⟨5161444552034573732505601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27527704277517726573363205 5161444552034573732505601)
                  ·
                    refine ⟨3871083414025930299379201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5161444552034573732505601 3871083414025930299379201)
                    ·
                      refine ⟨2903312560519447724534401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871083414025930299379201 2903312560519447724534401)
                      ·
                        rfl

theorem cell23_5654181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_5654181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654181 prefixEnd_5654181 := by exact prefixLift 5654181
  have htrace : WordTrace (prefixWord ++ tailWord_5654181) baseStart_5654181 baseEnd_5654181 := by
    simpa [prefixWord, tailWord_5654181, baseEnd_5654181] using wordTrace_append hprefix tailTrace_5654181
  have hstable : (prefixWord ++ tailWord_5654181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654181).length < 2 ^ (prefixWord ++ tailWord_5654181).sum := by decide
  have hdescent : baseEnd_5654181 < baseStart_5654181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654204 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 7]
def baseStart_5654204 : Nat := 118140960795 + 5654204 * 2 ^ 59
def prefixEnd_5654204 : Nat := 4983230072969 + 3 ^ 40 * 5654204 * 2
def baseEnd_5654204 : Nat := 322591596730500126060755

theorem tailTrace_5654204 : CollatzResearch.WordTrace tailWord_5654204 prefixEnd_5654204 322591596730500126060755 := by
  unfold tailWord_5654204
  simp only [CollatzResearch.WordTrace]
  refine ⟨103112881003896022004048833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137483841338528029338731777 103112881003896022004048833)
  ·
    refine ⟨77334660752922016503036625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103112881003896022004048833 77334660752922016503036625)
    ·
      refine ⟨58000995564691512377277469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77334660752922016503036625 58000995564691512377277469)
      ·
        refine ⟨21750373336759317141479051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58000995564691512377277469 21750373336759317141479051)
        ·
          refine ⟨32625560005138975712218577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21750373336759317141479051 32625560005138975712218577)
          ·
            refine ⟨24469170003854231784163933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32625560005138975712218577 24469170003854231784163933)
            ·
              refine ⟨9175938751445336919061475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24469170003854231784163933 9175938751445336919061475)
              ·
                refine ⟨13763908127168005378592213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9175938751445336919061475 13763908127168005378592213)
                ·
                  refine ⟨322591596730500126060755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13763908127168005378592213 322591596730500126060755)
                  ·
                    rfl

theorem cell23_5654204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_5654204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654204 prefixEnd_5654204 := by exact prefixLift 5654204
  have htrace : WordTrace (prefixWord ++ tailWord_5654204) baseStart_5654204 baseEnd_5654204 := by
    simpa [prefixWord, tailWord_5654204, baseEnd_5654204] using wordTrace_append hprefix tailTrace_5654204
  have hstable : (prefixWord ++ tailWord_5654204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654204).length < 2 ^ (prefixWord ++ tailWord_5654204).sum := by decide
  have hdescent : baseEnd_5654204 < baseStart_5654204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654224 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 4, 5, 2]
def baseStart_5654224 : Nat := 118140960795 + 5654224 * 2 ^ 59
def prefixEnd_5654224 : Nat := 4983230072969 + 3 ^ 40 * 5654224 * 2
def baseEnd_5654224 : Nat := 2903334640187591056296703

theorem tailTrace_5654224 : CollatzResearch.WordTrace tailWord_5654224 prefixEnd_5654224 2903334640187591056296703 := by
  unfold tailWord_5654224
  simp only [CollatzResearch.WordTrace]
  refine ⟨103113245733859793711912863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137484327645146391615883817 103113245733859793711912863)
  ·
    refine ⟨154669868600789690567869295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103113245733859793711912863 154669868600789690567869295)
    ·
      refine ⟨232004802901184535851803943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154669868600789690567869295 232004802901184535851803943)
      ·
        refine ⟨348007204351776803777705915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232004802901184535851803943 348007204351776803777705915)
        ·
          refine ⟨522010806527665205666558873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348007204351776803777705915 522010806527665205666558873)
          ·
            refine ⟨391508104895748904249919155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522010806527665205666558873 391508104895748904249919155)
            ·
              refine ⟨587262157343623356374878733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391508104895748904249919155 587262157343623356374878733)
              ·
                refine ⟨220223309003858758640579525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587262157343623356374878733 220223309003858758640579525)
                ·
                  refine ⟨41291870438223517245108661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220223309003858758640579525 41291870438223517245108661)
                  ·
                    refine ⟨3871112853583454741728937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41291870438223517245108661 3871112853583454741728937)
                    ·
                      refine ⟨2903334640187591056296703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871112853583454741728937 2903334640187591056296703)
                      ·
                        rfl

theorem cell23_5654224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 5, 2].length) (baseStart_5654224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654224 prefixEnd_5654224 := by exact prefixLift 5654224
  have htrace : WordTrace (prefixWord ++ tailWord_5654224) baseStart_5654224 baseEnd_5654224 := by
    simpa [prefixWord, tailWord_5654224, baseEnd_5654224] using wordTrace_append hprefix tailTrace_5654224
  have hstable : (prefixWord ++ tailWord_5654224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654224).length < 2 ^ (prefixWord ++ tailWord_5654224).sum := by decide
  have hdescent : baseEnd_5654224 < baseStart_5654224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654234 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_5654234 : Nat := 118140960795 + 5654234 * 2 ^ 59
def prefixEnd_5654234 : Nat := 4983230072969 + 3 ^ 40 * 5654234 * 2
def baseEnd_5654234 : Nat := 967779924998045339057219

theorem tailTrace_5654234 : CollatzResearch.WordTrace tailWord_5654234 prefixEnd_5654234 967779924998045339057219 := by
  unfold tailWord_5654234
  simp only [CollatzResearch.WordTrace]
  refine ⟨51556714049420839782922439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137484570798455572754459837 51556714049420839782922439)
  ·
    refine ⟨77335071074131259674383659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51556714049420839782922439 77335071074131259674383659)
    ·
      refine ⟨116002606611196889511575489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77335071074131259674383659 116002606611196889511575489)
      ·
        refine ⟨87001954958397667133681617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116002606611196889511575489 87001954958397667133681617)
        ·
          refine ⟨65251466218798250350261213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87001954958397667133681617 65251466218798250350261213)
          ·
            refine ⟨24469299832049343881347955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65251466218798250350261213 24469299832049343881347955)
            ·
              refine ⟨36703949748074015822021933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24469299832049343881347955 36703949748074015822021933)
              ·
                refine ⟨13763981155527755933258225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36703949748074015822021933 13763981155527755933258225)
                ·
                  refine ⟨10322985866645816949943669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13763981155527755933258225 10322985866645816949943669)
                  ·
                    refine ⟨967779924998045339057219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10322985866645816949943669 967779924998045339057219)
                    ·
                      rfl

theorem cell23_5654234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_5654234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654234 prefixEnd_5654234 := by exact prefixLift 5654234
  have htrace : WordTrace (prefixWord ++ tailWord_5654234) baseStart_5654234 baseEnd_5654234 := by
    simpa [prefixWord, tailWord_5654234, baseEnd_5654234] using wordTrace_append hprefix tailTrace_5654234
  have hstable : (prefixWord ++ tailWord_5654234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654234).length < 2 ^ (prefixWord ++ tailWord_5654234).sum := by decide
  have hdescent : baseEnd_5654234 < baseStart_5654234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654267 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 6]
def baseStart_5654267 : Nat := 118140960795 + 5654267 * 2 ^ 59
def prefixEnd_5654267 : Nat := 4983230072969 + 3 ^ 40 * 5654267 * 2
def baseEnd_5654267 : Nat := 2903356719855734388059005

theorem tailTrace_5654267 : CollatzResearch.WordTrace tailWord_5654267 prefixEnd_5654267 2903356719855734388059005 := by
  unfold tailWord_5654267
  simp only [CollatzResearch.WordTrace]
  refine ⟨206228059806563805767641055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137485373204375870511760703 206228059806563805767641055)
  ·
    refine ⟨309342089709845708651461583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206228059806563805767641055 309342089709845708651461583)
    ·
      refine ⟨464013134564768562977192375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309342089709845708651461583 464013134564768562977192375)
      ·
        refine ⟨696019701847152844465788563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464013134564768562977192375 696019701847152844465788563)
        ·
          refine ⟨1044029552770729266698682845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696019701847152844465788563 1044029552770729266698682845)
          ·
            refine ⟨391511082289023475012006067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1044029552770729266698682845 391511082289023475012006067)
            ·
              refine ⟨587266623433535212518009101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391511082289023475012006067 587266623433535212518009101)
              ·
                refine ⟨220224983787575704694253413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587266623433535212518009101 220224983787575704694253413)
                ·
                  refine ⟨41292184460170444630172515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220224983787575704694253413 41292184460170444630172515)
                  ·
                    refine ⟨61938276690255666945258773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41292184460170444630172515 61938276690255666945258773)
                    ·
                      refine ⟨2903356719855734388059005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61938276690255666945258773 2903356719855734388059005)
                      ·
                        rfl

theorem cell23_5654267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_5654267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654267 prefixEnd_5654267 := by exact prefixLift 5654267
  have htrace : WordTrace (prefixWord ++ tailWord_5654267) baseStart_5654267 baseEnd_5654267 := by
    simpa [prefixWord, tailWord_5654267, baseEnd_5654267] using wordTrace_append hprefix tailTrace_5654267
  have hstable : (prefixWord ++ tailWord_5654267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654267).length < 2 ^ (prefixWord ++ tailWord_5654267).sum := by decide
  have hdescent : baseEnd_5654267 < baseStart_5654267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654277 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 12]
def baseStart_5654277 : Nat := 118140960795 + 5654277 * 2 ^ 59
def prefixEnd_5654277 : Nat := 4983230072969 + 3 ^ 40 * 5654277 * 2
def baseEnd_5654277 : Nat := 322595761629142149881551

theorem tailTrace_5654277 : CollatzResearch.WordTrace tailWord_5654277 prefixEnd_5654277 322595761629142149881551 := by
  unfold tailWord_5654277
  simp only [CollatzResearch.WordTrace]
  refine ⟨206228424536527577475505085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137485616357685051650336723 206228424536527577475505085)
  ·
    refine ⟨77335659201197841553314407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206228424536527577475505085 77335659201197841553314407)
    ·
      refine ⟨116003488801796762329971611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77335659201197841553314407 116003488801796762329971611)
      ·
        refine ⟨174005233202695143494957417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116003488801796762329971611 174005233202695143494957417)
        ·
          refine ⟨130503924902021357621218063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174005233202695143494957417 130503924902021357621218063)
          ·
            refine ⟨195755887353032036431827095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130503924902021357621218063 195755887353032036431827095)
            ·
              refine ⟨293633831029548054647740643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195755887353032036431827095 293633831029548054647740643)
              ·
                refine ⟨440450746544322081971610965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293633831029548054647740643 440450746544322081971610965)
                ·
                  refine ⟨322595761629142149881551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 440450746544322081971610965 322595761629142149881551)
                  ·
                    rfl

theorem cell23_5654277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_5654277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654277 prefixEnd_5654277 := by exact prefixLift 5654277
  have htrace : WordTrace (prefixWord ++ tailWord_5654277) baseStart_5654277 baseEnd_5654277 := by
    simpa [prefixWord, tailWord_5654277, baseEnd_5654277] using wordTrace_append hprefix tailTrace_5654277
  have hstable : (prefixWord ++ tailWord_5654277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654277).length < 2 ^ (prefixWord ++ tailWord_5654277).sum := by decide
  have hdescent : baseEnd_5654277 < baseStart_5654277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654298 : List Nat := [3, 1, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_5654298 : Nat := 118140960795 + 5654298 * 2 ^ 59
def prefixEnd_5654298 : Nat := 4983230072969 + 3 ^ 40 * 5654298 * 2
def baseEnd_5654298 : Nat := 967790879252007922257121

theorem tailTrace_5654298 : CollatzResearch.WordTrace tailWord_5654298 prefixEnd_5654298 967790879252007922257121 := by
  unfold tailWord_5654298
  simp only [CollatzResearch.WordTrace]
  refine ⟨51557297617362874515504887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137486126979634332041346365 51557297617362874515504887)
  ·
    refine ⟨77335946426044311773257331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51557297617362874515504887 77335946426044311773257331)
    ·
      refine ⟨116003919639066467659885997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77335946426044311773257331 116003919639066467659885997)
      ·
        refine ⟨43501469864649925372457249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116003919639066467659885997 43501469864649925372457249)
        ·
          refine ⟨32626102398487444029342937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43501469864649925372457249 32626102398487444029342937)
          ·
            refine ⟨24469576798865583022007203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32626102398487444029342937 24469576798865583022007203)
            ·
              refine ⟨36704365198298374533010805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24469576798865583022007203 36704365198298374533010805)
              ·
                refine ⟨3441034237340472612469763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36704365198298374533010805 3441034237340472612469763)
                ·
                  refine ⟨5161551356010708918704645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3441034237340472612469763 5161551356010708918704645)
                  ·
                    refine ⟨967790879252007922257121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5161551356010708918704645 967790879252007922257121)
                    ·
                      rfl

theorem cell23_5654298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_5654298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654298 prefixEnd_5654298 := by exact prefixLift 5654298
  have htrace : WordTrace (prefixWord ++ tailWord_5654298) baseStart_5654298 baseEnd_5654298 := by
    simpa [prefixWord, tailWord_5654298, baseEnd_5654298] using wordTrace_append hprefix tailTrace_5654298
  have hstable : (prefixWord ++ tailWord_5654298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654298).length < 2 ^ (prefixWord ++ tailWord_5654298).sum := by decide
  have hdescent : baseEnd_5654298 < baseStart_5654298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654341 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_5654341 : Nat := 118140960795 + 5654341 * 2 ^ 59
def prefixEnd_5654341 : Nat := 4983230072969 + 3 ^ 40 * 5654341 * 2
def baseEnd_5654341 : Nat := 967798239141389032844555

theorem tailTrace_5654341 : CollatzResearch.WordTrace tailWord_5654341 prefixEnd_5654341 967798239141389032844555 := by
  unfold tailWord_5654341
  simp only [CollatzResearch.WordTrace]
  refine ⟨206230758808295716405834877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137487172538863810937223251 206230758808295716405834877)
  ·
    refine ⟨77336534553110893652188079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206230758808295716405834877 77336534553110893652188079)
    ·
      refine ⟨116004801829666340478282119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77336534553110893652188079 116004801829666340478282119)
      ·
        refine ⟨174007202744499510717423179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116004801829666340478282119 174007202744499510717423179)
        ·
          refine ⟨261010804116749266076134769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174007202744499510717423179 261010804116749266076134769)
          ·
            refine ⟨195758103087561949557101077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261010804116749266076134769 195758103087561949557101077)
            ·
              refine ⟨9176161082229466385489113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 195758103087561949557101077 9176161082229466385489113)
              ·
                refine ⟨6882120811672099789116835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9176161082229466385489113 6882120811672099789116835)
                ·
                  refine ⟨10323181217508149683675253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6882120811672099789116835 10323181217508149683675253)
                  ·
                    refine ⟨967798239141389032844555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10323181217508149683675253 967798239141389032844555)
                    ·
                      rfl

theorem cell23_5654341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_5654341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654341 prefixEnd_5654341 := by exact prefixLift 5654341
  have htrace : WordTrace (prefixWord ++ tailWord_5654341) baseStart_5654341 baseEnd_5654341 := by
    simpa [prefixWord, tailWord_5654341, baseEnd_5654341] using wordTrace_append hprefix tailTrace_5654341
  have hstable : (prefixWord ++ tailWord_5654341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654341).length < 2 ^ (prefixWord ++ tailWord_5654341).sum := by decide
  have hdescent : baseEnd_5654341 < baseStart_5654341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654361 : List Nat := [1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 4]
def baseStart_5654361 : Nat := 118140960795 + 5654361 * 2 ^ 59
def prefixEnd_5654361 : Nat := 4983230072969 + 3 ^ 40 * 5654361 * 2
def baseEnd_5654361 : Nat := 2903404987037257020283573

theorem tailTrace_5654361 : CollatzResearch.WordTrace tailWord_5654361 prefixEnd_5654361 2903404987037257020283573 := by
  unfold tailWord_5654361
  simp only [CollatzResearch.WordTrace]
  refine ⟨206231488268223259821562937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137487658845482173214375291 206231488268223259821562937)
  ·
    refine ⟨154673616201167444866172203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206231488268223259821562937 154673616201167444866172203)
    ·
      refine ⟨232010424301751167299258305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154673616201167444866172203 232010424301751167299258305)
      ·
        refine ⟨174007818226313375474443729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232010424301751167299258305 174007818226313375474443729)
        ·
          refine ⟨130505863669735031605832797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174007818226313375474443729 130505863669735031605832797)
          ·
            refine ⟨48939698876150636852187299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130505863669735031605832797 48939698876150636852187299)
            ·
              refine ⟨73409548314225955278280949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48939698876150636852187299 73409548314225955278280949)
              ·
                refine ⟨6882145154458683307338839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73409548314225955278280949 6882145154458683307338839)
                ·
                  refine ⟨10323217731688024961008259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6882145154458683307338839 10323217731688024961008259)
                  ·
                    refine ⟨15484826597532037441512389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10323217731688024961008259 15484826597532037441512389)
                    ·
                      refine ⟨2903404987037257020283573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15484826597532037441512389 2903404987037257020283573)
                      ·
                        rfl

theorem cell23_5654361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_5654361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654361 prefixEnd_5654361 := by exact prefixLift 5654361
  have htrace : WordTrace (prefixWord ++ tailWord_5654361) baseStart_5654361 baseEnd_5654361 := by
    simpa [prefixWord, tailWord_5654361, baseEnd_5654361] using wordTrace_append hprefix tailTrace_5654361
  have hstable : (prefixWord ++ tailWord_5654361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654361).length < 2 ^ (prefixWord ++ tailWord_5654361).sum := by decide
  have hdescent : baseEnd_5654361 < baseStart_5654361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654372 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_5654372 : Nat := 118140960795 + 5654372 * 2 ^ 59
def prefixEnd_5654372 : Nat := 4983230072969 + 3 ^ 40 * 5654372 * 2
def baseEnd_5654372 : Nat := 2903410635324456477246023

theorem tailTrace_5654372 : CollatzResearch.WordTrace tailWord_5654372 prefixEnd_5654372 2903410635324456477246023 := by
  unfold tailWord_5654372
  simp only [CollatzResearch.WordTrace]
  refine ⟨103115944735591704350106685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137487926314122272466808913 103115944735591704350106685)
  ·
    refine ⟨38668479275846889131290007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103115944735591704350106685 38668479275846889131290007)
    ·
      refine ⟨58002718913770333696935011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38668479275846889131290007 58002718913770333696935011)
      ·
        refine ⟨87004078370655500545402517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58002718913770333696935011 87004078370655500545402517)
        ·
          refine ⟨4078316173624476588065743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87004078370655500545402517 4078316173624476588065743)
          ·
            refine ⟨6117474260436714882098615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078316173624476588065743 6117474260436714882098615)
            ·
              refine ⟨9176211390655072323147923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6117474260436714882098615 9176211390655072323147923)
              ·
                refine ⟨13764317085982608484721885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9176211390655072323147923 13764317085982608484721885)
                ·
                  refine ⟨5161618907243478181770707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13764317085982608484721885 5161618907243478181770707)
                  ·
                    refine ⟨7742428360865217272656061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5161618907243478181770707 7742428360865217272656061)
                    ·
                      refine ⟨2903410635324456477246023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7742428360865217272656061 2903410635324456477246023)
                      ·
                        rfl

theorem cell23_5654372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_5654372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654372 prefixEnd_5654372 := by exact prefixLift 5654372
  have htrace : WordTrace (prefixWord ++ tailWord_5654372) baseStart_5654372 baseEnd_5654372 := by
    simpa [prefixWord, tailWord_5654372, baseEnd_5654372] using wordTrace_append hprefix tailTrace_5654372
  have hstable : (prefixWord ++ tailWord_5654372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654372).length < 2 ^ (prefixWord ++ tailWord_5654372).sum := by decide
  have hdescent : baseEnd_5654372 < baseStart_5654372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654381 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_5654381 : Nat := 118140960795 + 5654381 * 2 ^ 59
def prefixEnd_5654381 : Nat := 4983230072969 + 3 ^ 40 * 5654381 * 2
def baseEnd_5654381 : Nat := 2903415256650346942033481

theorem tailTrace_5654381 : CollatzResearch.WordTrace tailWord_5654381 prefixEnd_5654381 2903415256650346942033481 := by
  unfold tailWord_5654381
  simp only [CollatzResearch.WordTrace]
  refine ⟨206232217728150803237290997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137488145152100535491527331 206232217728150803237290997)
  ·
    refine ⟨19334270412014137803496031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206232217728150803237290997 19334270412014137803496031)
    ·
      refine ⟨29001405618021206705244047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19334270412014137803496031 29001405618021206705244047)
      ·
        refine ⟨43502108427031810057866071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29001405618021206705244047 43502108427031810057866071)
        ·
          refine ⟨65253162640547715086799107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43502108427031810057866071 65253162640547715086799107)
          ·
            refine ⟨97879743960821572630198661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65253162640547715086799107 97879743960821572630198661)
            ·
              refine ⟨18352451992654044868162249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97879743960821572630198661 18352451992654044868162249)
              ·
                refine ⟨13764338994490533651121687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18352451992654044868162249 13764338994490533651121687)
                ·
                  refine ⟨20646508491735800476682531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13764338994490533651121687 20646508491735800476682531)
                  ·
                    refine ⟨30969762737603700715023797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20646508491735800476682531 30969762737603700715023797)
                    ·
                      refine ⟨2903415256650346942033481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30969762737603700715023797 2903415256650346942033481)
                      ·
                        rfl

theorem cell23_5654381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_5654381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654381 prefixEnd_5654381 := by exact prefixLift 5654381
  have htrace : WordTrace (prefixWord ++ tailWord_5654381) baseStart_5654381 baseEnd_5654381 := by
    simpa [prefixWord, tailWord_5654381, baseEnd_5654381] using wordTrace_append hprefix tailTrace_5654381
  have hstable : (prefixWord ++ tailWord_5654381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654381).length < 2 ^ (prefixWord ++ tailWord_5654381).sum := by decide
  have hdescent : baseEnd_5654381 < baseStart_5654381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654408 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_5654408 : Nat := 118140960795 + 5654408 * 2 ^ 59
def prefixEnd_5654408 : Nat := 4983230072969 + 3 ^ 40 * 5654408 * 2
def baseEnd_5654408 : Nat := 2903429120628018336395857

theorem tailTrace_5654408 : CollatzResearch.WordTrace tailWord_5654408 prefixEnd_5654408 2903429120628018336395857 := by
  unfold tailWord_5654408
  simp only [CollatzResearch.WordTrace]
  refine ⟨103116601249526493424261939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137488801666035324565682585 103116601249526493424261939)
  ·
    refine ⟨154674901874289740136392909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103116601249526493424261939 154674901874289740136392909)
    ·
      refine ⟨58003088202858652551147341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154674901874289740136392909 58003088202858652551147341)
      ·
        refine ⟨21751158076071994706680253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58003088202858652551147341 21751158076071994706680253)
        ·
          refine ⟨8156684278526998015005095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21751158076071994706680253 8156684278526998015005095)
          ·
            refine ⟨12235026417790497022507643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156684278526998015005095 12235026417790497022507643)
            ·
              refine ⟨18352539626685745533761465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12235026417790497022507643 18352539626685745533761465)
              ·
                refine ⟨13764404720014309150321099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18352539626685745533761465 13764404720014309150321099)
                ·
                  refine ⟨20646607080021463725481649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13764404720014309150321099 20646607080021463725481649)
                  ·
                    refine ⟨15484955310016097794111237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20646607080021463725481649 15484955310016097794111237)
                    ·
                      refine ⟨2903429120628018336395857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15484955310016097794111237 2903429120628018336395857)
                      ·
                        rfl

theorem cell23_5654408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_5654408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654408 prefixEnd_5654408 := by exact prefixLift 5654408
  have htrace : WordTrace (prefixWord ++ tailWord_5654408) baseStart_5654408 baseEnd_5654408 := by
    simpa [prefixWord, tailWord_5654408, baseEnd_5654408] using wordTrace_append hprefix tailTrace_5654408
  have hstable : (prefixWord ++ tailWord_5654408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654408).length < 2 ^ (prefixWord ++ tailWord_5654408).sum := by decide
  have hdescent : baseEnd_5654408 < baseStart_5654408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654429 : List Nat := [1, 4, 2, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_5654429 : Nat := 118140960795 + 5654429 * 2 ^ 59
def prefixEnd_5654429 : Nat := 4983230072969 + 3 ^ 40 * 5654429 * 2
def baseEnd_5654429 : Nat := 2903439903721762754233261

theorem tailTrace_5654429 : CollatzResearch.WordTrace tailWord_5654429 prefixEnd_5654429 2903439903721762754233261 := by
  unfold tailWord_5654429
  simp only [CollatzResearch.WordTrace]
  refine ⟨206233968431976907435038341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137489312287984604956692227 206233968431976907435038341)
  ·
    refine ⟨38668869080995670144069689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206233968431976907435038341 38668869080995670144069689)
    ·
      refine ⟨29001651810746752608052267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38668869080995670144069689 29001651810746752608052267)
      ·
        refine ⟨43502477716120128912078401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29001651810746752608052267 43502477716120128912078401)
        ·
          refine ⟨32626858287090096684058801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43502477716120128912078401 32626858287090096684058801)
          ·
            refine ⟨24470143715317572513044101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32626858287090096684058801 24470143715317572513044101)
            ·
              refine ⟨4588151946622044846195769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24470143715317572513044101 4588151946622044846195769)
              ·
                refine ⟨3441113959966533634646827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4588151946622044846195769 3441113959966533634646827)
                ·
                  refine ⟨5161670939949800451970241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3441113959966533634646827 5161670939949800451970241)
                  ·
                    refine ⟨3871253204962350338977681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5161670939949800451970241 3871253204962350338977681)
                    ·
                      refine ⟨2903439903721762754233261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871253204962350338977681 2903439903721762754233261)
                      ·
                        rfl

theorem cell23_5654429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_5654429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654429 prefixEnd_5654429 := by exact prefixLift 5654429
  have htrace : WordTrace (prefixWord ++ tailWord_5654429) baseStart_5654429 baseEnd_5654429 := by
    simpa [prefixWord, tailWord_5654429, baseEnd_5654429] using wordTrace_append hprefix tailTrace_5654429
  have hstable : (prefixWord ++ tailWord_5654429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654429).length < 2 ^ (prefixWord ++ tailWord_5654429).sum := by decide
  have hdescent : baseEnd_5654429 < baseStart_5654429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654446 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5654446 : Nat := 118140960795 + 5654446 * 2 ^ 59
def prefixEnd_5654446 : Nat := 4983230072969 + 3 ^ 40 * 5654446 * 2
def baseEnd_5654446 : Nat := 2903448632892889187720683

theorem tailTrace_5654446 : CollatzResearch.WordTrace tailWord_5654446 prefixEnd_5654446 2903448632892889187720683 := by
  unfold tailWord_5654446
  simp only [CollatzResearch.WordTrace]
  refine ⟨25779323559114414917300899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137489725648610212892271461 25779323559114414917300899)
  ·
    refine ⟨38668985338671622375951349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25779323559114414917300899 38668985338671622375951349)
    ·
      refine ⟨3625217375500464597745439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38668985338671622375951349 3625217375500464597745439)
      ·
        refine ⟨5437826063250696896618159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3625217375500464597745439 5437826063250696896618159)
        ·
          refine ⟨8156739094876045344927239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5437826063250696896618159 8156739094876045344927239)
          ·
            refine ⟨12235108642314068017390859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156739094876045344927239 12235108642314068017390859)
            ·
              refine ⟨18352662963471102026086289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12235108642314068017390859 18352662963471102026086289)
              ·
                refine ⟨13764497222603326519564717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18352662963471102026086289 13764497222603326519564717)
                ·
                  refine ⟨5161686458476247444836769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13764497222603326519564717 5161686458476247444836769)
                  ·
                    refine ⟨3871264843857185583627577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5161686458476247444836769 3871264843857185583627577)
                    ·
                      refine ⟨2903448632892889187720683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871264843857185583627577 2903448632892889187720683)
                      ·
                        rfl

theorem cell23_5654446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5654446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654446 prefixEnd_5654446 := by exact prefixLift 5654446
  have htrace : WordTrace (prefixWord ++ tailWord_5654446) baseStart_5654446 baseEnd_5654446 := by
    simpa [prefixWord, tailWord_5654446, baseEnd_5654446] using wordTrace_append hprefix tailTrace_5654446
  have hstable : (prefixWord ++ tailWord_5654446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654446).length < 2 ^ (prefixWord ++ tailWord_5654446).sum := by decide
  have hdescent : baseEnd_5654446 < baseStart_5654446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654472 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 1, 3, 2]
def baseStart_5654472 : Nat := 118140960795 + 5654472 * 2 ^ 59
def prefixEnd_5654472 : Nat := 4983230072969 + 3 ^ 40 * 5654472 * 2
def baseEnd_5654472 : Nat := 2903461983389906085995563

theorem tailTrace_5654472 : CollatzResearch.WordTrace tailWord_5654472 prefixEnd_5654472 2903461983389906085995563 := by
  unfold tailWord_5654472
  simp only [CollatzResearch.WordTrace]
  refine ⟨103117768385410562889426835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137490357847214083852569113 103117768385410562889426835)
  ·
    refine ⟨154676652578115844334140253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103117768385410562889426835 154676652578115844334140253)
    ·
      refine ⟨58003744716793441625302595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154676652578115844334140253 58003744716793441625302595)
      ·
        refine ⟨87005617075190162437953893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58003744716793441625302595 87005617075190162437953893)
        ·
          refine ⟨16313553201598155457116355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87005617075190162437953893 16313553201598155457116355)
          ·
            refine ⟨24470329802397233185674533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16313553201598155457116355 24470329802397233185674533)
            ·
              refine ⟨4588186837949481222313975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24470329802397233185674533 4588186837949481222313975)
              ·
                refine ⟨6882280256924221833470963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4588186837949481222313975 6882280256924221833470963)
                ·
                  refine ⟨10323420385386332750206445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6882280256924221833470963 10323420385386332750206445)
                  ·
                    refine ⟨3871282644519874781327417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10323420385386332750206445 3871282644519874781327417)
                    ·
                      refine ⟨2903461983389906085995563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871282644519874781327417 2903461983389906085995563)
                      ·
                        rfl

theorem cell23_5654472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_5654472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654472 prefixEnd_5654472 := by exact prefixLift 5654472
  have htrace : WordTrace (prefixWord ++ tailWord_5654472) baseStart_5654472 baseEnd_5654472 := by
    simpa [prefixWord, tailWord_5654472, baseEnd_5654472] using wordTrace_append hprefix tailTrace_5654472
  have hstable : (prefixWord ++ tailWord_5654472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654472).length < 2 ^ (prefixWord ++ tailWord_5654472).sum := by decide
  have hdescent : baseEnd_5654472 < baseStart_5654472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654521 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 1, 7]
def baseStart_5654521 : Nat := 118140960795 + 5654521 * 2 ^ 59
def prefixEnd_5654521 : Nat := 4983230072969 + 3 ^ 40 * 5654521 * 2
def baseEnd_5654521 : Nat := 967829047980658798094279

theorem tailTrace_5654521 : CollatzResearch.WordTrace tailWord_5654521 prefixEnd_5654521 967829047980658798094279 := by
  unfold tailWord_5654521
  simp only [CollatzResearch.WordTrace]
  refine ⟨206237323947643607147387417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137491549298429071431591611 206237323947643607147387417)
  ·
    refine ⟨154677992960732705360540563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206237323947643607147387417 154677992960732705360540563)
    ·
      refine ⟨232016989441099058040810845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154677992960732705360540563 232016989441099058040810845)
      ·
        refine ⟨87006371040412146765304067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232016989441099058040810845 87006371040412146765304067)
        ·
          refine ⟨130509556560618220147956101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87006371040412146765304067 130509556560618220147956101)
          ·
            refine ⟨24470541855115916277741769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130509556560618220147956101 24470541855115916277741769)
            ·
              refine ⟨18352906391336937208306327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24470541855115916277741769 18352906391336937208306327)
              ·
                refine ⟨27529359587005405812459491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18352906391336937208306327 27529359587005405812459491)
                ·
                  refine ⟨41294039380508108718689237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27529359587005405812459491 41294039380508108718689237)
                  ·
                    refine ⟨967829047980658798094279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41294039380508108718689237 967829047980658798094279)
                    ·
                      rfl

theorem cell23_5654521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_5654521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654521 prefixEnd_5654521 := by exact prefixLift 5654521
  have htrace : WordTrace (prefixWord ++ tailWord_5654521) baseStart_5654521 baseEnd_5654521 := by
    simpa [prefixWord, tailWord_5654521, baseEnd_5654521] using wordTrace_append hprefix tailTrace_5654521
  have hstable : (prefixWord ++ tailWord_5654521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654521).length < 2 ^ (prefixWord ++ tailWord_5654521).sum := by decide
  have hdescent : baseEnd_5654521 < baseStart_5654521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654581 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 10]
def baseStart_5654581 : Nat := 118140960795 + 5654581 * 2 ^ 59
def prefixEnd_5654581 : Nat := 4983230072969 + 3 ^ 40 * 5654581 * 2
def baseEnd_5654581 : Nat := 322613105864582906614729

theorem tailTrace_5654581 : CollatzResearch.WordTrace tailWord_5654581 prefixEnd_5654581 322613105864582906614729 := by
  unfold tailWord_5654581
  simp only [CollatzResearch.WordTrace]
  refine ⟨206239512327426237394571597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137493008218284158263047731 206239512327426237394571597)
  ·
    refine ⟨77339817122784839022964349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206239512327426237394571597 77339817122784839022964349)
    ·
      refine ⟨29002431421044314633611631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77339817122784839022964349 29002431421044314633611631)
      ·
        refine ⟨43503647131566471950417447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29002431421044314633611631 43503647131566471950417447)
        ·
          refine ⟨65255470697349707925626171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43503647131566471950417447 65255470697349707925626171)
          ·
            refine ⟨97883206046024561888439257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65255470697349707925626171 97883206046024561888439257)
            ·
              refine ⟨73412404534518421416329443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97883206046024561888439257 73412404534518421416329443)
              ·
                refine ⟨110118606801777632124494165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73412404534518421416329443 110118606801777632124494165)
                ·
                  refine ⟨322613105864582906614729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 110118606801777632124494165 322613105864582906614729)
                  ·
                    rfl

theorem cell23_5654581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_5654581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654581 prefixEnd_5654581 := by exact prefixLift 5654581
  have htrace : WordTrace (prefixWord ++ tailWord_5654581) baseStart_5654581 baseEnd_5654581 := by
    simpa [prefixWord, tailWord_5654581, baseEnd_5654581] using wordTrace_append hprefix tailTrace_5654581
  have hstable : (prefixWord ++ tailWord_5654581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654581).length < 2 ^ (prefixWord ++ tailWord_5654581).sum := by decide
  have hdescent : baseEnd_5654581 < baseStart_5654581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654601 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_5654601 : Nat := 118140960795 + 5654601 * 2 ^ 59
def prefixEnd_5654601 : Nat := 4983230072969 + 3 ^ 40 * 5654601 * 2
def baseEnd_5654601 : Nat := 2903528222394336081282469

theorem tailTrace_5654601 : CollatzResearch.WordTrace tailWord_5654601 prefixEnd_5654601 2903528222394336081282469 := by
  unfold tailWord_5654601
  simp only [CollatzResearch.WordTrace]
  refine ⟨206240241787353780810299657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137493494524902520540199771 206240241787353780810299657)
  ·
    refine ⟨154680181340515335607724743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206240241787353780810299657 154680181340515335607724743)
    ·
      refine ⟨232020272010773003411587115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154680181340515335607724743 232020272010773003411587115)
      ·
        refine ⟨348030408016159505117380673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232020272010773003411587115 348030408016159505117380673)
        ·
          refine ⟨261022806012119628838035505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348030408016159505117380673 261022806012119628838035505)
          ·
            refine ⟨195767104509089721628526629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261022806012119628838035505 195767104509089721628526629)
            ·
              refine ⟨36706332095454322805348743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195767104509089721628526629 36706332095454322805348743)
              ·
                refine ⟨55059498143181484208023115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36706332095454322805348743 55059498143181484208023115)
                ·
                  refine ⟨82589247214772226312034673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55059498143181484208023115 82589247214772226312034673)
                  ·
                    refine ⟨61941935411079169734026005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82589247214772226312034673 61941935411079169734026005)
                    ·
                      refine ⟨2903528222394336081282469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61941935411079169734026005 2903528222394336081282469)
                      ·
                        rfl

theorem cell23_5654601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_5654601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654601 prefixEnd_5654601 := by exact prefixLift 5654601
  have htrace : WordTrace (prefixWord ++ tailWord_5654601) baseStart_5654601 baseEnd_5654601 := by
    simpa [prefixWord, tailWord_5654601, baseEnd_5654601] using wordTrace_append hprefix tailTrace_5654601
  have hstable : (prefixWord ++ tailWord_5654601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654601).length < 2 ^ (prefixWord ++ tailWord_5654601).sum := by decide
  have hdescent : baseEnd_5654601 < baseStart_5654601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654628 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_5654628 : Nat := 118140960795 + 5654628 * 2 ^ 59
def prefixEnd_5654628 : Nat := 4983230072969 + 3 ^ 40 * 5654628 * 2
def baseEnd_5654628 : Nat := 967847362124002491881615

theorem tailTrace_5654628 : CollatzResearch.WordTrace tailWord_5654628 prefixEnd_5654628 967847362124002491881615 := by
  unfold tailWord_5654628
  simp only [CollatzResearch.WordTrace]
  refine ⟨103120613279127982210766269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137494151038837309614355025 103120613279127982210766269)
  ·
    refine ⟨38670229979672993329037351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103120613279127982210766269 38670229979672993329037351)
    ·
      refine ⟨58005344969509489993556027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38670229979672993329037351 58005344969509489993556027)
      ·
        refine ⟨87008017454264234990334041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58005344969509489993556027 87008017454264234990334041)
        ·
          refine ⟨65256013090698176242750531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87008017454264234990334041 65256013090698176242750531)
          ·
            refine ⟨97884019636047264364125797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65256013090698176242750531 97884019636047264364125797)
            ·
              refine ⟨18353253681758862068273587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97884019636047264364125797 18353253681758862068273587)
              ·
                refine ⟨27529880522638293102410381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18353253681758862068273587 27529880522638293102410381)
                ·
                  refine ⟨10323705195989359913403893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27529880522638293102410381 10323705195989359913403893)
                  ·
                    refine ⟨967847362124002491881615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10323705195989359913403893 967847362124002491881615)
                    ·
                      rfl

theorem cell23_5654628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_5654628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654628 prefixEnd_5654628 := by exact prefixLift 5654628
  have htrace : WordTrace (prefixWord ++ tailWord_5654628) baseStart_5654628 baseEnd_5654628 := by
    simpa [prefixWord, tailWord_5654628, baseEnd_5654628] using wordTrace_append hprefix tailTrace_5654628
  have hstable : (prefixWord ++ tailWord_5654628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654628).length < 2 ^ (prefixWord ++ tailWord_5654628).sum := by decide
  have hdescent : baseEnd_5654628 < baseStart_5654628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654688 : List Nat := [2, 1, 1, 4, 2, 3, 1, 9]
def baseStart_5654688 : Nat := 118140960795 + 5654688 * 2 ^ 59
def prefixEnd_5654688 : Nat := 4983230072969 + 3 ^ 40 * 5654688 * 2
def baseEnd_5654688 : Nat := 107539736859676934847947

theorem tailTrace_5654688 : CollatzResearch.WordTrace tailWord_5654688 prefixEnd_5654688 107539736859676934847947 := by
  unfold tailWord_5654688
  simp only [CollatzResearch.WordTrace]
  refine ⟨103121707469019297334358359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137495609958692396445811145 103121707469019297334358359)
  ·
    refine ⟨154682561203528946001537539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103121707469019297334358359 154682561203528946001537539)
    ·
      refine ⟨232023841805293419002306309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154682561203528946001537539 232023841805293419002306309)
      ·
        refine ⟨43504470338492516062932433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232023841805293419002306309 43504470338492516062932433)
        ·
          refine ⟨32628352753869387047199325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43504470338492516062932433 32628352753869387047199325)
          ·
            refine ⟨12235632282701020142699747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32628352753869387047199325 12235632282701020142699747)
            ·
              refine ⟨18353448424051530214049621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12235632282701020142699747 18353448424051530214049621)
              ·
                refine ⟨107539736859676934847947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18353448424051530214049621 107539736859676934847947)
                ·
                  rfl

theorem cell23_5654688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 9].length) (baseStart_5654688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654688 prefixEnd_5654688 := by exact prefixLift 5654688
  have htrace : WordTrace (prefixWord ++ tailWord_5654688) baseStart_5654688 baseEnd_5654688 := by
    simpa [prefixWord, tailWord_5654688, baseEnd_5654688] using wordTrace_append hprefix tailTrace_5654688
  have hstable : (prefixWord ++ tailWord_5654688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654688).length < 2 ^ (prefixWord ++ tailWord_5654688).sum := by decide
  have hdescent : baseEnd_5654688 < baseStart_5654688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654705 : List Nat := [1, 2, 2, 5, 2, 2, 9]
def baseStart_5654705 : Nat := 118140960795 + 5654705 * 2 ^ 59
def prefixEnd_5654705 : Nat := 4983230072969 + 3 ^ 40 * 5654705 * 2
def baseEnd_5654705 : Nat := 35846686720770415733111

theorem tailTrace_5654705 : CollatzResearch.WordTrace tailWord_5654705 prefixEnd_5654705 35846686720770415733111 := by
  unfold tailWord_5654705
  simp only [CollatzResearch.WordTrace]
  refine ⟨206244034978977006572085569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137496023319318004381390379 206244034978977006572085569)
  ·
    refine ⟨154683026234232754929064177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206244034978977006572085569 154683026234232754929064177)
    ·
      refine ⟨116012269675674566196798133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154683026234232754929064177 116012269675674566196798133)
      ·
        refine ⟨10876150282094490580949825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116012269675674566196798133 10876150282094490580949825)
        ·
          refine ⟨8157112711570867935712369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10876150282094490580949825 8157112711570867935712369)
          ·
            refine ⟨6117834533678150951784277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8157112711570867935712369 6117834533678150951784277)
            ·
              refine ⟨35846686720770415733111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6117834533678150951784277 35846686720770415733111)
              ·
                rfl

theorem cell23_5654705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 9].length) (baseStart_5654705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654705 prefixEnd_5654705 := by exact prefixLift 5654705
  have htrace : WordTrace (prefixWord ++ tailWord_5654705) baseStart_5654705 baseEnd_5654705 := by
    simpa [prefixWord, tailWord_5654705, baseEnd_5654705] using wordTrace_append hprefix tailTrace_5654705
  have hstable : (prefixWord ++ tailWord_5654705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654705).length < 2 ^ (prefixWord ++ tailWord_5654705).sum := by decide
  have hdescent : baseEnd_5654705 < baseStart_5654705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654715 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 3]
def baseStart_5654715 : Nat := 118140960795 + 5654715 * 2 ^ 59
def prefixEnd_5654715 : Nat := 4983230072969 + 3 ^ 40 * 5654715 * 2
def baseEnd_5654715 : Nat := 2903586759188948635256945

theorem tailTrace_5654715 : CollatzResearch.WordTrace tailWord_5654715 prefixEnd_5654715 2903586759188948635256945 := by
  unfold tailWord_5654715
  simp only [CollatzResearch.WordTrace]
  refine ⟨206244399708940778279949599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137496266472627185519966399 206244399708940778279949599)
  ·
    refine ⟨309366599563411167419924399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206244399708940778279949599 309366599563411167419924399)
    ·
      refine ⟨464049899345116751129886599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309366599563411167419924399 464049899345116751129886599)
      ·
        refine ⟨696074849017675126694829899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464049899345116751129886599 696074849017675126694829899)
        ·
          refine ⟨1044112273526512690042244849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696074849017675126694829899 1044112273526512690042244849)
          ·
            refine ⟨783084205144884517531683637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044112273526512690042244849 783084205144884517531683637)
            ·
              refine ⟨73414144232332923518595341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 783084205144884517531683637 73414144232332923518595341)
              ·
                refine ⟨27530304087124846319473253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73414144232332923518595341 27530304087124846319473253)
                ·
                  refine ⟨5161932016335908684901235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27530304087124846319473253 5161932016335908684901235)
                  ·
                    refine ⟨7742898024503863027351853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5161932016335908684901235 7742898024503863027351853)
                    ·
                      refine ⟨2903586759188948635256945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7742898024503863027351853 2903586759188948635256945)
                      ·
                        rfl

theorem cell23_5654715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 1, 3].length) (baseStart_5654715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654715 prefixEnd_5654715 := by exact prefixLift 5654715
  have htrace : WordTrace (prefixWord ++ tailWord_5654715) baseStart_5654715 baseEnd_5654715 := by
    simpa [prefixWord, tailWord_5654715, baseEnd_5654715] using wordTrace_append hprefix tailTrace_5654715
  have hstable : (prefixWord ++ tailWord_5654715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654715).length < 2 ^ (prefixWord ++ tailWord_5654715).sum := by decide
  have hdescent : baseEnd_5654715 < baseStart_5654715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654716 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_5654716 : Nat := 118140960795 + 5654716 * 2 ^ 59
def prefixEnd_5654716 : Nat := 4983230072969 + 3 ^ 40 * 5654716 * 2
def baseEnd_5654716 : Nat := 2903587272669603131344441

theorem tailTrace_5654716 : CollatzResearch.WordTrace tailWord_5654716 prefixEnd_5654716 2903587272669603131344441 := by
  unfold tailWord_5654716
  simp only [CollatzResearch.WordTrace]
  refine ⟨103122218090968577725368001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137496290787958103633824001 103122218090968577725368001)
  ·
    refine ⟨77341663568226433294026001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103122218090968577725368001 77341663568226433294026001)
    ·
      refine ⟨58006247676169824970519501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77341663568226433294026001 58006247676169824970519501)
      ·
        refine ⟨21752342878563684363944813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58006247676169824970519501 21752342878563684363944813)
        ·
          refine ⟨8157128579461381636479305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21752342878563684363944813 8157128579461381636479305)
          ·
            refine ⟨6117846434596036227359479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8157128579461381636479305 6117846434596036227359479)
            ·
              refine ⟨9176769651894054341039219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6117846434596036227359479 9176769651894054341039219)
              ·
                refine ⟨13765154477841081511558829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9176769651894054341039219 13765154477841081511558829)
                ·
                  refine ⟨5161932929190405566834561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13765154477841081511558829 5161932929190405566834561)
                  ·
                    refine ⟨3871449696892804175125921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5161932929190405566834561 3871449696892804175125921)
                    ·
                      refine ⟨2903587272669603131344441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3871449696892804175125921 2903587272669603131344441)
                      ·
                        rfl

theorem cell23_5654716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_5654716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654716 prefixEnd_5654716 := by exact prefixLift 5654716
  have htrace : WordTrace (prefixWord ++ tailWord_5654716) baseStart_5654716 baseEnd_5654716 := by
    simpa [prefixWord, tailWord_5654716, baseEnd_5654716] using wordTrace_append hprefix tailTrace_5654716
  have hstable : (prefixWord ++ tailWord_5654716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654716).length < 2 ^ (prefixWord ++ tailWord_5654716).sum := by decide
  have hdescent : baseEnd_5654716 < baseStart_5654716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654722 : List Nat := [3, 5, 1, 1, 1, 1, 1, 10]
def baseStart_5654722 : Nat := 118140960795 + 5654722 * 2 ^ 59
def prefixEnd_5654722 : Nat := 4983230072969 + 3 ^ 40 * 5654722 * 2
def baseEnd_5654722 : Nat := 107540383464945559550719

theorem tailTrace_5654722 : CollatzResearch.WordTrace tailWord_5654722 prefixEnd_5654722 107540383464945559550719 := by
  unfold tailWord_5654722
  simp only [CollatzResearch.WordTrace]
  refine ⟨51561163754978854618863605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137496436679943612316969613 51561163754978854618863605)
  ·
    refine ⟨4833859102029267620518463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51561163754978854618863605 4833859102029267620518463)
    ·
      refine ⟨7250788653043901430777695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4833859102029267620518463 7250788653043901430777695)
      ·
        refine ⟨10876182979565852146166543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7250788653043901430777695 10876182979565852146166543)
        ·
          refine ⟨16314274469348778219249815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10876182979565852146166543 16314274469348778219249815)
          ·
            refine ⟨24471411704023167328874723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16314274469348778219249815 24471411704023167328874723)
            ·
              refine ⟨36707117556034750993312085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24471411704023167328874723 36707117556034750993312085)
              ·
                refine ⟨107540383464945559550719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36707117556034750993312085 107540383464945559550719)
                ·
                  rfl

theorem cell23_5654722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 10].length) (baseStart_5654722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654722 prefixEnd_5654722 := by exact prefixLift 5654722
  have htrace : WordTrace (prefixWord ++ tailWord_5654722) baseStart_5654722 baseEnd_5654722 := by
    simpa [prefixWord, tailWord_5654722, baseEnd_5654722] using wordTrace_append hprefix tailTrace_5654722
  have hstable : (prefixWord ++ tailWord_5654722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654722).length < 2 ^ (prefixWord ++ tailWord_5654722).sum := by decide
  have hdescent : baseEnd_5654722 < baseStart_5654722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5654768 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_5654768 : Nat := 118140960795 + 5654768 * 2 ^ 59
def prefixEnd_5654768 : Nat := 4983230072969 + 3 ^ 40 * 5654768 * 2
def baseEnd_5654768 : Nat := 2903613973663636927894201

theorem tailTrace_5654768 : CollatzResearch.WordTrace tailWord_5654768 prefixEnd_5654768 2903613973663636927894201 := by
  unfold tailWord_5654768
  simp only [CollatzResearch.WordTrace]
  refine ⟨103123166388874384165814479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137497555185165845554419305 103123166388874384165814479)
  ·
    refine ⟨154684749583311576248721719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103123166388874384165814479 154684749583311576248721719)
    ·
      refine ⟨232027124374967364373082579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154684749583311576248721719 232027124374967364373082579)
      ·
        refine ⟨348040686562451046559623869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232027124374967364373082579 348040686562451046559623869)
        ·
          refine ⟨130515257460919142459858951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348040686562451046559623869 130515257460919142459858951)
          ·
            refine ⟨195772886191378713689788427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130515257460919142459858951 195772886191378713689788427)
            ·
              refine ⟨293659329287068070534682641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195772886191378713689788427 293659329287068070534682641)
              ·
                refine ⟨220244496965301052901011981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293659329287068070534682641 220244496965301052901011981)
                ·
                  refine ⟨82591686361987894837879493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220244496965301052901011981 82591686361987894837879493)
                  ·
                    refine ⟨15485941192872730282102405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82591686361987894837879493 15485941192872730282102405)
                    ·
                      refine ⟨2903613973663636927894201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15485941192872730282102405 2903613973663636927894201)
                      ·
                        rfl

theorem cell23_5654768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_5654768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5654768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5654768 prefixEnd_5654768 := by exact prefixLift 5654768
  have htrace : WordTrace (prefixWord ++ tailWord_5654768) baseStart_5654768 baseEnd_5654768 := by
    simpa [prefixWord, tailWord_5654768, baseEnd_5654768] using wordTrace_append hprefix tailTrace_5654768
  have hstable : (prefixWord ++ tailWord_5654768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5654768).length < 2 ^ (prefixWord ++ tailWord_5654768).sum := by decide
  have hdescent : baseEnd_5654768 < baseStart_5654768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5654768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
