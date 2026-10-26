import V185TrunkScan23Chunk0427

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2530185 : List Nat := [1, 2, 1, 1, 5, 4, 1, 2, 6]
def baseStart_2530185 : Nat := 118140960795 + 2530185 * 2 ^ 59
def prefixEnd_2530185 : Nat := 4983230072969 + 3 ^ 40 * 2530185 * 2
def baseEnd_2530185 : Nat := 144355672199587597027933

theorem tailTrace_2530185 : CollatzResearch.WordTrace tailWord_2530185 prefixEnd_2530185 144355672199587597027933 := by
  unfold tailWord_2530185
  simp only [CollatzResearch.WordTrace]
  refine ⟨92283428338579341040184009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61522285559052894026789339 92283428338579341040184009)
  ·
    refine ⟨69212571253934505780138007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92283428338579341040184009 69212571253934505780138007)
    ·
      refine ⟨103818856880901758670207011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69212571253934505780138007 103818856880901758670207011)
      ·
        refine ⟨155728285321352638005310517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103818856880901758670207011 155728285321352638005310517)
        ·
          refine ⟨14599526748876809812997861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155728285321352638005310517 14599526748876809812997861)
          ·
            refine ⟨2737411265414401839937099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14599526748876809812997861 2737411265414401839937099)
            ·
              refine ⟨4106116898121602759905649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737411265414401839937099 4106116898121602759905649)
              ·
                refine ⟨3079587673591202069929237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106116898121602759905649 3079587673591202069929237)
                ·
                  refine ⟨144355672199587597027933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3079587673591202069929237 144355672199587597027933)
                  ·
                    rfl

theorem cell23_2530185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 6].length) (baseStart_2530185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530185 prefixEnd_2530185 := by exact prefixLift 2530185
  have htrace : WordTrace (prefixWord ++ tailWord_2530185) baseStart_2530185 baseEnd_2530185 := by
    simpa [prefixWord, tailWord_2530185, baseEnd_2530185] using wordTrace_append hprefix tailTrace_2530185
  have hstable : (prefixWord ++ tailWord_2530185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530185).length < 2 ^ (prefixWord ++ tailWord_2530185).sum := by decide
  have hdescent : baseEnd_2530185 < baseStart_2530185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530202 : List Nat := [3, 1, 1, 4, 3, 1, 3, 1, 6]
def baseStart_2530202 : Nat := 118140960795 + 2530202 * 2 ^ 59
def prefixEnd_2530202 : Nat := 4983230072969 + 3 ^ 40 * 2530202 * 2
def baseEnd_2530202 : Nat := 144356642107490534082091

theorem tailTrace_2530202 : CollatzResearch.WordTrace tailWord_2530202 prefixEnd_2530202 144356642107490534082091 := by
  unfold tailWord_2530202
  simp only [CollatzResearch.WordTrace]
  refine ⟨23071012094879438235888215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61522698919678501962368573 23071012094879438235888215)
  ·
    refine ⟨34606518142319157353832323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23071012094879438235888215 34606518142319157353832323)
    ·
      refine ⟨51909777213478736030748485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34606518142319157353832323 51909777213478736030748485)
      ·
        refine ⟨9733083227527263005765341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51909777213478736030748485 9733083227527263005765341)
        ·
          refine ⟨3649906210322723627162003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9733083227527263005765341 3649906210322723627162003)
          ·
            refine ⟨5474859315484085440743005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3649906210322723627162003 5474859315484085440743005)
            ·
              refine ⟨2053072243306532040278627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5474859315484085440743005 2053072243306532040278627)
              ·
                refine ⟨3079608364959798060417941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053072243306532040278627 3079608364959798060417941)
                ·
                  refine ⟨144356642107490534082091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3079608364959798060417941 144356642107490534082091)
                  ·
                    rfl

theorem cell23_2530202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_2530202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530202 prefixEnd_2530202 := by exact prefixLift 2530202
  have htrace : WordTrace (prefixWord ++ tailWord_2530202) baseStart_2530202 baseEnd_2530202 := by
    simpa [prefixWord, tailWord_2530202, baseEnd_2530202] using wordTrace_append hprefix tailTrace_2530202
  have hstable : (prefixWord ++ tailWord_2530202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530202).length < 2 ^ (prefixWord ++ tailWord_2530202).sum := by decide
  have hdescent : baseEnd_2530202 < baseStart_2530202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530205 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_2530205 : Nat := 118140960795 + 2530205 * 2 ^ 59
def prefixEnd_2530205 : Nat := 4983230072969 + 3 ^ 40 * 2530205 * 2
def baseEnd_2530205 : Nat := 1299211319409378295001305

theorem tailTrace_2530205 : CollatzResearch.WordTrace tailWord_2530205 prefixEnd_2530205 1299211319409378295001305 := by
  unfold tailWord_2530205
  simp only [CollatzResearch.WordTrace]
  refine ⟨92284157798506884455912069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61522771865671256303941379 92284157798506884455912069)
  ·
    refine ⟨17303279587220040835483513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92284157798506884455912069 17303279587220040835483513)
    ·
      refine ⟨12977459690415030626612635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17303279587220040835483513 12977459690415030626612635)
      ·
        refine ⟨19466189535622545939918953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12977459690415030626612635 19466189535622545939918953)
        ·
          refine ⟨14599642151716909454939215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19466189535622545939918953 14599642151716909454939215)
          ·
            refine ⟨21899463227575364182408823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14599642151716909454939215 21899463227575364182408823)
            ·
              refine ⟨32849194841363046273613235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21899463227575364182408823 32849194841363046273613235)
              ·
                refine ⟨49273792262044569410419853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32849194841363046273613235 49273792262044569410419853)
                ·
                  refine ⟨18477672098266713528907445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49273792262044569410419853 18477672098266713528907445)
                  ·
                    refine ⟨1732281759212504393335073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18477672098266713528907445 1732281759212504393335073)
                    ·
                      refine ⟨1299211319409378295001305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732281759212504393335073 1299211319409378295001305)
                      ·
                        rfl

theorem cell23_2530205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_2530205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530205 prefixEnd_2530205 := by exact prefixLift 2530205
  have htrace : WordTrace (prefixWord ++ tailWord_2530205) baseStart_2530205 baseEnd_2530205 := by
    simpa [prefixWord, tailWord_2530205, baseEnd_2530205] using wordTrace_append hprefix tailTrace_2530205
  have hstable : (prefixWord ++ tailWord_2530205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530205).length < 2 ^ (prefixWord ++ tailWord_2530205).sum := by decide
  have hdescent : baseEnd_2530205 < baseStart_2530205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530253 : List Nat := [1, 6, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2530253 : Nat := 118140960795 + 2530253 * 2 ^ 59
def prefixEnd_2530253 : Nat := 4983230072969 + 3 ^ 40 * 2530253 * 2
def baseEnd_2530253 : Nat := 144359551831199345244565

theorem tailTrace_2530253 : CollatzResearch.WordTrace tailWord_2530253 prefixEnd_2530253 144359551831199345244565 := by
  unfold tailWord_2530253
  simp only [CollatzResearch.WordTrace]
  refine ⟨92285908502332988653659413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61523939001555325769106275 92285908502332988653659413)
  ·
    refine ⟨4325901961046858843140285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92285908502332988653659413 4325901961046858843140285)
    ·
      refine ⟨1622213235392572066177607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4325901961046858843140285 1622213235392572066177607)
      ·
        refine ⟨2433319853088858099266411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622213235392572066177607 2433319853088858099266411)
        ·
          refine ⟨3649979779633287148899617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2433319853088858099266411 3649979779633287148899617)
          ·
            refine ⟨2737484834724965361674713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649979779633287148899617 2737484834724965361674713)
            ·
              refine ⟨2053113626043724021256035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2737484834724965361674713 2053113626043724021256035)
              ·
                refine ⟨3079670439065586031884053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053113626043724021256035 3079670439065586031884053)
                ·
                  refine ⟨144359551831199345244565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3079670439065586031884053 144359551831199345244565)
                  ·
                    rfl

theorem cell23_2530253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2530253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530253 prefixEnd_2530253 := by exact prefixLift 2530253
  have htrace : WordTrace (prefixWord ++ tailWord_2530253) baseStart_2530253 baseEnd_2530253 := by
    simpa [prefixWord, tailWord_2530253, baseEnd_2530253] using wordTrace_append hprefix tailTrace_2530253
  have hstable : (prefixWord ++ tailWord_2530253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530253).length < 2 ^ (prefixWord ++ tailWord_2530253).sum := by decide
  have hdescent : baseEnd_2530253 < baseStart_2530253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530269 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2530269 : Nat := 118140960795 + 2530269 * 2 ^ 59
def prefixEnd_2530269 : Nat := 4983230072969 + 3 ^ 40 * 2530269 * 2
def baseEnd_2530269 : Nat := 1299244182171266044601011

theorem tailTrace_2530269 : CollatzResearch.WordTrace tailWord_2530269 prefixEnd_2530269 1299244182171266044601011 := by
  unfold tailWord_2530269
  simp only [CollatzResearch.WordTrace]
  refine ⟨92286492070275023386241861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61524328046850015590827907 92286492070275023386241861)
  ·
    refine ⟨17303717263176566884920349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92286492070275023386241861 17303717263176566884920349)
    ·
      refine ⟨6488893973691212581845131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17303717263176566884920349 6488893973691212581845131)
      ·
        refine ⟨9733340960536818872767697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6488893973691212581845131 9733340960536818872767697)
        ·
          refine ⟨7300005720402614154575773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9733340960536818872767697 7300005720402614154575773)
          ·
            refine ⟨2737502145150980307965915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7300005720402614154575773 2737502145150980307965915)
            ·
              refine ⟨4106253217726470461948873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737502145150980307965915 4106253217726470461948873)
              ·
                refine ⟨3079689913294852846461655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106253217726470461948873 3079689913294852846461655)
                ·
                  refine ⟨4619534869942279269692483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079689913294852846461655 4619534869942279269692483)
                  ·
                    refine ⟨6929302304913418904538725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4619534869942279269692483 6929302304913418904538725)
                    ·
                      refine ⟨1299244182171266044601011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6929302304913418904538725 1299244182171266044601011)
                      ·
                        rfl

theorem cell23_2530269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2530269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530269 prefixEnd_2530269 := by exact prefixLift 2530269
  have htrace : WordTrace (prefixWord ++ tailWord_2530269) baseStart_2530269 baseEnd_2530269 := by
    simpa [prefixWord, tailWord_2530269, baseEnd_2530269] using wordTrace_append hprefix tailTrace_2530269
  have hstable : (prefixWord ++ tailWord_2530269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530269).length < 2 ^ (prefixWord ++ tailWord_2530269).sum := by decide
  have hdescent : baseEnd_2530269 < baseStart_2530269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530289 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 1, 2, 3]
def baseStart_2530289 : Nat := 118140960795 + 2530289 * 2 ^ 59
def prefixEnd_2530289 : Nat := 4983230072969 + 3 ^ 40 * 2530289 * 2
def baseEnd_2530289 : Nat := 1299254451784355966350919

theorem tailTrace_2530289 : CollatzResearch.WordTrace tailWord_2530289 prefixEnd_2530289 1299254451784355966350919 := by
  unfold tailWord_2530289
  simp only [CollatzResearch.WordTrace]
  refine ⟨92287221530202566801969921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61524814353468377867979947 92287221530202566801969921)
  ·
    refine ⟨69215416147651925101477441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92287221530202566801969921 69215416147651925101477441)
    ·
      refine ⟨51911562110738943826108081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69215416147651925101477441 51911562110738943826108081)
      ·
        refine ⟨38933671583054207869581061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51911562110738943826108081 38933671583054207869581061)
        ·
          refine ⟨7300063421822663975546449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38933671583054207869581061 7300063421822663975546449)
          ·
            refine ⟨5475047566366997981659837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7300063421822663975546449 5475047566366997981659837)
            ·
              refine ⟨2053142837387624243122439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5475047566366997981659837 2053142837387624243122439)
              ·
                refine ⟨3079714256081436364683659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053142837387624243122439 3079714256081436364683659)
                ·
                  refine ⟨4619571384122154547025489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079714256081436364683659 4619571384122154547025489)
                  ·
                    refine ⟨3464678538091615910269117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4619571384122154547025489 3464678538091615910269117)
                    ·
                      refine ⟨1299254451784355966350919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3464678538091615910269117 1299254451784355966350919)
                      ·
                        rfl

theorem cell23_2530289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_2530289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530289 prefixEnd_2530289 := by exact prefixLift 2530289
  have htrace : WordTrace (prefixWord ++ tailWord_2530289) baseStart_2530289 baseEnd_2530289 := by
    simpa [prefixWord, tailWord_2530289, baseEnd_2530289] using wordTrace_append hprefix tailTrace_2530289
  have hstable : (prefixWord ++ tailWord_2530289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530289).length < 2 ^ (prefixWord ++ tailWord_2530289).sum := by decide
  have hdescent : baseEnd_2530289 < baseStart_2530289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530298 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_2530298 : Nat := 118140960795 + 2530298 * 2 ^ 59
def prefixEnd_2530298 : Nat := 4983230072969 + 3 ^ 40 * 2530298 * 2
def baseEnd_2530298 : Nat := 1299259073110246431138377

theorem tailTrace_2530298 : CollatzResearch.WordTrace tailWord_2530298 prefixEnd_2530298 1299259073110246431138377 := by
  unfold tailWord_2530298
  simp only [CollatzResearch.WordTrace]
  refine ⟨23071887446792490334761887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61525033191446640892698365 23071887446792490334761887)
  ·
    refine ⟨34607831170188735502142831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23071887446792490334761887 34607831170188735502142831)
    ·
      refine ⟨51911746755283103253214247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34607831170188735502142831 51911746755283103253214247)
      ·
        refine ⟨77867620132924654879821371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51911746755283103253214247 77867620132924654879821371)
        ·
          refine ⟨116801430199386982319732057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77867620132924654879821371 116801430199386982319732057)
          ·
            refine ⟨87601072649540236739799043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116801430199386982319732057 87601072649540236739799043)
            ·
              refine ⟨131401608974310355109698565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87601072649540236739799043 131401608974310355109698565)
              ·
                refine ⟨24637801682683191583068481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131401608974310355109698565 24637801682683191583068481)
                ·
                  refine ⟨18478351262012393687301361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24637801682683191583068481 18478351262012393687301361)
                  ·
                    refine ⟨13858763446509295265476021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18478351262012393687301361 13858763446509295265476021)
                    ·
                      refine ⟨1299259073110246431138377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13858763446509295265476021 1299259073110246431138377)
                      ·
                        rfl

theorem cell23_2530298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_2530298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530298 prefixEnd_2530298 := by exact prefixLift 2530298
  have htrace : WordTrace (prefixWord ++ tailWord_2530298) baseStart_2530298 baseEnd_2530298 := by
    simpa [prefixWord, tailWord_2530298, baseEnd_2530298] using wordTrace_append hprefix tailTrace_2530298
  have hstable : (prefixWord ++ tailWord_2530298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530298).length < 2 ^ (prefixWord ++ tailWord_2530298).sum := by decide
  have hdescent : baseEnd_2530298 < baseStart_2530298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530312 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_2530312 : Nat := 118140960795 + 2530312 * 2 ^ 59
def prefixEnd_2530312 : Nat := 4983230072969 + 3 ^ 40 * 2530312 * 2
def baseEnd_2530312 : Nat := 1299266261839409376363313

theorem tailTrace_2530312 : CollatzResearch.WordTrace tailWord_2530312 prefixEnd_2530312 1299266261839409376363313 := by
  unfold tailWord_2530312
  simp only [CollatzResearch.WordTrace]
  refine ⟨46144030204559620865028595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61525373606079494486704793 46144030204559620865028595)
  ·
    refine ⟨69216045306839431297542893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46144030204559620865028595 69216045306839431297542893)
    ·
      refine ⟨25956016990064786736578585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69216045306839431297542893 25956016990064786736578585)
      ·
        refine ⟨19467012742548590052433939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25956016990064786736578585 19467012742548590052433939)
        ·
          refine ⟨29200519113822885078650909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19467012742548590052433939 29200519113822885078650909)
          ·
            refine ⟨10950194667683581904494091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29200519113822885078650909 10950194667683581904494091)
            ·
              refine ⟨16425292001525372856741137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10950194667683581904494091 16425292001525372856741137)
              ·
                refine ⟨12318969001144029642555853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16425292001525372856741137 12318969001144029642555853)
                ·
                  refine ⟨4619613375429011115958445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12318969001144029642555853 4619613375429011115958445)
                  ·
                    refine ⟨1732355015785879168484417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4619613375429011115958445 1732355015785879168484417)
                    ·
                      refine ⟨1299266261839409376363313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732355015785879168484417 1299266261839409376363313)
                      ·
                        rfl

theorem cell23_2530312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_2530312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530312 prefixEnd_2530312 := by exact prefixLift 2530312
  have htrace : WordTrace (prefixWord ++ tailWord_2530312) baseStart_2530312 baseEnd_2530312 := by
    simpa [prefixWord, tailWord_2530312, baseEnd_2530312] using wordTrace_append hprefix tailTrace_2530312
  have hstable : (prefixWord ++ tailWord_2530312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530312).length < 2 ^ (prefixWord ++ tailWord_2530312).sum := by decide
  have hdescent : baseEnd_2530312 < baseStart_2530312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530346 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_2530346 : Nat := 118140960795 + 2530346 * 2 ^ 59
def prefixEnd_2530346 : Nat := 4983230072969 + 3 ^ 40 * 2530346 * 2
def baseEnd_2530346 : Nat := 1299283720181662243338157

theorem tailTrace_2530346 : CollatzResearch.WordTrace tailWord_2530346 prefixEnd_2530346 1299283720181662243338157 := by
  unfold tailWord_2530346
  simp only [CollatzResearch.WordTrace]
  refine ⟨23072325122749016384198723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61526200327330710357863261 23072325122749016384198723)
  ·
    refine ⟨34608487684123524576298085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23072325122749016384198723 34608487684123524576298085)
    ·
      refine ⟨6489091440773160858055891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34608487684123524576298085 6489091440773160858055891)
      ·
        refine ⟨9733637161159741287083837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6489091440773160858055891 9733637161159741287083837)
        ·
          refine ⟨3650113935434902982656439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9733637161159741287083837 3650113935434902982656439)
          ·
            refine ⟨5475170903152354473984659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650113935434902982656439 5475170903152354473984659)
            ·
              refine ⟨8212756354728531710976989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5475170903152354473984659 8212756354728531710976989)
              ·
                refine ⟨3079783633023199391616371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8212756354728531710976989 3079783633023199391616371)
                ·
                  refine ⟨4619675449534799087424557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079783633023199391616371 4619675449534799087424557)
                  ·
                    refine ⟨1732378293575549657784209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4619675449534799087424557 1732378293575549657784209)
                    ·
                      refine ⟨1299283720181662243338157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732378293575549657784209 1299283720181662243338157)
                      ·
                        rfl

theorem cell23_2530346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_2530346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530346 prefixEnd_2530346 := by exact prefixLift 2530346
  have htrace : WordTrace (prefixWord ++ tailWord_2530346) baseStart_2530346 baseEnd_2530346 := by
    simpa [prefixWord, tailWord_2530346, baseEnd_2530346] using wordTrace_append hprefix tailTrace_2530346
  have hstable : (prefixWord ++ tailWord_2530346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530346).length < 2 ^ (prefixWord ++ tailWord_2530346).sum := by decide
  have hdescent : baseEnd_2530346 < baseStart_2530346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530348 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 9]
def baseStart_2530348 : Nat := 118140960795 + 2530348 * 2 ^ 59
def prefixEnd_2530348 : Nat := 4983230072969 + 3 ^ 40 * 2530348 * 2
def baseEnd_2530348 : Nat := 144364971904774581723683

theorem tailTrace_2530348 : CollatzResearch.WordTrace tailWord_2530348 prefixEnd_2530348 144364971904774581723683 := by
  unfold tailWord_2530348
  simp only [CollatzResearch.WordTrace]
  refine ⟨46144686718494409939183849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61526248957992546585578465 46144686718494409939183849)
  ·
    refine ⟨34608515038870807454387887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46144686718494409939183849 34608515038870807454387887)
    ·
      refine ⟨51912772558306211181581831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34608515038870807454387887 51912772558306211181581831)
      ·
        refine ⟨77869158837459316772372747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51912772558306211181581831 77869158837459316772372747)
        ·
          refine ⟨116803738256188975158559121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77869158837459316772372747 116803738256188975158559121)
          ·
            refine ⟨87602803692141731368919341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116803738256188975158559121 87602803692141731368919341)
            ·
              refine ⟨32851051384553149263344753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87602803692141731368919341 32851051384553149263344753)
              ·
                refine ⟨24638288538414861947508565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32851051384553149263344753 24638288538414861947508565)
                ·
                  refine ⟨144364971904774581723683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24638288538414861947508565 144364971904774581723683)
                  ·
                    rfl

theorem cell23_2530348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_2530348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530348 prefixEnd_2530348 := by exact prefixLift 2530348
  have htrace : WordTrace (prefixWord ++ tailWord_2530348) baseStart_2530348 baseEnd_2530348 := by
    simpa [prefixWord, tailWord_2530348, baseEnd_2530348] using wordTrace_append hprefix tailTrace_2530348
  have hstable : (prefixWord ++ tailWord_2530348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530348).length < 2 ^ (prefixWord ++ tailWord_2530348).sum := by decide
  have hdescent : baseEnd_2530348 < baseStart_2530348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530365 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 7]
def baseStart_2530365 : Nat := 118140960795 + 2530365 * 2 ^ 59
def prefixEnd_2530365 : Nat := 4983230072969 + 3 ^ 40 * 2530365 * 2
def baseEnd_2530365 : Nat := 144365941812677518777841

theorem tailTrace_2530365 : CollatzResearch.WordTrace tailWord_2530365 prefixEnd_2530365 144365941812677518777841 := by
  unfold tailWord_2530365
  simp only [CollatzResearch.WordTrace]
  refine ⟨92289993477927231781736549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61526662318618154521157699 92289993477927231781736549)
  ·
    refine ⟨17304373777111355959075603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92289993477927231781736549 17304373777111355959075603)
    ·
      refine ⟨25956560665667033938613405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17304373777111355959075603 25956560665667033938613405)
      ·
        refine ⟨9733710249625137726980027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25956560665667033938613405 9733710249625137726980027)
        ·
          refine ⟨14600565374437706590470041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9733710249625137726980027 14600565374437706590470041)
          ·
            refine ⟨10950424030828279942852531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14600565374437706590470041 10950424030828279942852531)
            ·
              refine ⟨16425636046242419914278797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10950424030828279942852531 16425636046242419914278797)
              ·
                refine ⟨6159613517340907467854549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16425636046242419914278797 6159613517340907467854549)
                ·
                  refine ⟨144365941812677518777841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6159613517340907467854549 144365941812677518777841)
                  ·
                    rfl

theorem cell23_2530365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_2530365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530365 prefixEnd_2530365 := by exact prefixLift 2530365
  have htrace : WordTrace (prefixWord ++ tailWord_2530365) baseStart_2530365 baseEnd_2530365 := by
    simpa [prefixWord, tailWord_2530365, baseEnd_2530365] using wordTrace_append hprefix tailTrace_2530365
  have hstable : (prefixWord ++ tailWord_2530365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530365).length < 2 ^ (prefixWord ++ tailWord_2530365).sum := by decide
  have hdescent : baseEnd_2530365 < baseStart_2530365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530376 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_2530376 : Nat := 118140960795 + 2530376 * 2 ^ 59
def prefixEnd_2530376 : Nat := 4983230072969 + 3 ^ 40 * 2530376 * 2
def baseEnd_2530376 : Nat := 1299299124601297125963019

theorem tailTrace_2530376 : CollatzResearch.WordTrace tailWord_2530376 prefixEnd_2530376 1299299124601297125963019 := by
  unfold tailWord_2530376
  simp only [CollatzResearch.WordTrace]
  refine ⟨46145197340443690330193491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61526929787258253773591321 46145197340443690330193491)
  ·
    refine ⟨69217796010665535495290237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46145197340443690330193491 69217796010665535495290237)
    ·
      refine ⟨25956673503999575810733839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69217796010665535495290237 25956673503999575810733839)
      ·
        refine ⟨38935010255999363716100759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25956673503999575810733839 38935010255999363716100759)
        ·
          refine ⟨58402515383999045574151139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38935010255999363716100759 58402515383999045574151139)
          ·
            refine ⟨87603773075998568361226709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58402515383999045574151139 87603773075998568361226709)
            ·
              refine ⟨2053213431468716445966251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87603773075998568361226709 2053213431468716445966251)
              ·
                refine ⟨3079820147203074668949377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053213431468716445966251 3079820147203074668949377)
                ·
                  refine ⟨2309865110402306001712033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3079820147203074668949377 2309865110402306001712033)
                  ·
                    refine ⟨1732398832801729501284025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2309865110402306001712033 1732398832801729501284025)
                    ·
                      refine ⟨1299299124601297125963019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732398832801729501284025 1299299124601297125963019)
                      ·
                        rfl

theorem cell23_2530376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_2530376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530376 prefixEnd_2530376 := by exact prefixLift 2530376
  have htrace : WordTrace (prefixWord ++ tailWord_2530376) baseStart_2530376 baseEnd_2530376 := by
    simpa [prefixWord, tailWord_2530376, baseEnd_2530376] using wordTrace_append hprefix tailTrace_2530376
  have hstable : (prefixWord ++ tailWord_2530376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530376).length < 2 ^ (prefixWord ++ tailWord_2530376).sum := by decide
  have hdescent : baseEnd_2530376 < baseStart_2530376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530405 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2530405 : Nat := 118140960795 + 2530405 * 2 ^ 59
def prefixEnd_2530405 : Nat := 4983230072969 + 3 ^ 40 * 2530405 * 2
def baseEnd_2530405 : Nat := 1299314015540277512500385

theorem tailTrace_2530405 : CollatzResearch.WordTrace tailWord_2530405 prefixEnd_2530405 1299314015540277512500385 := by
  unfold tailWord_2530405
  simp only [CollatzResearch.WordTrace]
  refine ⟨92291452397782318613192669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61527634931854879075461779 92291452397782318613192669)
  ·
    refine ⟨34609294649168369479947251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92291452397782318613192669 34609294649168369479947251)
    ·
      refine ⟨51913941973752554219920877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34609294649168369479947251 51913941973752554219920877)
      ·
        refine ⟨19467728240157207832470329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51913941973752554219920877 19467728240157207832470329)
        ·
          refine ⟨14600796180117905874352747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19467728240157207832470329 14600796180117905874352747)
          ·
            refine ⟨21901194270176858811529121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14600796180117905874352747 21901194270176858811529121)
            ·
              refine ⟨16425895702632644108646841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21901194270176858811529121 16425895702632644108646841)
              ·
                refine ⟨12319421776974483081485131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16425895702632644108646841 12319421776974483081485131)
                ·
                  refine ⟨18479132665461724622227697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12319421776974483081485131 18479132665461724622227697)
                  ·
                    refine ⟨13859349499096293466670773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18479132665461724622227697 13859349499096293466670773)
                    ·
                      refine ⟨1299314015540277512500385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13859349499096293466670773 1299314015540277512500385)
                      ·
                        rfl

theorem cell23_2530405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2530405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530405 prefixEnd_2530405 := by exact prefixLift 2530405
  have htrace : WordTrace (prefixWord ++ tailWord_2530405) baseStart_2530405 baseEnd_2530405 := by
    simpa [prefixWord, tailWord_2530405, baseEnd_2530405] using wordTrace_append hprefix tailTrace_2530405
  have hstable : (prefixWord ++ tailWord_2530405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530405).length < 2 ^ (prefixWord ++ tailWord_2530405).sum := by decide
  have hdescent : baseEnd_2530405 < baseStart_2530405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530422 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2530422 : Nat := 118140960795 + 2530422 * 2 ^ 59
def prefixEnd_2530422 : Nat := 4983230072969 + 3 ^ 40 * 2530422 * 2
def baseEnd_2530422 : Nat := 1299322744711403945987807

theorem tailTrace_2530422 : CollatzResearch.WordTrace tailWord_2530422 prefixEnd_2530422 1299322744711403945987807 := by
  unfold tailWord_2530422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5768254527420045657285095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61528048292480487011041013 5768254527420045657285095)
  ·
    refine ⟨8652381791130068485927643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5768254527420045657285095 8652381791130068485927643)
    ·
      refine ⟨12978572686695102728891465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8652381791130068485927643 12978572686695102728891465)
      ·
        refine ⟨9733929515021327046668599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12978572686695102728891465 9733929515021327046668599)
        ·
          refine ⟨14600894272531990570002899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9733929515021327046668599 14600894272531990570002899)
          ·
            refine ⟨21901341408797985855004349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14600894272531990570002899 21901341408797985855004349)
            ·
              refine ⟨8213003028299244695626631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21901341408797985855004349 8213003028299244695626631)
              ·
                refine ⟨12319504542448867043439947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8213003028299244695626631 12319504542448867043439947)
                ·
                  refine ⟨18479256813673300565159921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12319504542448867043439947 18479256813673300565159921)
                  ·
                    refine ⟨13859442610254975423869941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18479256813673300565159921 13859442610254975423869941)
                    ·
                      refine ⟨1299322744711403945987807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13859442610254975423869941 1299322744711403945987807)
                      ·
                        rfl

theorem cell23_2530422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2530422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530422 prefixEnd_2530422 := by exact prefixLift 2530422
  have htrace : WordTrace (prefixWord ++ tailWord_2530422) baseStart_2530422 baseEnd_2530422 := by
    simpa [prefixWord, tailWord_2530422, baseEnd_2530422] using wordTrace_append hprefix tailTrace_2530422
  have hstable : (prefixWord ++ tailWord_2530422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530422).length < 2 ^ (prefixWord ++ tailWord_2530422).sum := by decide
  have hdescent : baseEnd_2530422 < baseStart_2530422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530432 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 2, 4, 2]
def baseStart_2530432 : Nat := 118140960795 + 2530432 * 2 ^ 59
def prefixEnd_2530432 : Nat := 4983230072969 + 3 ^ 40 * 2530432 * 2
def baseEnd_2530432 : Nat := 1299327879517948906862761

theorem tailTrace_2530432 : CollatzResearch.WordTrace tailWord_2530432 prefixEnd_2530432 1299327879517948906862761 := by
  unfold tailWord_2530432
  simp only [CollatzResearch.WordTrace]
  refine ⟨46146218584342251112212775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61528291445789668149617033 46146218584342251112212775)
  ·
    refine ⟨69219327876513376668319163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46146218584342251112212775 69219327876513376668319163)
    ·
      refine ⟨103828991814770065002478745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69219327876513376668319163 103828991814770065002478745)
      ·
        refine ⟨77871743861077548751859059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103828991814770065002478745 77871743861077548751859059)
        ·
          refine ⟨116807615791616323127788589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77871743861077548751859059 116807615791616323127788589)
          ·
            refine ⟨43802855921856121172920721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116807615791616323127788589 43802855921856121172920721)
            ·
              refine ⟨32852141941392090879690541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43802855921856121172920721 32852141941392090879690541)
              ·
                refine ⟨12319553228022034079883953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32852141941392090879690541 12319553228022034079883953)
                ·
                  refine ⟨9239664921016525559912965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12319553228022034079883953 9239664921016525559912965)
                  ·
                    refine ⟨1732437172690598542483681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9239664921016525559912965 1732437172690598542483681)
                    ·
                      refine ⟨1299327879517948906862761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732437172690598542483681 1299327879517948906862761)
                      ·
                        rfl

theorem cell23_2530432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_2530432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530432 prefixEnd_2530432 := by exact prefixLift 2530432
  have htrace : WordTrace (prefixWord ++ tailWord_2530432) baseStart_2530432 baseEnd_2530432 := by
    simpa [prefixWord, tailWord_2530432, baseEnd_2530432] using wordTrace_append hprefix tailTrace_2530432
  have hstable : (prefixWord ++ tailWord_2530432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530432).length < 2 ^ (prefixWord ++ tailWord_2530432).sum := by decide
  have hdescent : baseEnd_2530432 < baseStart_2530432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530442 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_2530442 : Nat := 118140960795 + 2530442 * 2 ^ 59
def prefixEnd_2530442 : Nat := 4983230072969 + 3 ^ 40 * 2530442 * 2
def baseEnd_2530442 : Nat := 433111004774831289245905

theorem tailTrace_2530442 : CollatzResearch.WordTrace tailWord_2530442 prefixEnd_2530442 433111004774831289245905 := by
  unfold tailWord_2530442
  simp only [CollatzResearch.WordTrace]
  refine ⟨23073200474662068483072395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61528534599098849288193053 23073200474662068483072395)
  ·
    refine ⟨34609800711993102724608593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23073200474662068483072395 34609800711993102724608593)
    ·
      refine ⟨25957350533994827043456445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34609800711993102724608593 25957350533994827043456445)
      ·
        refine ⟨9734006450248060141296167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25957350533994827043456445 9734006450248060141296167)
        ·
          refine ⟨14601009675372090211944251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9734006450248060141296167 14601009675372090211944251)
          ·
            refine ⟨21901514513058135317916377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14601009675372090211944251 21901514513058135317916377)
            ·
              refine ⟨16426135884793601488437283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21901514513058135317916377 16426135884793601488437283)
              ·
                refine ⟨24639203827190402232655925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16426135884793601488437283 24639203827190402232655925)
                ·
                  refine ⟨2309925358799100209311493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24639203827190402232655925 2309925358799100209311493)
                  ·
                    refine ⟨433111004774831289245905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2309925358799100209311493 433111004774831289245905)
                    ·
                      rfl

theorem cell23_2530442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_2530442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530442 prefixEnd_2530442 := by exact prefixLift 2530442
  have htrace : WordTrace (prefixWord ++ tailWord_2530442) baseStart_2530442 baseEnd_2530442 := by
    simpa [prefixWord, tailWord_2530442, baseEnd_2530442] using wordTrace_append hprefix tailTrace_2530442
  have hstable : (prefixWord ++ tailWord_2530442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530442).length < 2 ^ (prefixWord ++ tailWord_2530442).sum := by decide
  have hdescent : baseEnd_2530442 < baseStart_2530442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530519 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 1, 5]
def baseStart_2530519 : Nat := 118140960795 + 2530519 * 2 ^ 59
def prefixEnd_2530519 : Nat := 4983230072969 + 3 ^ 40 * 2530519 * 2
def baseEnd_2530519 : Nat := 433124184111630022158287

theorem tailTrace_2530519 : CollatzResearch.WordTrace tailWord_2530519 prefixEnd_2530519 433124184111630022158287 := by
  unfold tailWord_2530519
  simp only [CollatzResearch.WordTrace]
  refine ⟨92295610319369316082842611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61530406879579544055228407 92295610319369316082842611)
  ·
    refine ⟨138443415479053974124263917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92295610319369316082842611 138443415479053974124263917)
    ·
      refine ⟨51916280804645240296598969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138443415479053974124263917 51916280804645240296598969)
      ·
        refine ⟨38937210603483930222449227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51916280804645240296598969 38937210603483930222449227)
        ·
          refine ⟨58405815905225895333673841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38937210603483930222449227 58405815905225895333673841)
          ·
            refine ⟨43804361928919421500255381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58405815905225895333673841 43804361928919421500255381)
            ·
              refine ⟨2053329465418097882824471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43804361928919421500255381 2053329465418097882824471)
              ·
                refine ⟨3079994198127146824236707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053329465418097882824471 3079994198127146824236707)
                ·
                  refine ⟨4619991297190720236355061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079994198127146824236707 4619991297190720236355061)
                  ·
                    refine ⟨433124184111630022158287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4619991297190720236355061 433124184111630022158287)
                    ·
                      rfl

theorem cell23_2530519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_2530519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530519 prefixEnd_2530519 := by exact prefixLift 2530519
  have htrace : WordTrace (prefixWord ++ tailWord_2530519) baseStart_2530519 baseEnd_2530519 := by
    simpa [prefixWord, tailWord_2530519, baseEnd_2530519] using wordTrace_append hprefix tailTrace_2530519
  have hstable : (prefixWord ++ tailWord_2530519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530519).length < 2 ^ (prefixWord ++ tailWord_2530519).sum := by decide
  have hdescent : baseEnd_2530519 < baseStart_2530519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530542 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2530542 : Nat := 118140960795 + 2530542 * 2 ^ 59
def prefixEnd_2530542 : Nat := 4983230072969 + 3 ^ 40 * 2530542 * 2
def baseEnd_2530542 : Nat := 1299384362389943476487255

theorem tailTrace_2530542 : CollatzResearch.WordTrace tailWord_2530542 prefixEnd_2530542 1299384362389943476487255 := by
  unfold tailWord_2530542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537056149785748876366235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61530966132190660673953253 11537056149785748876366235)
  ·
    refine ⟨17305584224678623314549353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11537056149785748876366235 17305584224678623314549353)
    ·
      refine ⟨12979188168508967485912015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17305584224678623314549353 12979188168508967485912015)
      ·
        refine ⟨19468782252763451228868023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979188168508967485912015 19468782252763451228868023)
        ·
          refine ⟨29203173379145176843302035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19468782252763451228868023 29203173379145176843302035)
          ·
            refine ⟨43804760068717765264953053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29203173379145176843302035 43804760068717765264953053)
            ·
              refine ⟨16426785025769161974357395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43804760068717765264953053 16426785025769161974357395)
              ·
                refine ⟨24640177538653742961536093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16426785025769161974357395 24640177538653742961536093)
                ·
                  refine ⟨9240066576995153610576035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24640177538653742961536093 9240066576995153610576035)
                  ·
                    refine ⟨13860099865492730415864053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9240066576995153610576035 13860099865492730415864053)
                    ·
                      refine ⟨1299384362389943476487255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13860099865492730415864053 1299384362389943476487255)
                      ·
                        rfl

theorem cell23_2530542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2530542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530542 prefixEnd_2530542 := by exact prefixLift 2530542
  have htrace : WordTrace (prefixWord ++ tailWord_2530542) baseStart_2530542 baseEnd_2530542 := by
    simpa [prefixWord, tailWord_2530542, baseEnd_2530542] using wordTrace_append hprefix tailTrace_2530542
  have hstable : (prefixWord ++ tailWord_2530542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530542).length < 2 ^ (prefixWord ++ tailWord_2530542).sum := by decide
  have hdescent : baseEnd_2530542 < baseStart_2530542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530545 : List Nat := [1, 2, 2, 2, 2, 1, 1, 12]
def baseStart_2530545 : Nat := 118140960795 + 2530545 * 2 ^ 59
def prefixEnd_2530545 : Nat := 4983230072969 + 3 ^ 40 * 2530545 * 2
def baseEnd_2530545 : Nat := 48125403808589146842583

theorem tailTrace_2530545 : CollatzResearch.WordTrace tailWord_2530545 prefixEnd_2530545 48125403808589146842583 := by
  unfold tailWord_2530545
  simp only [CollatzResearch.WordTrace]
  refine ⟨92296558617275122523289089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61531039078183415015526059 92296558617275122523289089)
  ·
    refine ⟨69222418962956341892466817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92296558617275122523289089 69222418962956341892466817)
    ·
      refine ⟨51916814222217256419350113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69222418962956341892466817 51916814222217256419350113)
      ·
        refine ⟨38937610666662942314512585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51916814222217256419350113 38937610666662942314512585)
        ·
          refine ⟨29203207999997206735884439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38937610666662942314512585 29203207999997206735884439)
          ·
            refine ⟨43804811999995810103826659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29203207999997206735884439 43804811999995810103826659)
            ·
              refine ⟨65707217999993715155739989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43804811999995810103826659 65707217999993715155739989)
              ·
                refine ⟨48125403808589146842583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 65707217999993715155739989 48125403808589146842583)
                ·
                  rfl

theorem cell23_2530545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 12].length) (baseStart_2530545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530545 prefixEnd_2530545 := by exact prefixLift 2530545
  have htrace : WordTrace (prefixWord ++ tailWord_2530545) baseStart_2530545 baseEnd_2530545 := by
    simpa [prefixWord, tailWord_2530545, baseEnd_2530545] using wordTrace_append hprefix tailTrace_2530545
  have hstable : (prefixWord ++ tailWord_2530545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530545).length < 2 ^ (prefixWord ++ tailWord_2530545).sum := by decide
  have hdescent : baseEnd_2530545 < baseStart_2530545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530556 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_2530556 : Nat := 118140960795 + 2530556 * 2 ^ 59
def prefixEnd_2530556 : Nat := 4983230072969 + 3 ^ 40 * 2530556 * 2
def baseEnd_2530556 : Nat := 1299391551119106421712191

theorem tailTrace_2530556 : CollatzResearch.WordTrace tailWord_2530556 prefixEnd_2530556 1299391551119106421712191 := by
  unfold tailWord_2530556
  simp only [CollatzResearch.WordTrace]
  refine ⟨46148479910117635700969761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61531306546823514267959681 46148479910117635700969761)
  ·
    refine ⟨34611359932588226775727321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46148479910117635700969761 34611359932588226775727321)
    ·
      refine ⟨25958519949441170081795491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34611359932588226775727321 25958519949441170081795491)
      ·
        refine ⟨38937779924161755122693237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25958519949441170081795491 38937779924161755122693237)
        ·
          refine ⟨3650416867890164542752491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38937779924161755122693237 3650416867890164542752491)
          ·
            refine ⟨5475625301835246814128737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650416867890164542752491 5475625301835246814128737)
            ·
              refine ⟨4106718976376435110596553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5475625301835246814128737 4106718976376435110596553)
              ·
                refine ⟨3080039232282326332947415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106718976376435110596553 3080039232282326332947415)
                ·
                  refine ⟨4620058848423489499421123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080039232282326332947415 4620058848423489499421123)
                  ·
                    refine ⟨6930088272635234249131685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4620058848423489499421123 6930088272635234249131685)
                    ·
                      refine ⟨1299391551119106421712191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6930088272635234249131685 1299391551119106421712191)
                      ·
                        rfl

theorem cell23_2530556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_2530556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530556 prefixEnd_2530556 := by exact prefixLift 2530556
  have htrace : WordTrace (prefixWord ++ tailWord_2530556) baseStart_2530556 baseEnd_2530556 := by
    simpa [prefixWord, tailWord_2530556, baseEnd_2530556] using wordTrace_append hprefix tailTrace_2530556
  have hstable : (prefixWord ++ tailWord_2530556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530556).length < 2 ^ (prefixWord ++ tailWord_2530556).sum := by decide
  have hdescent : baseEnd_2530556 < baseStart_2530556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530559 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 3]
def baseStart_2530559 : Nat := 118140960795 + 2530559 * 2 ^ 59
def prefixEnd_2530559 : Nat := 4983230072969 + 3 ^ 40 * 2530559 * 2
def baseEnd_2530559 : Nat := 1299393091561069909974677

theorem tailTrace_2530559 : CollatzResearch.WordTrace tailWord_2530559 prefixEnd_2530559 1299393091561069909974677 := by
  unfold tailWord_2530559
  simp only [CollatzResearch.WordTrace]
  refine ⟨92297069239224402914298731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61531379492816268609532487 92297069239224402914298731)
  ·
    refine ⟨138445603858836604371448097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92297069239224402914298731 138445603858836604371448097)
    ·
      refine ⟨103834202894127453278586073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138445603858836604371448097 103834202894127453278586073)
      ·
        refine ⟨77875652170595589958939555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103834202894127453278586073 77875652170595589958939555)
        ·
          refine ⟨116813478255893384938409333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77875652170595589958939555 116813478255893384938409333)
          ·
            refine ⟨10951263586490004837975875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116813478255893384938409333 10951263586490004837975875)
            ·
              refine ⟨16426895379735007256963813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10951263586490004837975875 16426895379735007256963813)
              ·
                refine ⟨3080042883700313860680715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16426895379735007256963813 3080042883700313860680715)
                ·
                  refine ⟨4620064325550470791021073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080042883700313860680715 4620064325550470791021073)
                  ·
                    refine ⟨3465048244162853093265805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4620064325550470791021073 3465048244162853093265805)
                    ·
                      refine ⟨1299393091561069909974677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3465048244162853093265805 1299393091561069909974677)
                      ·
                        rfl

theorem cell23_2530559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_2530559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530559 prefixEnd_2530559 := by exact prefixLift 2530559
  have htrace : WordTrace (prefixWord ++ tailWord_2530559) baseStart_2530559 baseEnd_2530559 := by
    simpa [prefixWord, tailWord_2530559, baseEnd_2530559] using wordTrace_append hprefix tailTrace_2530559
  have hstable : (prefixWord ++ tailWord_2530559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530559).length < 2 ^ (prefixWord ++ tailWord_2530559).sum := by decide
  have hdescent : baseEnd_2530559 < baseStart_2530559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530575 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 3, 9]
def baseStart_2530575 : Nat := 118140960795 + 2530575 * 2 ^ 59
def prefixEnd_2530575 : Nat := 4983230072969 + 3 ^ 40 * 2530575 * 2
def baseEnd_2530575 : Nat := 433133769083847282458201

theorem tailTrace_2530575 : CollatzResearch.WordTrace tailWord_2530575 prefixEnd_2530575 433133769083847282458201 := by
  unfold tailWord_2530575
  simp only [CollatzResearch.WordTrace]
  refine ⟨92297652807166437646881179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61531768538110958431254119 92297652807166437646881179)
  ·
    refine ⟨138446479210749656470321769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92297652807166437646881179 138446479210749656470321769)
    ·
      refine ⟨103834859408062242352741327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138446479210749656470321769 103834859408062242352741327)
      ·
        refine ⟨155752289112093363529111991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103834859408062242352741327 155752289112093363529111991)
        ·
          refine ⟨233628433668140045293667987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155752289112093363529111991 233628433668140045293667987)
          ·
            refine ⟨350442650502210067940501981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233628433668140045293667987 350442650502210067940501981)
            ·
              refine ⟨131415993938328775477688243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350442650502210067940501981 131415993938328775477688243)
              ·
                refine ⟨197123990907493163216532365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131415993938328775477688243 197123990907493163216532365)
                ·
                  refine ⟨73921496590309936206199637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197123990907493163216532365 73921496590309936206199637)
                  ·
                    refine ⟨433133769083847282458201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73921496590309936206199637 433133769083847282458201)
                    ·
                      rfl

theorem cell23_2530575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_2530575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530575 prefixEnd_2530575 := by exact prefixLift 2530575
  have htrace : WordTrace (prefixWord ++ tailWord_2530575) baseStart_2530575 baseEnd_2530575 := by
    simpa [prefixWord, tailWord_2530575, baseEnd_2530575] using wordTrace_append hprefix tailTrace_2530575
  have hstable : (prefixWord ++ tailWord_2530575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530575).length < 2 ^ (prefixWord ++ tailWord_2530575).sum := by decide
  have hdescent : baseEnd_2530575 < baseStart_2530575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530642 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2530642 : Nat := 118140960795 + 2530642 * 2 ^ 59
def prefixEnd_2530642 : Nat := 4983230072969 + 3 ^ 40 * 2530642 * 2
def baseEnd_2530642 : Nat := 1299435710455393085236795

theorem tailTrace_2530642 : CollatzResearch.WordTrace tailWord_2530642 prefixEnd_2530642 1299435710455393085236795 := by
  unfold tailWord_2530642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23075024124480927022392545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61533397665282472059713453 23075024124480927022392545)
  ·
    refine ⟨17306268093360695266794409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23075024124480927022392545 17306268093360695266794409)
    ·
      refine ⟨12979701070020521450095807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17306268093360695266794409 12979701070020521450095807)
      ·
        refine ⟨19469551605030782175143711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979701070020521450095807 19469551605030782175143711)
        ·
          refine ⟨29204327407546173262715567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19469551605030782175143711 29204327407546173262715567)
          ·
            refine ⟨43806491111319259894073351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29204327407546173262715567 43806491111319259894073351)
            ·
              refine ⟨65709736666978889841110027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43806491111319259894073351 65709736666978889841110027)
              ·
                refine ⟨98564605000468334761665041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65709736666978889841110027 98564605000468334761665041)
                ·
                  refine ⟨73923453750351251071248781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98564605000468334761665041 73923453750351251071248781)
                  ·
                    refine ⟨27721295156381719151718293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73923453750351251071248781 27721295156381719151718293)
                    ·
                      refine ⟨1299435710455393085236795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27721295156381719151718293 1299435710455393085236795)
                      ·
                        rfl

theorem cell23_2530642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2530642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530642 prefixEnd_2530642 := by exact prefixLift 2530642
  have htrace : WordTrace (prefixWord ++ tailWord_2530642) baseStart_2530642 baseEnd_2530642 := by
    simpa [prefixWord, tailWord_2530642, baseEnd_2530642] using wordTrace_append hprefix tailTrace_2530642
  have hstable : (prefixWord ++ tailWord_2530642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530642).length < 2 ^ (prefixWord ++ tailWord_2530642).sum := by decide
  have hdescent : baseEnd_2530642 < baseStart_2530642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530659 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 4]
def baseStart_2530659 : Nat := 118140960795 + 2530659 * 2 ^ 59
def prefixEnd_2530659 : Nat := 4983230072969 + 3 ^ 40 * 2530659 * 2
def baseEnd_2530659 : Nat := 1299444439626519518724217

theorem tailTrace_2530659 : CollatzResearch.WordTrace tailWord_2530659 prefixEnd_2530659 1299444439626519518724217 := by
  unfold tailWord_2530659
  simp only [CollatzResearch.WordTrace]
  refine ⟨92300716538862119992939031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61533811025908079995292687 92300716538862119992939031)
  ·
    refine ⟨138451074808293179989408547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92300716538862119992939031 138451074808293179989408547)
    ·
      refine ⟨207676612212439769984112821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138451074808293179989408547 207676612212439769984112821)
      ·
        refine ⟨19469682394916228436010577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207676612212439769984112821 19469682394916228436010577)
        ·
          refine ⟨14602261796187171327007933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19469682394916228436010577 14602261796187171327007933)
          ·
            refine ⟨5475848173570189247627975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14602261796187171327007933 5475848173570189247627975)
            ·
              refine ⟨8213772260355283871441963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5475848173570189247627975 8213772260355283871441963)
              ·
                refine ⟨12320658390532925807162945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8213772260355283871441963 12320658390532925807162945)
                ·
                  refine ⟨9240493792899694355372209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12320658390532925807162945 9240493792899694355372209)
                  ·
                    refine ⟨6930370344674770766529157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9240493792899694355372209 6930370344674770766529157)
                    ·
                      refine ⟨1299444439626519518724217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6930370344674770766529157 1299444439626519518724217)
                      ·
                        rfl

theorem cell23_2530659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_2530659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530659 prefixEnd_2530659 := by exact prefixLift 2530659
  have htrace : WordTrace (prefixWord ++ tailWord_2530659) baseStart_2530659 baseEnd_2530659 := by
    simpa [prefixWord, tailWord_2530659, baseEnd_2530659] using wordTrace_append hprefix tailTrace_2530659
  have hstable : (prefixWord ++ tailWord_2530659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530659).length < 2 ^ (prefixWord ++ tailWord_2530659).sum := by decide
  have hdescent : baseEnd_2530659 < baseStart_2530659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530663 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_2530663 : Nat := 118140960795 + 2530663 * 2 ^ 59
def prefixEnd_2530663 : Nat := 4983230072969 + 3 ^ 40 * 2530663 * 2
def baseEnd_2530663 : Nat := 1299446493549137503074199

theorem tailTrace_2530663 : CollatzResearch.WordTrace tailWord_2530663 prefixEnd_2530663 1299446493549137503074199 := by
  unfold tailWord_2530663
  simp only [CollatzResearch.WordTrace]
  refine ⟨92300862430847628676084643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61533908287231752450723095 92300862430847628676084643)
  ·
    refine ⟨138451293646271443014126965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92300862430847628676084643 138451293646271443014126965)
    ·
      refine ⟨12979808779337947782574403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138451293646271443014126965 12979808779337947782574403)
      ·
        refine ⟨19469713169006921673861605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979808779337947782574403 19469713169006921673861605)
        ·
          refine ⟨3650571219188797813849051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19469713169006921673861605 3650571219188797813849051)
          ·
            refine ⟨5475856828783196720773577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650571219188797813849051 5475856828783196720773577)
            ·
              refine ⟨4106892621587397540580183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5475856828783196720773577 4106892621587397540580183)
              ·
                refine ⟨6160338932381096310870275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4106892621587397540580183 6160338932381096310870275)
                ·
                  refine ⟨9240508398571644466305413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6160338932381096310870275 9240508398571644466305413)
                  ·
                    refine ⟨1732595324732183337432265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9240508398571644466305413 1732595324732183337432265)
                    ·
                      refine ⟨1299446493549137503074199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732595324732183337432265 1299446493549137503074199)
                      ·
                        rfl

theorem cell23_2530663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_2530663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530663 prefixEnd_2530663 := by exact prefixLift 2530663
  have htrace : WordTrace (prefixWord ++ tailWord_2530663) baseStart_2530663 baseEnd_2530663 := by
    simpa [prefixWord, tailWord_2530663, baseEnd_2530663] using wordTrace_append hprefix tailTrace_2530663
  have hstable : (prefixWord ++ tailWord_2530663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530663).length < 2 ^ (prefixWord ++ tailWord_2530663).sum := by decide
  have hdescent : baseEnd_2530663 < baseStart_2530663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530669 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 7]
def baseStart_2530669 : Nat := 118140960795 + 2530669 * 2 ^ 59
def prefixEnd_2530669 : Nat := 4983230072969 + 3 ^ 40 * 2530669 * 2
def baseEnd_2530669 : Nat := 144383286048118275511019

theorem tailTrace_2530669 : CollatzResearch.WordTrace tailWord_2530669 prefixEnd_2530669 144383286048118275511019 := by
  unfold tailWord_2530669
  simp only [CollatzResearch.WordTrace]
  refine ⟨92301081268825891700803061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61534054179217261133868707 92301081268825891700803061)
  ·
    refine ⟨8653226368952427346950287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92301081268825891700803061 8653226368952427346950287)
    ·
      refine ⟨12979839553428641020425431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8653226368952427346950287 12979839553428641020425431)
      ·
        refine ⟨19469759330142961530638147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979839553428641020425431 19469759330142961530638147)
        ·
          refine ⟨29204638995214442295957221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19469759330142961530638147 29204638995214442295957221)
          ·
            refine ⟨5475869811602707930491979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29204638995214442295957221 5475869811602707930491979)
            ·
              refine ⟨8213804717404061895737969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5475869811602707930491979 8213804717404061895737969)
              ·
                refine ⟨6160353538053046421803477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8213804717404061895737969 6160353538053046421803477)
                ·
                  refine ⟨144383286048118275511019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6160353538053046421803477 144383286048118275511019)
                  ·
                    rfl

theorem cell23_2530669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_2530669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530669 prefixEnd_2530669 := by exact prefixLift 2530669
  have htrace : WordTrace (prefixWord ++ tailWord_2530669) baseStart_2530669 baseEnd_2530669 := by
    simpa [prefixWord, tailWord_2530669, baseEnd_2530669] using wordTrace_append hprefix tailTrace_2530669
  have hstable : (prefixWord ++ tailWord_2530669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530669).length < 2 ^ (prefixWord ++ tailWord_2530669).sum := by decide
  have hdescent : baseEnd_2530669 < baseStart_2530669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530682 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_2530682 : Nat := 118140960795 + 2530682 * 2 ^ 59
def prefixEnd_2530682 : Nat := 4983230072969 + 3 ^ 40 * 2530682 * 2
def baseEnd_2530682 : Nat := 433152083227190976245537

theorem tailTrace_2530682 : CollatzResearch.WordTrace tailWord_2530682 prefixEnd_2530682 433152083227190976245537 := by
  unfold tailWord_2530682
  simp only [CollatzResearch.WordTrace]
  refine ⟨23075388854444698730256575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61534370278519196614017533 23075388854444698730256575)
  ·
    refine ⟨34613083281667048095384863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23075388854444698730256575 34613083281667048095384863)
    ·
      refine ⟨51919624922500572143077295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34613083281667048095384863 51919624922500572143077295)
      ·
        refine ⟨77879437383750858214615943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51919624922500572143077295 77879437383750858214615943)
        ·
          refine ⟨116819156075626287321923915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77879437383750858214615943 116819156075626287321923915)
          ·
            refine ⟨175228734113439430982885873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116819156075626287321923915 175228734113439430982885873)
            ·
              refine ⟨131421550585079573237164405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175228734113439430982885873 131421550585079573237164405)
              ·
                refine ⟨12320770367351209990984163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131421550585079573237164405 12320770367351209990984163)
                ·
                  refine ⟨18481155551026814986476245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12320770367351209990984163 18481155551026814986476245)
                  ·
                    refine ⟨433152083227190976245537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18481155551026814986476245 433152083227190976245537)
                    ·
                      rfl

theorem cell23_2530682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_2530682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530682 prefixEnd_2530682 := by exact prefixLift 2530682
  have htrace : WordTrace (prefixWord ++ tailWord_2530682) baseStart_2530682 baseEnd_2530682 := by
    simpa [prefixWord, tailWord_2530682, baseEnd_2530682] using wordTrace_append hprefix tailTrace_2530682
  have hstable : (prefixWord ++ tailWord_2530682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530682).length < 2 ^ (prefixWord ++ tailWord_2530682).sum := by decide
  have hdescent : baseEnd_2530682 < baseStart_2530682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530697 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 2, 2, 2]
def baseStart_2530697 : Nat := 118140960795 + 2530697 * 2 ^ 59
def prefixEnd_2530697 : Nat := 4983230072969 + 3 ^ 40 * 2530697 * 2
def baseEnd_2530697 : Nat := 1299463951891390370049043

theorem tailTrace_2530697 : CollatzResearch.WordTrace tailWord_2530697 prefixEnd_2530697 1299463951891390370049043 := by
  unfold tailWord_2530697
  simp only [CollatzResearch.WordTrace]
  refine ⟨92302102512724452482822345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61534735008482968321881563 92302102512724452482822345)
  ·
    refine ⟨69226576884543339362116759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92302102512724452482822345 69226576884543339362116759)
    ·
      refine ⟨103839865326815009043175139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69226576884543339362116759 103839865326815009043175139)
      ·
        refine ⟨155759797990222513564762709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103839865326815009043175139 155759797990222513564762709)
        ·
          refine ⟨1825310132697920080837063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 155759797990222513564762709 1825310132697920080837063)
          ·
            refine ⟨2737965199046880121255595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825310132697920080837063 2737965199046880121255595)
            ·
              refine ⟨4106947798570320181883393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737965199046880121255595 4106947798570320181883393)
              ·
                refine ⟨3080210848927740136412545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106947798570320181883393 3080210848927740136412545)
                ·
                  refine ⟨2310158136695805102309409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3080210848927740136412545 2310158136695805102309409)
                  ·
                    refine ⟨1732618602521853826732057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2310158136695805102309409 1732618602521853826732057)
                    ·
                      refine ⟨1299463951891390370049043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732618602521853826732057 1299463951891390370049043)
                      ·
                        rfl

theorem cell23_2530697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 2, 2].length) (baseStart_2530697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530697 prefixEnd_2530697 := by exact prefixLift 2530697
  have htrace : WordTrace (prefixWord ++ tailWord_2530697) baseStart_2530697 baseEnd_2530697 := by
    simpa [prefixWord, tailWord_2530697, baseEnd_2530697] using wordTrace_append hprefix tailTrace_2530697
  have hstable : (prefixWord ++ tailWord_2530697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530697).length < 2 ^ (prefixWord ++ tailWord_2530697).sum := by decide
  have hdescent : baseEnd_2530697 < baseStart_2530697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530719 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2530719 : Nat := 118140960795 + 2530719 * 2 ^ 59
def prefixEnd_2530719 : Nat := 4983230072969 + 3 ^ 40 * 2530719 * 2
def baseEnd_2530719 : Nat := 1299475248465789283973941

theorem tailTrace_2530719 : CollatzResearch.WordTrace tailWord_2530719 prefixEnd_2530719 1299475248465789283973941 := by
  unfold tailWord_2530719
  simp only [CollatzResearch.WordTrace]
  refine ⟨92302904918644750240123211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61535269945763166826748807 92302904918644750240123211)
  ·
    refine ⟨138454357377967125360184817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92302904918644750240123211 138454357377967125360184817)
    ·
      refine ⟨103840768033475344020138613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138454357377967125360184817 103840768033475344020138613)
      ·
        refine ⟨9735072003138313501887995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103840768033475344020138613 9735072003138313501887995)
        ·
          refine ⟨14602608004707470252831993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9735072003138313501887995 14602608004707470252831993)
          ·
            refine ⟨10951956003530602689623995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14602608004707470252831993 10951956003530602689623995)
            ·
              refine ⟨16427934005295904034435993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10951956003530602689623995 16427934005295904034435993)
              ·
                refine ⟨12320950503971928025826995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16427934005295904034435993 12320950503971928025826995)
                ·
                  refine ⟨18481425755957892038740493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12320950503971928025826995 18481425755957892038740493)
                  ·
                    refine ⟨6930534658484209514527685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18481425755957892038740493 6930534658484209514527685)
                    ·
                      refine ⟨1299475248465789283973941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6930534658484209514527685 1299475248465789283973941)
                      ·
                        rfl

theorem cell23_2530719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2530719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530719 prefixEnd_2530719 := by exact prefixLift 2530719
  have htrace : WordTrace (prefixWord ++ tailWord_2530719) baseStart_2530719 baseEnd_2530719 := by
    simpa [prefixWord, tailWord_2530719, baseEnd_2530719] using wordTrace_append hprefix tailTrace_2530719
  have hstable : (prefixWord ++ tailWord_2530719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530719).length < 2 ^ (prefixWord ++ tailWord_2530719).sum := by decide
  have hdescent : baseEnd_2530719 < baseStart_2530719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530739 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 3]
def baseStart_2530739 : Nat := 118140960795 + 2530739 * 2 ^ 59
def prefixEnd_2530739 : Nat := 4983230072969 + 3 ^ 40 * 2530739 * 2
def baseEnd_2530739 : Nat := 1299485518078879205723849

theorem tailTrace_2530739 : CollatzResearch.WordTrace tailWord_2530739 prefixEnd_2530739 1299485518078879205723849 := by
  unfold tailWord_2530739
  simp only [CollatzResearch.WordTrace]
  refine ⟨92303634378572293655851271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61535756252381529103900847 92303634378572293655851271)
  ·
    refine ⟨138455451567858440483776907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92303634378572293655851271 138455451567858440483776907)
    ·
      refine ⟨207683177351787660725665361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138455451567858440483776907 207683177351787660725665361)
      ·
        refine ⟨155762383013840745544249021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207683177351787660725665361 155762383013840745544249021)
        ·
          refine ⟨58410893630190279579093383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155762383013840745544249021 58410893630190279579093383)
          ·
            refine ⟨87616340445285419368640075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58410893630190279579093383 87616340445285419368640075)
            ·
              refine ⟨131424510667928129052960113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87616340445285419368640075 131424510667928129052960113)
              ·
                refine ⟨98568383000946096789720085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131424510667928129052960113 98568383000946096789720085)
                ·
                  refine ⟨4620392953169348287018129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98568383000946096789720085 4620392953169348287018129)
                  ·
                    refine ⟨3465294714877011215263597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4620392953169348287018129 3465294714877011215263597)
                    ·
                      refine ⟨1299485518078879205723849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3465294714877011215263597 1299485518078879205723849)
                      ·
                        rfl

theorem cell23_2530739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_2530739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530739 prefixEnd_2530739 := by exact prefixLift 2530739
  have htrace : WordTrace (prefixWord ++ tailWord_2530739) baseStart_2530739 baseEnd_2530739 := by
    simpa [prefixWord, tailWord_2530739, baseEnd_2530739] using wordTrace_append hprefix tailTrace_2530739
  have hstable : (prefixWord ++ tailWord_2530739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530739).length < 2 ^ (prefixWord ++ tailWord_2530739).sum := by decide
  have hdescent : baseEnd_2530739 < baseStart_2530739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530754 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2530754 : Nat := 118140960795 + 2530754 * 2 ^ 59
def prefixEnd_2530754 : Nat := 4983230072969 + 3 ^ 40 * 2530754 * 2
def baseEnd_2530754 : Nat := 144388135587632960781809

theorem tailTrace_2530754 : CollatzResearch.WordTrace tailWord_2530754 prefixEnd_2530754 144388135587632960781809 := by
  unfold tailWord_2530754
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076045368379487804411829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61536120982345300811764877 23076045368379487804411829)
  ·
    refine ⟨2163379253285576981663609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23076045368379487804411829 2163379253285576981663609)
    ·
      refine ⟨1622534439964182736247707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2163379253285576981663609 1622534439964182736247707)
      ·
        refine ⟨2433801659946274104371561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622534439964182736247707 2433801659946274104371561)
        ·
          refine ⟨1825351244959705578278671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433801659946274104371561 1825351244959705578278671)
          ·
            refine ⟨2738026867439558367418007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825351244959705578278671 2738026867439558367418007)
            ·
              refine ⟨4107040301159337551127011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738026867439558367418007 4107040301159337551127011)
              ·
                refine ⟨6160560451739006326690517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4107040301159337551127011 6160560451739006326690517)
                ·
                  refine ⟨144388135587632960781809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6160560451739006326690517 144388135587632960781809)
                  ·
                    rfl

theorem cell23_2530754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2530754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530754 prefixEnd_2530754 := by exact prefixLift 2530754
  have htrace : WordTrace (prefixWord ++ tailWord_2530754) baseStart_2530754 baseEnd_2530754 := by
    simpa [prefixWord, tailWord_2530754, baseEnd_2530754] using wordTrace_append hprefix tailTrace_2530754
  have hstable : (prefixWord ++ tailWord_2530754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530754).length < 2 ^ (prefixWord ++ tailWord_2530754).sum := by decide
  have hdescent : baseEnd_2530754 < baseStart_2530754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530759 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 6]
def baseStart_2530759 : Nat := 118140960795 + 2530759 * 2 ^ 59
def prefixEnd_2530759 : Nat := 4983230072969 + 3 ^ 40 * 2530759 * 2
def baseEnd_2530759 : Nat := 144388420854663236385973

theorem tailTrace_2530759 : CollatzResearch.WordTrace tailWord_2530759 prefixEnd_2530759 144388420854663236385973 := by
  unfold tailWord_2530759
  simp only [CollatzResearch.WordTrace]
  refine ⟨92304363838499837071579331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61536242558999891381052887 92304363838499837071579331)
  ·
    refine ⟨138456545757749755607368997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92304363838499837071579331 138456545757749755607368997)
    ·
      refine ⟨25960602329578079176381687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138456545757749755607368997 25960602329578079176381687)
      ·
        refine ⟨38940903494367118764572531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25960602329578079176381687 38940903494367118764572531)
        ·
          refine ⟨58411355241550678146858797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38940903494367118764572531 58411355241550678146858797)
          ·
            refine ⟨21904258215581504305072049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58411355241550678146858797 21904258215581504305072049)
            ·
              refine ⟨16428193661686128228804037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21904258215581504305072049 16428193661686128228804037)
              ·
                refine ⟨3080286311566149042900757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16428193661686128228804037 3080286311566149042900757)
                ·
                  refine ⟨144388420854663236385973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3080286311566149042900757 144388420854663236385973)
                  ·
                    rfl

theorem cell23_2530759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 6].length) (baseStart_2530759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530759 prefixEnd_2530759 := by exact prefixLift 2530759
  have htrace : WordTrace (prefixWord ++ tailWord_2530759) baseStart_2530759 baseEnd_2530759 := by
    simpa [prefixWord, tailWord_2530759, baseEnd_2530759] using wordTrace_append hprefix tailTrace_2530759
  have hstable : (prefixWord ++ tailWord_2530759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530759).length < 2 ^ (prefixWord ++ tailWord_2530759).sum := by decide
  have hdescent : baseEnd_2530759 < baseStart_2530759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530776 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 6]
def baseStart_2530776 : Nat := 118140960795 + 2530776 * 2 ^ 59
def prefixEnd_2530776 : Nat := 4983230072969 + 3 ^ 40 * 2530776 * 2
def baseEnd_2530776 : Nat := 144389390762566173440131

theorem tailTrace_2530776 : CollatzResearch.WordTrace tailWord_2530776 prefixEnd_2530776 144389390762566173440131 := by
  unfold tailWord_2530776
  simp only [CollatzResearch.WordTrace]
  refine ⟨46152491939719124487474091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61536655919625499316632121 46152491939719124487474091)
  ·
    refine ⟨69228737909578686731211137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46152491939719124487474091 69228737909578686731211137)
    ·
      refine ⟨51921553432184015048408353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69228737909578686731211137 51921553432184015048408353)
      ·
        refine ⟨38941165074138011286306265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51921553432184015048408353 38941165074138011286306265)
        ·
          refine ⟨29205873805603508464729699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38941165074138011286306265 29205873805603508464729699)
          ·
            refine ⟨43808810708405262697094549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29205873805603508464729699 43808810708405262697094549)
            ·
              refine ⟨2053538001956496688926307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43808810708405262697094549 2053538001956496688926307)
              ·
                refine ⟨3080307002934745033389461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053538001956496688926307 3080307002934745033389461)
                ·
                  refine ⟨144389390762566173440131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3080307002934745033389461 144389390762566173440131)
                  ·
                    rfl

theorem cell23_2530776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 6].length) (baseStart_2530776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530776 prefixEnd_2530776 := by exact prefixLift 2530776
  have htrace : WordTrace (prefixWord ++ tailWord_2530776) baseStart_2530776 baseEnd_2530776 := by
    simpa [prefixWord, tailWord_2530776, baseEnd_2530776] using wordTrace_append hprefix tailTrace_2530776
  have hstable : (prefixWord ++ tailWord_2530776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530776).length < 2 ^ (prefixWord ++ tailWord_2530776).sum := by decide
  have hdescent : baseEnd_2530776 < baseStart_2530776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530813 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_2530813 : Nat := 118140960795 + 2530813 * 2 ^ 59
def prefixEnd_2530813 : Nat := 4983230072969 + 3 ^ 40 * 2530813 * 2
def baseEnd_2530813 : Nat := 1299523515647311916198509

theorem tailTrace_2530813 : CollatzResearch.WordTrace tailWord_2530813 prefixEnd_2530813 1299523515647311916198509 := by
  unfold tailWord_2530813
  simp only [CollatzResearch.WordTrace]
  refine ⟨92306333380304204294045093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61537555586869469529363395 92306333380304204294045093)
  ·
    refine ⟨17307437508807038305133455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92306333380304204294045093 17307437508807038305133455)
    ·
      refine ⟨25961156263210557457700183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17307437508807038305133455 25961156263210557457700183)
      ·
        refine ⟨38941734394815836186550275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25961156263210557457700183 38941734394815836186550275)
        ·
          refine ⟨58412601592223754279825413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38941734394815836186550275 58412601592223754279825413)
          ·
            refine ⟨10952362798541953927467265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58412601592223754279825413 10952362798541953927467265)
            ·
              refine ⟨8214272098906465445600449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10952362798541953927467265 8214272098906465445600449)
              ·
                refine ⟨6160704074179849084200337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8214272098906465445600449 6160704074179849084200337)
                ·
                  refine ⟨4620528055634886813150253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6160704074179849084200337 4620528055634886813150253)
                  ·
                    refine ⟨1732698020863082554931345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4620528055634886813150253 1732698020863082554931345)
                    ·
                      refine ⟨1299523515647311916198509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732698020863082554931345 1299523515647311916198509)
                      ·
                        rfl

theorem cell23_2530813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_2530813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530813 prefixEnd_2530813 := by exact prefixLift 2530813
  have htrace : WordTrace (prefixWord ++ tailWord_2530813) baseStart_2530813 baseEnd_2530813 := by
    simpa [prefixWord, tailWord_2530813, baseEnd_2530813] using wordTrace_append hprefix tailTrace_2530813
  have hstable : (prefixWord ++ tailWord_2530813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530813).length < 2 ^ (prefixWord ++ tailWord_2530813).sum := by decide
  have hdescent : baseEnd_2530813 < baseStart_2530813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530826 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_2530826 : Nat := 118140960795 + 2530826 * 2 ^ 59
def prefixEnd_2530826 : Nat := 4983230072969 + 3 ^ 40 * 2530826 * 2
def baseEnd_2530826 : Nat := 1299530190895820365335949

theorem tailTrace_2530826 : CollatzResearch.WordTrace tailWord_2530826 prefixEnd_2530826 1299530190895820365335949 := by
  unfold tailWord_2530826
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076701882314276878567083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61537871686171405009512221 23076701882314276878567083)
  ·
    refine ⟨34615052823471415317850625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23076701882314276878567083 34615052823471415317850625)
    ·
      refine ⟨25961289617603561488387969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34615052823471415317850625 25961289617603561488387969)
      ·
        refine ⟨19470967213202671116290977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25961289617603561488387969 19470967213202671116290977)
        ·
          refine ⟨14603225409902003337218233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19470967213202671116290977 14603225409902003337218233)
          ·
            refine ⟨10952419057426502502913675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14603225409902003337218233 10952419057426502502913675)
            ·
              refine ⟨16428628586139753754370513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10952419057426502502913675 16428628586139753754370513)
              ·
                refine ⟨12321471439604815315777885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16428628586139753754370513 12321471439604815315777885)
                ·
                  refine ⟨4620551789851805743416707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12321471439604815315777885 4620551789851805743416707)
                  ·
                    refine ⟨6930827684777708615125061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4620551789851805743416707 6930827684777708615125061)
                    ·
                      refine ⟨1299530190895820365335949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6930827684777708615125061 1299530190895820365335949)
                      ·
                        rfl

theorem cell23_2530826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_2530826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530826 prefixEnd_2530826 := by exact prefixLift 2530826
  have htrace : WordTrace (prefixWord ++ tailWord_2530826) baseStart_2530826 baseEnd_2530826 := by
    simpa [prefixWord, tailWord_2530826, baseEnd_2530826] using wordTrace_append hprefix tailTrace_2530826
  have hstable : (prefixWord ++ tailWord_2530826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530826).length < 2 ^ (prefixWord ++ tailWord_2530826).sum := by decide
  have hdescent : baseEnd_2530826 < baseStart_2530826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530870 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2530870 : Nat := 118140960795 + 2530870 * 2 ^ 59
def prefixEnd_2530870 : Nat := 4983230072969 + 3 ^ 40 * 2530870 * 2
def baseEnd_2530870 : Nat := 433184261348206064395249

theorem tailTrace_2530870 : CollatzResearch.WordTrace tailWord_2530870 prefixEnd_2530870 433184261348206064395249 := by
  unfold tailWord_2530870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5769275771318606439304379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61538941560731802019246709 5769275771318606439304379)
  ·
    refine ⟨8653913656977909658956569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5769275771318606439304379 8653913656977909658956569)
    ·
      refine ⟨6490435242733432244217427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8653913656977909658956569 6490435242733432244217427)
      ·
        refine ⟨9735652864100148366326141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6490435242733432244217427 9735652864100148366326141)
        ·
          refine ⟨3650869824037555637372303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9735652864100148366326141 3650869824037555637372303)
          ·
            refine ⟨5476304736056333456058455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650869824037555637372303 5476304736056333456058455)
            ·
              refine ⟨8214457104084500184087683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476304736056333456058455 8214457104084500184087683)
              ·
                refine ⟨12321685656126750276131525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8214457104084500184087683 12321685656126750276131525)
                ·
                  refine ⟨2310316060523765676774661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12321685656126750276131525 2310316060523765676774661)
                  ·
                    refine ⟨433184261348206064395249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2310316060523765676774661 433184261348206064395249)
                    ·
                      rfl

theorem cell23_2530870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2530870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530870 prefixEnd_2530870 := by exact prefixLift 2530870
  have htrace : WordTrace (prefixWord ++ tailWord_2530870) baseStart_2530870 baseEnd_2530870 := by
    simpa [prefixWord, tailWord_2530870, baseEnd_2530870] using wordTrace_append hprefix tailTrace_2530870
  have hstable : (prefixWord ++ tailWord_2530870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530870).length < 2 ^ (prefixWord ++ tailWord_2530870).sum := by decide
  have hdescent : baseEnd_2530870 < baseStart_2530870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530877 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_2530877 : Nat := 118140960795 + 2530877 * 2 ^ 59
def prefixEnd_2530877 : Nat := 4983230072969 + 3 ^ 40 * 2530877 * 2
def baseEnd_2530877 : Nat := 1299556378409199665798215

theorem tailTrace_2530877 : CollatzResearch.WordTrace tailWord_2530877 prefixEnd_2530877 1299556378409199665798215 := by
  unfold tailWord_2530877
  simp only [CollatzResearch.WordTrace]
  refine ⟨92308667652072343224374885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61539111768048228816249923 92308667652072343224374885)
  ·
    refine ⟨17307875184763564354570291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92308667652072343224374885 17307875184763564354570291)
    ·
      refine ⟨25961812777145346531855437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17307875184763564354570291 25961812777145346531855437)
      ·
        refine ⟨9735679791429504949445789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25961812777145346531855437 9735679791429504949445789)
        ·
          refine ⟨3650879921786064356042171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9735679791429504949445789 3650879921786064356042171)
          ·
            refine ⟨5476319882679096534063257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650879921786064356042171 5476319882679096534063257)
            ·
              refine ⟨4107239912009322400547443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5476319882679096534063257 4107239912009322400547443)
              ·
                refine ⟨6160859868013983600821165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4107239912009322400547443 6160859868013983600821165)
                ·
                  refine ⟨2310322450505243850307937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6160859868013983600821165 2310322450505243850307937)
                  ·
                    refine ⟨1732741837878932887730953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2310322450505243850307937 1732741837878932887730953)
                    ·
                      refine ⟨1299556378409199665798215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732741837878932887730953 1299556378409199665798215)
                      ·
                        rfl

theorem cell23_2530877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_2530877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530877 prefixEnd_2530877 := by exact prefixLift 2530877
  have htrace : WordTrace (prefixWord ++ tailWord_2530877) baseStart_2530877 baseEnd_2530877 := by
    simpa [prefixWord, tailWord_2530877, baseEnd_2530877] using wordTrace_append hprefix tailTrace_2530877
  have hstable : (prefixWord ++ tailWord_2530877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530877).length < 2 ^ (prefixWord ++ tailWord_2530877).sum := by decide
  have hdescent : baseEnd_2530877 < baseStart_2530877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530889 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 5]
def baseStart_2530889 : Nat := 118140960795 + 2530889 * 2 ^ 59
def prefixEnd_2530889 : Nat := 4983230072969 + 3 ^ 40 * 2530889 * 2
def baseEnd_2530889 : Nat := 1299562540177053618848159

theorem tailTrace_2530889 : CollatzResearch.WordTrace tailWord_2530889 prefixEnd_2530889 1299562540177053618848159 := by
  unfold tailWord_2530889
  simp only [CollatzResearch.WordTrace]
  refine ⟨92309105328028869273811721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61539403552019246182541147 92309105328028869273811721)
  ·
    refine ⟨69231828996021651955358791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92309105328028869273811721 69231828996021651955358791)
    ·
      refine ⟨103847743494032477933038187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69231828996021651955358791 103847743494032477933038187)
      ·
        refine ⟨155771615241048716899557281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103847743494032477933038187 155771615241048716899557281)
        ·
          refine ⟨116828711430786537674667961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155771615241048716899557281 116828711430786537674667961)
          ·
            refine ⟨87621533573089903256000971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116828711430786537674667961 87621533573089903256000971)
            ·
              refine ⟨131432300359634854884001457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87621533573089903256000971 131432300359634854884001457)
              ·
                refine ⟨98574225269726141163001093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131432300359634854884001457 98574225269726141163001093)
                ·
                  refine ⟨18482667238073651468062705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98574225269726141163001093 18482667238073651468062705)
                  ·
                    refine ⟨13862000428555238601047029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18482667238073651468062705 13862000428555238601047029)
                    ·
                      refine ⟨1299562540177053618848159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13862000428555238601047029 1299562540177053618848159)
                      ·
                        rfl

theorem cell23_2530889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_2530889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530889 prefixEnd_2530889 := by exact prefixLift 2530889
  have htrace : WordTrace (prefixWord ++ tailWord_2530889) baseStart_2530889 baseEnd_2530889 := by
    simpa [prefixWord, tailWord_2530889, baseEnd_2530889] using wordTrace_append hprefix tailTrace_2530889
  have hstable : (prefixWord ++ tailWord_2530889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530889).length < 2 ^ (prefixWord ++ tailWord_2530889).sum := by decide
  have hdescent : baseEnd_2530889 < baseStart_2530889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530973 : List Nat := [1, 4, 2, 1, 1, 1, 1, 7, 5]
def baseStart_2530973 : Nat := 118140960795 + 2530973 * 2 ^ 59
def prefixEnd_2530973 : Nat := 4983230072969 + 3 ^ 40 * 2530973 * 2
def baseEnd_2530973 : Nat := 144400630283559032244197

theorem tailTrace_2530973 : CollatzResearch.WordTrace tailWord_2530973 prefixEnd_2530973 144400630283559032244197 := by
  unfold tailWord_2530973
  simp only [CollatzResearch.WordTrace]
  refine ⟨92312169059724551619869573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61541446039816367746579715 92312169059724551619869573)
  ·
    refine ⟨17308531698698353428725545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92312169059724551619869573 17308531698698353428725545)
    ·
      refine ⟨12981398774023765071544159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17308531698698353428725545 12981398774023765071544159)
      ·
        refine ⟨19472098161035647607316239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12981398774023765071544159 19472098161035647607316239)
        ·
          refine ⟨29208147241553471410974359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19472098161035647607316239 29208147241553471410974359)
          ·
            refine ⟨43812220862330207116461539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29208147241553471410974359 43812220862330207116461539)
            ·
              refine ⟨65718331293495310674692309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43812220862330207116461539 65718331293495310674692309)
              ·
                refine ⟨1540273389691296343938101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65718331293495310674692309 1540273389691296343938101)
                ·
                  refine ⟨144400630283559032244197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1540273389691296343938101 144400630283559032244197)
                  ·
                    rfl

theorem cell23_2530973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_2530973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2530973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2530973 prefixEnd_2530973 := by exact prefixLift 2530973
  have htrace : WordTrace (prefixWord ++ tailWord_2530973) baseStart_2530973 baseEnd_2530973 := by
    simpa [prefixWord, tailWord_2530973, baseEnd_2530973] using wordTrace_append hprefix tailTrace_2530973
  have hstable : (prefixWord ++ tailWord_2530973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530973).length < 2 ^ (prefixWord ++ tailWord_2530973).sum := by decide
  have hdescent : baseEnd_2530973 < baseStart_2530973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531066 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_2531066 : Nat := 118140960795 + 2531066 * 2 ^ 59
def prefixEnd_2531066 : Nat := 4983230072969 + 3 ^ 40 * 2531066 * 2
def baseEnd_2531066 : Nat := 1299653426252899426334845

theorem tailTrace_2531066 : CollatzResearch.WordTrace tailWord_2531066 prefixEnd_2531066 1299653426252899426334845 := by
  unfold tailWord_2531066
  simp only [CollatzResearch.WordTrace]
  refine ⟨23078890262096907125751263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61543707365591752335336701 23078890262096907125751263)
  ·
    refine ⟨34618335393145360688626895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23078890262096907125751263 34618335393145360688626895)
    ·
      refine ⟨51927503089718041032940343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34618335393145360688626895 51927503089718041032940343)
      ·
        refine ⟨77891254634577061549410515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51927503089718041032940343 77891254634577061549410515)
        ·
          refine ⟨116836881951865592324115773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77891254634577061549410515 116836881951865592324115773)
          ·
            refine ⟨43813830731949597121543415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116836881951865592324115773 43813830731949597121543415)
            ·
              refine ⟨65720746097924395682315123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43813830731949597121543415 65720746097924395682315123)
              ·
                refine ⟨98581119146886593523472685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65720746097924395682315123 98581119146886593523472685)
                ·
                  refine ⟨36967919680082472571302257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98581119146886593523472685 36967919680082472571302257)
                  ·
                    refine ⟨27725939760061854428476693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36967919680082472571302257 27725939760061854428476693)
                    ·
                      refine ⟨1299653426252899426334845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27725939760061854428476693 1299653426252899426334845)
                      ·
                        rfl

theorem cell23_2531066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_2531066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531066 prefixEnd_2531066 := by exact prefixLift 2531066
  have htrace : WordTrace (prefixWord ++ tailWord_2531066) baseStart_2531066 baseEnd_2531066 := by
    simpa [prefixWord, tailWord_2531066, baseEnd_2531066] using wordTrace_append hprefix tailTrace_2531066
  have hstable : (prefixWord ++ tailWord_2531066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531066).length < 2 ^ (prefixWord ++ tailWord_2531066).sum := by decide
  have hdescent : baseEnd_2531066 < baseStart_2531066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531107 : List Nat := [1, 1, 1, 4, 2, 1, 2, 6, 1, 1, 3]
def baseStart_2531107 : Nat := 118140960795 + 2531107 * 2 ^ 59
def prefixEnd_2531107 : Nat := 4983230072969 + 3 ^ 40 * 2531107 * 2
def baseEnd_2531107 : Nat := 1299674478959733765922157

theorem tailTrace_2531107 : CollatzResearch.WordTrace tailWord_2531107 prefixEnd_2531107 1299674478959733765922157 := by
  unfold tailWord_2531107
  simp only [CollatzResearch.WordTrace]
  refine ⟨92317056441239092505247575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61544704294159395003498383 92317056441239092505247575)
  ·
    refine ⟨138475584661858638757871363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92317056441239092505247575 138475584661858638757871363)
    ·
      refine ⟨207713376992787958136807045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138475584661858638757871363 207713376992787958136807045)
      ·
        refine ⟨38946258186147742150651321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207713376992787958136807045 38946258186147742150651321)
        ·
          refine ⟨29209693639610806612988491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38946258186147742150651321 29209693639610806612988491)
          ·
            refine ⟨43814540459416209919482737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29209693639610806612988491 43814540459416209919482737)
            ·
              refine ⟨32860905344562157439612053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43814540459416209919482737 32860905344562157439612053)
              ·
                refine ⟨1540354938026351129981815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32860905344562157439612053 1540354938026351129981815)
                ·
                  refine ⟨2310532407039526694972723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540354938026351129981815 2310532407039526694972723)
                  ·
                    refine ⟨3465798610559290042459085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2310532407039526694972723 3465798610559290042459085)
                    ·
                      refine ⟨1299674478959733765922157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3465798610559290042459085 1299674478959733765922157)
                      ·
                        rfl

theorem cell23_2531107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_2531107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531107 prefixEnd_2531107 := by exact prefixLift 2531107
  have htrace : WordTrace (prefixWord ++ tailWord_2531107) baseStart_2531107 baseEnd_2531107 := by
    simpa [prefixWord, tailWord_2531107, baseEnd_2531107] using wordTrace_append hprefix tailTrace_2531107
  have hstable : (prefixWord ++ tailWord_2531107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531107).length < 2 ^ (prefixWord ++ tailWord_2531107).sum := by decide
  have hdescent : baseEnd_2531107 < baseStart_2531107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531130 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_2531130 : Nat := 118140960795 + 2531130 * 2 ^ 59
def prefixEnd_2531130 : Nat := 4983230072969 + 3 ^ 40 * 2531130 * 2
def baseEnd_2531130 : Nat := 1299686289014787175934551

theorem tailTrace_2531130 : CollatzResearch.WordTrace tailWord_2531130 prefixEnd_2531130 1299686289014787175934551 := by
  unfold tailWord_2531130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23079473830038941858333711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61545263546770511622223229 23079473830038941858333711)
  ·
    refine ⟨34619210745058412787500567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23079473830038941858333711 34619210745058412787500567)
    ·
      refine ⟨51928816117587619181250851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34619210745058412787500567 51928816117587619181250851)
      ·
        refine ⟨77893224176381428771876277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51928816117587619181250851 77893224176381428771876277)
        ·
          refine ⟨7302489766535758947363401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77893224176381428771876277 7302489766535758947363401)
          ·
            refine ⟨5476867324901819210522551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7302489766535758947363401 5476867324901819210522551)
            ·
              refine ⟨8215300987352728815783827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476867324901819210522551 8215300987352728815783827)
              ·
                refine ⟨12322951481029093223675741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8215300987352728815783827 12322951481029093223675741)
                ·
                  refine ⟨4621106805385909958878403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12322951481029093223675741 4621106805385909958878403)
                  ·
                    refine ⟨6931660208078864938317605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4621106805385909958878403 6931660208078864938317605)
                    ·
                      refine ⟨1299686289014787175934551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6931660208078864938317605 1299686289014787175934551)
                      ·
                        rfl

theorem cell23_2531130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_2531130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531130 prefixEnd_2531130 := by exact prefixLift 2531130
  have htrace : WordTrace (prefixWord ++ tailWord_2531130) baseStart_2531130 baseEnd_2531130 := by
    simpa [prefixWord, tailWord_2531130, baseEnd_2531130] using wordTrace_append hprefix tailTrace_2531130
  have hstable : (prefixWord ++ tailWord_2531130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531130).length < 2 ^ (prefixWord ++ tailWord_2531130).sum := by decide
  have hdescent : baseEnd_2531130 < baseStart_2531130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531134 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_2531134 : Nat := 118140960795 + 2531134 * 2 ^ 59
def prefixEnd_2531134 : Nat := 4983230072969 + 3 ^ 40 * 2531134 * 2
def baseEnd_2531134 : Nat := 1299688342937405160284533

theorem tailTrace_2531134 : CollatzResearch.WordTrace tailWord_2531134 prefixEnd_2531134 1299688342937405160284533 := by
  unfold tailWord_2531134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11539755151517659514560057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61545360808094184077653637 11539755151517659514560057)
  ·
    refine ⟨8654816363638244635920043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11539755151517659514560057 8654816363638244635920043)
    ·
      refine ⟨12982224545457366953880065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8654816363638244635920043 12982224545457366953880065)
      ·
        refine ⟨9736668409093025215410049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12982224545457366953880065 9736668409093025215410049)
        ·
          refine ⟨7302501306819768911557537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9736668409093025215410049 7302501306819768911557537)
          ·
            refine ⟨5476875980114826683668153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7302501306819768911557537 5476875980114826683668153)
            ·
              refine ⟨4107656985086120012751115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5476875980114826683668153 4107656985086120012751115)
              ·
                refine ⟨6161485477629180019126673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4107656985086120012751115 6161485477629180019126673)
                ·
                  refine ⟨4621114108221885014345005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6161485477629180019126673 4621114108221885014345005)
                  ·
                    refine ⟨1732917790583206880379377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4621114108221885014345005 1732917790583206880379377)
                    ·
                      refine ⟨1299688342937405160284533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732917790583206880379377 1299688342937405160284533)
                      ·
                        rfl

theorem cell23_2531134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_2531134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531134 prefixEnd_2531134 := by exact prefixLift 2531134
  have htrace : WordTrace (prefixWord ++ tailWord_2531134) baseStart_2531134 baseEnd_2531134 := by
    simpa [prefixWord, tailWord_2531134, baseEnd_2531134] using wordTrace_append hprefix tailTrace_2531134
  have hstable : (prefixWord ++ tailWord_2531134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531134).length < 2 ^ (prefixWord ++ tailWord_2531134).sum := by decide
  have hdescent : baseEnd_2531134 < baseStart_2531134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531143 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_2531143 : Nat := 118140960795 + 2531143 * 2 ^ 59
def prefixEnd_2531143 : Nat := 4983230072969 + 3 ^ 40 * 2531143 * 2
def baseEnd_2531143 : Nat := 1299692964263295625071991

theorem tailTrace_2531143 : CollatzResearch.WordTrace tailWord_2531143 prefixEnd_2531143 1299692964263295625071991 := by
  unfold tailWord_2531143
  simp only [CollatzResearch.WordTrace]
  refine ⟨92318369469108670653558083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61545579646072447102372055 92318369469108670653558083)
  ·
    refine ⟨138477554203663005980337125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92318369469108670653558083 138477554203663005980337125)
    ·
      refine ⟨25964541413186813621313211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138477554203663005980337125 25964541413186813621313211)
      ·
        refine ⟨38946812119780220431969817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25964541413186813621313211 38946812119780220431969817)
        ·
          refine ⟨29210109089835165323977363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38946812119780220431969817 29210109089835165323977363)
          ·
            refine ⟨43815163634752747985966045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29210109089835165323977363 43815163634752747985966045)
            ·
              refine ⟨16430686363032280494737267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43815163634752747985966045 16430686363032280494737267)
              ·
                refine ⟨24646029544548420742105901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16430686363032280494737267 24646029544548420742105901)
                ·
                  refine ⟨9242261079205657778289713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24646029544548420742105901 9242261079205657778289713)
                  ·
                    refine ⟨6931695809404243333717285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9242261079205657778289713 6931695809404243333717285)
                    ·
                      refine ⟨1299692964263295625071991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6931695809404243333717285 1299692964263295625071991)
                      ·
                        rfl

theorem cell23_2531143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_2531143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531143 prefixEnd_2531143 := by exact prefixLift 2531143
  have htrace : WordTrace (prefixWord ++ tailWord_2531143) baseStart_2531143 baseEnd_2531143 := by
    simpa [prefixWord, tailWord_2531143, baseEnd_2531143] using wordTrace_append hprefix tailTrace_2531143
  have hstable : (prefixWord ++ tailWord_2531143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531143).length < 2 ^ (prefixWord ++ tailWord_2531143).sum := by decide
  have hdescent : baseEnd_2531143 < baseStart_2531143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531157 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 2, 4]
def baseStart_2531157 : Nat := 118140960795 + 2531157 * 2 ^ 59
def prefixEnd_2531157 : Nat := 4983230072969 + 3 ^ 40 * 2531157 * 2
def baseEnd_2531157 : Nat := 433233384330819523432309

theorem tailTrace_2531157 : CollatzResearch.WordTrace tailWord_2531157 prefixEnd_2531157 433233384330819523432309 := by
  unfold tailWord_2531157
  simp only [CollatzResearch.WordTrace]
  refine ⟨92318880091057951044567725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61545920060705300696378483 92318880091057951044567725)
  ·
    refine ⟨34619580034146731641712897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92318880091057951044567725 34619580034146731641712897)
    ·
      refine ⟨25964685025610048731284673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34619580034146731641712897 25964685025610048731284673)
      ·
        refine ⟨19473513769207536548463505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25964685025610048731284673 19473513769207536548463505)
        ·
          refine ⟨14605135326905652411347629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19473513769207536548463505 14605135326905652411347629)
          ·
            refine ⟨5476925747589619654255361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14605135326905652411347629 5476925747589619654255361)
            ·
              refine ⟨4107694310692214740691521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5476925747589619654255361 4107694310692214740691521)
              ·
                refine ⟨3080770733019161055518641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4107694310692214740691521 3080770733019161055518641)
                ·
                  refine ⟨2310578049764370791638981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3080770733019161055518641 2310578049764370791638981)
                  ·
                    refine ⟨433233384330819523432309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2310578049764370791638981 433233384330819523432309)
                    ·
                      rfl

theorem cell23_2531157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_2531157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531157 prefixEnd_2531157 := by exact prefixLift 2531157
  have htrace : WordTrace (prefixWord ++ tailWord_2531157) baseStart_2531157 baseEnd_2531157 := by
    simpa [prefixWord, tailWord_2531157, baseEnd_2531157] using wordTrace_append hprefix tailTrace_2531157
  have hstable : (prefixWord ++ tailWord_2531157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531157).length < 2 ^ (prefixWord ++ tailWord_2531157).sum := by decide
  have hdescent : baseEnd_2531157 < baseStart_2531157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531170 : List Nat := [3, 3, 2, 1, 2, 1, 3, 8]
def baseStart_2531170 : Nat := 118140960795 + 2531170 * 2 ^ 59
def prefixEnd_2531170 : Nat := 4983230072969 + 3 ^ 40 * 2531170 * 2
def baseEnd_2531170 : Nat := 48137289934850630349421

theorem tailTrace_2531170 : CollatzResearch.WordTrace tailWord_2531170 prefixEnd_2531170 48137289934850630349421 := by
  unfold tailWord_2531170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23079838560002713566197741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61546236160007236176527309 23079838560002713566197741)
  ·
    refine ⟨8654939460001017587324153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23079838560002713566197741 8654939460001017587324153)
    ·
      refine ⟨6491204595000763190493115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8654939460001017587324153 6491204595000763190493115)
      ·
        refine ⟨9736806892501144785739673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6491204595000763190493115 9736806892501144785739673)
        ·
          refine ⟨7302605169375858589304755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9736806892501144785739673 7302605169375858589304755)
          ·
            refine ⟨10953907754063787883957133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7302605169375858589304755 10953907754063787883957133)
            ·
              refine ⟨4107715407773920456483925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10953907754063787883957133 4107715407773920456483925)
              ·
                refine ⟨48137289934850630349421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4107715407773920456483925 48137289934850630349421)
                ·
                  rfl

theorem cell23_2531170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 8].length) (baseStart_2531170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531170 prefixEnd_2531170 := by exact prefixLift 2531170
  have htrace : WordTrace (prefixWord ++ tailWord_2531170) baseStart_2531170 baseEnd_2531170 := by
    simpa [prefixWord, tailWord_2531170, baseEnd_2531170] using wordTrace_append hprefix tailTrace_2531170
  have hstable : (prefixWord ++ tailWord_2531170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531170).length < 2 ^ (prefixWord ++ tailWord_2531170).sum := by decide
  have hdescent : baseEnd_2531170 < baseStart_2531170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531180 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_2531180 : Nat := 118140960795 + 2531180 * 2 ^ 59
def prefixEnd_2531180 : Nat := 4983230072969 + 3 ^ 40 * 2531180 * 2
def baseEnd_2531180 : Nat := 1299711963047511980309321

theorem tailTrace_2531180 : CollatzResearch.WordTrace tailWord_2531180 prefixEnd_2531180 1299711963047511980309321 := by
  unfold tailWord_2531180
  simp only [CollatzResearch.WordTrace]
  refine ⟨46159859484987312986327497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61546479313316417315103329 46159859484987312986327497)
  ·
    refine ⟨34619894613740484739745623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46159859484987312986327497 34619894613740484739745623)
    ·
      refine ⟨51929841920610727109618435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34619894613740484739745623 51929841920610727109618435)
      ·
        refine ⟨77894762880916090664427653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51929841920610727109618435 77894762880916090664427653)
        ·
          refine ⟨14605268040171766999580185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77894762880916090664427653 14605268040171766999580185)
          ·
            refine ⟨10953951030128825249685139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14605268040171766999580185 10953951030128825249685139)
            ·
              refine ⟨16430926545193237874527709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10953951030128825249685139 16430926545193237874527709)
              ·
                refine ⟨6161597454447464202947891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16430926545193237874527709 6161597454447464202947891)
                ·
                  refine ⟨9242396181671196304421837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161597454447464202947891 9242396181671196304421837)
                  ·
                    refine ⟨3465898568126698614158189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9242396181671196304421837 3465898568126698614158189)
                    ·
                      refine ⟨1299711963047511980309321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3465898568126698614158189 1299711963047511980309321)
                      ·
                        rfl

theorem cell23_2531180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_2531180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531180 prefixEnd_2531180 := by exact prefixLift 2531180
  have htrace : WordTrace (prefixWord ++ tailWord_2531180) baseStart_2531180 baseEnd_2531180 := by
    simpa [prefixWord, tailWord_2531180, baseEnd_2531180] using wordTrace_append hprefix tailTrace_2531180
  have hstable : (prefixWord ++ tailWord_2531180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531180).length < 2 ^ (prefixWord ++ tailWord_2531180).sum := by decide
  have hdescent : baseEnd_2531180 < baseStart_2531180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531193 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2531193 : Nat := 118140960795 + 2531193 * 2 ^ 59
def prefixEnd_2531193 : Nat := 4983230072969 + 3 ^ 40 * 2531193 * 2
def baseEnd_2531193 : Nat := 1299718638296020429446761

theorem tailTrace_2531193 : CollatzResearch.WordTrace tailWord_2531193 prefixEnd_2531193 1299718638296020429446761 := by
  unfold tailWord_2531193
  simp only [CollatzResearch.WordTrace]
  refine ⟨92320193118927529192878233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61546795412618352795252155 92320193118927529192878233)
  ·
    refine ⟨69240144839195646894658675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92320193118927529192878233 69240144839195646894658675)
    ·
      refine ⟨103860217258793470341988013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69240144839195646894658675 103860217258793470341988013)
      ·
        refine ⟨38947581472047551378245505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103860217258793470341988013 38947581472047551378245505)
        ·
          refine ⟨29210686104035663533684129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38947581472047551378245505 29210686104035663533684129)
          ·
            refine ⟨21908014578026747650263097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29210686104035663533684129 21908014578026747650263097)
            ·
              refine ⟨16431010933520060737697323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21908014578026747650263097 16431010933520060737697323)
              ·
                refine ⟨24646516400280091106545985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16431010933520060737697323 24646516400280091106545985)
                ·
                  refine ⟨18484887300210068329909489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24646516400280091106545985 18484887300210068329909489)
                  ·
                    refine ⟨13863665475157551247432117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18484887300210068329909489 13863665475157551247432117)
                    ·
                      refine ⟨1299718638296020429446761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13863665475157551247432117 1299718638296020429446761)
                      ·
                        rfl

theorem cell23_2531193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2531193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531193 prefixEnd_2531193 := by exact prefixLift 2531193
  have htrace : WordTrace (prefixWord ++ tailWord_2531193) baseStart_2531193 baseEnd_2531193 := by
    simpa [prefixWord, tailWord_2531193, baseEnd_2531193] using wordTrace_append hprefix tailTrace_2531193
  have hstable : (prefixWord ++ tailWord_2531193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531193).length < 2 ^ (prefixWord ++ tailWord_2531193).sum := by decide
  have hdescent : baseEnd_2531193 < baseStart_2531193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531198 : List Nat := [4, 2, 3, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2531198 : Nat := 118140960795 + 2531198 * 2 ^ 59
def prefixEnd_2531198 : Nat := 4983230072969 + 3 ^ 40 * 2531198 * 2
def baseEnd_2531198 : Nat := 1299721205699292909884239

theorem tailTrace_2531198 : CollatzResearch.WordTrace tailWord_2531198 prefixEnd_2531198 1299721205699292909884239 := by
  unfold tailWord_2531198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11540046935488676880851281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61546916989272943364540165 11540046935488676880851281)
  ·
    refine ⟨8655035201616507660638461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11540046935488676880851281 8655035201616507660638461)
    ·
      refine ⟨3245638200606190372739423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8655035201616507660638461 3245638200606190372739423)
      ·
        refine ⟨4868457300909285559109135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3245638200606190372739423 4868457300909285559109135)
        ·
          refine ⟨7302685951363928338663703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4868457300909285559109135 7302685951363928338663703)
          ·
            refine ⟨10954028927045892507995555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7302685951363928338663703 10954028927045892507995555)
            ·
              refine ⟨16431043390568838761993333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10954028927045892507995555 16431043390568838761993333)
              ·
                refine ⟨1540410317865828633936875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16431043390568838761993333 1540410317865828633936875)
                ·
                  refine ⟨2310615476798742950905313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540410317865828633936875 2310615476798742950905313)
                  ·
                    refine ⟨1732961607599057213178985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2310615476798742950905313 1732961607599057213178985)
                    ·
                      refine ⟨1299721205699292909884239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1732961607599057213178985 1299721205699292909884239)
                      ·
                        rfl

theorem cell23_2531198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2531198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531198 prefixEnd_2531198 := by exact prefixLift 2531198
  have htrace : WordTrace (prefixWord ++ tailWord_2531198) baseStart_2531198 baseEnd_2531198 := by
    simpa [prefixWord, tailWord_2531198, baseEnd_2531198] using wordTrace_append hprefix tailTrace_2531198
  have hstable : (prefixWord ++ tailWord_2531198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531198).length < 2 ^ (prefixWord ++ tailWord_2531198).sum := by decide
  have hdescent : baseEnd_2531198 < baseStart_2531198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531231 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 2, 1, 3]
def baseStart_2531231 : Nat := 118140960795 + 2531231 * 2 ^ 59
def prefixEnd_2531231 : Nat := 4983230072969 + 3 ^ 40 * 2531231 * 2
def baseEnd_2531231 : Nat := 1299738150560891280771587

theorem tailTrace_2531231 : CollatzResearch.WordTrace tailWord_2531231 prefixEnd_2531231 1299738150560891280771587 := by
  unfold tailWord_2531231
  simp only [CollatzResearch.WordTrace]
  refine ⟨92321579092789861682761547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61547719395193241121841031 92321579092789861682761547)
  ·
    refine ⟨138482368639184792524142321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92321579092789861682761547 138482368639184792524142321)
    ·
      refine ⟨103861776479388594393106741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138482368639184792524142321 103861776479388594393106741)
      ·
        refine ⟨9737041544942680724353757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103861776479388594393106741 9737041544942680724353757)
        ·
          refine ⟨3651390579353505271632659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9737041544942680724353757 3651390579353505271632659)
          ·
            refine ⟨5477085869030257907448989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651390579353505271632659 5477085869030257907448989)
            ·
              refine ⟨2053907200886346715293371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5477085869030257907448989 2053907200886346715293371)
              ·
                refine ⟨3080860801329520072940057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053907200886346715293371 3080860801329520072940057)
                ·
                  refine ⟨2310645600997140054705043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3080860801329520072940057 2310645600997140054705043)
                  ·
                    refine ⟨3465968401495710082057565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2310645600997140054705043 3465968401495710082057565)
                    ·
                      refine ⟨1299738150560891280771587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3465968401495710082057565 1299738150560891280771587)
                      ·
                        rfl

theorem cell23_2531231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_2531231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531231 prefixEnd_2531231 := by exact prefixLift 2531231
  have htrace : WordTrace (prefixWord ++ tailWord_2531231) baseStart_2531231 baseEnd_2531231 := by
    simpa [prefixWord, tailWord_2531231, baseEnd_2531231] using wordTrace_append hprefix tailTrace_2531231
  have hstable : (prefixWord ++ tailWord_2531231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531231).length < 2 ^ (prefixWord ++ tailWord_2531231).sum := by decide
  have hdescent : baseEnd_2531231 < baseStart_2531231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531292 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_2531292 : Nat := 118140960795 + 2531292 * 2 ^ 59
def prefixEnd_2531292 : Nat := 4983230072969 + 3 ^ 40 * 2531292 * 2
def baseEnd_2531292 : Nat := 1299769472880815542108807

theorem tailTrace_2531292 : CollatzResearch.WordTrace tailWord_2531292 prefixEnd_2531292 1299769472880815542108807 := by
  unfold tailWord_2531292
  simp only [CollatzResearch.WordTrace]
  refine ⟨46161901972784434550366065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61549202630379246067154753 46161901972784434550366065)
  ·
    refine ⟨34621426479588325912774549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46161901972784434550366065 34621426479588325912774549)
    ·
      refine ⟨1622879366230702777161307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34621426479588325912774549 1622879366230702777161307)
      ·
        refine ⟨2434319049346054165741961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622879366230702777161307 2434319049346054165741961)
        ·
          refine ⟨1825739287009540624306471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2434319049346054165741961 1825739287009540624306471)
          ·
            refine ⟨2738608930514310936459707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825739287009540624306471 2738608930514310936459707)
            ·
              refine ⟨4107913395771466404689561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738608930514310936459707 4107913395771466404689561)
              ·
                refine ⟨3080935046828599803517171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4107913395771466404689561 3080935046828599803517171)
                ·
                  refine ⟨4621402570242899705275757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080935046828599803517171 4621402570242899705275757)
                  ·
                    refine ⟨1733025963841087389478409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4621402570242899705275757 1733025963841087389478409)
                    ·
                      refine ⟨1299769472880815542108807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733025963841087389478409 1299769472880815542108807)
                      ·
                        rfl

theorem cell23_2531292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_2531292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531292 prefixEnd_2531292 := by exact prefixLift 2531292
  have htrace : WordTrace (prefixWord ++ tailWord_2531292) baseStart_2531292 baseEnd_2531292 := by
    simpa [prefixWord, tailWord_2531292, baseEnd_2531292] using wordTrace_append hprefix tailTrace_2531292
  have hstable : (prefixWord ++ tailWord_2531292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531292).length < 2 ^ (prefixWord ++ tailWord_2531292).sum := by decide
  have hdescent : baseEnd_2531292 < baseStart_2531292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531361 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 2, 1, 4]
def baseStart_2531361 : Nat := 118140960795 + 2531361 * 2 ^ 59
def prefixEnd_2531361 : Nat := 4983230072969 + 3 ^ 40 * 2531361 * 2
def baseEnd_2531361 : Nat := 1299804903045975772145989

theorem tailTrace_2531361 : CollatzResearch.WordTrace tailWord_2531361 prefixEnd_2531361 1299804903045975772145989 := by
  unfold tailWord_2531361
  simp only [CollatzResearch.WordTrace]
  refine ⟨92326320582318893884993937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61550880388212595923329291 92326320582318893884993937)
  ·
    refine ⟨69244740436739170413745453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92326320582318893884993937 69244740436739170413745453)
    ·
      refine ⟨25966777663777188905154545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69244740436739170413745453 25966777663777188905154545)
      ·
        refine ⟨19475083247832891678865909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25966777663777188905154545 19475083247832891678865909)
        ·
          refine ⟨1825789054484333594893679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19475083247832891678865909 1825789054484333594893679)
          ·
            refine ⟨2738683581726500392340519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825789054484333594893679 2738683581726500392340519)
            ·
              refine ⟨4108025372589750588510779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738683581726500392340519 4108025372589750588510779)
              ·
                refine ⟨6162038058884625882766169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108025372589750588510779 6162038058884625882766169)
                ·
                  refine ⟨4621528544163469412074627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6162038058884625882766169 4621528544163469412074627)
                  ·
                    refine ⟨6932292816245204118111941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4621528544163469412074627 6932292816245204118111941)
                    ·
                      refine ⟨1299804903045975772145989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6932292816245204118111941 1299804903045975772145989)
                      ·
                        rfl

theorem cell23_2531361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_2531361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531361 prefixEnd_2531361 := by exact prefixLift 2531361
  have htrace : WordTrace (prefixWord ++ tailWord_2531361) baseStart_2531361 baseEnd_2531361 := by
    simpa [prefixWord, tailWord_2531361, baseEnd_2531361] using wordTrace_append hprefix tailTrace_2531361
  have hstable : (prefixWord ++ tailWord_2531361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531361).length < 2 ^ (prefixWord ++ tailWord_2531361).sum := by decide
  have hdescent : baseEnd_2531361 < baseStart_2531361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531364 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2531364 : Nat := 118140960795 + 2531364 * 2 ^ 59
def prefixEnd_2531364 : Nat := 4983230072969 + 3 ^ 40 * 2531364 * 2
def baseEnd_2531364 : Nat := 1299806443487939260408475

theorem tailTrace_2531364 : CollatzResearch.WordTrace tailWord_2531364 prefixEnd_2531364 1299806443487939260408475 := by
  unfold tailWord_2531364
  simp only [CollatzResearch.WordTrace]
  refine ⟨46163215000654012698676573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61550953334205350264902097 46163215000654012698676573)
  ·
    refine ⟨17311205625245254762003715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46163215000654012698676573 17311205625245254762003715)
    ·
      refine ⟨25966808437867882143005573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17311205625245254762003715 25966808437867882143005573)
      ·
        refine ⟨4868776582100227901813545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25966808437867882143005573 4868776582100227901813545)
        ·
          refine ⟨3651582436575170926360159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4868776582100227901813545 3651582436575170926360159)
          ·
            refine ⟨5477373654862756389540239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651582436575170926360159 5477373654862756389540239)
            ·
              refine ⟨8216060482294134584310359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5477373654862756389540239 8216060482294134584310359)
              ·
                refine ⟨12324090723441201876465539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8216060482294134584310359 12324090723441201876465539)
                ·
                  refine ⟨18486136085161802814698309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12324090723441201876465539 18486136085161802814698309)
                  ·
                    refine ⟨3466150515967838027755933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18486136085161802814698309 3466150515967838027755933)
                    ·
                      refine ⟨1299806443487939260408475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3466150515967838027755933 1299806443487939260408475)
                      ·
                        rfl

theorem cell23_2531364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2531364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531364 prefixEnd_2531364 := by exact prefixLift 2531364
  have htrace : WordTrace (prefixWord ++ tailWord_2531364) baseStart_2531364 baseEnd_2531364 := by
    simpa [prefixWord, tailWord_2531364, baseEnd_2531364] using wordTrace_append hprefix tailTrace_2531364
  have hstable : (prefixWord ++ tailWord_2531364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531364).length < 2 ^ (prefixWord ++ tailWord_2531364).sum := by decide
  have hdescent : baseEnd_2531364 < baseStart_2531364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531384 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 6]
def baseStart_2531384 : Nat := 118140960795 + 2531384 * 2 ^ 59
def prefixEnd_2531384 : Nat := 4983230072969 + 3 ^ 40 * 2531384 * 2
def baseEnd_2531384 : Nat := 144424079233447686906487

theorem tailTrace_2531384 : CollatzResearch.WordTrace tailWord_2531384 prefixEnd_2531384 144424079233447686906487 := by
  unfold tailWord_2531384
  simp only [CollatzResearch.WordTrace]
  refine ⟨46163579730617784406540603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61551439640823712542054137 46163579730617784406540603)
  ·
    refine ⟨69245369595926676609810905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46163579730617784406540603 69245369595926676609810905)
    ·
      refine ⟨51934027196945007457358179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69245369595926676609810905 51934027196945007457358179)
      ·
        refine ⟨77901040795417511186037269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51934027196945007457358179 77901040795417511186037269)
        ·
          refine ⟨3651611287285195836845497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77901040795417511186037269 3651611287285195836845497)
          ·
            refine ⟨2738708465463896877634123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3651611287285195836845497 2738708465463896877634123)
            ·
              refine ⟨4108062698195845316451185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738708465463896877634123 4108062698195845316451185)
              ·
                refine ⟨3081047023646883987338389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4108062698195845316451185 3081047023646883987338389)
                ·
                  refine ⟨144424079233447686906487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3081047023646883987338389 144424079233447686906487)
                  ·
                    rfl

theorem cell23_2531384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 6].length) (baseStart_2531384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531384 prefixEnd_2531384 := by exact prefixLift 2531384
  have htrace : WordTrace (prefixWord ++ tailWord_2531384) baseStart_2531384 baseEnd_2531384 := by
    simpa [prefixWord, tailWord_2531384, baseEnd_2531384] using wordTrace_append hprefix tailTrace_2531384
  have hstable : (prefixWord ++ tailWord_2531384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531384).length < 2 ^ (prefixWord ++ tailWord_2531384).sum := by decide
  have hdescent : baseEnd_2531384 < baseStart_2531384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531400 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_2531400 : Nat := 118140960795 + 2531400 * 2 ^ 59
def prefixEnd_2531400 : Nat := 4983230072969 + 3 ^ 40 * 2531400 * 2
def baseEnd_2531400 : Nat := 1299824928791501119558309

theorem tailTrace_2531400 : CollatzResearch.WordTrace tailWord_2531400 prefixEnd_2531400 1299824928791501119558309 := by
  unfold tailWord_2531400
  simp only [CollatzResearch.WordTrace]
  refine ⟨46163871514588801772831827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61551828686118402363775769 46163871514588801772831827)
  ·
    refine ⟨69245807271883202659247741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46163871514588801772831827 69245807271883202659247741)
    ·
      refine ⟨25967177726956200997217903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69245807271883202659247741 25967177726956200997217903)
      ·
        refine ⟨38950766590434301495826855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25967177726956200997217903 38950766590434301495826855)
        ·
          refine ⟨58426149885651452243740283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38950766590434301495826855 58426149885651452243740283)
          ·
            refine ⟨87639224828477178365610425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58426149885651452243740283 87639224828477178365610425)
            ·
              refine ⟨65729418621357883774207819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87639224828477178365610425 65729418621357883774207819)
              ·
                refine ⟨98594127932036825661311729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65729418621357883774207819 98594127932036825661311729)
                ·
                  refine ⟨73945595949027619245983797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98594127932036825661311729 73945595949027619245983797)
                  ·
                    refine ⟨6932399620221339304310981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73945595949027619245983797 6932399620221339304310981)
                    ·
                      refine ⟨1299824928791501119558309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6932399620221339304310981 1299824928791501119558309)
                      ·
                        rfl

theorem cell23_2531400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_2531400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531400 prefixEnd_2531400 := by exact prefixLift 2531400
  have htrace : WordTrace (prefixWord ++ tailWord_2531400) baseStart_2531400 baseEnd_2531400 := by
    simpa [prefixWord, tailWord_2531400, baseEnd_2531400] using wordTrace_append hprefix tailTrace_2531400
  have hstable : (prefixWord ++ tailWord_2531400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531400).length < 2 ^ (prefixWord ++ tailWord_2531400).sum := by decide
  have hdescent : baseEnd_2531400 < baseStart_2531400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531417 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 2, 6, 2]
def baseStart_2531417 : Nat := 118140960795 + 2531417 * 2 ^ 59
def prefixEnd_2531417 : Nat := 4983230072969 + 3 ^ 40 * 2531417 * 2
def baseEnd_2531417 : Nat := 1299833657962627553045731

theorem tailTrace_2531417 : CollatzResearch.WordTrace tailWord_2531417 prefixEnd_2531417 1299833657962627553045731 := by
  unfold tailWord_2531417
  simp only [CollatzResearch.WordTrace]
  refine ⟨92328363070116015449032505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61552242046744010299355003 92328363070116015449032505)
  ·
    refine ⟨69246272302587011586774379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92328363070116015449032505 69246272302587011586774379)
    ·
      refine ⟨103869408453880517380161569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69246272302587011586774379 103869408453880517380161569)
      ·
        refine ⟨77902056340410388035121177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103869408453880517380161569 77902056340410388035121177)
        ·
          refine ⟨58426542255307791026340883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77902056340410388035121177 58426542255307791026340883)
          ·
            refine ⟨87639813382961686539511325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58426542255307791026340883 87639813382961686539511325)
            ·
              refine ⟨32864930018610632452316747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87639813382961686539511325 32864930018610632452316747)
              ·
                refine ⟨49297395027915948678475121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32864930018610632452316747 49297395027915948678475121)
                ·
                  refine ⟨36973046270936961508856341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49297395027915948678475121 36973046270936961508856341)
                  ·
                    refine ⟨1733111543950170070727641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36973046270936961508856341 1733111543950170070727641)
                    ·
                      refine ⟨1299833657962627553045731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733111543950170070727641 1299833657962627553045731)
                      ·
                        rfl

theorem cell23_2531417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_2531417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531417 prefixEnd_2531417 := by exact prefixLift 2531417
  have htrace : WordTrace (prefixWord ++ tailWord_2531417) baseStart_2531417 baseEnd_2531417 := by
    simpa [prefixWord, tailWord_2531417, baseEnd_2531417] using wordTrace_append hprefix tailTrace_2531417
  have hstable : (prefixWord ++ tailWord_2531417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531417).length < 2 ^ (prefixWord ++ tailWord_2531417).sum := by decide
  have hdescent : baseEnd_2531417 < baseStart_2531417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531421 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2531421 : Nat := 118140960795 + 2531421 * 2 ^ 59
def prefixEnd_2531421 : Nat := 4983230072969 + 3 ^ 40 * 2531421 * 2
def baseEnd_2531421 : Nat := 1299835711885245537395713

theorem tailTrace_2531421 : CollatzResearch.WordTrace tailWord_2531421 prefixEnd_2531421 1299835711885245537395713 := by
  unfold tailWord_2531421
  simp only [CollatzResearch.WordTrace]
  refine ⟨92328508962101524132178117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61552339308067682754785411 92328508962101524132178117)
  ·
    refine ⟨17311595430394035774783397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92328508962101524132178117 17311595430394035774783397)
    ·
      refine ⟨3245924143198881707771887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17311595430394035774783397 3245924143198881707771887)
      ·
        refine ⟨4868886214798322561657831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3245924143198881707771887 4868886214798322561657831)
        ·
          refine ⟨7303329322197483842486747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4868886214798322561657831 7303329322197483842486747)
          ·
            refine ⟨10954993983296225763730121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7303329322197483842486747 10954993983296225763730121)
            ·
              refine ⟨8216245487472169322797591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10954993983296225763730121 8216245487472169322797591)
              ·
                refine ⟨12324368231208253984196387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8216245487472169322797591 12324368231208253984196387)
                ·
                  refine ⟨18486552346812380976294581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12324368231208253984196387 18486552346812380976294581)
                  ·
                    refine ⟨1733114282513660716527617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18486552346812380976294581 1733114282513660716527617)
                    ·
                      refine ⟨1299835711885245537395713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733114282513660716527617 1299835711885245537395713)
                      ·
                        rfl

theorem cell23_2531421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2531421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531421 prefixEnd_2531421 := by exact prefixLift 2531421
  have htrace : WordTrace (prefixWord ++ tailWord_2531421) baseStart_2531421 baseEnd_2531421 := by
    simpa [prefixWord, tailWord_2531421, baseEnd_2531421] using wordTrace_append hprefix tailTrace_2531421
  have hstable : (prefixWord ++ tailWord_2531421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531421).length < 2 ^ (prefixWord ++ tailWord_2531421).sum := by decide
  have hdescent : baseEnd_2531421 < baseStart_2531421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531422 : List Nat := [4, 4, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2531422 : Nat := 118140960795 + 2531422 * 2 ^ 59
def prefixEnd_2531422 : Nat := 4983230072969 + 3 ^ 40 * 2531422 * 2
def baseEnd_2531422 : Nat := 433278741788633344494403

theorem tailTrace_2531422 : CollatzResearch.WordTrace tailWord_2531422 prefixEnd_2531422 433278741788633344494403 := by
  unfold tailWord_2531422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11541068179387237662870565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61552363623398600868643013 11541068179387237662870565)
  ·
    refine ⟨2163950283635107061788231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11541068179387237662870565 2163950283635107061788231)
    ·
      refine ⟨3245925425452660592682347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2163950283635107061788231 3245925425452660592682347)
      ·
        refine ⟨4868888138178990889023521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3245925425452660592682347 4868888138178990889023521)
        ·
          refine ⟨3651666103634243166767641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4868888138178990889023521 3651666103634243166767641)
          ·
            refine ⟨2738749577725682375075731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3651666103634243166767641 2738749577725682375075731)
            ·
              refine ⟨4108124366588523562613597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738749577725682375075731 4108124366588523562613597)
              ·
                refine ⟨1540546637470696335980099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4108124366588523562613597 1540546637470696335980099)
                ·
                  refine ⟨2310819956206044503970149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540546637470696335980099 2310819956206044503970149)
                  ·
                    refine ⟨433278741788633344494403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2310819956206044503970149 433278741788633344494403)
                    ·
                      rfl

theorem cell23_2531422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2531422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531422 prefixEnd_2531422 := by exact prefixLift 2531422
  have htrace : WordTrace (prefixWord ++ tailWord_2531422) baseStart_2531422 baseEnd_2531422 := by
    simpa [prefixWord, tailWord_2531422, baseEnd_2531422] using wordTrace_append hprefix tailTrace_2531422
  have hstable : (prefixWord ++ tailWord_2531422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531422).length < 2 ^ (prefixWord ++ tailWord_2531422).sum := by decide
  have hdescent : baseEnd_2531422 < baseStart_2531422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531427 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 4, 4]
def baseStart_2531427 : Nat := 118140960795 + 2531427 * 2 ^ 59
def prefixEnd_2531427 : Nat := 4983230072969 + 3 ^ 40 * 2531427 * 2
def baseEnd_2531427 : Nat := 433279597589724171306895

theorem tailTrace_2531427 : CollatzResearch.WordTrace tailWord_2531427 prefixEnd_2531427 433279597589724171306895 := by
  unfold tailWord_2531427
  simp only [CollatzResearch.WordTrace]
  refine ⟨92328727800079787156896535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61552485200053191437931023 92328727800079787156896535)
  ·
    refine ⟨138493091700119680735344803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92328727800079787156896535 138493091700119680735344803)
    ·
      refine ⟨207739637550179521103017205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138493091700119680735344803 207739637550179521103017205)
      ·
        refine ⟨19475591020329330103407863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207739637550179521103017205 19475591020329330103407863)
        ·
          refine ⟨29213386530493995155111795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19475591020329330103407863 29213386530493995155111795)
          ·
            refine ⟨43820079795740992732667693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29213386530493995155111795 43820079795740992732667693)
            ·
              refine ⟨16432529923402872274750385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43820079795740992732667693 16432529923402872274750385)
              ·
                refine ⟨12324397442552154206062789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16432529923402872274750385 12324397442552154206062789)
                ·
                  refine ⟨2310824520478528913636773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12324397442552154206062789 2310824520478528913636773)
                  ·
                    refine ⟨433279597589724171306895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2310824520478528913636773 433279597589724171306895)
                    ·
                      rfl

theorem cell23_2531427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 4].length) (baseStart_2531427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531427 prefixEnd_2531427 := by exact prefixLift 2531427
  have htrace : WordTrace (prefixWord ++ tailWord_2531427) baseStart_2531427 baseEnd_2531427 := by
    simpa [prefixWord, tailWord_2531427, baseEnd_2531427] using wordTrace_append hprefix tailTrace_2531427
  have hstable : (prefixWord ++ tailWord_2531427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531427).length < 2 ^ (prefixWord ++ tailWord_2531427).sum := by decide
  have hdescent : baseEnd_2531427 < baseStart_2531427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531440 : List Nat := [2, 1, 1, 1, 5, 2, 11]
def baseStart_2531440 : Nat := 118140960795 + 2531440 * 2 ^ 59
def prefixEnd_2531440 : Nat := 4983230072969 + 3 ^ 40 * 2531440 * 2
def baseEnd_2531440 : Nat := 16047474913798530408125

theorem tailTrace_2531440 : CollatzResearch.WordTrace tailWord_2531440 prefixEnd_2531440 16047474913798530408125 := by
  unfold tailWord_2531440
  simp only [CollatzResearch.WordTrace]
  refine ⟨46164600974516345188559887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61552801299355126918079849 46164600974516345188559887)
  ·
    refine ⟨69246901461774517782839831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46164600974516345188559887 69246901461774517782839831)
    ·
      refine ⟨103870352192661776674259747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69246901461774517782839831 103870352192661776674259747)
      ·
        refine ⟨155805528288992665011389621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103870352192661776674259747 155805528288992665011389621)
        ·
          refine ⟨14606768277093062344817777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155805528288992665011389621 14606768277093062344817777)
          ·
            refine ⟨10955076207819796758613333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14606768277093062344817777 10955076207819796758613333)
            ·
              refine ⟨16047474913798530408125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10955076207819796758613333 16047474913798530408125)
              ·
                rfl

theorem cell23_2531440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 11].length) (baseStart_2531440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531440 prefixEnd_2531440 := by exact prefixLift 2531440
  have htrace : WordTrace (prefixWord ++ tailWord_2531440) baseStart_2531440 baseEnd_2531440 := by
    simpa [prefixWord, tailWord_2531440, baseEnd_2531440] using wordTrace_append hprefix tailTrace_2531440
  have hstable : (prefixWord ++ tailWord_2531440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531440).length < 2 ^ (prefixWord ++ tailWord_2531440).sum := by decide
  have hdescent : baseEnd_2531440 < baseStart_2531440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531461 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_2531461 : Nat := 118140960795 + 2531461 * 2 ^ 59
def prefixEnd_2531461 : Nat := 4983230072969 + 3 ^ 40 * 2531461 * 2
def baseEnd_2531461 : Nat := 433285417037141793631843

theorem tailTrace_2531461 : CollatzResearch.WordTrace tailWord_2531461 prefixEnd_2531461 433285417037141793631843 := by
  unfold tailWord_2531461
  simp only [CollatzResearch.WordTrace]
  refine ⟨92329967881956610963634237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61553311921304407309089491 92329967881956610963634237)
  ·
    refine ⟨34623737955733729111362839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92329967881956610963634237 34623737955733729111362839)
    ·
      refine ⟨51935606933600593667044259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34623737955733729111362839 51935606933600593667044259)
      ·
        refine ⟨77903410400400890500566389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51935606933600593667044259 77903410400400890500566389)
        ·
          refine ⟨7303444725037583484428099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77903410400400890500566389 7303444725037583484428099)
          ·
            refine ⟨10955167087556375226642149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7303444725037583484428099 10955167087556375226642149)
            ·
              refine ⟨2054093828916820354995403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10955167087556375226642149 2054093828916820354995403)
              ·
                refine ⟨3081140743375230532493105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054093828916820354995403 3081140743375230532493105)
                ·
                  refine ⟨2310855557531422899369829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3081140743375230532493105 2310855557531422899369829)
                  ·
                    refine ⟨433285417037141793631843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2310855557531422899369829 433285417037141793631843)
                    ·
                      rfl

theorem cell23_2531461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_2531461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531461 prefixEnd_2531461 := by exact prefixLift 2531461
  have htrace : WordTrace (prefixWord ++ tailWord_2531461) baseStart_2531461 baseEnd_2531461 := by
    simpa [prefixWord, tailWord_2531461, baseEnd_2531461] using wordTrace_append hprefix tailTrace_2531461
  have hstable : (prefixWord ++ tailWord_2531461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531461).length < 2 ^ (prefixWord ++ tailWord_2531461).sum := by decide
  have hdescent : baseEnd_2531461 < baseStart_2531461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531484 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2531484 : Nat := 118140960795 + 2531484 * 2 ^ 59
def prefixEnd_2531484 : Nat := 4983230072969 + 3 ^ 40 * 2531484 * 2
def baseEnd_2531484 : Nat := 1299868061166478790907923

theorem tailTrace_2531484 : CollatzResearch.WordTrace tailWord_2531484 prefixEnd_2531484 1299868061166478790907923 := by
  unfold tailWord_2531484
  simp only [CollatzResearch.WordTrace]
  refine ⟨46165403380436642945860753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61553871173915523927814337 46165403380436642945860753)
  ·
    refine ⟨34624052535327482209395565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46165403380436642945860753 34624052535327482209395565)
    ·
      refine ⟨12984019700747805828523337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34624052535327482209395565 12984019700747805828523337)
      ·
        refine ⟨9738014775560854371392503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12984019700747805828523337 9738014775560854371392503)
        ·
          refine ⟨14607022163341281557088755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9738014775560854371392503 14607022163341281557088755)
          ·
            refine ⟨21910533245011922335633133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14607022163341281557088755 21910533245011922335633133)
            ·
              refine ⟨8216449966879470875862425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21910533245011922335633133 8216449966879470875862425)
              ·
                refine ⟨6162337475159603156896819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8216449966879470875862425 6162337475159603156896819)
                ·
                  refine ⟨9243506212739404735345229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6162337475159603156896819 9243506212739404735345229)
                  ·
                    refine ⟨3466314829777276775754461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9243506212739404735345229 3466314829777276775754461)
                    ·
                      refine ⟨1299868061166478790907923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3466314829777276775754461 1299868061166478790907923)
                      ·
                        rfl

theorem cell23_2531484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2531484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531484 prefixEnd_2531484 := by exact prefixLift 2531484
  have htrace : WordTrace (prefixWord ++ tailWord_2531484) baseStart_2531484 baseEnd_2531484 := by
    simpa [prefixWord, tailWord_2531484, baseEnd_2531484] using wordTrace_append hprefix tailTrace_2531484
  have hstable : (prefixWord ++ tailWord_2531484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531484).length < 2 ^ (prefixWord ++ tailWord_2531484).sum := by decide
  have hdescent : baseEnd_2531484 < baseStart_2531484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531564 : List Nat := [2, 2, 1, 1, 2, 3, 1, 6, 5]
def baseStart_2531564 : Nat := 118140960795 + 2531564 * 2 ^ 59
def prefixEnd_2531564 : Nat := 4983230072969 + 3 ^ 40 * 2531564 * 2
def baseEnd_2531564 : Nat := 144434348846537608656395

theorem tailTrace_2531564 : CollatzResearch.WordTrace tailWord_2531564 prefixEnd_2531564 144434348846537608656395 := by
  unfold tailWord_2531564
  simp only [CollatzResearch.WordTrace]
  refine ⟨46166862300291729777316873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61555816400388973036422497 46166862300291729777316873)
  ·
    refine ⟨34625146725218797332987655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46166862300291729777316873 34625146725218797332987655)
    ·
      refine ⟨51937720087828195999481483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34625146725218797332987655 51937720087828195999481483)
      ·
        refine ⟨77906580131742293999222225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51937720087828195999481483 77906580131742293999222225)
        ·
          refine ⟨58429935098806720499416669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77906580131742293999222225 58429935098806720499416669)
          ·
            refine ⟨21911225662052520187281251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58429935098806720499416669 21911225662052520187281251)
            ·
              refine ⟨32866838493078780280921877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21911225662052520187281251 32866838493078780280921877)
              ·
                refine ⟨1540633054363067825668213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32866838493078780280921877 1540633054363067825668213)
                ·
                  refine ⟨144434348846537608656395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1540633054363067825668213 144434348846537608656395)
                  ·
                    rfl

theorem cell23_2531564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_2531564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531564 prefixEnd_2531564 := by exact prefixLift 2531564
  have htrace : WordTrace (prefixWord ++ tailWord_2531564) baseStart_2531564 baseEnd_2531564 := by
    simpa [prefixWord, tailWord_2531564, baseEnd_2531564] using wordTrace_append hprefix tailTrace_2531564
  have hstable : (prefixWord ++ tailWord_2531564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531564).length < 2 ^ (prefixWord ++ tailWord_2531564).sum := by decide
  have hdescent : baseEnd_2531564 < baseStart_2531564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531577 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 6, 5]
def baseStart_2531577 : Nat := 118140960795 + 2531577 * 2 ^ 59
def prefixEnd_2531577 : Nat := 4983230072969 + 3 ^ 40 * 2531577 * 2
def baseEnd_2531577 : Nat := 433305271622448975681665

theorem tailTrace_2531577 : CollatzResearch.WordTrace tailWord_2531577 prefixEnd_2531577 433305271622448975681665 := by
  unfold tailWord_2531577
  simp only [CollatzResearch.WordTrace]
  refine ⟨92334198749536362774856985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61556132499690908516571323 92334198749536362774856985)
  ·
    refine ⟨69250649062152272081142739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92334198749536362774856985 69250649062152272081142739)
    ·
      refine ⟨103875973593228408121714109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69250649062152272081142739 103875973593228408121714109)
      ·
        refine ⟨38953490097460653045642791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103875973593228408121714109 38953490097460653045642791)
        ·
          refine ⟨58430235146190979568464187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38953490097460653045642791 58430235146190979568464187)
          ·
            refine ⟨87645352719286469352696281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58430235146190979568464187 87645352719286469352696281)
            ·
              refine ⟨65734014539464852014522211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87645352719286469352696281 65734014539464852014522211)
              ·
                refine ⟨98601021809197278021783317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65734014539464852014522211 98601021809197278021783317)
                ·
                  refine ⟨4621922897306122407271093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98601021809197278021783317 4621922897306122407271093)
                  ·
                    refine ⟨433305271622448975681665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4621922897306122407271093 433305271622448975681665)
                    ·
                      rfl

theorem cell23_2531577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_2531577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531577 prefixEnd_2531577 := by exact prefixLift 2531577
  have htrace : WordTrace (prefixWord ++ tailWord_2531577) baseStart_2531577 baseEnd_2531577 := by
    simpa [prefixWord, tailWord_2531577, baseEnd_2531577] using wordTrace_append hprefix tailTrace_2531577
  have hstable : (prefixWord ++ tailWord_2531577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531577).length < 2 ^ (prefixWord ++ tailWord_2531577).sum := by decide
  have hdescent : baseEnd_2531577 < baseStart_2531577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531584 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 2, 5, 2]
def baseStart_2531584 : Nat := 118140960795 + 2531584 * 2 ^ 59
def prefixEnd_2531584 : Nat := 4983230072969 + 3 ^ 40 * 2531584 * 2
def baseEnd_2531584 : Nat := 1299919409231928399657463

theorem tailTrace_2531584 : CollatzResearch.WordTrace tailWord_2531584 prefixEnd_2531584 1299919409231928399657463 := by
  unfold tailWord_2531584
  simp only [CollatzResearch.WordTrace]
  refine ⟨46167227030255501485180903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61556302707007335313574537 46167227030255501485180903)
  ·
    refine ⟨69250840545383252227771355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46167227030255501485180903 69250840545383252227771355)
    ·
      refine ⟨103876260818074878341657033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69250840545383252227771355 103876260818074878341657033)
      ·
        refine ⟨77907195613556158756242775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103876260818074878341657033 77907195613556158756242775)
        ·
          refine ⟨116860793420334238134364163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77907195613556158756242775 116860793420334238134364163)
          ·
            refine ⟨175291190130501357201546245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116860793420334238134364163 175291190130501357201546245)
            ·
              refine ⟨32867098149469004475289921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175291190130501357201546245 32867098149469004475289921)
              ·
                refine ⟨24650323612101753356467441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32867098149469004475289921 24650323612101753356467441)
                ·
                  refine ⟨18487742709076315017350581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24650323612101753356467441 18487742709076315017350581)
                  ·
                    refine ⟨1733225878975904532876617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18487742709076315017350581 1733225878975904532876617)
                    ·
                      refine ⟨1299919409231928399657463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733225878975904532876617 1299919409231928399657463)
                      ·
                        rfl

theorem cell23_2531584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_2531584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531584 prefixEnd_2531584 := by exact prefixLift 2531584
  have htrace : WordTrace (prefixWord ++ tailWord_2531584) baseStart_2531584 baseEnd_2531584 := by
    simpa [prefixWord, tailWord_2531584, baseEnd_2531584] using wordTrace_append hprefix tailTrace_2531584
  have hstable : (prefixWord ++ tailWord_2531584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531584).length < 2 ^ (prefixWord ++ tailWord_2531584).sum := by decide
  have hdescent : baseEnd_2531584 < baseStart_2531584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531657 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_2531657 : Nat := 118140960795 + 2531657 * 2 ^ 59
def prefixEnd_2531657 : Nat := 4983230072969 + 3 ^ 40 * 2531657 * 2
def baseEnd_2531657 : Nat := 1299956893319706614044627

theorem tailTrace_2531657 : CollatzResearch.WordTrace tailWord_2531657 prefixEnd_2531657 1299956893319706614044627 := by
  unfold tailWord_2531657
  simp only [CollatzResearch.WordTrace]
  refine ⟨92337116589246536437769225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61558077726164357625179483 92337116589246536437769225)
  ·
    refine ⟨69252837441934902328326919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92337116589246536437769225 69252837441934902328326919)
    ·
      refine ⟨103879256162902353492490379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69252837441934902328326919 103879256162902353492490379)
      ·
        refine ⟨155818884244353530238735569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103879256162902353492490379 155818884244353530238735569)
        ·
          refine ⟨116864163183265147679051677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155818884244353530238735569 116864163183265147679051677)
          ·
            refine ⟨43824061193724430379644379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116864163183265147679051677 43824061193724430379644379)
            ·
              refine ⟨65736091790586645569466569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43824061193724430379644379 65736091790586645569466569)
              ·
                refine ⟨49302068842939984177099927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65736091790586645569466569 49302068842939984177099927)
                ·
                  refine ⟨73953103264409976265649891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49302068842939984177099927 73953103264409976265649891)
                  ·
                    refine ⟨110929654896614964398474837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73953103264409976265649891 110929654896614964398474837)
                    ·
                      refine ⟨1299956893319706614044627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 110929654896614964398474837 1299956893319706614044627)
                      ·
                        rfl

theorem cell23_2531657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_2531657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531657 prefixEnd_2531657 := by exact prefixLift 2531657
  have htrace : WordTrace (prefixWord ++ tailWord_2531657) baseStart_2531657 baseEnd_2531657 := by
    simpa [prefixWord, tailWord_2531657, baseEnd_2531657] using wordTrace_append hprefix tailTrace_2531657
  have hstable : (prefixWord ++ tailWord_2531657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531657).length < 2 ^ (prefixWord ++ tailWord_2531657).sum := by decide
  have hdescent : baseEnd_2531657 < baseStart_2531657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531684 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_2531684 : Nat := 118140960795 + 2531684 * 2 ^ 59
def prefixEnd_2531684 : Nat := 4983230072969 + 3 ^ 40 * 2531684 * 2
def baseEnd_2531684 : Nat := 433323585765792669469001

theorem tailTrace_2531684 : CollatzResearch.WordTrace tailWord_2531684 prefixEnd_2531684 433323585765792669469001 := by
  unfold tailWord_2531684
  simp only [CollatzResearch.WordTrace]
  refine ⟨46169050680074360024501053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61558734240099146699334737 46169050680074360024501053)
  ·
    refine ⟨17313394005027885009187895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46169050680074360024501053 17313394005027885009187895)
    ·
      refine ⟨25970091007541827513781843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17313394005027885009187895 25970091007541827513781843)
      ·
        refine ⟨38955136511312741270672765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25970091007541827513781843 38955136511312741270672765)
        ·
          refine ⟨14608176191742277976502287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38955136511312741270672765 14608176191742277976502287)
          ·
            refine ⟨21912264287613416964753431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14608176191742277976502287 21912264287613416964753431)
            ·
              refine ⟨32868396431420125447130147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21912264287613416964753431 32868396431420125447130147)
              ·
                refine ⟨49302594647130188170695221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32868396431420125447130147 49302594647130188170695221)
                ·
                  refine ⟨4622118248168455141002677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49302594647130188170695221 4622118248168455141002677)
                  ·
                    refine ⟨433323585765792669469001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4622118248168455141002677 433323585765792669469001)
                    ·
                      rfl

theorem cell23_2531684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_2531684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531684 prefixEnd_2531684 := by exact prefixLift 2531684
  have htrace : WordTrace (prefixWord ++ tailWord_2531684) baseStart_2531684 baseEnd_2531684 := by
    simpa [prefixWord, tailWord_2531684, baseEnd_2531684] using wordTrace_append hprefix tailTrace_2531684
  have hstable : (prefixWord ++ tailWord_2531684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531684).length < 2 ^ (prefixWord ++ tailWord_2531684).sum := by decide
  have hdescent : baseEnd_2531684 < baseStart_2531684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531698 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_2531698 : Nat := 118140960795 + 2531698 * 2 ^ 59
def prefixEnd_2531698 : Nat := 4983230072969 + 3 ^ 40 * 2531698 * 2
def baseEnd_2531698 : Nat := 1299977946026540953631939

theorem tailTrace_2531698 : CollatzResearch.WordTrace tailWord_2531698 prefixEnd_2531698 1299977946026540953631939 := by
  unfold tailWord_2531698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23084652995524500110002937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61559074654732000293341165 23084652995524500110002937)
  ·
    refine ⟨17313489746643375082502203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23084652995524500110002937 17313489746643375082502203)
    ·
      refine ⟨25970234619965062623753305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17313489746643375082502203 25970234619965062623753305)
      ·
        refine ⟨19477675964973796967814979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25970234619965062623753305 19477675964973796967814979)
        ·
          refine ⟨29216513947460695451722469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19477675964973796967814979 29216513947460695451722469)
          ·
            refine ⟨5478096365148880397197963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29216513947460695451722469 5478096365148880397197963)
            ·
              refine ⟨8217144547723320595796945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5478096365148880397197963 8217144547723320595796945)
              ·
                refine ⟨6162858410792490446847709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8217144547723320595796945 6162858410792490446847709)
                ·
                  refine ⟨2311071904047183917567891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6162858410792490446847709 2311071904047183917567891)
                  ·
                    refine ⟨3466607856070775876351837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311071904047183917567891 3466607856070775876351837)
                    ·
                      refine ⟨1299977946026540953631939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3466607856070775876351837 1299977946026540953631939)
                      ·
                        rfl

theorem cell23_2531698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_2531698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531698 prefixEnd_2531698 := by exact prefixLift 2531698
  have htrace : WordTrace (prefixWord ++ tailWord_2531698) baseStart_2531698 baseEnd_2531698 := by
    simpa [prefixWord, tailWord_2531698, baseEnd_2531698] using wordTrace_append hprefix tailTrace_2531698
  have hstable : (prefixWord ++ tailWord_2531698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531698).length < 2 ^ (prefixWord ++ tailWord_2531698).sum := by decide
  have hdescent : baseEnd_2531698 < baseStart_2531698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531701 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2531701 : Nat := 118140960795 + 2531701 * 2 ^ 59
def prefixEnd_2531701 : Nat := 4983230072969 + 3 ^ 40 * 2531701 * 2
def baseEnd_2531701 : Nat := 433326495489501480631475

theorem tailTrace_2531701 : CollatzResearch.WordTrace tailWord_2531701 prefixEnd_2531701 433326495489501480631475 := by
  unfold tailWord_2531701
  simp only [CollatzResearch.WordTrace]
  refine ⟨92338721401087131952370957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61559147600724754634913971 92338721401087131952370957)
  ·
    refine ⟨34627020525407674482139109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92338721401087131952370957 34627020525407674482139109)
    ·
      refine ⟨6492566348513938965401083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34627020525407674482139109 6492566348513938965401083)
      ·
        refine ⟨9738849522770908448101625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6492566348513938965401083 9738849522770908448101625)
        ·
          refine ⟨7304137142078181336076219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9738849522770908448101625 7304137142078181336076219)
          ·
            refine ⟨10956205713117272004114329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7304137142078181336076219 10956205713117272004114329)
            ·
              refine ⟨8217154284837954003085747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10956205713117272004114329 8217154284837954003085747)
              ·
                refine ⟨12325731427256931004628621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8217154284837954003085747 12325731427256931004628621)
                ·
                  refine ⟨4622149285221349126735733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12325731427256931004628621 4622149285221349126735733)
                  ·
                    refine ⟨433326495489501480631475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4622149285221349126735733 433326495489501480631475)
                    ·
                      rfl

theorem cell23_2531701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2531701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531701 prefixEnd_2531701 := by exact prefixLift 2531701
  have htrace : WordTrace (prefixWord ++ tailWord_2531701) baseStart_2531701 baseEnd_2531701 := by
    simpa [prefixWord, tailWord_2531701, baseEnd_2531701] using wordTrace_append hprefix tailTrace_2531701
  have hstable : (prefixWord ++ tailWord_2531701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531701).length < 2 ^ (prefixWord ++ tailWord_2531701).sum := by decide
  have hdescent : baseEnd_2531701 < baseStart_2531701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531702 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2531702 : Nat := 118140960795 + 2531702 * 2 ^ 59
def prefixEnd_2531702 : Nat := 4983230072969 + 3 ^ 40 * 2531702 * 2
def baseEnd_2531702 : Nat := 1299979999949158937981921

theorem tailTrace_2531702 : CollatzResearch.WordTrace tailWord_2531702 prefixEnd_2531702 1299979999949158937981921 := by
  unfold tailWord_2531702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5771172367130219320197335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61559171916055672748771573 5771172367130219320197335)
  ·
    refine ⟨8656758550695328980296003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5771172367130219320197335 8656758550695328980296003)
    ·
      refine ⟨12985137826042993470444005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656758550695328980296003 12985137826042993470444005)
      ·
        refine ⟨2434713342383061275708251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12985137826042993470444005 2434713342383061275708251)
        ·
          refine ⟨3652070013574591913562377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434713342383061275708251 3652070013574591913562377)
          ·
            refine ⟨2739052510180943935171783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3652070013574591913562377 2739052510180943935171783)
            ·
              refine ⟨4108578765271415902757675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739052510180943935171783 4108578765271415902757675)
              ·
                refine ⟨6162868147907123854136513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108578765271415902757675 6162868147907123854136513)
                ·
                  refine ⟨4622151110930342890602385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6162868147907123854136513 4622151110930342890602385)
                  ·
                    refine ⟨3466613333197757167951789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4622151110930342890602385 3466613333197757167951789)
                    ·
                      refine ⟨1299979999949158937981921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3466613333197757167951789 1299979999949158937981921)
                      ·
                        rfl

theorem cell23_2531702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2531702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531702 prefixEnd_2531702 := by exact prefixLift 2531702
  have htrace : WordTrace (prefixWord ++ tailWord_2531702) baseStart_2531702 baseEnd_2531702 := by
    simpa [prefixWord, tailWord_2531702, baseEnd_2531702] using wordTrace_append hprefix tailTrace_2531702
  have hstable : (prefixWord ++ tailWord_2531702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531702).length < 2 ^ (prefixWord ++ tailWord_2531702).sum := by decide
  have hdescent : baseEnd_2531702 < baseStart_2531702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531751 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2531751 : Nat := 118140960795 + 2531751 * 2 ^ 59
def prefixEnd_2531751 : Nat := 4983230072969 + 3 ^ 40 * 2531751 * 2
def baseEnd_2531751 : Nat := 1300005160501229246269195

theorem tailTrace_2531751 : CollatzResearch.WordTrace tailWord_2531751 prefixEnd_2531751 1300005160501229246269195 := by
  unfold tailWord_2531751
  simp only [CollatzResearch.WordTrace]
  refine ⟨92340545050905990491691107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61560363367270660327794071 92340545050905990491691107)
  ·
    refine ⟨138510817576358985737536661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92340545050905990491691107 138510817576358985737536661)
    ·
      refine ⟨6492694573891827456447031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138510817576358985737536661 6492694573891827456447031)
      ·
        refine ⟨9739041860837741184670547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6492694573891827456447031 9739041860837741184670547)
        ·
          refine ⟨14608562791256611777005821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9739041860837741184670547 14608562791256611777005821)
          ·
            refine ⟨5478211046721229416377183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14608562791256611777005821 5478211046721229416377183)
            ·
              refine ⟨8217316570081844124565775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5478211046721229416377183 8217316570081844124565775)
              ·
                refine ⟨12325974855122766186848663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8217316570081844124565775 12325974855122766186848663)
                ·
                  refine ⟨18488962282684149280272995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12325974855122766186848663 18488962282684149280272995)
                  ·
                    refine ⟨27733443424026223920409493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18488962282684149280272995 27733443424026223920409493)
                    ·
                      refine ⟨1300005160501229246269195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27733443424026223920409493 1300005160501229246269195)
                      ·
                        rfl

theorem cell23_2531751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2531751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531751 prefixEnd_2531751 := by exact prefixLift 2531751
  have htrace : WordTrace (prefixWord ++ tailWord_2531751) baseStart_2531751 baseEnd_2531751 := by
    simpa [prefixWord, tailWord_2531751, baseEnd_2531751] using wordTrace_append hprefix tailTrace_2531751
  have hstable : (prefixWord ++ tailWord_2531751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531751).length < 2 ^ (prefixWord ++ tailWord_2531751).sum := by decide
  have hdescent : baseEnd_2531751 < baseStart_2531751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531761 : List Nat := [1, 2, 2, 4, 1, 2, 4, 7]
def baseStart_2531761 : Nat := 118140960795 + 2531761 * 2 ^ 59
def prefixEnd_2531761 : Nat := 4983230072969 + 3 ^ 40 * 2531761 * 2
def baseEnd_2531761 : Nat := 48148529455843489153487

theorem tailTrace_2531761 : CollatzResearch.WordTrace tailWord_2531761 prefixEnd_2531761 48148529455843489153487 := by
  unfold tailWord_2531761
  simp only [CollatzResearch.WordTrace]
  refine ⟨92340909780869762199555137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61560606520579841466370091 92340909780869762199555137)
  ·
    refine ⟨69255682335652321649666353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92340909780869762199555137 69255682335652321649666353)
    ·
      refine ⟨51941761751739241237249765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69255682335652321649666353 51941761751739241237249765)
      ·
        refine ⟨9739080328451107731984331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51941761751739241237249765 9739080328451107731984331)
        ·
          refine ⟨14608620492676661597976497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9739080328451107731984331 14608620492676661597976497)
          ·
            refine ⟨10956465369507496198482373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14608620492676661597976497 10956465369507496198482373)
            ·
              refine ⟨2054337256782655537215445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10956465369507496198482373 2054337256782655537215445)
              ·
                refine ⟨48148529455843489153487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2054337256782655537215445 48148529455843489153487)
                ·
                  rfl

theorem cell23_2531761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 7].length) (baseStart_2531761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531761 prefixEnd_2531761 := by exact prefixLift 2531761
  have htrace : WordTrace (prefixWord ++ tailWord_2531761) baseStart_2531761 baseEnd_2531761 := by
    simpa [prefixWord, tailWord_2531761, baseEnd_2531761] using wordTrace_append hprefix tailTrace_2531761
  have hstable : (prefixWord ++ tailWord_2531761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531761).length < 2 ^ (prefixWord ++ tailWord_2531761).sum := by decide
  have hdescent : baseEnd_2531761 < baseStart_2531761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531805 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2531805 : Nat := 118140960795 + 2531805 * 2 ^ 59
def prefixEnd_2531805 : Nat := 4983230072969 + 3 ^ 40 * 2531805 * 2
def baseEnd_2531805 : Nat := 1300032888456572034993947

theorem tailTrace_2531805 : CollatzResearch.WordTrace tailWord_2531805 prefixEnd_2531805 1300032888456572034993947 := by
  unfold tailWord_2531805
  simp only [CollatzResearch.WordTrace]
  refine ⟨92342514592710357714156869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61561676395140238476104579 92342514592710357714156869)
  ·
    refine ⟨17314221486133192071404413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92342514592710357714156869 17314221486133192071404413)
    ·
      refine ⟨6492833057299947026776655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17314221486133192071404413 6492833057299947026776655)
      ·
        refine ⟨9739249585949920540164983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6492833057299947026776655 9739249585949920540164983)
        ·
          refine ⟨14608874378924880810247475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9739249585949920540164983 14608874378924880810247475)
          ·
            refine ⟨21913311568387321215371213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14608874378924880810247475 21913311568387321215371213)
            ·
              refine ⟨8217491838145245455764205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21913311568387321215371213 8217491838145245455764205)
              ·
                refine ⟨3081559439304467045911577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8217491838145245455764205 3081559439304467045911577)
                ·
                  refine ⟨2311169579478350284433683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3081559439304467045911577 2311169579478350284433683)
                  ·
                    refine ⟨3466754369217525426650525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311169579478350284433683 3466754369217525426650525)
                    ·
                      refine ⟨1300032888456572034993947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3466754369217525426650525 1300032888456572034993947)
                      ·
                        rfl

theorem cell23_2531805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2531805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531805 prefixEnd_2531805 := by exact prefixLift 2531805
  have htrace : WordTrace (prefixWord ++ tailWord_2531805) baseStart_2531805 baseEnd_2531805 := by
    simpa [prefixWord, tailWord_2531805, baseEnd_2531805] using wordTrace_append hprefix tailTrace_2531805
  have hstable : (prefixWord ++ tailWord_2531805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531805).length < 2 ^ (prefixWord ++ tailWord_2531805).sum := by decide
  have hdescent : baseEnd_2531805 < baseStart_2531805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531834 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 11]
def baseStart_2531834 : Nat := 118140960795 + 2531834 * 2 ^ 59
def prefixEnd_2531834 : Nat := 4983230072969 + 3 ^ 40 * 2531834 * 2
def baseEnd_2531834 : Nat := 144449753266172491281257

theorem tailTrace_2531834 : CollatzResearch.WordTrace tailWord_2531834 prefixEnd_2531834 144449753266172491281257 := by
  unfold tailWord_2531834
  simp only [CollatzResearch.WordTrace]
  refine ⟨23085893077401323916740639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61562381539736863777975037 23085893077401323916740639)
  ·
    refine ⟨34628839616101985875110959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23085893077401323916740639 34628839616101985875110959)
    ·
      refine ⟨51943259424152978812666439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34628839616101985875110959 51943259424152978812666439)
      ·
        refine ⟨77914889136229468218999659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51943259424152978812666439 77914889136229468218999659)
        ·
          refine ⟨116872333704344202328499489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77914889136229468218999659 116872333704344202328499489)
          ·
            refine ⟨87654250278258151746374617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116872333704344202328499489 87654250278258151746374617)
            ·
              refine ⟨65740687708693613809780963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87654250278258151746374617 65740687708693613809780963)
              ·
                refine ⟨98611031563040420714671445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65740687708693613809780963 98611031563040420714671445)
                ·
                  refine ⟨144449753266172491281257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 98611031563040420714671445 144449753266172491281257)
                  ·
                    rfl

theorem cell23_2531834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_2531834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531834 prefixEnd_2531834 := by exact prefixLift 2531834
  have htrace : WordTrace (prefixWord ++ tailWord_2531834) baseStart_2531834 baseEnd_2531834 := by
    simpa [prefixWord, tailWord_2531834, baseEnd_2531834] using wordTrace_append hprefix tailTrace_2531834
  have hstable : (prefixWord ++ tailWord_2531834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531834).length < 2 ^ (prefixWord ++ tailWord_2531834).sum := by decide
  have hdescent : baseEnd_2531834 < baseStart_2531834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531845 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 2, 2, 2]
def baseStart_2531845 : Nat := 118140960795 + 2531845 * 2 ^ 59
def prefixEnd_2531845 : Nat := 4983230072969 + 3 ^ 40 * 2531845 * 2
def baseEnd_2531845 : Nat := 1300053427682751878493763

theorem tailTrace_2531845 : CollatzResearch.WordTrace tailWord_2531845 prefixEnd_2531845 1300053427682751878493763 := by
  unfold tailWord_2531845
  simp only [CollatzResearch.WordTrace]
  refine ⟨92343973512565444545612989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61562649008376963030408659 92343973512565444545612989)
  ·
    refine ⟨34628990067212041704604871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92343973512565444545612989 34628990067212041704604871)
    ·
      refine ⟨51943485100818062556907307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34628990067212041704604871 51943485100818062556907307)
      ·
        refine ⟨77915227651227093835360961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51943485100818062556907307 77915227651227093835360961)
        ·
          refine ⟨58436420738420320376520721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77915227651227093835360961 58436420738420320376520721)
          ·
            refine ⟨43827315553815240282390541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58436420738420320376520721 43827315553815240282390541)
            ·
              refine ⟨16435243332680715105896453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43827315553815240282390541 16435243332680715105896453)
              ·
                refine ⟨3081608124877634082355585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16435243332680715105896453 3081608124877634082355585)
                ·
                  refine ⟨2311206093658225561766689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3081608124877634082355585 2311206093658225561766689)
                  ·
                    refine ⟨1733404570243669171325017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2311206093658225561766689 1733404570243669171325017)
                    ·
                      refine ⟨1300053427682751878493763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733404570243669171325017 1300053427682751878493763)
                      ·
                        rfl

theorem cell23_2531845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_2531845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531845 prefixEnd_2531845 := by exact prefixLift 2531845
  have htrace : WordTrace (prefixWord ++ tailWord_2531845) baseStart_2531845 baseEnd_2531845 := by
    simpa [prefixWord, tailWord_2531845, baseEnd_2531845] using wordTrace_append hprefix tailTrace_2531845
  have hstable : (prefixWord ++ tailWord_2531845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531845).length < 2 ^ (prefixWord ++ tailWord_2531845).sum := by decide
  have hdescent : baseEnd_2531845 < baseStart_2531845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531928 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 3, 4]
def baseStart_2531928 : Nat := 118140960795 + 2531928 * 2 ^ 59
def prefixEnd_2531928 : Nat := 4983230072969 + 3 ^ 40 * 2531928 * 2
def baseEnd_2531928 : Nat := 433365348859025017918627

theorem tailTrace_2531928 : CollatzResearch.WordTrace tailWord_2531928 prefixEnd_2531928 433365348859025017918627 := by
  unfold tailWord_2531928
  simp only [CollatzResearch.WordTrace]
  refine ⟨46173500385632374860442219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61564667180843166480589625 46173500385632374860442219)
  ·
    refine ⟨69260250578448562290663329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46173500385632374860442219 69260250578448562290663329)
    ·
      refine ⟨51945187933836421717997497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69260250578448562290663329 51945187933836421717997497)
      ·
        refine ⟨38958890950377316288498123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51945187933836421717997497 38958890950377316288498123)
        ·
          refine ⟨58438336425565974432747185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38958890950377316288498123 58438336425565974432747185)
          ·
            refine ⟨43828752319174480824560389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58438336425565974432747185 43828752319174480824560389)
            ·
              refine ⟨8217891059845215154605073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43828752319174480824560389 8217891059845215154605073)
              ·
                refine ⟨6163418294883911365953805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8217891059845215154605073 6163418294883911365953805)
                ·
                  refine ⟨2311281860581466762232677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6163418294883911365953805 2311281860581466762232677)
                  ·
                    refine ⟨433365348859025017918627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2311281860581466762232677 433365348859025017918627)
                    ·
                      rfl

theorem cell23_2531928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_2531928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2531928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2531928 prefixEnd_2531928 := by exact prefixLift 2531928
  have htrace : WordTrace (prefixWord ++ tailWord_2531928) baseStart_2531928 baseEnd_2531928 := by
    simpa [prefixWord, tailWord_2531928, baseEnd_2531928] using wordTrace_append hprefix tailTrace_2531928
  have hstable : (prefixWord ++ tailWord_2531928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531928).length < 2 ^ (prefixWord ++ tailWord_2531928).sum := by decide
  have hdescent : baseEnd_2531928 < baseStart_2531928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532019 : List Nat := [1, 1, 1, 2, 3, 4, 4, 2, 1, 1, 3]
def baseStart_2532019 : Nat := 118140960795 + 2532019 * 2 ^ 59
def prefixEnd_2532019 : Nat := 4983230072969 + 3 ^ 40 * 2532019 * 2
def baseEnd_2532019 : Nat := 1300142773316634197717963

theorem tailTrace_2532019 : CollatzResearch.WordTrace tailWord_2532019 prefixEnd_2532019 1300142773316634197717963 := by
  unfold tailWord_2532019
  simp only [CollatzResearch.WordTrace]
  refine ⟨92350319813935072262447111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61566879875956714841631407 92350319813935072262447111)
  ·
    refine ⟨138525479720902608393670667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92350319813935072262447111 138525479720902608393670667)
    ·
      refine ⟨207788219581353912590506001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138525479720902608393670667 207788219581353912590506001)
      ·
        refine ⟨155841164686015434442879501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207788219581353912590506001 155841164686015434442879501)
        ·
          refine ⟨58440436757255787916079813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155841164686015434442879501 58440436757255787916079813)
          ·
            refine ⟨10957581891985460234264965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58440436757255787916079813 10957581891985460234264965)
            ·
              refine ⟨2054546604747273793924681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10957581891985460234264965 2054546604747273793924681)
              ·
                refine ⟨1540909953560455345443511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054546604747273793924681 1540909953560455345443511)
                ·
                  refine ⟨2311364930340683018165267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540909953560455345443511 2311364930340683018165267)
                  ·
                    refine ⟨3467047395511024527247901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311364930340683018165267 3467047395511024527247901)
                    ·
                      refine ⟨1300142773316634197717963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3467047395511024527247901 1300142773316634197717963)
                      ·
                        rfl

theorem cell23_2532019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 1, 1, 3].length) (baseStart_2532019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532019 prefixEnd_2532019 := by exact prefixLift 2532019
  have htrace : WordTrace (prefixWord ++ tailWord_2532019) baseStart_2532019 baseEnd_2532019 := by
    simpa [prefixWord, tailWord_2532019, baseEnd_2532019] using wordTrace_append hprefix tailTrace_2532019
  have hstable : (prefixWord ++ tailWord_2532019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532019).length < 2 ^ (prefixWord ++ tailWord_2532019).sum := by decide
  have hdescent : baseEnd_2532019 < baseStart_2532019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532028 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2532028 : Nat := 118140960795 + 2532028 * 2 ^ 59
def prefixEnd_2532028 : Nat := 4983230072969 + 3 ^ 40 * 2532028 * 2
def baseEnd_2532028 : Nat := 1300147394642524662505421

theorem tailTrace_2532028 : CollatzResearch.WordTrace tailWord_2532028 prefixEnd_2532028 1300147394642524662505421 := by
  unfold tailWord_2532028
  simp only [CollatzResearch.WordTrace]
  refine ⟨46175324035451233399762369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61567098713934977866349825 46175324035451233399762369)
  ·
    refine ⟨34631493026588425049821777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46175324035451233399762369 34631493026588425049821777)
    ·
      refine ⟨25973619769941318787366333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34631493026588425049821777 25973619769941318787366333)
      ·
        refine ⟨9740107413727994545262375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25973619769941318787366333 9740107413727994545262375)
        ·
          refine ⟨14610161120591991817893563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9740107413727994545262375 14610161120591991817893563)
          ·
            refine ⟨21915241680887987726840345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14610161120591991817893563 21915241680887987726840345)
            ·
              refine ⟨16436431260665990795130259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21915241680887987726840345 16436431260665990795130259)
              ·
                refine ⟨24654646890998986192695389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16436431260665990795130259 24654646890998986192695389)
                ·
                  refine ⟨9245492584124619822260771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24654646890998986192695389 9245492584124619822260771)
                  ·
                    refine ⟨13868238876186929733391157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9245492584124619822260771 13868238876186929733391157)
                    ·
                      refine ⟨1300147394642524662505421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13868238876186929733391157 1300147394642524662505421)
                      ·
                        rfl

theorem cell23_2532028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2532028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532028 prefixEnd_2532028 := by exact prefixLift 2532028
  have htrace : WordTrace (prefixWord ++ tailWord_2532028) baseStart_2532028 baseEnd_2532028 := by
    simpa [prefixWord, tailWord_2532028, baseEnd_2532028] using wordTrace_append hprefix tailTrace_2532028
  have hstable : (prefixWord ++ tailWord_2532028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532028).length < 2 ^ (prefixWord ++ tailWord_2532028).sum := by decide
  have hdescent : baseEnd_2532028 < baseStart_2532028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532041 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_2532041 : Nat := 118140960795 + 2532041 * 2 ^ 59
def prefixEnd_2532041 : Nat := 4983230072969 + 3 ^ 40 * 2532041 * 2
def baseEnd_2532041 : Nat := 1300154069891033111642861

theorem tailTrace_2532041 : CollatzResearch.WordTrace tailWord_2532041 prefixEnd_2532041 1300154069891033111642861 := by
  unfold tailWord_2532041
  simp only [CollatzResearch.WordTrace]
  refine ⟨92351122219855370019747977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61567414813236913346498651 92351122219855370019747977)
  ·
    refine ⟨69263341664891527514810983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92351122219855370019747977 69263341664891527514810983)
    ·
      refine ⟨103895012497337291272216475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69263341664891527514810983 103895012497337291272216475)
      ·
        refine ⟨155842518746005936908324713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103895012497337291272216475 155842518746005936908324713)
        ·
          refine ⟨116881889059504452681243535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155842518746005936908324713 116881889059504452681243535)
          ·
            refine ⟨175322833589256679021865303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116881889059504452681243535 175322833589256679021865303)
            ·
              refine ⟨262984250383885018532797955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175322833589256679021865303 262984250383885018532797955)
              ·
                refine ⟨394476375575827527799196933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262984250383885018532797955 394476375575827527799196933)
                ·
                  refine ⟨73964320420467661462349425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 394476375575827527799196933 73964320420467661462349425)
                  ·
                    refine ⟨55473240315350746096762069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73964320420467661462349425 55473240315350746096762069)
                    ·
                      refine ⟨1300154069891033111642861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55473240315350746096762069 1300154069891033111642861)
                      ·
                        rfl

theorem cell23_2532041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_2532041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532041 prefixEnd_2532041 := by exact prefixLift 2532041
  have htrace : WordTrace (prefixWord ++ tailWord_2532041) baseStart_2532041 baseEnd_2532041 := by
    simpa [prefixWord, tailWord_2532041, baseEnd_2532041] using wordTrace_append hprefix tailTrace_2532041
  have hstable : (prefixWord ++ tailWord_2532041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532041).length < 2 ^ (prefixWord ++ tailWord_2532041).sum := by decide
  have hdescent : baseEnd_2532041 < baseStart_2532041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532042 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_2532042 : Nat := 118140960795 + 2532042 * 2 ^ 59
def prefixEnd_2532042 : Nat := 4983230072969 + 3 ^ 40 * 2532042 * 2
def baseEnd_2532042 : Nat := 1300154583371687607730357

theorem tailTrace_2532042 : CollatzResearch.WordTrace tailWord_2532042 prefixEnd_2532042 1300154583371687607730357 := by
  unfold tailWord_2532042
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087789673212936797633595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61567439128567831460356253 23087789673212936797633595)
  ·
    refine ⟨34631684509819405196450393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23087789673212936797633595 34631684509819405196450393)
    ·
      refine ⟨25973763382364553897337795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34631684509819405196450393 25973763382364553897337795)
      ·
        refine ⟨38960645073546830846006693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25973763382364553897337795 38960645073546830846006693)
        ·
          refine ⟨7305120951290030783626255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38960645073546830846006693 7305120951290030783626255)
          ·
            refine ⟨10957681426935046175439383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305120951290030783626255 10957681426935046175439383)
            ·
              refine ⟨16436522140402569263159075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10957681426935046175439383 16436522140402569263159075)
              ·
                refine ⟨24654783210603853894738613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16436522140402569263159075 24654783210603853894738613)
                ·
                  refine ⟨2311385925994111302631745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24654783210603853894738613 2311385925994111302631745)
                  ·
                    refine ⟨1733539444495583476973809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2311385925994111302631745 1733539444495583476973809)
                    ·
                      refine ⟨1300154583371687607730357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733539444495583476973809 1300154583371687607730357)
                      ·
                        rfl

theorem cell23_2532042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_2532042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532042 prefixEnd_2532042 := by exact prefixLift 2532042
  have htrace : WordTrace (prefixWord ++ tailWord_2532042) baseStart_2532042 baseEnd_2532042 := by
    simpa [prefixWord, tailWord_2532042, baseEnd_2532042] using wordTrace_append hprefix tailTrace_2532042
  have hstable : (prefixWord ++ tailWord_2532042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532042).length < 2 ^ (prefixWord ++ tailWord_2532042).sum := by decide
  have hdescent : baseEnd_2532042 < baseStart_2532042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532092 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_2532092 : Nat := 118140960795 + 2532092 * 2 ^ 59
def prefixEnd_2532092 : Nat := 4983230072969 + 3 ^ 40 * 2532092 * 2
def baseEnd_2532092 : Nat := 1300180257404412412105127

theorem tailTrace_2532092 : CollatzResearch.WordTrace tailWord_2532092 prefixEnd_2532092 1300180257404412412105127 := by
  unfold tailWord_2532092
  simp only [CollatzResearch.WordTrace]
  refine ⟨46176491171335302864927265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61568654895113737153236353 46176491171335302864927265)
  ·
    refine ⟨34632368378501477148695449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46176491171335302864927265 34632368378501477148695449)
    ·
      refine ⟨25974276283876107861521587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34632368378501477148695449 25974276283876107861521587)
      ·
        refine ⟨38961414425814161792282381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25974276283876107861521587 38961414425814161792282381)
        ·
          refine ⟨14610530409680310672105893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38961414425814161792282381 14610530409680310672105893)
          ·
            refine ⟨2739474451815058251019855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14610530409680310672105893 2739474451815058251019855)
            ·
              refine ⟨4109211677722587376529783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739474451815058251019855 4109211677722587376529783)
              ·
                refine ⟨6163817516583881064794675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109211677722587376529783 6163817516583881064794675)
                ·
                  refine ⟨9245726274875821597192013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6163817516583881064794675 9245726274875821597192013)
                  ·
                    refine ⟨3467147353078433098947005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9245726274875821597192013 3467147353078433098947005)
                    ·
                      refine ⟨1300180257404412412105127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3467147353078433098947005 1300180257404412412105127)
                      ·
                        rfl

theorem cell23_2532092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_2532092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532092 prefixEnd_2532092 := by exact prefixLift 2532092
  have htrace : WordTrace (prefixWord ++ tailWord_2532092) baseStart_2532092 baseEnd_2532092 := by
    simpa [prefixWord, tailWord_2532092, baseEnd_2532092] using wordTrace_append hprefix tailTrace_2532092
  have hstable : (prefixWord ++ tailWord_2532092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532092).length < 2 ^ (prefixWord ++ tailWord_2532092).sum := by decide
  have hdescent : baseEnd_2532092 < baseStart_2532092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532115 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 3, 4, 2]
def baseStart_2532115 : Nat := 118140960795 + 2532115 * 2 ^ 59
def prefixEnd_2532115 : Nat := 4983230072969 + 3 ^ 40 * 2532115 * 2
def baseEnd_2532115 : Nat := 1300192067459465822117521

theorem tailTrace_2532115 : CollatzResearch.WordTrace tailWord_2532115 prefixEnd_2532115 1300192067459465822117521 := by
  unfold tailWord_2532115
  simp only [CollatzResearch.WordTrace]
  refine ⟨92353821221587280657941799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61569214147724853771961199 92353821221587280657941799)
  ·
    refine ⟨138530731832380920986912699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92353821221587280657941799 138530731832380920986912699)
    ·
      refine ⟨207796097748571381480369049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138530731832380920986912699 207796097748571381480369049)
      ·
        refine ⟨155847073311428536110276787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207796097748571381480369049 155847073311428536110276787)
        ·
          refine ⟨233770609967142804165415181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155847073311428536110276787 233770609967142804165415181)
          ·
            refine ⟨87663978737678551562030693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233770609967142804165415181 87663978737678551562030693)
            ·
              refine ⟨16436996013314728417880755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87663978737678551562030693 16436996013314728417880755)
              ·
                refine ⟨24655494019972092626821133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16436996013314728417880755 24655494019972092626821133)
                ·
                  refine ⟨9245810257489534735057925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24655494019972092626821133 9245810257489534735057925)
                  ·
                    refine ⟨1733589423279287762823361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9245810257489534735057925 1733589423279287762823361)
                    ·
                      refine ⟨1300192067459465822117521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733589423279287762823361 1300192067459465822117521)
                      ·
                        rfl

theorem cell23_2532115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 4, 2].length) (baseStart_2532115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532115 prefixEnd_2532115 := by exact prefixLift 2532115
  have htrace : WordTrace (prefixWord ++ tailWord_2532115) baseStart_2532115 baseEnd_2532115 := by
    simpa [prefixWord, tailWord_2532115, baseEnd_2532115] using wordTrace_append hprefix tailTrace_2532115
  have hstable : (prefixWord ++ tailWord_2532115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532115).length < 2 ^ (prefixWord ++ tailWord_2532115).sum := by decide
  have hdescent : baseEnd_2532115 < baseStart_2532115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532175 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 6, 5, 2]
def baseStart_2532175 : Nat := 118140960795 + 2532175 * 2 ^ 59
def prefixEnd_2532175 : Nat := 4983230072969 + 3 ^ 40 * 2532175 * 2
def baseEnd_2532175 : Nat := 1300222876298735587367245

theorem tailTrace_2532175 : CollatzResearch.WordTrace tailWord_2532175 prefixEnd_2532175 1300222876298735587367245 := by
  unfold tailWord_2532175
  simp only [CollatzResearch.WordTrace]
  refine ⟨92356009601369910905125979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61570673067579940603417319 92356009601369910905125979)
  ·
    refine ⟨138534014402054866357688969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92356009601369910905125979 138534014402054866357688969)
    ·
      refine ⟨103900510801541149768266727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138534014402054866357688969 103900510801541149768266727)
      ·
        refine ⟨155850766202311724652400091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103900510801541149768266727 155850766202311724652400091)
        ·
          refine ⟨233776149303467586978600137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155850766202311724652400091 233776149303467586978600137)
          ·
            refine ⟨175332111977600690233950103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233776149303467586978600137 175332111977600690233950103)
            ·
              refine ⟨262998167966401035350925155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175332111977600690233950103 262998167966401035350925155)
              ·
                refine ⟨394497251949601553026387733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262998167966401035350925155 394497251949601553026387733)
                ·
                  refine ⟨18492058685137572798111925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 394497251949601553026387733 18492058685137572798111925)
                  ·
                    refine ⟨1733630501731647449822993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18492058685137572798111925 1733630501731647449822993)
                    ·
                      refine ⟨1300222876298735587367245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733630501731647449822993 1300222876298735587367245)
                      ·
                        rfl

theorem cell23_2532175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 5, 2].length) (baseStart_2532175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532175 prefixEnd_2532175 := by exact prefixLift 2532175
  have htrace : WordTrace (prefixWord ++ tailWord_2532175) baseStart_2532175 baseEnd_2532175 := by
    simpa [prefixWord, tailWord_2532175, baseEnd_2532175] using wordTrace_append hprefix tailTrace_2532175
  have hstable : (prefixWord ++ tailWord_2532175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532175).length < 2 ^ (prefixWord ++ tailWord_2532175).sum := by decide
  have hdescent : baseEnd_2532175 < baseStart_2532175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532185 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 2, 5]
def baseStart_2532185 : Nat := 118140960795 + 2532185 * 2 ^ 59
def prefixEnd_2532185 : Nat := 4983230072969 + 3 ^ 40 * 2532185 * 2
def baseEnd_2532185 : Nat := 433409337035093516080733

theorem tailTrace_2532185 : CollatzResearch.WordTrace tailWord_2532185 prefixEnd_2532185 433409337035093516080733 := by
  unfold tailWord_2532185
  simp only [CollatzResearch.WordTrace]
  refine ⟨92356374331333682612990009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61570916220889121741993339 92356374331333682612990009)
  ·
    refine ⟨69267280748500261959742507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92356374331333682612990009 69267280748500261959742507)
    ·
      refine ⟨103900921122750392939613761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69267280748500261959742507 103900921122750392939613761)
      ·
        refine ⟨77925690842062794704710321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103900921122750392939613761 77925690842062794704710321)
        ·
          refine ⟨58444268131547096028532741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77925690842062794704710321 58444268131547096028532741)
          ·
            refine ⟨10958300274665080505349889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58444268131547096028532741 10958300274665080505349889)
            ·
              refine ⟨8218725205998810379012417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10958300274665080505349889 8218725205998810379012417)
              ·
                refine ⟨6164043904499107784259313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8218725205998810379012417 6164043904499107784259313)
                ·
                  refine ⟨4623032928374330838194485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6164043904499107784259313 4623032928374330838194485)
                  ·
                    refine ⟨433409337035093516080733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4623032928374330838194485 433409337035093516080733)
                    ·
                      rfl

theorem cell23_2532185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_2532185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532185 prefixEnd_2532185 := by exact prefixLift 2532185
  have htrace : WordTrace (prefixWord ++ tailWord_2532185) baseStart_2532185 baseEnd_2532185 := by
    simpa [prefixWord, tailWord_2532185, baseEnd_2532185] using wordTrace_append hprefix tailTrace_2532185
  have hstable : (prefixWord ++ tailWord_2532185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532185).length < 2 ^ (prefixWord ++ tailWord_2532185).sum := by decide
  have hdescent : baseEnd_2532185 < baseStart_2532185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532195 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 5]
def baseStart_2532195 : Nat := 118140960795 + 2532195 * 2 ^ 59
def prefixEnd_2532195 : Nat := 4983230072969 + 3 ^ 40 * 2532195 * 2
def baseEnd_2532195 : Nat := 1300233145911825509117153

theorem tailTrace_2532195 : CollatzResearch.WordTrace tailWord_2532195 prefixEnd_2532195 1300233145911825509117153 := by
  unfold tailWord_2532195
  simp only [CollatzResearch.WordTrace]
  refine ⟨92356739061297454320854039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61571159374198302880569359 92356739061297454320854039)
  ·
    refine ⟨138535108591946181481281059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92356739061297454320854039 138535108591946181481281059)
    ·
      refine ⟨207802662887919272221921589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138535108591946181481281059 207802662887919272221921589)
      ·
        refine ⟨19481499645742431770805149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207802662887919272221921589 19481499645742431770805149)
        ·
          refine ⟨7305562367153411914051931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19481499645742431770805149 7305562367153411914051931)
          ·
            refine ⟨10958343550730117871077897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305562367153411914051931 10958343550730117871077897)
            ·
              refine ⟨8218757663047588403308423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10958343550730117871077897 8218757663047588403308423)
              ·
                refine ⟨12328136494571382604962635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8218757663047588403308423 12328136494571382604962635)
                ·
                  refine ⟨18492204741857073907443953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12328136494571382604962635 18492204741857073907443953)
                  ·
                    refine ⟨13869153556392805430582965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18492204741857073907443953 13869153556392805430582965)
                    ·
                      refine ⟨1300233145911825509117153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13869153556392805430582965 1300233145911825509117153)
                      ·
                        rfl

theorem cell23_2532195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_2532195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532195 prefixEnd_2532195 := by exact prefixLift 2532195
  have htrace : WordTrace (prefixWord ++ tailWord_2532195) baseStart_2532195 baseEnd_2532195 := by
    simpa [prefixWord, tailWord_2532195, baseEnd_2532195] using wordTrace_append hprefix tailTrace_2532195
  have hstable : (prefixWord ++ tailWord_2532195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532195).length < 2 ^ (prefixWord ++ tailWord_2532195).sum := by decide
  have hdescent : baseEnd_2532195 < baseStart_2532195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532205 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2532205 : Nat := 118140960795 + 2532205 * 2 ^ 59
def prefixEnd_2532205 : Nat := 4983230072969 + 3 ^ 40 * 2532205 * 2
def baseEnd_2532205 : Nat := 1300238280718370469992107

theorem tailTrace_2532205 : CollatzResearch.WordTrace tailWord_2532205 prefixEnd_2532205 1300238280718370469992107 := by
  unfold tailWord_2532205
  simp only [CollatzResearch.WordTrace]
  refine ⟨92357103791261226028718069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61571402527507484019145379 92357103791261226028718069)
  ·
    refine ⟨8658478480430739940192319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92357103791261226028718069 8658478480430739940192319)
    ·
      refine ⟨12987717720646109910288479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8658478480430739940192319 12987717720646109910288479)
      ·
        refine ⟨19481576580969164865432719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12987717720646109910288479 19481576580969164865432719)
        ·
          refine ⟨29222364871453747298149079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19481576580969164865432719 29222364871453747298149079)
          ·
            refine ⟨43833547307180620947223619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29222364871453747298149079 43833547307180620947223619)
            ·
              refine ⟨65750320960770931420835429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43833547307180620947223619 65750320960770931420835429)
              ·
                refine ⟨12328185180144549641406643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65750320960770931420835429 12328185180144549641406643)
                ·
                  refine ⟨18492277770216824462109965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12328185180144549641406643 18492277770216824462109965)
                  ·
                    refine ⟨6934604163831309173291237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18492277770216824462109965 6934604163831309173291237)
                    ·
                      refine ⟨1300238280718370469992107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6934604163831309173291237 1300238280718370469992107)
                      ·
                        rfl

theorem cell23_2532205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2532205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532205 prefixEnd_2532205 := by exact prefixLift 2532205
  have htrace : WordTrace (prefixWord ++ tailWord_2532205) baseStart_2532205 baseEnd_2532205 := by
    simpa [prefixWord, tailWord_2532205, baseEnd_2532205] using wordTrace_append hprefix tailTrace_2532205
  have hstable : (prefixWord ++ tailWord_2532205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532205).length < 2 ^ (prefixWord ++ tailWord_2532205).sum := by decide
  have hdescent : baseEnd_2532205 < baseStart_2532205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532245 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 8]
def baseStart_2532245 : Nat := 118140960795 + 2532245 * 2 ^ 59
def prefixEnd_2532245 : Nat := 4983230072969 + 3 ^ 40 * 2532245 * 2
def baseEnd_2532245 : Nat := 144473202216061145943547

theorem tailTrace_2532245 : CollatzResearch.WordTrace tailWord_2532245 prefixEnd_2532245 144473202216061145943547 := by
  unfold tailWord_2532245
  simp only [CollatzResearch.WordTrace]
  refine ⟨92358562711116312860174189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61572375140744208573449459 92358562711116312860174189)
  ·
    refine ⟨34634461016668617322565321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92358562711116312860174189 34634461016668617322565321)
    ·
      refine ⟨25975845762501462991923991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34634461016668617322565321 25975845762501462991923991)
      ·
        refine ⟨38963768643752194487885987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25975845762501462991923991 38963768643752194487885987)
        ·
          refine ⟨58445652965628291731828981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38963768643752194487885987 58445652965628291731828981)
          ·
            refine ⟨5479279965527652349858967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58445652965628291731828981 5479279965527652349858967)
            ·
              refine ⟨8218919948291478524788451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479279965527652349858967 8218919948291478524788451)
              ·
                refine ⟨12328379922437217787182677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8218919948291478524788451 12328379922437217787182677)
                ·
                  refine ⟨144473202216061145943547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12328379922437217787182677 144473202216061145943547)
                  ·
                    rfl

theorem cell23_2532245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_2532245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532245 prefixEnd_2532245 := by exact prefixLift 2532245
  have htrace : WordTrace (prefixWord ++ tailWord_2532245) baseStart_2532245 baseEnd_2532245 := by
    simpa [prefixWord, tailWord_2532245, baseEnd_2532245] using wordTrace_append hprefix tailTrace_2532245
  have hstable : (prefixWord ++ tailWord_2532245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532245).length < 2 ^ (prefixWord ++ tailWord_2532245).sum := by decide
  have hdescent : baseEnd_2532245 < baseStart_2532245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532282 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2]
def baseStart_2532282 : Nat := 118140960795 + 2532282 * 2 ^ 59
def prefixEnd_2532282 : Nat := 4983230072969 + 3 ^ 40 * 2532282 * 2
def baseEnd_2532282 : Nat := 1300277818728766668729253

theorem tailTrace_2532282 : CollatzResearch.WordTrace tailWord_2532282 prefixEnd_2532282 1300277818728766668729253 := by
  unfold tailWord_2532282
  simp only [CollatzResearch.WordTrace]
  refine ⟨23089978052995567044817775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61573274807988178786180733 23089978052995567044817775)
  ·
    refine ⟨34634967079493350567226663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23089978052995567044817775 34634967079493350567226663)
    ·
      refine ⟨51952450619240025850839995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34634967079493350567226663 51952450619240025850839995)
      ·
        refine ⟨77928675928860038776259993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51952450619240025850839995 77928675928860038776259993)
        ·
          refine ⟨58446506946645029082194995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77928675928860038776259993 58446506946645029082194995)
          ·
            refine ⟨87669760419967543623292493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58446506946645029082194995 87669760419967543623292493)
            ·
              refine ⟨32876160157487828858734685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87669760419967543623292493 32876160157487828858734685)
              ·
                refine ⟨12328560059057935822025507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32876160157487828858734685 12328560059057935822025507)
                ·
                  refine ⟨18492840088586903733038261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12328560059057935822025507 18492840088586903733038261)
                  ·
                    refine ⟨1733703758305022224972337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18492840088586903733038261 1733703758305022224972337)
                    ·
                      refine ⟨1300277818728766668729253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733703758305022224972337 1300277818728766668729253)
                      ·
                        rfl

theorem cell23_2532282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_2532282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532282 prefixEnd_2532282 := by exact prefixLift 2532282
  have htrace : WordTrace (prefixWord ++ tailWord_2532282) baseStart_2532282 baseEnd_2532282 := by
    simpa [prefixWord, tailWord_2532282, baseEnd_2532282] using wordTrace_append hprefix tailTrace_2532282
  have hstable : (prefixWord ++ tailWord_2532282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532282).length < 2 ^ (prefixWord ++ tailWord_2532282).sum := by decide
  have hdescent : baseEnd_2532282 < baseStart_2532282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532299 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 2, 3, 2]
def baseStart_2532299 : Nat := 118140960795 + 2532299 * 2 ^ 59
def prefixEnd_2532299 : Nat := 4983230072969 + 3 ^ 40 * 2532299 * 2
def baseEnd_2532299 : Nat := 1300286547899893102216675

theorem tailTrace_2532299 : CollatzResearch.WordTrace tailWord_2532299 prefixEnd_2532299 1300286547899893102216675 := by
  unfold tailWord_2532299
  simp only [CollatzResearch.WordTrace]
  refine ⟨92360532252920680082639951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61573688168613786721759967 92360532252920680082639951)
  ·
    refine ⟨138540798379381020123959927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92360532252920680082639951 138540798379381020123959927)
    ·
      refine ⟨207811197569071530185939891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138540798379381020123959927 207811197569071530185939891)
      ·
        refine ⟨311716796353607295278909837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207811197569071530185939891 311716796353607295278909837)
        ·
          refine ⟨116893798632602735729591189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311716796353607295278909837 116893798632602735729591189)
          ·
            refine ⟨5479396810903253237324587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116893798632602735729591189 5479396810903253237324587)
            ·
              refine ⟨8219095216354879855986881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479396810903253237324587 8219095216354879855986881)
              ·
                refine ⟨6164321412266159891990161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8219095216354879855986881 6164321412266159891990161)
                ·
                  refine ⟨4623241059199619918992621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6164321412266159891990161 4623241059199619918992621)
                  ·
                    refine ⟨1733715397199857469622233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4623241059199619918992621 1733715397199857469622233)
                    ·
                      refine ⟨1300286547899893102216675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733715397199857469622233 1300286547899893102216675)
                      ·
                        rfl

theorem cell23_2532299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 3, 2].length) (baseStart_2532299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532299 prefixEnd_2532299 := by exact prefixLift 2532299
  have htrace : WordTrace (prefixWord ++ tailWord_2532299) baseStart_2532299 baseEnd_2532299 := by
    simpa [prefixWord, tailWord_2532299, baseEnd_2532299] using wordTrace_append hprefix tailTrace_2532299
  have hstable : (prefixWord ++ tailWord_2532299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532299).length < 2 ^ (prefixWord ++ tailWord_2532299).sum := by decide
  have hdescent : baseEnd_2532299 < baseStart_2532299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532306 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2532306 : Nat := 118140960795 + 2532306 * 2 ^ 59
def prefixEnd_2532306 : Nat := 4983230072969 + 3 ^ 40 * 2532306 * 2
def baseEnd_2532306 : Nat := 1300290142264474574829143

theorem tailTrace_2532306 : CollatzResearch.WordTrace tailWord_2532306 prefixEnd_2532306 1300290142264474574829143 := by
  unfold tailWord_2532306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23090196890973830069536193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61573858375930213518763181 23090196890973830069536193)
  ·
    refine ⟨17317647668230372552152145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23090196890973830069536193 17317647668230372552152145)
    ·
      refine ⟨12988235751172779414114109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17317647668230372552152145 12988235751172779414114109)
      ·
        refine ⟨4870588406689792280292791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12988235751172779414114109 4870588406689792280292791)
        ·
          refine ⟨7305882610034688420439187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870588406689792280292791 7305882610034688420439187)
          ·
            refine ⟨10958823915052032630658781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305882610034688420439187 10958823915052032630658781)
            ·
              refine ⟨4109558968144512236497043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10958823915052032630658781 4109558968144512236497043)
              ·
                refine ⟨6164338452216768354745565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109558968144512236497043 6164338452216768354745565)
                ·
                  refine ⟨2311626919581288133029587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6164338452216768354745565 2311626919581288133029587)
                  ·
                    refine ⟨3467440379371932199544381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311626919581288133029587 3467440379371932199544381)
                    ·
                      refine ⟨1300290142264474574829143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3467440379371932199544381 1300290142264474574829143)
                      ·
                        rfl

theorem cell23_2532306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2532306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532306 prefixEnd_2532306 := by exact prefixLift 2532306
  have htrace : WordTrace (prefixWord ++ tailWord_2532306) baseStart_2532306 baseEnd_2532306 := by
    simpa [prefixWord, tailWord_2532306, baseEnd_2532306] using wordTrace_append hprefix tailTrace_2532306
  have hstable : (prefixWord ++ tailWord_2532306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532306).length < 2 ^ (prefixWord ++ tailWord_2532306).sum := by decide
  have hdescent : baseEnd_2532306 < baseStart_2532306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532335 : List Nat := [1, 1, 2, 1, 4, 3, 2, 9]
def baseStart_2532335 : Nat := 118140960795 + 2532335 * 2 ^ 59
def prefixEnd_2532335 : Nat := 4983230072969 + 3 ^ 40 * 2532335 * 2
def baseEnd_2532335 : Nat := 48159445674202035606167

theorem tailTrace_2532335 : CollatzResearch.WordTrace tailWord_2532335 prefixEnd_2532335 48159445674202035606167 := by
  unfold tailWord_2532335
  simp only [CollatzResearch.WordTrace]
  refine ⟨92361845280790258230950459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61574563520526838820633639 92361845280790258230950459)
  ·
    refine ⟨138542767921185387346425689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92361845280790258230950459 138542767921185387346425689)
    ·
      refine ⟨103907075940889040509819267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138542767921185387346425689 103907075940889040509819267)
      ·
        refine ⟨155860613911333560764728901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103907075940889040509819267 155860613911333560764728901)
        ·
          refine ⟨29223865108375042643386669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155860613911333560764728901 29223865108375042643386669)
          ·
            refine ⟨10958949415640640991270001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29223865108375042643386669 10958949415640640991270001)
            ·
              refine ⟨8219212061730480743452501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10958949415640640991270001 8219212061730480743452501)
              ·
                refine ⟨48159445674202035606167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8219212061730480743452501 48159445674202035606167)
                ·
                  rfl

theorem cell23_2532335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 9].length) (baseStart_2532335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532335 prefixEnd_2532335 := by exact prefixLift 2532335
  have htrace : WordTrace (prefixWord ++ tailWord_2532335) baseStart_2532335 baseEnd_2532335 := by
    simpa [prefixWord, tailWord_2532335, baseEnd_2532335] using wordTrace_append hprefix tailTrace_2532335
  have hstable : (prefixWord ++ tailWord_2532335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532335).length < 2 ^ (prefixWord ++ tailWord_2532335).sum := by decide
  have hdescent : baseEnd_2532335 < baseStart_2532335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532363 : List Nat := [1, 1, 1, 1, 6, 3, 1, 4, 1, 2, 2]
def baseStart_2532363 : Nat := 118140960795 + 2532363 * 2 ^ 59
def prefixEnd_2532363 : Nat := 4983230072969 + 3 ^ 40 * 2532363 * 2
def baseEnd_2532363 : Nat := 1300319410661780851816381

theorem tailTrace_2532363 : CollatzResearch.WordTrace tailWord_2532363 prefixEnd_2532363 1300319410661780851816381 := by
  unfold tailWord_2532363
  simp only [CollatzResearch.WordTrace]
  refine ⟨92362866524688819012969743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61575244349792546008646495 92362866524688819012969743)
  ·
    refine ⟨138544299787033228519454615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92362866524688819012969743 138544299787033228519454615)
    ·
      refine ⟨207816449680549842779181923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138544299787033228519454615 207816449680549842779181923)
      ·
        refine ⟨311724674520824764168772885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207816449680549842779181923 311724674520824764168772885)
        ·
          refine ⟨14612094118163660820411229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 311724674520824764168772885 14612094118163660820411229)
          ·
            refine ⟨5479535294311372807654211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14612094118163660820411229 5479535294311372807654211)
            ·
              refine ⟨8219302941467059211481317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479535294311372807654211 8219302941467059211481317)
              ·
                refine ⟨1541119301525073602152747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8219302941467059211481317 1541119301525073602152747)
                ·
                  refine ⟨2311678952287610403229121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541119301525073602152747 2311678952287610403229121)
                  ·
                    refine ⟨1733759214215707802421841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2311678952287610403229121 1733759214215707802421841)
                    ·
                      refine ⟨1300319410661780851816381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733759214215707802421841 1300319410661780851816381)
                      ·
                        rfl

theorem cell23_2532363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 2, 2].length) (baseStart_2532363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532363 prefixEnd_2532363 := by exact prefixLift 2532363
  have htrace : WordTrace (prefixWord ++ tailWord_2532363) baseStart_2532363 baseEnd_2532363 := by
    simpa [prefixWord, tailWord_2532363, baseEnd_2532363] using wordTrace_append hprefix tailTrace_2532363
  have hstable : (prefixWord ++ tailWord_2532363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532363).length < 2 ^ (prefixWord ++ tailWord_2532363).sum := by decide
  have hdescent : baseEnd_2532363 < baseStart_2532363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532389 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 3, 3, 2]
def baseStart_2532389 : Nat := 118140960795 + 2532389 * 2 ^ 59
def prefixEnd_2532389 : Nat := 4983230072969 + 3 ^ 40 * 2532389 * 2
def baseEnd_2532389 : Nat := 1300332761158797750091261

theorem tailTrace_2532389 : CollatzResearch.WordTrace tailWord_2532389 prefixEnd_2532389 1300332761158797750091261 := by
  unfold tailWord_2532389
  simp only [CollatzResearch.WordTrace]
  refine ⟨92363814822594625453416221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61575876548396416968944147 92363814822594625453416221)
  ·
    refine ⟨34636430558472984545031083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92363814822594625453416221 34636430558472984545031083)
    ·
      refine ⟨51954645837709476817546625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34636430558472984545031083 51954645837709476817546625)
      ·
        refine ⟨38965984378282107613159969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51954645837709476817546625 38965984378282107613159969)
        ·
          refine ⟨29224488283711580709869977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38965984378282107613159969 29224488283711580709869977)
          ·
            refine ⟨21918366212783685532402483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29224488283711580709869977 21918366212783685532402483)
            ·
              refine ⟨32877549319175528298603725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21918366212783685532402483 32877549319175528298603725)
              ·
                refine ⟨12329080994690823111976397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32877549319175528298603725 12329080994690823111976397)
                ·
                  refine ⟨4623405373009058666991149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12329080994690823111976397 4623405373009058666991149)
                  ·
                    refine ⟨1733777014878397000121681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4623405373009058666991149 1733777014878397000121681)
                    ·
                      refine ⟨1300332761158797750091261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733777014878397000121681 1300332761158797750091261)
                      ·
                        rfl

theorem cell23_2532389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_2532389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532389 prefixEnd_2532389 := by exact prefixLift 2532389
  have htrace : WordTrace (prefixWord ++ tailWord_2532389) baseStart_2532389 baseEnd_2532389 := by
    simpa [prefixWord, tailWord_2532389, baseEnd_2532389] using wordTrace_append hprefix tailTrace_2532389
  have hstable : (prefixWord ++ tailWord_2532389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532389).length < 2 ^ (prefixWord ++ tailWord_2532389).sum := by decide
  have hdescent : baseEnd_2532389 < baseStart_2532389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532395 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 1, 8]
def baseStart_2532395 : Nat := 118140960795 + 2532395 * 2 ^ 59
def prefixEnd_2532395 : Nat := 4983230072969 + 3 ^ 40 * 2532395 * 2
def baseEnd_2532395 : Nat := 433445280680908242205411

theorem tailTrace_2532395 : CollatzResearch.WordTrace tailWord_2532395 prefixEnd_2532395 433445280680908242205411 := by
  unfold tailWord_2532395
  simp only [CollatzResearch.WordTrace]
  refine ⟨92364033660572888478134639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61576022440381925652089759 92364033660572888478134639)
  ·
    refine ⟨138546050490859332717201959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92364033660572888478134639 138546050490859332717201959)
    ·
      refine ⟨207819075736288999075802939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138546050490859332717201959 207819075736288999075802939)
      ·
        refine ⟨311728613604433498613704409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207819075736288999075802939 311728613604433498613704409)
        ·
          refine ⟨233796460203325123960278307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311728613604433498613704409 233796460203325123960278307)
          ·
            refine ⟨350694690304987685940417461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233796460203325123960278307 350694690304987685940417461)
            ·
              refine ⟨32877627216092595556914137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350694690304987685940417461 32877627216092595556914137)
              ·
                refine ⟨24658220412069446667685603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32877627216092595556914137 24658220412069446667685603)
                ·
                  refine ⟨36987330618104170001528405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24658220412069446667685603 36987330618104170001528405)
                  ·
                    refine ⟨433445280680908242205411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36987330618104170001528405 433445280680908242205411)
                    ·
                      rfl

theorem cell23_2532395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 8].length) (baseStart_2532395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532395 prefixEnd_2532395 := by exact prefixLift 2532395
  have htrace : WordTrace (prefixWord ++ tailWord_2532395) baseStart_2532395 baseEnd_2532395 := by
    simpa [prefixWord, tailWord_2532395, baseEnd_2532395] using wordTrace_append hprefix tailTrace_2532395
  have hstable : (prefixWord ++ tailWord_2532395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532395).length < 2 ^ (prefixWord ++ tailWord_2532395).sum := by decide
  have hdescent : baseEnd_2532395 < baseStart_2532395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532412 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_2532412 : Nat := 118140960795 + 2532412 * 2 ^ 59
def prefixEnd_2532412 : Nat := 4983230072969 + 3 ^ 40 * 2532412 * 2
def baseEnd_2532412 : Nat := 433448190404617053367885

theorem tailTrace_2532412 : CollatzResearch.WordTrace tailWord_2532412 prefixEnd_2532412 433448190404617053367885 := by
  unfold tailWord_2532412
  simp only [CollatzResearch.WordTrace]
  refine ⟨46182326850755650190751745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61576435801007533587668993 46182326850755650190751745)
  ·
    refine ⟨34636745138066737643063809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46182326850755650190751745 34636745138066737643063809)
    ·
      refine ⟨25977558853550053232297857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34636745138066737643063809 25977558853550053232297857)
      ·
        refine ⟨19483169140162539924223393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25977558853550053232297857 19483169140162539924223393)
        ·
          refine ⟨14612376855121904943167545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19483169140162539924223393 14612376855121904943167545)
          ·
            refine ⟨10959282641341428707375659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14612376855121904943167545 10959282641341428707375659)
            ·
              refine ⟨16438923962012143061063489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10959282641341428707375659 16438923962012143061063489)
              ·
                refine ⟨12329192971509107295797617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16438923962012143061063489 12329192971509107295797617)
                ·
                  refine ⟨9246894728631830471848213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12329192971509107295797617 9246894728631830471848213)
                  ·
                    refine ⟨433448190404617053367885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9246894728631830471848213 433448190404617053367885)
                    ·
                      rfl

theorem cell23_2532412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_2532412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532412 prefixEnd_2532412 := by exact prefixLift 2532412
  have htrace : WordTrace (prefixWord ++ tailWord_2532412) baseStart_2532412 baseEnd_2532412 := by
    simpa [prefixWord, tailWord_2532412, baseEnd_2532412] using wordTrace_append hprefix tailTrace_2532412
  have hstable : (prefixWord ++ tailWord_2532412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532412).length < 2 ^ (prefixWord ++ tailWord_2532412).sum := by decide
  have hdescent : baseEnd_2532412 < baseStart_2532412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532413 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2532413 : Nat := 118140960795 + 2532413 * 2 ^ 59
def prefixEnd_2532413 : Nat := 4983230072969 + 3 ^ 40 * 2532413 * 2
def baseEnd_2532413 : Nat := 1300345084694505656191151

theorem tailTrace_2532413 : CollatzResearch.WordTrace tailWord_2532413 prefixEnd_2532413 1300345084694505656191151 := by
  unfold tailWord_2532413
  simp only [CollatzResearch.WordTrace]
  refine ⟨92364690174507677552289893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61576460116338451701526595 92364690174507677552289893)
  ·
    refine ⟨17318379407720189541054355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92364690174507677552289893 17318379407720189541054355)
    ·
      refine ⟨25977569111580284311581533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17318379407720189541054355 25977569111580284311581533)
      ·
        refine ⟨9741588416842606616843075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25977569111580284311581533 9741588416842606616843075)
        ·
          refine ⟨14612382625263909925264613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9741588416842606616843075 14612382625263909925264613)
          ·
            refine ⟨2739821742236983110987115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14612382625263909925264613 2739821742236983110987115)
            ·
              refine ⟨4109732613355474666480673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739821742236983110987115 4109732613355474666480673)
              ·
                refine ⟨3082299460016605999860505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4109732613355474666480673 3082299460016605999860505)
                ·
                  refine ⟨2311724595012454499895379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3082299460016605999860505 2311724595012454499895379)
                  ·
                    refine ⟨3467586892518681749843069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2311724595012454499895379 3467586892518681749843069)
                    ·
                      refine ⟨1300345084694505656191151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3467586892518681749843069 1300345084694505656191151)
                      ·
                        rfl

theorem cell23_2532413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2532413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532413 prefixEnd_2532413 := by exact prefixLift 2532413
  have htrace : WordTrace (prefixWord ++ tailWord_2532413) baseStart_2532413 baseEnd_2532413 := by
    simpa [prefixWord, tailWord_2532413, baseEnd_2532413] using wordTrace_append hprefix tailTrace_2532413
  have hstable : (prefixWord ++ tailWord_2532413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532413).length < 2 ^ (prefixWord ++ tailWord_2532413).sum := by decide
  have hdescent : baseEnd_2532413 < baseStart_2532413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532429 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2532429 : Nat := 118140960795 + 2532429 * 2 ^ 59
def prefixEnd_2532429 : Nat := 4983230072969 + 3 ^ 40 * 2532429 * 2
def baseEnd_2532429 : Nat := 433451100128325864530359

theorem tailTrace_2532429 : CollatzResearch.WordTrace tailWord_2532429 prefixEnd_2532429 433451100128325864530359 := by
  unfold tailWord_2532429
  simp only [CollatzResearch.WordTrace]
  refine ⟨92365273742449712284872341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61576849161633141523248227 92365273742449712284872341)
  ·
    refine ⟨4329622206677330263353391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92365273742449712284872341 4329622206677330263353391)
    ·
      refine ⟨6494433310015995395030087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4329622206677330263353391 6494433310015995395030087)
      ·
        refine ⟨9741649965023993092545131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6494433310015995395030087 9741649965023993092545131)
        ·
          refine ⟨14612474947535989638817697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9741649965023993092545131 14612474947535989638817697)
          ·
            refine ⟨10959356210651992229113273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14612474947535989638817697 10959356210651992229113273)
            ·
              refine ⟨8219517157988994171834955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10959356210651992229113273 8219517157988994171834955)
              ·
                refine ⟨12329275736983491257752433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8219517157988994171834955 12329275736983491257752433)
                ·
                  refine ⟨9246956802737618443314325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12329275736983491257752433 9246956802737618443314325)
                  ·
                    refine ⟨433451100128325864530359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9246956802737618443314325 433451100128325864530359)
                    ·
                      rfl

theorem cell23_2532429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2532429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532429 prefixEnd_2532429 := by exact prefixLift 2532429
  have htrace : WordTrace (prefixWord ++ tailWord_2532429) baseStart_2532429 baseEnd_2532429 := by
    simpa [prefixWord, tailWord_2532429, baseEnd_2532429] using wordTrace_append hprefix tailTrace_2532429
  have hstable : (prefixWord ++ tailWord_2532429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532429).length < 2 ^ (prefixWord ++ tailWord_2532429).sum := by decide
  have hdescent : baseEnd_2532429 < baseStart_2532429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532436 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_2532436 : Nat := 118140960795 + 2532436 * 2 ^ 59
def prefixEnd_2532436 : Nat := 4983230072969 + 3 ^ 40 * 2532436 * 2
def baseEnd_2532436 : Nat := 1300356894749559066203545

theorem tailTrace_2532436 : CollatzResearch.WordTrace tailWord_2532436 prefixEnd_2532436 1300356894749559066203545 := by
  unfold tailWord_2532436
  simp only [CollatzResearch.WordTrace]
  refine ⟨46182764526712176240188581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61577019368949568320251441 46182764526712176240188581)
  ·
    refine ⟨8659268348758533045035359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46182764526712176240188581 8659268348758533045035359)
    ·
      refine ⟨12988902523137799567553039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8659268348758533045035359 12988902523137799567553039)
      ·
        refine ⟨19483353784706699351329559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12988902523137799567553039 19483353784706699351329559)
        ·
          refine ⟨29225030677060049026994339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19483353784706699351329559 29225030677060049026994339)
          ·
            refine ⟨43837546015590073540491509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29225030677060049026994339 43837546015590073540491509)
            ·
              refine ⟨4109769938961569394421079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43837546015590073540491509 4109769938961569394421079)
              ·
                refine ⟨6164654908442354091631619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109769938961569394421079 6164654908442354091631619)
                ·
                  refine ⟨9246982362663531137447429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6164654908442354091631619 9246982362663531137447429)
                  ·
                    refine ⟨1733809192999412088271393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9246982362663531137447429 1733809192999412088271393)
                    ·
                      refine ⟨1300356894749559066203545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1733809192999412088271393 1300356894749559066203545)
                      ·
                        rfl

theorem cell23_2532436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_2532436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532436 prefixEnd_2532436 := by exact prefixLift 2532436
  have htrace : WordTrace (prefixWord ++ tailWord_2532436) baseStart_2532436 baseEnd_2532436 := by
    simpa [prefixWord, tailWord_2532436, baseEnd_2532436] using wordTrace_append hprefix tailTrace_2532436
  have hstable : (prefixWord ++ tailWord_2532436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532436).length < 2 ^ (prefixWord ++ tailWord_2532436).sum := by decide
  have hdescent : baseEnd_2532436 < baseStart_2532436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532456 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2532456 : Nat := 118140960795 + 2532456 * 2 ^ 59
def prefixEnd_2532456 : Nat := 4983230072969 + 3 ^ 40 * 2532456 * 2
def baseEnd_2532456 : Nat := 1300367164362648987953453

theorem tailTrace_2532456 : CollatzResearch.WordTrace tailWord_2532456 prefixEnd_2532456 1300367164362648987953453 := by
  unfold tailWord_2532456
  simp only [CollatzResearch.WordTrace]
  refine ⟨46183129256675947948052611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61577505675567930597403481 46183129256675947948052611)
  ·
    refine ⟨69274693885013921922078917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46183129256675947948052611 69274693885013921922078917)
    ·
      refine ⟨12989005103440110360389797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69274693885013921922078917 12989005103440110360389797)
      ·
        refine ⟨2435438456895020692573087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12989005103440110360389797 2435438456895020692573087)
        ·
          refine ⟨3653157685342531038859631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2435438456895020692573087 3653157685342531038859631)
          ·
            refine ⟨5479736528013796558289447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653157685342531038859631 5479736528013796558289447)
            ·
              refine ⟨8219604792020694837434171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479736528013796558289447 8219604792020694837434171)
              ·
                refine ⟨12329407188031042256151257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8219604792020694837434171 12329407188031042256151257)
                ·
                  refine ⟨9247055391023281692113443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12329407188031042256151257 9247055391023281692113443)
                  ·
                    refine ⟨13870583086534922538170165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9247055391023281692113443 13870583086534922538170165)
                    ·
                      refine ⟨1300367164362648987953453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13870583086534922538170165 1300367164362648987953453)
                      ·
                        rfl

theorem cell23_2532456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2532456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532456 prefixEnd_2532456 := by exact prefixLift 2532456
  have htrace : WordTrace (prefixWord ++ tailWord_2532456) baseStart_2532456 baseEnd_2532456 := by
    simpa [prefixWord, tailWord_2532456, baseEnd_2532456] using wordTrace_append hprefix tailTrace_2532456
  have hstable : (prefixWord ++ tailWord_2532456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532456).length < 2 ^ (prefixWord ++ tailWord_2532456).sum := by decide
  have hdescent : baseEnd_2532456 < baseStart_2532456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532472 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 4, 5]
def baseStart_2532472 : Nat := 118140960795 + 2532472 * 2 ^ 59
def prefixEnd_2532472 : Nat := 4983230072969 + 3 ^ 40 * 2532472 * 2
def baseEnd_2532472 : Nat := 433458460017706975117793

theorem tailTrace_2532472 : CollatzResearch.WordTrace tailWord_2532472 prefixEnd_2532472 433458460017706975117793 := by
  unfold tailWord_2532472
  simp only [CollatzResearch.WordTrace]
  refine ⟨46183421040646965314343835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61577894720862620419125113 46183421040646965314343835)
  ·
    refine ⟨69275131560970447971515753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46183421040646965314343835 69275131560970447971515753)
    ·
      refine ⟨51956348670727835978636815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69275131560970447971515753 51956348670727835978636815)
      ·
        refine ⟨77934523006091753967955223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51956348670727835978636815 77934523006091753967955223)
        ·
          refine ⟨116901784509137630951932835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77934523006091753967955223 116901784509137630951932835)
          ·
            refine ⟨175352676763706446427899253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116901784509137630951932835 175352676763706446427899253)
            ·
              refine ⟨16439313446597479352615555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175352676763706446427899253 16439313446597479352615555)
              ·
                refine ⟨24658970169896219028923333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16439313446597479352615555 24658970169896219028923333)
                ·
                  refine ⟨4623556906855541067923125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24658970169896219028923333 4623556906855541067923125)
                  ·
                    refine ⟨433458460017706975117793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4623556906855541067923125 433458460017706975117793)
                    ·
                      rfl

theorem cell23_2532472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_2532472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532472 prefixEnd_2532472 := by exact prefixLift 2532472
  have htrace : WordTrace (prefixWord ++ tailWord_2532472) baseStart_2532472 baseEnd_2532472 := by
    simpa [prefixWord, tailWord_2532472, baseEnd_2532472] using wordTrace_append hprefix tailTrace_2532472
  have hstable : (prefixWord ++ tailWord_2532472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532472).length < 2 ^ (prefixWord ++ tailWord_2532472).sum := by decide
  have hdescent : baseEnd_2532472 < baseStart_2532472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532476 : List Nat := [2, 2, 2, 1, 1, 3, 5, 2, 5]
def baseStart_2532476 : Nat := 118140960795 + 2532476 * 2 ^ 59
def prefixEnd_2532476 : Nat := 4983230072969 + 3 ^ 40 * 2532476 * 2
def baseEnd_2532476 : Nat := 144486381552859878855929

theorem tailTrace_2532476 : CollatzResearch.WordTrace tailWord_2532476 prefixEnd_2532476 144486381552859878855929 := by
  unfold tailWord_2532476
  simp only [CollatzResearch.WordTrace]
  refine ⟨46183493986639719655916641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61577991982186292874555521 46183493986639719655916641)
  ·
    refine ⟨34637620489979789741937481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46183493986639719655916641 34637620489979789741937481)
    ·
      refine ⟨25978215367484842306453111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34637620489979789741937481 25978215367484842306453111)
      ·
        refine ⟨38967323051227263459679667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25978215367484842306453111 38967323051227263459679667)
        ·
          refine ⟨58450984576840895189519501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38967323051227263459679667 58450984576840895189519501)
          ·
            refine ⟨21919119216315335696069813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58450984576840895189519501 21919119216315335696069813)
            ·
              refine ⟨2054917426529562721506545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21919119216315335696069813 2054917426529562721506545)
              ·
                refine ⟨1541188069897172041129909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054917426529562721506545 1541188069897172041129909)
                ·
                  refine ⟨144486381552859878855929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1541188069897172041129909 144486381552859878855929)
                  ·
                    rfl

theorem cell23_2532476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_2532476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532476 prefixEnd_2532476 := by exact prefixLift 2532476
  have htrace : WordTrace (prefixWord ++ tailWord_2532476) baseStart_2532476 baseEnd_2532476 := by
    simpa [prefixWord, tailWord_2532476, baseEnd_2532476] using wordTrace_append hprefix tailTrace_2532476
  have hstable : (prefixWord ++ tailWord_2532476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532476).length < 2 ^ (prefixWord ++ tailWord_2532476).sum := by decide
  have hdescent : baseEnd_2532476 < baseStart_2532476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532492 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2532492 : Nat := 118140960795 + 2532492 * 2 ^ 59
def prefixEnd_2532492 : Nat := 4983230072969 + 3 ^ 40 * 2532492 * 2
def baseEnd_2532492 : Nat := 1300385649666210847103287

theorem tailTrace_2532492 : CollatzResearch.WordTrace tailWord_2532492 prefixEnd_2532492 1300385649666210847103287 := by
  unfold tailWord_2532492
  simp only [CollatzResearch.WordTrace]
  refine ⟨46183785770610737022207865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61578381027480982696277153 46183785770610737022207865)
  ·
    refine ⟨34637839327958052766655899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46183785770610737022207865 34637839327958052766655899)
    ·
      refine ⟨51956758991937079149983849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34637839327958052766655899 51956758991937079149983849)
      ·
        refine ⟨38967569243952809362487887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51956758991937079149983849 38967569243952809362487887)
        ·
          refine ⟨58451353865929214043731831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38967569243952809362487887 58451353865929214043731831)
          ·
            refine ⟨87677030798893821065597747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58451353865929214043731831 87677030798893821065597747)
            ·
              refine ⟨131515546198340731598396621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87677030798893821065597747 131515546198340731598396621)
              ·
                refine ⟨49318329824377774349398733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131515546198340731598396621 49318329824377774349398733)
                ·
                  refine ⟨18494373684141665381024525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49318329824377774349398733 18494373684141665381024525)
                  ·
                    refine ⟨6935390131553124517884197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18494373684141665381024525 6935390131553124517884197)
                    ·
                      refine ⟨1300385649666210847103287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6935390131553124517884197 1300385649666210847103287)
                      ·
                        rfl

theorem cell23_2532492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2532492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532492 prefixEnd_2532492 := by exact prefixLift 2532492
  have htrace : WordTrace (prefixWord ++ tailWord_2532492) baseStart_2532492 baseEnd_2532492 := by
    simpa [prefixWord, tailWord_2532492, baseEnd_2532492] using wordTrace_append hprefix tailTrace_2532492
  have hstable : (prefixWord ++ tailWord_2532492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532492).length < 2 ^ (prefixWord ++ tailWord_2532492).sum := by decide
  have hdescent : baseEnd_2532492 < baseStart_2532492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532506 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_2532506 : Nat := 118140960795 + 2532506 * 2 ^ 59
def prefixEnd_2532506 : Nat := 4983230072969 + 3 ^ 40 * 2532506 * 2
def baseEnd_2532506 : Nat := 433464279465124597442741

theorem tailTrace_2532506 : CollatzResearch.WordTrace tailWord_2532506 prefixEnd_2532506 433464279465124597442741 := by
  unfold tailWord_2532506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23092020540792688608856343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61578721442113836290283581 23092020540792688608856343)
  ·
    refine ⟨34638030811189032913284515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23092020540792688608856343 34638030811189032913284515)
    ·
      refine ⟨51957046216783549369926773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34638030811189032913284515 51957046216783549369926773)
      ·
        refine ⟨4870973082823457753430635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51957046216783549369926773 4870973082823457753430635)
        ·
          refine ⟨7306459624235186630145953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4870973082823457753430635 7306459624235186630145953)
          ·
            refine ⟨5479844718176389972609465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7306459624235186630145953 5479844718176389972609465)
            ·
              refine ⟨4109883538632292479457099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5479844718176389972609465 4109883538632292479457099)
              ·
                refine ⟨6164825307948438719185649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109883538632292479457099 6164825307948438719185649)
                ·
                  refine ⟨4623618980961329039389237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6164825307948438719185649 4623618980961329039389237)
                  ·
                    refine ⟨433464279465124597442741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4623618980961329039389237 433464279465124597442741)
                    ·
                      rfl

theorem cell23_2532506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_2532506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532506 prefixEnd_2532506 := by exact prefixLift 2532506
  have htrace : WordTrace (prefixWord ++ tailWord_2532506) baseStart_2532506 baseEnd_2532506 := by
    simpa [prefixWord, tailWord_2532506, baseEnd_2532506] using wordTrace_append hprefix tailTrace_2532506
  have hstable : (prefixWord ++ tailWord_2532506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532506).length < 2 ^ (prefixWord ++ tailWord_2532506).sum := by decide
  have hdescent : baseEnd_2532506 < baseStart_2532506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532557 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2532557 : Nat := 118140960795 + 2532557 * 2 ^ 59
def prefixEnd_2532557 : Nat := 4983230072969 + 3 ^ 40 * 2532557 * 2
def baseEnd_2532557 : Nat := 433473008636251030930163

theorem tailTrace_2532557 : CollatzResearch.WordTrace tailWord_2532557 prefixEnd_2532557 433473008636251030930163 := by
  unfold tailWord_2532557
  simp only [CollatzResearch.WordTrace]
  refine ⟨92369942285985990145531925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61579961523990660097021283 92369942285985990145531925)
  ·
    refine ⟨4329841044655593288071809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92369942285985990145531925 4329841044655593288071809)
    ·
      refine ⟨3247380783491694966053857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4329841044655593288071809 3247380783491694966053857)
      ·
        refine ⟨2435535587618771224540393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3247380783491694966053857 2435535587618771224540393)
        ·
          refine ⟨1826651690714078418405295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2435535587618771224540393 1826651690714078418405295)
          ·
            refine ⟨2739977536071117627607943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826651690714078418405295 2739977536071117627607943)
            ·
              refine ⟨4109966304106676441411915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739977536071117627607943 4109966304106676441411915)
              ·
                refine ⟨6164949456160014662117873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109966304106676441411915 6164949456160014662117873)
                ·
                  refine ⟨4623712092120010996588405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6164949456160014662117873 4623712092120010996588405)
                  ·
                    refine ⟨433473008636251030930163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4623712092120010996588405 433473008636251030930163)
                    ·
                      rfl

theorem cell23_2532557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2532557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532557 prefixEnd_2532557 := by exact prefixLift 2532557
  have htrace : WordTrace (prefixWord ++ tailWord_2532557) baseStart_2532557 baseEnd_2532557 := by
    simpa [prefixWord, tailWord_2532557, baseEnd_2532557] using wordTrace_append hprefix tailTrace_2532557
  have hstable : (prefixWord ++ tailWord_2532557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532557).length < 2 ^ (prefixWord ++ tailWord_2532557).sum := by decide
  have hdescent : baseEnd_2532557 < baseStart_2532557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532583 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 6]
def baseStart_2532583 : Nat := 118140960795 + 2532583 * 2 ^ 59
def prefixEnd_2532583 : Nat := 4983230072969 + 3 ^ 40 * 2532583 * 2
def baseEnd_2532583 : Nat := 144492486267307776785041

theorem tailTrace_2532583 : CollatzResearch.WordTrace tailWord_2532583 prefixEnd_2532583 144492486267307776785041 := by
  unfold tailWord_2532583
  simp only [CollatzResearch.WordTrace]
  refine ⟨92370890583891796585978403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61580593722594531057318935 92370890583891796585978403)
  ·
    refine ⟨138556335875837694878967605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92370890583891796585978403 138556335875837694878967605)
    ·
      refine ⟨12989656488359783894903213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138556335875837694878967605 12989656488359783894903213)
      ·
        refine ⟨4871121183134918960588705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12989656488359783894903213 4871121183134918960588705)
        ·
          refine ⟨3653340887351189220441529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4871121183134918960588705 3653340887351189220441529)
          ·
            refine ⟨2740005665513391915331147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3653340887351189220441529 2740005665513391915331147)
            ·
              refine ⟨4110008498270087872996721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2740005665513391915331147 4110008498270087872996721)
              ·
                refine ⟨3082506373702565904747541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4110008498270087872996721 3082506373702565904747541)
                ·
                  refine ⟨144492486267307776785041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3082506373702565904747541 144492486267307776785041)
                  ·
                    rfl

theorem cell23_2532583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 6].length) (baseStart_2532583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532583 prefixEnd_2532583 := by exact prefixLift 2532583
  have htrace : WordTrace (prefixWord ++ tailWord_2532583) baseStart_2532583 baseEnd_2532583 := by
    simpa [prefixWord, tailWord_2532583, baseEnd_2532583] using wordTrace_append hprefix tailTrace_2532583
  have hstable : (prefixWord ++ tailWord_2532583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532583).length < 2 ^ (prefixWord ++ tailWord_2532583).sum := by decide
  have hdescent : baseEnd_2532583 < baseStart_2532583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532592 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 10]
def baseStart_2532592 : Nat := 118140960795 + 2532592 * 2 ^ 59
def prefixEnd_2532592 : Nat := 4983230072969 + 3 ^ 40 * 2532592 * 2
def baseEnd_2532592 : Nat := 433478999243886818617609

theorem tailTrace_2532592 : CollatzResearch.WordTrace tailWord_2532592 prefixEnd_2532592 433478999243886818617609 := by
  unfold tailWord_2532592
  simp only [CollatzResearch.WordTrace]
  refine ⟨46185609420429595561528015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61580812560572794082037353 46185609420429595561528015)
  ·
    refine ⟨69278414130644393342292023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46185609420429595561528015 69278414130644393342292023)
    ·
      refine ⟨103917621195966590013438035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69278414130644393342292023 103917621195966590013438035)
      ·
        refine ⟨155876431793949885020157053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103917621195966590013438035 155876431793949885020157053)
        ·
          refine ⟨58453661922731206882558895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155876431793949885020157053 58453661922731206882558895)
          ·
            refine ⟨87680492884096810323838343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58453661922731206882558895 87680492884096810323838343)
            ·
              refine ⟨131520739326145215485757515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87680492884096810323838343 131520739326145215485757515)
              ·
                refine ⟨197281108989217823228636273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131520739326145215485757515 197281108989217823228636273)
                ·
                  refine ⟨147960831741913367421477205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197281108989217823228636273 147960831741913367421477205)
                  ·
                    refine ⟨433478999243886818617609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 147960831741913367421477205 433478999243886818617609)
                    ·
                      rfl

theorem cell23_2532592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_2532592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532592 prefixEnd_2532592 := by exact prefixLift 2532592
  have htrace : WordTrace (prefixWord ++ tailWord_2532592) baseStart_2532592 baseEnd_2532592 := by
    simpa [prefixWord, tailWord_2532592, baseEnd_2532592] using wordTrace_append hprefix tailTrace_2532592
  have hstable : (prefixWord ++ tailWord_2532592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532592).length < 2 ^ (prefixWord ++ tailWord_2532592).sum := by decide
  have hdescent : baseEnd_2532592 < baseStart_2532592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532629 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_2532629 : Nat := 118140960795 + 2532629 * 2 ^ 59
def prefixEnd_2532629 : Nat := 4983230072969 + 3 ^ 40 * 2532629 * 2
def baseEnd_2532629 : Nat := 1300455996515876811090157

theorem tailTrace_2532629 : CollatzResearch.WordTrace tailWord_2532629 prefixEnd_2532629 1300455996515876811090157 := by
  unfold tailWord_2532629
  simp only [CollatzResearch.WordTrace]
  refine ⟨92372568341725146442152941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61581712227816764294768627 92372568341725146442152941)
  ·
    refine ⟨34639713128146929915807353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92372568341725146442152941 34639713128146929915807353)
    ·
      refine ⟨25979784846110197436855515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34639713128146929915807353 25979784846110197436855515)
      ·
        refine ⟨38969677269165296155283273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25979784846110197436855515 38969677269165296155283273)
        ·
          refine ⟨29227257951873972116462455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38969677269165296155283273 29227257951873972116462455)
          ·
            refine ⟨43840886927810958174693683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29227257951873972116462455 43840886927810958174693683)
            ·
              refine ⟨65761330391716437262040525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43840886927810958174693683 65761330391716437262040525)
              ·
                refine ⟨24660498896893663973265197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65761330391716437262040525 24660498896893663973265197)
                ·
                  refine ⟨9247687086335123989974449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24660498896893663973265197 9247687086335123989974449)
                  ·
                    refine ⟨6935765314751342992480837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9247687086335123989974449 6935765314751342992480837)
                    ·
                      refine ⟨1300455996515876811090157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6935765314751342992480837 1300455996515876811090157)
                      ·
                        rfl

theorem cell23_2532629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_2532629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532629 prefixEnd_2532629 := by exact prefixLift 2532629
  have htrace : WordTrace (prefixWord ++ tailWord_2532629) baseStart_2532629 baseEnd_2532629 := by
    simpa [prefixWord, tailWord_2532629, baseEnd_2532629] using wordTrace_append hprefix tailTrace_2532629
  have hstable : (prefixWord ++ tailWord_2532629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532629).length < 2 ^ (prefixWord ++ tailWord_2532629).sum := by decide
  have hdescent : baseEnd_2532629 < baseStart_2532629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532653 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2532653 : Nat := 118140960795 + 2532653 * 2 ^ 59
def prefixEnd_2532653 : Nat := 4983230072969 + 3 ^ 40 * 2532653 * 2
def baseEnd_2532653 : Nat := 1300468320051584717190047

theorem tailTrace_2532653 : CollatzResearch.WordTrace tailWord_2532653 prefixEnd_2532653 1300468320051584717190047 := by
  unfold tailWord_2532653
  simp only [CollatzResearch.WordTrace]
  refine ⟨92373443693638198541026613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61582295795758799027351075 92373443693638198541026613)
  ·
    refine ⟨8660010346278581113221245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92373443693638198541026613 8660010346278581113221245)
    ·
      refine ⟨3247503879854467917457967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8660010346278581113221245 3247503879854467917457967)
      ·
        refine ⟨4871255819781701876186951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3247503879854467917457967 4871255819781701876186951)
        ·
          refine ⟨7306883729672552814280427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4871255819781701876186951 7306883729672552814280427)
          ·
            refine ⟨10960325594508829221420641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7306883729672552814280427 10960325594508829221420641)
            ·
              refine ⟨8220244195881621916065481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10960325594508829221420641 8220244195881621916065481)
              ·
                refine ⟨6165183146911216437049111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8220244195881621916065481 6165183146911216437049111)
                ·
                  refine ⟨9247774720366824655573667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6165183146911216437049111 9247774720366824655573667)
                  ·
                    refine ⟨13871662080550236983360501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9247774720366824655573667 13871662080550236983360501)
                    ·
                      refine ⟨1300468320051584717190047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13871662080550236983360501 1300468320051584717190047)
                      ·
                        rfl

theorem cell23_2532653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2532653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532653 prefixEnd_2532653 := by exact prefixLift 2532653
  have htrace : WordTrace (prefixWord ++ tailWord_2532653) baseStart_2532653 baseEnd_2532653 := by
    simpa [prefixWord, tailWord_2532653, baseEnd_2532653] using wordTrace_append hprefix tailTrace_2532653
  have hstable : (prefixWord ++ tailWord_2532653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532653).length < 2 ^ (prefixWord ++ tailWord_2532653).sum := by decide
  have hdescent : baseEnd_2532653 < baseStart_2532653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532666 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_2532666 : Nat := 118140960795 + 2532666 * 2 ^ 59
def prefixEnd_2532666 : Nat := 4983230072969 + 3 ^ 40 * 2532666 * 2
def baseEnd_2532666 : Nat := 1300474995300093166327487

theorem tailTrace_2532666 : CollatzResearch.WordTrace tailWord_2532666 prefixEnd_2532666 1300474995300093166327487 := by
  unfold tailWord_2532666
  simp only [CollatzResearch.WordTrace]
  refine ⟨23093479460647775440312463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61582611895060734507499901 23093479460647775440312463)
  ·
    refine ⟨34640219190971663160468695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23093479460647775440312463 34640219190971663160468695)
    ·
      refine ⟨51960328786457494740703043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34640219190971663160468695 51960328786457494740703043)
      ·
        refine ⟨77940493179686242111054565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51960328786457494740703043 77940493179686242111054565)
        ·
          refine ⟨14613842471191170395822731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77940493179686242111054565 14613842471191170395822731)
          ·
            refine ⟨21920763706786755593734097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14613842471191170395822731 21920763706786755593734097)
            ·
              refine ⟨16440572780090066695300573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21920763706786755593734097 16440572780090066695300573)
              ·
                refine ⟨6165214792533775010737715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16440572780090066695300573 6165214792533775010737715)
                ·
                  refine ⟨9247822188800662516106573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6165214792533775010737715 9247822188800662516106573)
                  ·
                    refine ⟨3467933320800248443539965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9247822188800662516106573 3467933320800248443539965)
                    ·
                      refine ⟨1300474995300093166327487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3467933320800248443539965 1300474995300093166327487)
                      ·
                        rfl

theorem cell23_2532666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_2532666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532666 prefixEnd_2532666 := by exact prefixLift 2532666
  have htrace : WordTrace (prefixWord ++ tailWord_2532666) baseStart_2532666 baseEnd_2532666 := by
    simpa [prefixWord, tailWord_2532666, baseEnd_2532666] using wordTrace_append hprefix tailTrace_2532666
  have hstable : (prefixWord ++ tailWord_2532666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532666).length < 2 ^ (prefixWord ++ tailWord_2532666).sum := by decide
  have hdescent : baseEnd_2532666 < baseStart_2532666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532706 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2532706 : Nat := 118140960795 + 2532706 * 2 ^ 59
def prefixEnd_2532706 : Nat := 4983230072969 + 3 ^ 40 * 2532706 * 2
def baseEnd_2532706 : Nat := 1300495534526273009827303

theorem tailTrace_2532706 : CollatzResearch.WordTrace tailWord_2532706 prefixEnd_2532706 1300495534526273009827303 := by
  unfold tailWord_2532706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23093844190611547148176493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61583584508297459061803981 23093844190611547148176493)
  ·
    refine ⟨8660191571479330180566185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23093844190611547148176493 8660191571479330180566185)
    ·
      refine ⟨6495143678609497635424639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8660191571479330180566185 6495143678609497635424639)
      ·
        refine ⟨9742715517914246453136959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6495143678609497635424639 9742715517914246453136959)
        ·
          refine ⟨14614073276871369679705439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9742715517914246453136959 14614073276871369679705439)
          ·
            refine ⟨21921109915307054519558159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14614073276871369679705439 21921109915307054519558159)
            ·
              refine ⟨32881664872960581779337239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21921109915307054519558159 32881664872960581779337239)
              ·
                refine ⟨49322497309440872669005859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32881664872960581779337239 49322497309440872669005859)
                ·
                  refine ⟨73983745964161309003508789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49322497309440872669005859 73983745964161309003508789)
                  ·
                    refine ⟨6935976184140122719078949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73983745964161309003508789 6935976184140122719078949)
                    ·
                      refine ⟨1300495534526273009827303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6935976184140122719078949 1300495534526273009827303)
                      ·
                        rfl

theorem cell23_2532706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2532706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532706 prefixEnd_2532706 := by exact prefixLift 2532706
  have htrace : WordTrace (prefixWord ++ tailWord_2532706) baseStart_2532706 baseEnd_2532706 := by
    simpa [prefixWord, tailWord_2532706, baseEnd_2532706] using wordTrace_append hprefix tailTrace_2532706
  have hstable : (prefixWord ++ tailWord_2532706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532706).length < 2 ^ (prefixWord ++ tailWord_2532706).sum := by decide
  have hdescent : baseEnd_2532706 < baseStart_2532706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532716 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_2532716 : Nat := 118140960795 + 2532716 * 2 ^ 59
def prefixEnd_2532716 : Nat := 4983230072969 + 3 ^ 40 * 2532716 * 2
def baseEnd_2532716 : Nat := 433500223110939323567419

theorem tailTrace_2532716 : CollatzResearch.WordTrace tailWord_2532716 prefixEnd_2532716 433500223110939323567419 := by
  unfold tailWord_2532716
  simp only [CollatzResearch.WordTrace]
  refine ⟨46187870746204980150285001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61583827661606640200380001 46187870746204980150285001)
  ·
    refine ⟨34640903059653735112713751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46187870746204980150285001 34640903059653735112713751)
    ·
      refine ⟨51961354589480602669070627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34640903059653735112713751 51961354589480602669070627)
      ·
        refine ⟨77942031884220904003605941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51961354589480602669070627 77942031884220904003605941)
        ·
          refine ⟨7307065489145709750338057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77942031884220904003605941 7307065489145709750338057)
          ·
            refine ⟨5480299116859282312753543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7307065489145709750338057 5480299116859282312753543)
            ·
              refine ⟨8220448675288923469130315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5480299116859282312753543 8220448675288923469130315)
              ·
                refine ⟨12330673012933385203695473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8220448675288923469130315 12330673012933385203695473)
                ·
                  refine ⟨9248004759700038902771605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12330673012933385203695473 9248004759700038902771605)
                  ·
                    refine ⟨433500223110939323567419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9248004759700038902771605 433500223110939323567419)
                    ·
                      rfl

theorem cell23_2532716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_2532716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532716 prefixEnd_2532716 := by exact prefixLift 2532716
  have htrace : WordTrace (prefixWord ++ tailWord_2532716) baseStart_2532716 baseEnd_2532716 := by
    simpa [prefixWord, tailWord_2532716, baseEnd_2532716] using wordTrace_append hprefix tailTrace_2532716
  have hstable : (prefixWord ++ tailWord_2532716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532716).length < 2 ^ (prefixWord ++ tailWord_2532716).sum := by decide
  have hdescent : baseEnd_2532716 < baseStart_2532716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532729 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 9]
def baseStart_2532729 : Nat := 118140960795 + 2532729 * 2 ^ 59
def prefixEnd_2532729 : Nat := 4983230072969 + 3 ^ 40 * 2532729 * 2
def baseEnd_2532729 : Nat := 144500816064591824426633

theorem tailTrace_2532729 : CollatzResearch.WordTrace tailWord_2532729 prefixEnd_2532729 144500816064591824426633 := by
  unfold tailWord_2532729
  simp only [CollatzResearch.WordTrace]
  refine ⟨92376215641362863520793241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61584143760908575680528827 92376215641362863520793241)
  ·
    refine ⟨69282161731022147640594931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92376215641362863520793241 69282161731022147640594931)
    ·
      refine ⟨103923242596533221460892397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69282161731022147640594931 103923242596533221460892397)
      ·
        refine ⟨38971215973699958047834649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103923242596533221460892397 38971215973699958047834649)
        ·
          refine ⟨29228411980274968535875987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38971215973699958047834649 29228411980274968535875987)
          ·
            refine ⟨43842617970412452803813981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29228411980274968535875987 43842617970412452803813981)
            ·
              refine ⟨16440981738904669801430243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43842617970412452803813981 16440981738904669801430243)
              ·
                refine ⟨24661472608357004702145365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16440981738904669801430243 24661472608357004702145365)
                ·
                  refine ⟨144500816064591824426633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24661472608357004702145365 144500816064591824426633)
                  ·
                    rfl

theorem cell23_2532729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 9].length) (baseStart_2532729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532729 prefixEnd_2532729 := by exact prefixLift 2532729
  have htrace : WordTrace (prefixWord ++ tailWord_2532729) baseStart_2532729 baseEnd_2532729 := by
    simpa [prefixWord, tailWord_2532729, baseEnd_2532729] using wordTrace_append hprefix tailTrace_2532729
  have hstable : (prefixWord ++ tailWord_2532729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532729).length < 2 ^ (prefixWord ++ tailWord_2532729).sum := by decide
  have hdescent : baseEnd_2532729 < baseStart_2532729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532850 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2532850 : Nat := 118140960795 + 2532850 * 2 ^ 59
def prefixEnd_2532850 : Nat := 4983230072969 + 3 ^ 40 * 2532850 * 2
def baseEnd_2532850 : Nat := 1300569475740520446426641

theorem tailTrace_2532850 : CollatzResearch.WordTrace tailWord_2532850 prefixEnd_2532850 1300569475740520446426641 := by
  unfold tailWord_2532850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23095157218481125296487001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61587085915949667457298669 23095157218481125296487001)
  ·
    refine ⟨17321367913860843972365251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23095157218481125296487001 17321367913860843972365251)
    ·
      refine ⟨25982051870791265958547877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17321367913860843972365251 25982051870791265958547877)
      ·
        refine ⟨4871634725773362367227727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25982051870791265958547877 4871634725773362367227727)
        ·
          refine ⟨7307452088660043550841591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4871634725773362367227727 7307452088660043550841591)
          ·
            refine ⟨10961178132990065326262387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7307452088660043550841591 10961178132990065326262387)
            ·
              refine ⟨16441767199485097989393581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10961178132990065326262387 16441767199485097989393581)
              ·
                refine ⟨6165662699806911746022593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16441767199485097989393581 6165662699806911746022593)
                ·
                  refine ⟨4624247024855183809516945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6165662699806911746022593 4624247024855183809516945)
                  ·
                    refine ⟨3468185268641387857137709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4624247024855183809516945 3468185268641387857137709)
                    ·
                      refine ⟨1300569475740520446426641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3468185268641387857137709 1300569475740520446426641)
                      ·
                        rfl

theorem cell23_2532850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2532850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532850 prefixEnd_2532850 := by exact prefixLift 2532850
  have htrace : WordTrace (prefixWord ++ tailWord_2532850) baseStart_2532850 baseEnd_2532850 := by
    simpa [prefixWord, tailWord_2532850, baseEnd_2532850] using wordTrace_append hprefix tailTrace_2532850
  have hstable : (prefixWord ++ tailWord_2532850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532850).length < 2 ^ (prefixWord ++ tailWord_2532850).sum := by decide
  have hdescent : baseEnd_2532850 < baseStart_2532850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532863 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 3]
def baseStart_2532863 : Nat := 118140960795 + 2532863 * 2 ^ 59
def prefixEnd_2532863 : Nat := 4983230072969 + 3 ^ 40 * 2532863 * 2
def baseEnd_2532863 : Nat := 1300576150989028895564081

theorem tailTrace_2532863 : CollatzResearch.WordTrace tailWord_2532863 prefixEnd_2532863 1300576150989028895564081 := by
  unfold tailWord_2532863
  simp only [CollatzResearch.WordTrace]
  refine ⟨92381103022877404406171243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61587402015251602937447495 92381103022877404406171243)
  ·
    refine ⟨138571654534316106609256865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92381103022877404406171243 138571654534316106609256865)
    ·
      refine ⟨103928740900737079956942649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138571654534316106609256865 103928740900737079956942649)
      ·
        refine ⟨77946555675552809967706987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103928740900737079956942649 77946555675552809967706987)
        ·
          refine ⟨116919833513329214951560481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77946555675552809967706987 116919833513329214951560481)
          ·
            refine ⟨87689875134996911213670361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116919833513329214951560481 87689875134996911213670361)
            ·
              refine ⟨65767406351247683410252771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87689875134996911213670361 65767406351247683410252771)
              ·
                refine ⟨98651109526871525115379157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65767406351247683410252771 98651109526871525115379157)
                ·
                  refine ⟨2312135379536051369891699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 98651109526871525115379157 2312135379536051369891699)
                  ·
                    refine ⟨3468203069304077054837549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2312135379536051369891699 3468203069304077054837549)
                    ·
                      refine ⟨1300576150989028895564081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3468203069304077054837549 1300576150989028895564081)
                      ·
                        rfl

theorem cell23_2532863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_2532863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532863 prefixEnd_2532863 := by exact prefixLift 2532863
  have htrace : WordTrace (prefixWord ++ tailWord_2532863) baseStart_2532863 baseEnd_2532863 := by
    simpa [prefixWord, tailWord_2532863, baseEnd_2532863] using wordTrace_append hprefix tailTrace_2532863
  have hstable : (prefixWord ++ tailWord_2532863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532863).length < 2 ^ (prefixWord ++ tailWord_2532863).sum := by decide
  have hdescent : baseEnd_2532863 < baseStart_2532863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532874 : List Nat := [3, 1, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_2532874 : Nat := 118140960795 + 2532874 * 2 ^ 59
def prefixEnd_2532874 : Nat := 4983230072969 + 3 ^ 40 * 2532874 * 2
def baseEnd_2532874 : Nat := 433527266425409450842177

theorem tailTrace_2532874 : CollatzResearch.WordTrace tailWord_2532874 prefixEnd_2532874 433527266425409450842177 := by
  unfold tailWord_2532874
  simp only [CollatzResearch.WordTrace]
  refine ⟨23095376056459388321205419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61587669483891702189881117 23095376056459388321205419)
  ·
    refine ⟨34643064084689082481808129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23095376056459388321205419 34643064084689082481808129)
    ·
      refine ⟨25982298063516811861356097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34643064084689082481808129 25982298063516811861356097)
      ·
        refine ⟨19486723547637608896017073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25982298063516811861356097 19486723547637608896017073)
        ·
          refine ⟨14615042660728206672012805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19486723547637608896017073 14615042660728206672012805)
          ·
            refine ⟨2740320498886538751002401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14615042660728206672012805 2740320498886538751002401)
            ·
              refine ⟨2055240374164904063251801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2740320498886538751002401 2055240374164904063251801)
              ·
                refine ⟨1541430280623678047438851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055240374164904063251801 1541430280623678047438851)
                ·
                  refine ⟨2312145420935517071158277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541430280623678047438851 2312145420935517071158277)
                  ·
                    refine ⟨433527266425409450842177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2312145420935517071158277 433527266425409450842177)
                    ·
                      rfl

theorem cell23_2532874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_2532874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532874 prefixEnd_2532874 := by exact prefixLift 2532874
  have htrace : WordTrace (prefixWord ++ tailWord_2532874) baseStart_2532874 baseEnd_2532874 := by
    simpa [prefixWord, tailWord_2532874, baseEnd_2532874] using wordTrace_append hprefix tailTrace_2532874
  have hstable : (prefixWord ++ tailWord_2532874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532874).length < 2 ^ (prefixWord ++ tailWord_2532874).sum := by decide
  have hdescent : baseEnd_2532874 < baseStart_2532874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532913 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 4, 4]
def baseStart_2532913 : Nat := 118140960795 + 2532913 * 2 ^ 59
def prefixEnd_2532913 : Nat := 4983230072969 + 3 ^ 40 * 2532913 * 2
def baseEnd_2532913 : Nat := 433533941673917899979617

theorem tailTrace_2532913 : CollatzResearch.WordTrace tailWord_2532913 prefixEnd_2532913 433533941673917899979617 := by
  unfold tailWord_2532913
  simp only [CollatzResearch.WordTrace]
  refine ⟨92382926672696262945491393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61588617781797508630327595 92382926672696262945491393)
  ·
    refine ⟨69287195004522197209118545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92382926672696262945491393 69287195004522197209118545)
    ·
      refine ⟨51965396253391647906838909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69287195004522197209118545 51965396253391647906838909)
      ·
        refine ⟨19487023595021867965064591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51965396253391647906838909 19487023595021867965064591)
        ·
          refine ⟨29230535392532801947596887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19487023595021867965064591 29230535392532801947596887)
          ·
            refine ⟨43845803088799202921395331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29230535392532801947596887 43845803088799202921395331)
            ·
              refine ⟨65768704633198804382092997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43845803088799202921395331 65768704633198804382092997)
              ·
                refine ⟨12331632118724775821642437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65768704633198804382092997 12331632118724775821642437)
                ·
                  refine ⟨2312181022260895466557957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12331632118724775821642437 2312181022260895466557957)
                  ·
                    refine ⟨433533941673917899979617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2312181022260895466557957 433533941673917899979617)
                    ·
                      rfl

theorem cell23_2532913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 4, 4].length) (baseStart_2532913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532913 prefixEnd_2532913 := by exact prefixLift 2532913
  have htrace : WordTrace (prefixWord ++ tailWord_2532913) baseStart_2532913 baseEnd_2532913 := by
    simpa [prefixWord, tailWord_2532913, baseEnd_2532913] using wordTrace_append hprefix tailTrace_2532913
  have hstable : (prefixWord ++ tailWord_2532913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532913).length < 2 ^ (prefixWord ++ tailWord_2532913).sum := by decide
  have hdescent : baseEnd_2532913 < baseStart_2532913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532917 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2532917 : Nat := 118140960795 + 2532917 * 2 ^ 59
def prefixEnd_2532917 : Nat := 4983230072969 + 3 ^ 40 * 2532917 * 2
def baseEnd_2532917 : Nat := 433534626314790561429611

theorem tailTrace_2532917 : CollatzResearch.WordTrace tailWord_2532917 prefixEnd_2532917 433534626314790561429611 := by
  unfold tailWord_2532917
  simp only [CollatzResearch.WordTrace]
  refine ⟨92383072564681771628637005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61588715043121181085758003 92383072564681771628637005)
  ·
    refine ⟨34643652211755664360738877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92383072564681771628637005 34643652211755664360738877)
    ·
      refine ⟨12991369579408374135277079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34643652211755664360738877 12991369579408374135277079)
      ·
        refine ⟨19487054369112561202915619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12991369579408374135277079 19487054369112561202915619)
        ·
          refine ⟨29230581553668841804373429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19487054369112561202915619 29230581553668841804373429)
          ·
            refine ⟨2740367020656453919160009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29230581553668841804373429 2740367020656453919160009)
            ·
              refine ⟨2055275265492340439370007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2740367020656453919160009 2055275265492340439370007)
              ·
                refine ⟨3082912898238510659055011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055275265492340439370007 3082912898238510659055011)
                ·
                  refine ⟨4624369347357765988582517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082912898238510659055011 4624369347357765988582517)
                  ·
                    refine ⟨433534626314790561429611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4624369347357765988582517 433534626314790561429611)
                    ·
                      rfl

theorem cell23_2532917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2532917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532917 prefixEnd_2532917 := by exact prefixLift 2532917
  have htrace : WordTrace (prefixWord ++ tailWord_2532917) baseStart_2532917 baseEnd_2532917 := by
    simpa [prefixWord, tailWord_2532917, baseEnd_2532917] using wordTrace_append hprefix tailTrace_2532917
  have hstable : (prefixWord ++ tailWord_2532917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532917).length < 2 ^ (prefixWord ++ tailWord_2532917).sum := by decide
  have hdescent : baseEnd_2532917 < baseStart_2532917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532920 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_2532920 : Nat := 118140960795 + 2532920 * 2 ^ 59
def prefixEnd_2532920 : Nat := 4983230072969 + 3 ^ 40 * 2532920 * 2
def baseEnd_2532920 : Nat := 1300605419386335172551319

theorem tailTrace_2532920 : CollatzResearch.WordTrace tailWord_2532920 prefixEnd_2532920 1300605419386335172551319 := by
  unfold tailWord_2532920
  simp only [CollatzResearch.WordTrace]
  refine ⟨46191590991835451570498107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61588787989113935427330809 46191590991835451570498107)
  ·
    refine ⟨69287386487753177355747161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46191590991835451570498107 69287386487753177355747161)
    ·
      refine ⟨51965539865814883016810371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69287386487753177355747161 51965539865814883016810371)
      ·
        refine ⟨77948309798722324525215557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51965539865814883016810371 77948309798722324525215557)
        ·
          refine ⟨14615308087260435848477917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77948309798722324525215557 14615308087260435848477917)
          ·
            refine ⟨5480740532722663443179219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14615308087260435848477917 5480740532722663443179219)
            ·
              refine ⟨8221110799083995164768829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5480740532722663443179219 8221110799083995164768829)
              ·
                refine ⟨3082916549656498186788311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8221110799083995164768829 3082916549656498186788311)
                ·
                  refine ⟨4624374824484747280182467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082916549656498186788311 4624374824484747280182467)
                  ·
                    refine ⟨6936562236727120920273701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4624374824484747280182467 6936562236727120920273701)
                    ·
                      refine ⟨1300605419386335172551319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6936562236727120920273701 1300605419386335172551319)
                      ·
                        rfl

theorem cell23_2532920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_2532920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532920 prefixEnd_2532920 := by exact prefixLift 2532920
  have htrace : WordTrace (prefixWord ++ tailWord_2532920) baseStart_2532920 baseEnd_2532920 := by
    simpa [prefixWord, tailWord_2532920, baseEnd_2532920] using wordTrace_append hprefix tailTrace_2532920
  have hstable : (prefixWord ++ tailWord_2532920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532920).length < 2 ^ (prefixWord ++ tailWord_2532920).sum := by decide
  have hdescent : baseEnd_2532920 < baseStart_2532920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532936 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2532936 : Nat := 118140960795 + 2532936 * 2 ^ 59
def prefixEnd_2532936 : Nat := 4983230072969 + 3 ^ 40 * 2532936 * 2
def baseEnd_2532936 : Nat := 1300613635076807109951245

theorem tailTrace_2532936 : CollatzResearch.WordTrace tailWord_2532936 prefixEnd_2532936 1300613635076807109951245 := by
  unfold tailWord_2532936
  simp only [CollatzResearch.WordTrace]
  refine ⟨46191882775806468936789331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61589177034408625249052441 46191882775806468936789331)
  ·
    refine ⟨69287824163709703405183997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46191882775806468936789331 69287824163709703405183997)
    ·
      refine ⟨25982934061391138776943999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69287824163709703405183997 25982934061391138776943999)
      ·
        refine ⟨38974401092086708165415999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25982934061391138776943999 38974401092086708165415999)
        ·
          refine ⟨58461601638130062248123999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38974401092086708165415999 58461601638130062248123999)
          ·
            refine ⟨87692402457195093372185999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58461601638130062248123999 87692402457195093372185999)
            ·
              refine ⟨131538603685792640058278999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87692402457195093372185999 131538603685792640058278999)
              ·
                refine ⟨197307905528688960087418499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131538603685792640058278999 197307905528688960087418499)
                ·
                  refine ⟨295961858293033440131127749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197307905528688960087418499 295961858293033440131127749)
                  ·
                    refine ⟨55492848429943770024586453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 295961858293033440131127749 55492848429943770024586453)
                    ·
                      refine ⟨1300613635076807109951245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55492848429943770024586453 1300613635076807109951245)
                      ·
                        rfl

theorem cell23_2532936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2532936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2532936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2532936 prefixEnd_2532936 := by exact prefixLift 2532936
  have htrace : WordTrace (prefixWord ++ tailWord_2532936) baseStart_2532936 baseEnd_2532936 := by
    simpa [prefixWord, tailWord_2532936, baseEnd_2532936] using wordTrace_append hprefix tailTrace_2532936
  have hstable : (prefixWord ++ tailWord_2532936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532936).length < 2 ^ (prefixWord ++ tailWord_2532936).sum := by decide
  have hdescent : baseEnd_2532936 < baseStart_2532936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533063 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 1, 7]
def baseStart_2533063 : Nat := 118140960795 + 2533063 * 2 ^ 59
def prefixEnd_2533063 : Nat := 4983230072969 + 3 ^ 40 * 2533063 * 2
def baseEnd_2533063 : Nat := 433559615706642704354387

theorem tailTrace_2533063 : CollatzResearch.WordTrace tailWord_2533063 prefixEnd_2533063 433559615706642704354387 := by
  unfold tailWord_2533063
  simp only [CollatzResearch.WordTrace]
  refine ⟨92388397622152838563451843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61592265081435225708967895 92388397622152838563451843)
  ·
    refine ⟨138582596433229257845177765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92388397622152838563451843 138582596433229257845177765)
    ·
      refine ⟨25984236831230485845970831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138582596433229257845177765 25984236831230485845970831)
      ·
        refine ⟨38976355246845728768956247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25984236831230485845970831 38976355246845728768956247)
        ·
          refine ⟨58464532870268593153434371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38976355246845728768956247 58464532870268593153434371)
          ·
            refine ⟨87696799305402889730151557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58464532870268593153434371 87696799305402889730151557)
            ·
              refine ⟨16443149869763041824403417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87696799305402889730151557 16443149869763041824403417)
              ·
                refine ⟨12332362402322281368302563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16443149869763041824403417 12332362402322281368302563)
                ·
                  refine ⟨18498543603483422052453845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12332362402322281368302563 18498543603483422052453845)
                  ·
                    refine ⟨433559615706642704354387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18498543603483422052453845 433559615706642704354387)
                    ·
                      rfl

theorem cell23_2533063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_2533063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533063 prefixEnd_2533063 := by exact prefixLift 2533063
  have htrace : WordTrace (prefixWord ++ tailWord_2533063) baseStart_2533063 baseEnd_2533063 := by
    simpa [prefixWord, tailWord_2533063, baseEnd_2533063] using wordTrace_append hprefix tailTrace_2533063
  have hstable : (prefixWord ++ tailWord_2533063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533063).length < 2 ^ (prefixWord ++ tailWord_2533063).sum := by decide
  have hdescent : baseEnd_2533063 < baseStart_2533063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533095 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2533095 : Nat := 118140960795 + 2533095 * 2 ^ 59
def prefixEnd_2533095 : Nat := 4983230072969 + 3 ^ 40 * 2533095 * 2
def baseEnd_2533095 : Nat := 1300695278500871987863015

theorem tailTrace_2533095 : CollatzResearch.WordTrace tailWord_2533095 prefixEnd_2533095 1300695278500871987863015 := by
  unfold tailWord_2533095
  simp only [CollatzResearch.WordTrace]
  refine ⟨92389564758036908028616739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61593043172024605352411159 92389564758036908028616739)
  ·
    refine ⟨138584347137055362042925109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92389564758036908028616739 138584347137055362042925109)
    ·
      refine ⟨12992282544098940191524229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138584347137055362042925109 12992282544098940191524229)
      ·
        refine ⟨2436052977018551285910793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12992282544098940191524229 2436052977018551285910793)
        ·
          refine ⟨1827039732763913464433095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2436052977018551285910793 1827039732763913464433095)
          ·
            refine ⟨2740559599145870196649643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827039732763913464433095 2740559599145870196649643)
            ·
              refine ⟨4110839398718805294974465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2740559599145870196649643 4110839398718805294974465)
              ·
                refine ⟨3083129549039103971230849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4110839398718805294974465 3083129549039103971230849)
                ·
                  refine ⟨2312347161779327978423137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3083129549039103971230849 2312347161779327978423137)
                  ·
                    refine ⟨1734260371334495983817353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2312347161779327978423137 1734260371334495983817353)
                    ·
                      refine ⟨1300695278500871987863015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734260371334495983817353 1300695278500871987863015)
                      ·
                        rfl

theorem cell23_2533095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2533095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533095 prefixEnd_2533095 := by exact prefixLift 2533095
  have htrace : WordTrace (prefixWord ++ tailWord_2533095) baseStart_2533095 baseEnd_2533095 := by
    simpa [prefixWord, tailWord_2533095, baseEnd_2533095] using wordTrace_append hprefix tailTrace_2533095
  have hstable : (prefixWord ++ tailWord_2533095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533095).length < 2 ^ (prefixWord ++ tailWord_2533095).sum := by decide
  have hdescent : baseEnd_2533095 < baseStart_2533095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533100 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 4]
def baseStart_2533100 : Nat := 118140960795 + 2533100 * 2 ^ 59
def prefixEnd_2533100 : Nat := 4983230072969 + 3 ^ 40 * 2533100 * 2
def baseEnd_2533100 : Nat := 1300697845904144468300491

theorem tailTrace_2533100 : CollatzResearch.WordTrace tailWord_2533100 prefixEnd_2533100 1300697845904144468300491 := by
  unfold tailWord_2533100
  simp only [CollatzResearch.WordTrace]
  refine ⟨46194873561509396941274377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61593164748679195921699169 46194873561509396941274377)
  ·
    refine ⟨34646155171132047705955783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46194873561509396941274377 34646155171132047705955783)
    ·
      refine ⟨51969232756698071558933675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34646155171132047705955783 51969232756698071558933675)
      ·
        refine ⟨77953849135047107338400513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51969232756698071558933675 77953849135047107338400513)
        ·
          refine ⟨58465386851285330503800385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77953849135047107338400513 58465386851285330503800385)
          ·
            refine ⟨43849040138463997877850289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58465386851285330503800385 43849040138463997877850289)
            ·
              refine ⟨32886780103847998408387717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43849040138463997877850289 32886780103847998408387717)
              ·
                refine ⟨6166271269471499701572697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32886780103847998408387717 6166271269471499701572697)
                ·
                  refine ⟨4624703452103624776179523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6166271269471499701572697 4624703452103624776179523)
                  ·
                    refine ⟨6937055178155437164269285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4624703452103624776179523 6937055178155437164269285)
                    ·
                      refine ⟨1300697845904144468300491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6937055178155437164269285 1300697845904144468300491)
                      ·
                        rfl

theorem cell23_2533100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_2533100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533100 prefixEnd_2533100 := by exact prefixLift 2533100
  have htrace : WordTrace (prefixWord ++ tailWord_2533100) baseStart_2533100 baseEnd_2533100 := by
    simpa [prefixWord, tailWord_2533100, baseEnd_2533100] using wordTrace_append hprefix tailTrace_2533100
  have hstable : (prefixWord ++ tailWord_2533100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533100).length < 2 ^ (prefixWord ++ tailWord_2533100).sum := by decide
  have hdescent : baseEnd_2533100 < baseStart_2533100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533120 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 3]
def baseStart_2533120 : Nat := 118140960795 + 2533120 * 2 ^ 59
def prefixEnd_2533120 : Nat := 4983230072969 + 3 ^ 40 * 2533120 * 2
def baseEnd_2533120 : Nat := 1300708115517234390050399

theorem tailTrace_2533120 : CollatzResearch.WordTrace tailWord_2533120 prefixEnd_2533120 1300708115517234390050399 := by
  unfold tailWord_2533120
  simp only [CollatzResearch.WordTrace]
  refine ⟨46195238291473168649138407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61593651055297558198851209 46195238291473168649138407)
  ·
    refine ⟨69292857437209752973707611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46195238291473168649138407 69292857437209752973707611)
    ·
      refine ⟨103939286155814629460561417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69292857437209752973707611 103939286155814629460561417)
      ·
        refine ⟨77954464616860972095421063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103939286155814629460561417 77954464616860972095421063)
        ·
          refine ⟨116931696925291458143131595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77954464616860972095421063 116931696925291458143131595)
          ·
            refine ⟨175397545387937187214697393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116931696925291458143131595 175397545387937187214697393)
            ·
              refine ⟨131548159040952890411023045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175397545387937187214697393 131548159040952890411023045)
              ·
                refine ⟨24665279820178666952066821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131548159040952890411023045 24665279820178666952066821)
                ·
                  refine ⟨4624739966283500053512529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24665279820178666952066821 4624739966283500053512529)
                  ·
                    refine ⟨3468554974712625040134397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4624739966283500053512529 3468554974712625040134397)
                    ·
                      refine ⟨1300708115517234390050399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3468554974712625040134397 1300708115517234390050399)
                      ·
                        rfl

theorem cell23_2533120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_2533120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533120 prefixEnd_2533120 := by exact prefixLift 2533120
  have htrace : WordTrace (prefixWord ++ tailWord_2533120) baseStart_2533120 baseEnd_2533120 := by
    simpa [prefixWord, tailWord_2533120, baseEnd_2533120] using wordTrace_append hprefix tailTrace_2533120
  have hstable : (prefixWord ++ tailWord_2533120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533120).length < 2 ^ (prefixWord ++ tailWord_2533120).sum := by decide
  have hdescent : baseEnd_2533120 < baseStart_2533120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533144 : List Nat := [2, 1, 2, 3, 1, 1, 5, 3, 1, 4]
def baseStart_2533144 : Nat := 118140960795 + 2533144 * 2 ^ 59
def prefixEnd_2533144 : Nat := 4983230072969 + 3 ^ 40 * 2533144 * 2
def baseEnd_2533144 : Nat := 433573479684314098716763

theorem tailTrace_2533144 : CollatzResearch.WordTrace tailWord_2533144 prefixEnd_2533144 433573479684314098716763 := by
  unfold tailWord_2533144
  simp only [CollatzResearch.WordTrace]
  refine ⟨46195675967429694698575243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61594234623239592931433657 46195675967429694698575243)
  ·
    refine ⟨69293513951144542047862865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46195675967429694698575243 69293513951144542047862865)
    ·
      refine ⟨51970135463358406535897149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69293513951144542047862865 51970135463358406535897149)
      ·
        refine ⟨19488800798759402450961431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51970135463358406535897149 19488800798759402450961431)
        ·
          refine ⟨29233201198139103676442147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19488800798759402450961431 29233201198139103676442147)
          ·
            refine ⟨43849801797208655514663221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29233201198139103676442147 43849801797208655514663221)
            ·
              refine ⟨4110918918488311454499677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43849801797208655514663221 4110918918488311454499677)
              ·
                refine ⟨1541594594433116795437379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4110918918488311454499677 1541594594433116795437379)
                ·
                  refine ⟨2312391891649675193156069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541594594433116795437379 2312391891649675193156069)
                  ·
                    refine ⟨433573479684314098716763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2312391891649675193156069 433573479684314098716763)
                    ·
                      rfl

theorem cell23_2533144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_2533144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533144 prefixEnd_2533144 := by exact prefixLift 2533144
  have htrace : WordTrace (prefixWord ++ tailWord_2533144) baseStart_2533144 baseEnd_2533144 := by
    simpa [prefixWord, tailWord_2533144, baseEnd_2533144] using wordTrace_append hprefix tailTrace_2533144
  have hstable : (prefixWord ++ tailWord_2533144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533144).length < 2 ^ (prefixWord ++ tailWord_2533144).sum := by decide
  have hdescent : baseEnd_2533144 < baseStart_2533144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533174 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2533174 : Nat := 118140960795 + 2533174 * 2 ^ 59
def prefixEnd_2533174 : Nat := 4983230072969 + 3 ^ 40 * 2533174 * 2
def baseEnd_2533174 : Nat := 144526204830286353197239

theorem tailTrace_2533174 : CollatzResearch.WordTrace tailWord_2533174 prefixEnd_2533174 144526204830286353197239 := by
  unfold tailWord_2533174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774527882796919032546411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61594964083167136347161717 5774527882796919032546411)
  ·
    refine ⟨8661791824195378548819617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5774527882796919032546411 8661791824195378548819617)
    ·
      refine ⟨6496343868146533911614713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8661791824195378548819617 6496343868146533911614713)
      ·
        refine ⟨4872257901109900433711035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6496343868146533911614713 4872257901109900433711035)
        ·
          refine ⟨7308386851664850650566553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4872257901109900433711035 7308386851664850650566553)
          ·
            refine ⟨5481290138748637987924915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7308386851664850650566553 5481290138748637987924915)
            ·
              refine ⟨8221935208122956981887373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481290138748637987924915 8221935208122956981887373)
              ·
                refine ⟨3083225703046108868207765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8221935208122956981887373 3083225703046108868207765)
                ·
                  refine ⟨144526204830286353197239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3083225703046108868207765 144526204830286353197239)
                  ·
                    rfl

theorem cell23_2533174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2533174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533174 prefixEnd_2533174 := by exact prefixLift 2533174
  have htrace : WordTrace (prefixWord ++ tailWord_2533174) baseStart_2533174 baseEnd_2533174 := by
    simpa [prefixWord, tailWord_2533174, baseEnd_2533174] using wordTrace_append hprefix tailTrace_2533174
  have hstable : (prefixWord ++ tailWord_2533174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533174).length < 2 ^ (prefixWord ++ tailWord_2533174).sum := by decide
  have hdescent : baseEnd_2533174 < baseStart_2533174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533187 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 1, 5]
def baseStart_2533187 : Nat := 118140960795 + 2533187 * 2 ^ 59
def prefixEnd_2533187 : Nat := 4983230072969 + 3 ^ 40 * 2533187 * 2
def baseEnd_2533187 : Nat := 433580839573695209304197

theorem tailTrace_2533187 : CollatzResearch.WordTrace tailWord_2533187 prefixEnd_2533187 433580839573695209304197 := by
  unfold tailWord_2533187
  simp only [CollatzResearch.WordTrace]
  refine ⟨92392920273703607740965815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61595280182469071827310543 92392920273703607740965815)
  ·
    refine ⟨138589380410555411611448723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92392920273703607740965815 138589380410555411611448723)
    ·
      refine ⟨207884070615833117417173085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138589380410555411611448723 207884070615833117417173085)
      ·
        refine ⟨77956526480937419031439907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207884070615833117417173085 77956526480937419031439907)
        ·
          refine ⟨116934789721406128547159861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77956526480937419031439907 116934789721406128547159861)
          ·
            refine ⟨10962636536381824551296237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116934789721406128547159861 10962636536381824551296237)
            ·
              refine ⟨4110988701143184206736089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10962636536381824551296237 4110988701143184206736089)
              ·
                refine ⟨3083241525857388155052067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4110988701143184206736089 3083241525857388155052067)
                ·
                  refine ⟨4624862288786082232578101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083241525857388155052067 4624862288786082232578101)
                  ·
                    refine ⟨433580839573695209304197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4624862288786082232578101 433580839573695209304197)
                    ·
                      rfl

theorem cell23_2533187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 5].length) (baseStart_2533187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533187 prefixEnd_2533187 := by exact prefixLift 2533187
  have htrace : WordTrace (prefixWord ++ tailWord_2533187) baseStart_2533187 baseEnd_2533187 := by
    simpa [prefixWord, tailWord_2533187, baseEnd_2533187] using wordTrace_append hprefix tailTrace_2533187
  have hstable : (prefixWord ++ tailWord_2533187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533187).length < 2 ^ (prefixWord ++ tailWord_2533187).sum := by decide
  have hdescent : baseEnd_2533187 < baseStart_2533187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533194 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_2533194 : Nat := 118140960795 + 2533194 * 2 ^ 59
def prefixEnd_2533194 : Nat := 4983230072969 + 3 ^ 40 * 2533194 * 2
def baseEnd_2533194 : Nat := 1300746113085667100525059

theorem tailTrace_2533194 : CollatzResearch.WordTrace tailWord_2533194 prefixEnd_2533194 1300746113085667100525059 := by
  unfold tailWord_2533194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23098293896169561984117659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61595450389785498624313757 23098293896169561984117659)
  ·
    refine ⟨34647440844254342976176489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23098293896169561984117659 34647440844254342976176489)
    ·
      refine ⟨25985580633190757232132367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34647440844254342976176489 25985580633190757232132367)
      ·
        refine ⟨38978370949786135848198551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25985580633190757232132367 38978370949786135848198551)
        ·
          refine ⟨58467556424679203772297827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38978370949786135848198551 58467556424679203772297827)
          ·
            refine ⟨87701334637018805658446741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58467556424679203772297827 87701334637018805658446741)
            ·
              refine ⟨4111000061110256515239691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87701334637018805658446741 4111000061110256515239691)
              ·
                refine ⟨6166500091665384772859537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111000061110256515239691 6166500091665384772859537)
                ·
                  refine ⟨4624875068749038579644653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6166500091665384772859537 4624875068749038579644653)
                  ·
                    refine ⟨1734328150780889467366745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4624875068749038579644653 1734328150780889467366745)
                    ·
                      refine ⟨1300746113085667100525059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734328150780889467366745 1300746113085667100525059)
                      ·
                        rfl

theorem cell23_2533194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_2533194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533194 prefixEnd_2533194 := by exact prefixLift 2533194
  have htrace : WordTrace (prefixWord ++ tailWord_2533194) baseStart_2533194 baseEnd_2533194 := by
    simpa [prefixWord, tailWord_2533194, baseEnd_2533194] using wordTrace_append hprefix tailTrace_2533194
  have hstable : (prefixWord ++ tailWord_2533194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533194).length < 2 ^ (prefixWord ++ tailWord_2533194).sum := by decide
  have hdescent : baseEnd_2533194 < baseStart_2533194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533218 : List Nat := [3, 3, 2, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_2533218 : Nat := 118140960795 + 2533218 * 2 ^ 59
def prefixEnd_2533218 : Nat := 4983230072969 + 3 ^ 40 * 2533218 * 2
def baseEnd_2533218 : Nat := 1300758436621375006624949

theorem tailTrace_2533218 : CollatzResearch.WordTrace tailWord_2533218 prefixEnd_2533218 1300758436621375006624949 := by
  unfold tailWord_2533218
  simp only [CollatzResearch.WordTrace]
  refine ⟨23098512734147825008836077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61596033957727533356896205 23098512734147825008836077)
  ·
    refine ⟨8661942275305434378313529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23098512734147825008836077 8661942275305434378313529)
    ·
      refine ⟨6496456706479075783735147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8661942275305434378313529 6496456706479075783735147)
      ·
        refine ⟨9744685059718613675602721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6496456706479075783735147 9744685059718613675602721)
        ·
          refine ⟨7308513794788960256702041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9744685059718613675602721 7308513794788960256702041)
          ·
            refine ⟨5481385346091720192526531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7308513794788960256702041 5481385346091720192526531)
            ·
              refine ⟨8222078019137580288789797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481385346091720192526531 8222078019137580288789797)
              ·
                refine ⟨1541639628588296304148087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8222078019137580288789797 1541639628588296304148087)
                ·
                  refine ⟨2312459442882444456222131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541639628588296304148087 2312459442882444456222131)
                  ·
                    refine ⟨3468689164323666684333197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2312459442882444456222131 3468689164323666684333197)
                    ·
                      refine ⟨1300758436621375006624949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3468689164323666684333197 1300758436621375006624949)
                      ·
                        rfl

theorem cell23_2533218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_2533218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533218 prefixEnd_2533218 := by exact prefixLift 2533218
  have htrace : WordTrace (prefixWord ++ tailWord_2533218) baseStart_2533218 baseEnd_2533218 := by
    simpa [prefixWord, tailWord_2533218, baseEnd_2533218] using wordTrace_append hprefix tailTrace_2533218
  have hstable : (prefixWord ++ tailWord_2533218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533218).length < 2 ^ (prefixWord ++ tailWord_2533218).sum := by decide
  have hdescent : baseEnd_2533218 < baseStart_2533218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533257 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 3]
def baseStart_2533257 : Nat := 118140960795 + 2533257 * 2 ^ 59
def prefixEnd_2533257 : Nat := 4983230072969 + 3 ^ 40 * 2533257 * 2
def baseEnd_2533257 : Nat := 1300778462366900354037269

theorem tailTrace_2533257 : CollatzResearch.WordTrace tailWord_2533257 prefixEnd_2533257 1300778462366900354037269 := by
  unfold tailWord_2533257
  simp only [CollatzResearch.WordTrace]
  refine ⟨92395473383450009696014025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61596982255633339797342683 92395473383450009696014025)
  ·
    refine ⟨69296605037587507272010519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92395473383450009696014025 69296605037587507272010519)
    ·
      refine ⟨103944907556381260908015779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69296605037587507272010519 103944907556381260908015779)
      ·
        refine ⟨155917361334571891362023669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103944907556381260908015779 155917361334571891362023669)
        ·
          refine ⟨14617252625116114815189719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155917361334571891362023669 14617252625116114815189719)
          ·
            refine ⟨21925878937674172222784579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14617252625116114815189719 21925878937674172222784579)
            ·
              refine ⟨32888818406511258334176869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21925878937674172222784579 32888818406511258334176869)
              ·
                refine ⟨6166653451220860937658163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32888818406511258334176869 6166653451220860937658163)
                ·
                  refine ⟨9249980176831291406487245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6166653451220860937658163 9249980176831291406487245)
                  ·
                    refine ⟨3468742566311734277432717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9249980176831291406487245 3468742566311734277432717)
                    ·
                      refine ⟨1300778462366900354037269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3468742566311734277432717 1300778462366900354037269)
                      ·
                        rfl

theorem cell23_2533257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_2533257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533257 prefixEnd_2533257 := by exact prefixLift 2533257
  have htrace : WordTrace (prefixWord ++ tailWord_2533257) baseStart_2533257 baseEnd_2533257 := by
    simpa [prefixWord, tailWord_2533257, baseEnd_2533257] using wordTrace_append hprefix tailTrace_2533257
  have hstable : (prefixWord ++ tailWord_2533257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533257).length < 2 ^ (prefixWord ++ tailWord_2533257).sum := by decide
  have hdescent : baseEnd_2533257 < baseStart_2533257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533258 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_2533258 : Nat := 118140960795 + 2533258 * 2 ^ 59
def prefixEnd_2533258 : Nat := 4983230072969 + 3 ^ 40 * 2533258 * 2
def baseEnd_2533258 : Nat := 1300778975847554850124765

theorem tailTrace_2533258 : CollatzResearch.WordTrace tailWord_2533258 prefixEnd_2533258 1300778975847554850124765 := by
  unfold tailWord_2533258
  simp only [CollatzResearch.WordTrace]
  refine ⟨23098877464111596716700107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61597006570964257911200285 23098877464111596716700107)
  ·
    refine ⟨34648316196167395075050161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23098877464111596716700107 34648316196167395075050161)
    ·
      refine ⟨25986237147125546306287621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34648316196167395075050161 25986237147125546306287621)
      ·
        refine ⟨4872419465086039932428929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25986237147125546306287621 4872419465086039932428929)
        ·
          refine ⟨3654314598814529949321697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4872419465086039932428929 3654314598814529949321697)
          ·
            refine ⟨2740735949110897461991273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3654314598814529949321697 2740735949110897461991273)
            ·
              refine ⟨2055551961833173096493455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2740735949110897461991273 2055551961833173096493455)
              ·
                refine ⟨3083327942749759644740183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055551961833173096493455 3083327942749759644740183)
                ·
                  refine ⟨4624991914124639467110275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083327942749759644740183 4624991914124639467110275)
                  ·
                    refine ⟨6937487871186959200665413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4624991914124639467110275 6937487871186959200665413)
                    ·
                      refine ⟨1300778975847554850124765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6937487871186959200665413 1300778975847554850124765)
                      ·
                        rfl

theorem cell23_2533258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_2533258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533258 prefixEnd_2533258 := by exact prefixLift 2533258
  have htrace : WordTrace (prefixWord ++ tailWord_2533258) baseStart_2533258 baseEnd_2533258 := by
    simpa [prefixWord, tailWord_2533258, baseEnd_2533258] using wordTrace_append hprefix tailTrace_2533258
  have hstable : (prefixWord ++ tailWord_2533258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533258).length < 2 ^ (prefixWord ++ tailWord_2533258).sum := by decide
  have hdescent : baseEnd_2533258 < baseStart_2533258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533288 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2533288 : Nat := 118140960795 + 2533288 * 2 ^ 59
def prefixEnd_2533288 : Nat := 4983230072969 + 3 ^ 40 * 2533288 * 2
def baseEnd_2533288 : Nat := 1300794380267189732749627

theorem tailTrace_2533288 : CollatzResearch.WordTrace tailWord_2533288 prefixEnd_2533288 1300794380267189732749627 := by
  unfold tailWord_2533288
  simp only [CollatzResearch.WordTrace]
  refine ⟨46198302023168850995196259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61597736030891801326928345 46198302023168850995196259)
  ·
    refine ⟨69297453034753276492794389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46198302023168850995196259 69297453034753276492794389)
    ·
      refine ⟨3248318111004059835599737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69297453034753276492794389 3248318111004059835599737)
      ·
        refine ⟨2436238583253044876699803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3248318111004059835599737 2436238583253044876699803)
        ·
          refine ⟨3654357874879567315049705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436238583253044876699803 3654357874879567315049705)
          ·
            refine ⟨2740768406159675486287279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3654357874879567315049705 2740768406159675486287279)
            ·
              refine ⟨4111152609239513229430919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2740768406159675486287279 4111152609239513229430919)
              ·
                refine ⟨6166728913859269844146379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111152609239513229430919 6166728913859269844146379)
                ·
                  refine ⟨9250093370788904766219569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6166728913859269844146379 9250093370788904766219569)
                  ·
                    refine ⟨6937570028091678574664677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9250093370788904766219569 6937570028091678574664677)
                    ·
                      refine ⟨1300794380267189732749627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6937570028091678574664677 1300794380267189732749627)
                      ·
                        rfl

theorem cell23_2533288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2533288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533288 prefixEnd_2533288 := by exact prefixLift 2533288
  have htrace : WordTrace (prefixWord ++ tailWord_2533288) baseStart_2533288 baseEnd_2533288 := by
    simpa [prefixWord, tailWord_2533288, baseEnd_2533288] using wordTrace_append hprefix tailTrace_2533288
  have hstable : (prefixWord ++ tailWord_2533288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533288).length < 2 ^ (prefixWord ++ tailWord_2533288).sum := by decide
  have hdescent : baseEnd_2533288 < baseStart_2533288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533301 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 1, 3, 2]
def baseStart_2533301 : Nat := 118140960795 + 2533301 * 2 ^ 59
def prefixEnd_2533301 : Nat := 4983230072969 + 3 ^ 40 * 2533301 * 2
def baseEnd_2533301 : Nat := 1300801055515698181887067

theorem tailTrace_2533301 : CollatzResearch.WordTrace tailWord_2533301 prefixEnd_2533301 1300801055515698181887067 := by
  unfold tailWord_2533301
  simp only [CollatzResearch.WordTrace]
  refine ⟨92397078195290605210615757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61598052130193736807077171 92397078195290605210615757)
  ·
    refine ⟨34648904323233976953980909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92397078195290605210615757 34648904323233976953980909)
    ·
      refine ⟨12993339121212741357742841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34648904323233976953980909 12993339121212741357742841)
      ·
        refine ⟨9745004340909556018307131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12993339121212741357742841 9745004340909556018307131)
        ·
          refine ⟨14617506511364334027460697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9745004340909556018307131 14617506511364334027460697)
          ·
            refine ⟨10963129883523250520595523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14617506511364334027460697 10963129883523250520595523)
            ·
              refine ⟨16444694825284875780893285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10963129883523250520595523 16444694825284875780893285)
              ·
                refine ⟨3083380279740914208917491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16444694825284875780893285 3083380279740914208917491)
                ·
                  refine ⟨4625070419611371313376237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083380279740914208917491 4625070419611371313376237)
                  ·
                    refine ⟨1734401407354264242516089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4625070419611371313376237 1734401407354264242516089)
                    ·
                      refine ⟨1300801055515698181887067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734401407354264242516089 1300801055515698181887067)
                      ·
                        rfl

theorem cell23_2533301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_2533301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533301 prefixEnd_2533301 := by exact prefixLift 2533301
  have htrace : WordTrace (prefixWord ++ tailWord_2533301) baseStart_2533301 baseEnd_2533301 := by
    simpa [prefixWord, tailWord_2533301, baseEnd_2533301] using wordTrace_append hprefix tailTrace_2533301
  have hstable : (prefixWord ++ tailWord_2533301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533301).length < 2 ^ (prefixWord ++ tailWord_2533301).sum := by decide
  have hdescent : baseEnd_2533301 < baseStart_2533301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533377 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2533377 : Nat := 118140960795 + 2533377 * 2 ^ 59
def prefixEnd_2533377 : Nat := 4983230072969 + 3 ^ 40 * 2533377 * 2
def baseEnd_2533377 : Nat := 1300840080045439884536717

theorem tailTrace_2533377 : CollatzResearch.WordTrace tailWord_2533377 prefixEnd_2533377 1300840080045439884536717 := by
  unfold tailWord_2533377
  simp only [CollatzResearch.WordTrace]
  refine ⟨92399850143015270190382385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61599900095343513460254923 92399850143015270190382385)
  ·
    refine ⟨69299887607261452642786789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92399850143015270190382385 69299887607261452642786789)
    ·
      refine ⟨12993728926361522370522523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69299887607261452642786789 12993728926361522370522523)
      ·
        refine ⟨19490593389542283555783785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12993728926361522370522523 19490593389542283555783785)
        ·
          refine ⟨14617945042156712666837839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19490593389542283555783785 14617945042156712666837839)
          ·
            refine ⟨21926917563235069000256759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14617945042156712666837839 21926917563235069000256759)
            ·
              refine ⟨32890376344852603500385139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21926917563235069000256759 32890376344852603500385139)
              ·
                refine ⟨49335564517278905250577709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32890376344852603500385139 49335564517278905250577709)
                ·
                  refine ⟨18500836693979589468966641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49335564517278905250577709 18500836693979589468966641)
                  ·
                    refine ⟨13875627520484692101724981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18500836693979589468966641 13875627520484692101724981)
                    ·
                      refine ⟨1300840080045439884536717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13875627520484692101724981 1300840080045439884536717)
                      ·
                        rfl

theorem cell23_2533377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2533377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533377 prefixEnd_2533377 := by exact prefixLift 2533377
  have htrace : WordTrace (prefixWord ++ tailWord_2533377) baseStart_2533377 baseEnd_2533377 := by
    simpa [prefixWord, tailWord_2533377, baseEnd_2533377] using wordTrace_append hprefix tailTrace_2533377
  have hstable : (prefixWord ++ tailWord_2533377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533377).length < 2 ^ (prefixWord ++ tailWord_2533377).sum := by decide
  have hdescent : baseEnd_2533377 < baseStart_2533377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533424 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 3]
def baseStart_2533424 : Nat := 118140960795 + 2533424 * 2 ^ 59
def prefixEnd_2533424 : Nat := 4983230072969 + 3 ^ 40 * 2533424 * 2
def baseEnd_2533424 : Nat := 1300864213636201200649001

theorem tailTrace_2533424 : CollatzResearch.WordTrace tailWord_2533424 prefixEnd_2533424 1300864213636201200649001 := by
  unfold tailWord_2533424
  simp only [CollatzResearch.WordTrace]
  refine ⟨46200782186922498608671663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61601042915896664811562217 46200782186922498608671663)
  ·
    refine ⟨69301173280383747913007495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46200782186922498608671663 69301173280383747913007495)
    ·
      refine ⟨103951759920575621869511243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69301173280383747913007495 103951759920575621869511243)
      ·
        refine ⟨155927639880863432804266865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103951759920575621869511243 155927639880863432804266865)
        ·
          refine ⟨116945729910647574603200149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155927639880863432804266865 116945729910647574603200149)
          ·
            refine ⟨5481831089561605059525007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116945729910647574603200149 5481831089561605059525007)
            ·
              refine ⟨8222746634342407589287511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481831089561605059525007 8222746634342407589287511)
              ·
                refine ⟨12334119951513611383931267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8222746634342407589287511 12334119951513611383931267)
                ·
                  refine ⟨18501179927270417075896901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12334119951513611383931267 18501179927270417075896901)
                  ·
                    refine ⟨3468971236363203201730669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18501179927270417075896901 3468971236363203201730669)
                    ·
                      refine ⟨1300864213636201200649001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3468971236363203201730669 1300864213636201200649001)
                      ·
                        rfl

theorem cell23_2533424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_2533424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533424 prefixEnd_2533424 := by exact prefixLift 2533424
  have htrace : WordTrace (prefixWord ++ tailWord_2533424) baseStart_2533424 baseEnd_2533424 := by
    simpa [prefixWord, tailWord_2533424, baseEnd_2533424] using wordTrace_append hprefix tailTrace_2533424
  have hstable : (prefixWord ++ tailWord_2533424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533424).length < 2 ^ (prefixWord ++ tailWord_2533424).sum := by decide
  have hdescent : baseEnd_2533424 < baseStart_2533424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533431 : List Nat := [1, 1, 3, 1, 2, 2, 3, 5, 1, 4]
def baseStart_2533431 : Nat := 118140960795 + 2533431 * 2 ^ 59
def prefixEnd_2533431 : Nat := 4983230072969 + 3 ^ 40 * 2533431 * 2
def baseEnd_2533431 : Nat := 433622602666927557753823

theorem tailTrace_2533431 : CollatzResearch.WordTrace tailWord_2533431 prefixEnd_2533431 433622602666927557753823 := by
  unfold tailWord_2533431
  simp only [CollatzResearch.WordTrace]
  refine ⟨92401819684819637412848147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61601213123213091608565431 92401819684819637412848147)
  ·
    refine ⟨138602729527229456119272221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92401819684819637412848147 138602729527229456119272221)
    ·
      refine ⟨51976023572711046044727083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138602729527229456119272221 51976023572711046044727083)
      ·
        refine ⟨77964035359066569067090625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51976023572711046044727083 77964035359066569067090625)
        ·
          refine ⟨58473026519299926800317969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77964035359066569067090625 58473026519299926800317969)
          ·
            refine ⟨43854769889474945100238477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58473026519299926800317969 43854769889474945100238477)
            ·
              refine ⟨16445538708553104412589429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43854769889474945100238477 16445538708553104412589429)
              ·
                refine ⟨1541769253926853538680259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16445538708553104412589429 1541769253926853538680259)
                ·
                  refine ⟨2312653880890280308020389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541769253926853538680259 2312653880890280308020389)
                  ·
                    refine ⟨433622602666927557753823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2312653880890280308020389 433622602666927557753823)
                    ·
                      rfl

theorem cell23_2533431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_2533431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533431 prefixEnd_2533431 := by exact prefixLift 2533431
  have htrace : WordTrace (prefixWord ++ tailWord_2533431) baseStart_2533431 baseEnd_2533431 := by
    simpa [prefixWord, tailWord_2533431, baseEnd_2533431] using wordTrace_append hprefix tailTrace_2533431
  have hstable : (prefixWord ++ tailWord_2533431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533431).length < 2 ^ (prefixWord ++ tailWord_2533431).sum := by decide
  have hdescent : baseEnd_2533431 < baseStart_2533431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533447 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_2533447 : Nat := 118140960795 + 2533447 * 2 ^ 59
def prefixEnd_2533447 : Nat := 4983230072969 + 3 ^ 40 * 2533447 * 2
def baseEnd_2533447 : Nat := 1300876023691254610661395

theorem tailTrace_2533447 : CollatzResearch.WordTrace tailWord_2533447 prefixEnd_2533447 1300876023691254610661395 := by
  unfold tailWord_2533447
  simp only [CollatzResearch.WordTrace]
  refine ⟨92402403252761672145430595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61601602168507781430287063 92402403252761672145430595)
  ·
    refine ⟨138603604879142508218145893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92402403252761672145430595 138603604879142508218145893)
    ·
      refine ⟨25988175914839220290902355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138603604879142508218145893 25988175914839220290902355)
      ·
        refine ⟨38982263872258830436353533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25988175914839220290902355 38982263872258830436353533)
        ·
          refine ⟨14618348952097061413632575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38982263872258830436353533 14618348952097061413632575)
          ·
            refine ⟨21927523428145592120448863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14618348952097061413632575 21927523428145592120448863)
            ·
              refine ⟨32891285142218388180673295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21927523428145592120448863 32891285142218388180673295)
              ·
                refine ⟨49336927713327582271009943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32891285142218388180673295 49336927713327582271009943)
                ·
                  refine ⟨74005391569991373406514915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49336927713327582271009943 74005391569991373406514915)
                  ·
                    refine ⟨111008087354987060109772373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74005391569991373406514915 111008087354987060109772373)
                    ·
                      refine ⟨1300876023691254610661395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 111008087354987060109772373 1300876023691254610661395)
                      ·
                        rfl

theorem cell23_2533447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_2533447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533447 prefixEnd_2533447 := by exact prefixLift 2533447
  have htrace : WordTrace (prefixWord ++ tailWord_2533447) baseStart_2533447 baseEnd_2533447 := by
    simpa [prefixWord, tailWord_2533447, baseEnd_2533447] using wordTrace_append hprefix tailTrace_2533447
  have hstable : (prefixWord ++ tailWord_2533447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533447).length < 2 ^ (prefixWord ++ tailWord_2533447).sum := by decide
  have hdescent : baseEnd_2533447 < baseStart_2533447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533461 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 6]
def baseStart_2533461 : Nat := 118140960795 + 2533461 * 2 ^ 59
def prefixEnd_2533461 : Nat := 4983230072969 + 3 ^ 40 * 2533461 * 2
def baseEnd_2533461 : Nat := 144542579157824172876259

theorem tailTrace_2533461 : CollatzResearch.WordTrace tailWord_2533461 prefixEnd_2533461 144542579157824172876259 := by
  unfold tailWord_2533461
  simp only [CollatzResearch.WordTrace]
  refine ⟨92402913874710952536440237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61601942583140635024293491 92402913874710952536440237)
  ·
    refine ⟨34651092703016607201165089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92402913874710952536440237 34651092703016607201165089)
    ·
      refine ⟨25988319527262455400873817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34651092703016607201165089 25988319527262455400873817)
      ·
        refine ⟨19491239645446841550655363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25988319527262455400873817 19491239645446841550655363)
        ·
          refine ⟨29236859468170262325983045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19491239645446841550655363 29236859468170262325983045)
          ·
            refine ⟨5481911150281924186121821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29236859468170262325983045 5481911150281924186121821)
            ·
              refine ⟨2055716681355721569795683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5481911150281924186121821 2055716681355721569795683)
              ·
                refine ⟨3083575022033582354693525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055716681355721569795683 3083575022033582354693525)
                ·
                  refine ⟨144542579157824172876259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3083575022033582354693525 144542579157824172876259)
                  ·
                    rfl

theorem cell23_2533461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 6].length) (baseStart_2533461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533461 prefixEnd_2533461 := by exact prefixLift 2533461
  have htrace : WordTrace (prefixWord ++ tailWord_2533461) baseStart_2533461 baseEnd_2533461 := by
    simpa [prefixWord, tailWord_2533461, baseEnd_2533461] using wordTrace_append hprefix tailTrace_2533461
  have hstable : (prefixWord ++ tailWord_2533461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533461).length < 2 ^ (prefixWord ++ tailWord_2533461).sum := by decide
  have hdescent : baseEnd_2533461 < baseStart_2533461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533481 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 2, 3, 2]
def baseStart_2533481 : Nat := 118140960795 + 2533481 * 2 ^ 59
def prefixEnd_2533481 : Nat := 4983230072969 + 3 ^ 40 * 2533481 * 2
def baseEnd_2533481 : Nat := 1300893482033507477636239

theorem tailTrace_2533481 : CollatzResearch.WordTrace tailWord_2533481 prefixEnd_2533481 1300893482033507477636239 := by
  unfold tailWord_2533481
  simp only [CollatzResearch.WordTrace]
  refine ⟨92403643334638495952168297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61602428889758997301445531 92403643334638495952168297)
  ·
    refine ⟨69302732500978871964126223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92403643334638495952168297 69302732500978871964126223)
    ·
      refine ⟨103954098751468307946189335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69302732500978871964126223 103954098751468307946189335)
      ·
        refine ⟨155931148127202461919284003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103954098751468307946189335 155931148127202461919284003)
        ·
          refine ⟨233896722190803692878926005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155931148127202461919284003 233896722190803692878926005)
          ·
            refine ⟨21927817705387846207399313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 233896722190803692878926005 21927817705387846207399313)
            ·
              refine ⟨16445863279040884655549485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21927817705387846207399313 16445863279040884655549485)
              ·
                refine ⟨6167198729640331745831057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16445863279040884655549485 6167198729640331745831057)
                ·
                  refine ⟨4625399047230248809373293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6167198729640331745831057 4625399047230248809373293)
                  ·
                    refine ⟨1734524642711343303514985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4625399047230248809373293 1734524642711343303514985)
                    ·
                      refine ⟨1300893482033507477636239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734524642711343303514985 1300893482033507477636239)
                      ·
                        rfl

theorem cell23_2533481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 3, 2].length) (baseStart_2533481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533481 prefixEnd_2533481 := by exact prefixLift 2533481
  have htrace : WordTrace (prefixWord ++ tailWord_2533481) baseStart_2533481 baseEnd_2533481 := by
    simpa [prefixWord, tailWord_2533481, baseEnd_2533481] using wordTrace_append hprefix tailTrace_2533481
  have hstable : (prefixWord ++ tailWord_2533481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533481).length < 2 ^ (prefixWord ++ tailWord_2533481).sum := by decide
  have hdescent : baseEnd_2533481 < baseStart_2533481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533482 : List Nat := [3, 1, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_2533482 : Nat := 118140960795 + 2533482 * 2 ^ 59
def prefixEnd_2533482 : Nat := 4983230072969 + 3 ^ 40 * 2533482 * 2
def baseEnd_2533482 : Nat := 433631331838053991241245

theorem tailTrace_2533482 : CollatzResearch.WordTrace tailWord_2533482 prefixEnd_2533482 433631331838053991241245 := by
  unfold tailWord_2533482
  simp only [CollatzResearch.WordTrace]
  refine ⟨23100919951908718280738675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61602453205089915415303133 23100919951908718280738675)
  ·
    refine ⟨34651379927863077421108013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23100919951908718280738675 34651379927863077421108013)
    ·
      refine ⟨12994267472948654032915505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34651379927863077421108013 12994267472948654032915505)
      ·
        refine ⟨9745700604711490524686629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12994267472948654032915505 9745700604711490524686629)
        ·
          refine ⟨1827318863383404473378743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9745700604711490524686629 1827318863383404473378743)
          ·
            refine ⟨2740978295075106710068115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827318863383404473378743 2740978295075106710068115)
            ·
              refine ⟨4111467442612660065102173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2740978295075106710068115 4111467442612660065102173)
              ·
                refine ⟨1541800290979747524413315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4111467442612660065102173 1541800290979747524413315)
                ·
                  refine ⟨2312700436469621286619973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541800290979747524413315 2312700436469621286619973)
                  ·
                    refine ⟨433631331838053991241245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2312700436469621286619973 433631331838053991241245)
                    ·
                      rfl

theorem cell23_2533482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_2533482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533482 prefixEnd_2533482 := by exact prefixLift 2533482
  have htrace : WordTrace (prefixWord ++ tailWord_2533482) baseStart_2533482 baseEnd_2533482 := by
    simpa [prefixWord, tailWord_2533482, baseEnd_2533482] using wordTrace_append hprefix tailTrace_2533482
  have hstable : (prefixWord ++ tailWord_2533482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533482).length < 2 ^ (prefixWord ++ tailWord_2533482).sum := by decide
  have hdescent : baseEnd_2533482 < baseStart_2533482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533505 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2533505 : Nat := 118140960795 + 2533505 * 2 ^ 59
def prefixEnd_2533505 : Nat := 4983230072969 + 3 ^ 40 * 2533505 * 2
def baseEnd_2533505 : Nat := 1300905805569215383736129

theorem tailTrace_2533505 : CollatzResearch.WordTrace tailWord_2533505 prefixEnd_2533505 1300905805569215383736129 := by
  unfold tailWord_2533505
  simp only [CollatzResearch.WordTrace]
  refine ⟨92404518686551548051041969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61603012457701032034027979 92404518686551548051041969)
  ·
    refine ⟨69303389014913661038281477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92404518686551548051041969 69303389014913661038281477)
    ·
      refine ⟨12994385440296311444677777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69303389014913661038281477 12994385440296311444677777)
      ·
        refine ⟨9745789080222233583508333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12994385440296311444677777 9745789080222233583508333)
        ·
          refine ⟨3654670905083337593815625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9745789080222233583508333 3654670905083337593815625)
          ·
            refine ⟨2741003178812503195361719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3654670905083337593815625 2741003178812503195361719)
            ·
              refine ⟨4111504768218754793042579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741003178812503195361719 4111504768218754793042579)
              ·
                refine ⟨6167257152328132189563869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111504768218754793042579 6167257152328132189563869)
                ·
                  refine ⟨2312721432123049571086451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6167257152328132189563869 2312721432123049571086451)
                  ·
                    refine ⟨3469082148184574356629677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2312721432123049571086451 3469082148184574356629677)
                    ·
                      refine ⟨1300905805569215383736129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3469082148184574356629677 1300905805569215383736129)
                      ·
                        rfl

theorem cell23_2533505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2533505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533505 prefixEnd_2533505 := by exact prefixLift 2533505
  have htrace : WordTrace (prefixWord ++ tailWord_2533505) baseStart_2533505 baseEnd_2533505 := by
    simpa [prefixWord, tailWord_2533505, baseEnd_2533505] using wordTrace_append hprefix tailTrace_2533505
  have hstable : (prefixWord ++ tailWord_2533505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533505).length < 2 ^ (prefixWord ++ tailWord_2533505).sum := by decide
  have hdescent : baseEnd_2533505 < baseStart_2533505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533556 : List Nat := [2, 5, 3, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_2533556 : Nat := 118140960795 + 2533556 * 2 ^ 59
def prefixEnd_2533556 : Nat := 4983230072969 + 3 ^ 40 * 2533556 * 2
def baseEnd_2533556 : Nat := 1300931993082594684198395

theorem tailTrace_2533556 : CollatzResearch.WordTrace tailWord_2533556 prefixEnd_2533556 1300931993082594684198395 := by
  unfold tailWord_2533556
  simp only [CollatzResearch.WordTrace]
  refine ⟨46203189404683391880574261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61604252539577855840765681 46203189404683391880574261)
  ·
    refine ⟨4331549006689067988803837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46203189404683391880574261 4331549006689067988803837)
    ·
      refine ⟨1624330877508400495801439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4331549006689067988803837 1624330877508400495801439)
      ·
        refine ⟨2436496316262600743702159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624330877508400495801439 2436496316262600743702159)
        ·
          refine ⟨3654744474393901115553239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436496316262600743702159 3654744474393901115553239)
          ·
            refine ⟨5482116711590851673329859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654744474393901115553239 5482116711590851673329859)
            ·
              refine ⟨8223175067386277509994789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482116711590851673329859 8223175067386277509994789)
              ·
                refine ⟨1541845325134927033124023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8223175067386277509994789 1541845325134927033124023)
                ·
                  refine ⟨2312767987702390549686035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541845325134927033124023 2312767987702390549686035)
                  ·
                    refine ⟨3469151981553585824529053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2312767987702390549686035 3469151981553585824529053)
                    ·
                      refine ⟨1300931993082594684198395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3469151981553585824529053 1300931993082594684198395)
                      ·
                        rfl

theorem cell23_2533556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_2533556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533556 prefixEnd_2533556 := by exact prefixLift 2533556
  have htrace : WordTrace (prefixWord ++ tailWord_2533556) baseStart_2533556 baseEnd_2533556 := by
    simpa [prefixWord, tailWord_2533556, baseEnd_2533556] using wordTrace_append hprefix tailTrace_2533556
  have hstable : (prefixWord ++ tailWord_2533556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533556).length < 2 ^ (prefixWord ++ tailWord_2533556).sum := by decide
  have hdescent : baseEnd_2533556 < baseStart_2533556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533562 : List Nat := [3, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2]
def baseStart_2533562 : Nat := 118140960795 + 2533562 * 2 ^ 59
def prefixEnd_2533562 : Nat := 4983230072969 + 3 ^ 40 * 2533562 * 2
def baseEnd_2533562 : Nat := 1300935073966521660723367

theorem tailTrace_2533562 : CollatzResearch.WordTrace tailWord_2533562 prefixEnd_2533562 1300935073966521660723367 := by
  unfold tailWord_2533562
  simp only [CollatzResearch.WordTrace]
  refine ⟨23101649411836261696466735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61604398431563364523911293 23101649411836261696466735)
  ·
    refine ⟨34652474117754392544700103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23101649411836261696466735 34652474117754392544700103)
    ·
      refine ⟨51978711176631588817050155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34652474117754392544700103 51978711176631588817050155)
      ·
        refine ⟨77968066764947383225575233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51978711176631588817050155 77968066764947383225575233)
        ·
          refine ⟨58476050073710537419181425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77968066764947383225575233 58476050073710537419181425)
          ·
            refine ⟨43857037555282903064386069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58476050073710537419181425 43857037555282903064386069)
            ·
              refine ⟨2055798635403886081143097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43857037555282903064386069 2055798635403886081143097)
              ·
                refine ⟨1541848976552914560857323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055798635403886081143097 1541848976552914560857323)
                ·
                  refine ⟨2312773464829371841285985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541848976552914560857323 2312773464829371841285985)
                  ·
                    refine ⟨1734580098622028880964489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2312773464829371841285985 1734580098622028880964489)
                    ·
                      refine ⟨1300935073966521660723367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734580098622028880964489 1300935073966521660723367)
                      ·
                        rfl

theorem cell23_2533562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_2533562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533562 prefixEnd_2533562 := by exact prefixLift 2533562
  have htrace : WordTrace (prefixWord ++ tailWord_2533562) baseStart_2533562 baseEnd_2533562 := by
    simpa [prefixWord, tailWord_2533562, baseEnd_2533562] using wordTrace_append hprefix tailTrace_2533562
  have hstable : (prefixWord ++ tailWord_2533562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533562).length < 2 ^ (prefixWord ++ tailWord_2533562).sum := by decide
  have hdescent : baseEnd_2533562 < baseStart_2533562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533578 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_2533578 : Nat := 118140960795 + 2533578 * 2 ^ 59
def prefixEnd_2533578 : Nat := 4983230072969 + 3 ^ 40 * 2533578 * 2
def baseEnd_2533578 : Nat := 1300943289656993598123293

theorem tailTrace_2533578 : CollatzResearch.WordTrace tailWord_2533578 prefixEnd_2533578 1300943289656993598123293 := by
  unfold tailWord_2533578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23101795303821770379612347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61604787476858054345632925 23101795303821770379612347)
  ·
    refine ⟨34652692955732655569418521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23101795303821770379612347 34652692955732655569418521)
    ·
      refine ⟨25989519716799491677063891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34652692955732655569418521 25989519716799491677063891)
      ·
        refine ⟨38984279575199237515595837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25989519716799491677063891 38984279575199237515595837)
        ·
          refine ⟨14619104840699714068348439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38984279575199237515595837 14619104840699714068348439)
          ·
            refine ⟨21928657261049571102522659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14619104840699714068348439 21928657261049571102522659)
            ·
              refine ⟨32892985891574356653783989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21928657261049571102522659 32892985891574356653783989)
              ·
                refine ⟨3083717427335095936292249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32892985891574356653783989 3083717427335095936292249)
                ·
                  refine ⟨2312788070501321952219187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3083717427335095936292249 2312788070501321952219187)
                  ·
                    refine ⟨3469182105751982928328781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2312788070501321952219187 3469182105751982928328781)
                    ·
                      refine ⟨1300943289656993598123293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3469182105751982928328781 1300943289656993598123293)
                      ·
                        rfl

theorem cell23_2533578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_2533578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533578 prefixEnd_2533578 := by exact prefixLift 2533578
  have htrace : WordTrace (prefixWord ++ tailWord_2533578) baseStart_2533578 baseEnd_2533578 := by
    simpa [prefixWord, tailWord_2533578, baseEnd_2533578] using wordTrace_append hprefix tailTrace_2533578
  have hstable : (prefixWord ++ tailWord_2533578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533578).length < 2 ^ (prefixWord ++ tailWord_2533578).sum := by decide
  have hdescent : baseEnd_2533578 < baseStart_2533578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533596 : List Nat := [2, 2, 5, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2533596 : Nat := 118140960795 + 2533596 * 2 ^ 59
def prefixEnd_2533596 : Nat := 4983230072969 + 3 ^ 40 * 2533596 * 2
def baseEnd_2533596 : Nat := 1300952532308774527698211

theorem tailTrace_2533596 : CollatzResearch.WordTrace tailWord_2533596 prefixEnd_2533596 1300952532308774527698211 := by
  unfold tailWord_2533596
  simp only [CollatzResearch.WordTrace]
  refine ⟨46203918864610935296302321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61605225152814580395069761 46203918864610935296302321)
  ·
    refine ⟨34652939148458201472226741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46203918864610935296302321 34652939148458201472226741)
    ·
      refine ⟨3248713045167956388021257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34652939148458201472226741 3248713045167956388021257)
      ·
        refine ⟨2436534783875967291015943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3248713045167956388021257 2436534783875967291015943)
        ·
          refine ⟨3654802175813950936523915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436534783875967291015943 3654802175813950936523915)
          ·
            refine ⟨5482203263720926404785873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654802175813950936523915 5482203263720926404785873)
            ·
              refine ⟨4111652447790694803589405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5482203263720926404785873 4111652447790694803589405)
              ·
                refine ⟨1541869667921510551346027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4111652447790694803589405 1541869667921510551346027)
                ·
                  refine ⟨2312804501882265827019041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541869667921510551346027 2312804501882265827019041)
                  ·
                    refine ⟨1734603376411699370264281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2312804501882265827019041 1734603376411699370264281)
                    ·
                      refine ⟨1300952532308774527698211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734603376411699370264281 1300952532308774527698211)
                      ·
                        rfl

theorem cell23_2533596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2533596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533596 prefixEnd_2533596 := by exact prefixLift 2533596
  have htrace : WordTrace (prefixWord ++ tailWord_2533596) baseStart_2533596 baseEnd_2533596 := by
    simpa [prefixWord, tailWord_2533596, baseEnd_2533596] using wordTrace_append hprefix tailTrace_2533596
  have hstable : (prefixWord ++ tailWord_2533596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533596).length < 2 ^ (prefixWord ++ tailWord_2533596).sum := by decide
  have hdescent : baseEnd_2533596 < baseStart_2533596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533604 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_2533604 : Nat := 118140960795 + 2533604 * 2 ^ 59
def prefixEnd_2533604 : Nat := 4983230072969 + 3 ^ 40 * 2533604 * 2
def baseEnd_2533604 : Nat := 1300956640154010496398173

theorem tailTrace_2533604 : CollatzResearch.WordTrace tailWord_2533604 prefixEnd_2533604 1300956640154010496398173 := by
  unfold tailWord_2533604
  simp only [CollatzResearch.WordTrace]
  refine ⟨46204064756596443979447933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61605419675461925305930577 46204064756596443979447933)
  ·
    refine ⟨17326524283723666492292975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46204064756596443979447933 17326524283723666492292975)
    ·
      refine ⟨25989786425585499738439463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17326524283723666492292975 25989786425585499738439463)
      ·
        refine ⟨38984679638378249607659195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25989786425585499738439463 38984679638378249607659195)
        ·
          refine ⟨58477019457567374411488793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38984679638378249607659195 58477019457567374411488793)
          ·
            refine ⟨43857764593175530808616595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58477019457567374411488793 43857764593175530808616595)
            ·
              refine ⟨65786646889763296212924893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43857764593175530808616595 65786646889763296212924893)
              ·
                refine ⟨24669992583661236079846835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65786646889763296212924893 24669992583661236079846835)
                ·
                  refine ⟨37004988875491854119770253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24669992583661236079846835 37004988875491854119770253)
                  ·
                    refine ⟨13876870828309445294913845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37004988875491854119770253 13876870828309445294913845)
                    ·
                      refine ⟨1300956640154010496398173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13876870828309445294913845 1300956640154010496398173)
                      ·
                        rfl

theorem cell23_2533604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_2533604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533604 prefixEnd_2533604 := by exact prefixLift 2533604
  have htrace : WordTrace (prefixWord ++ tailWord_2533604) baseStart_2533604 baseEnd_2533604 := by
    simpa [prefixWord, tailWord_2533604, baseEnd_2533604] using wordTrace_append hprefix tailTrace_2533604
  have hstable : (prefixWord ++ tailWord_2533604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533604).length < 2 ^ (prefixWord ++ tailWord_2533604).sum := by decide
  have hdescent : baseEnd_2533604 < baseStart_2533604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533605 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 1, 3, 2]
def baseStart_2533605 : Nat := 118140960795 + 2533605 * 2 ^ 59
def prefixEnd_2533605 : Nat := 4983230072969 + 3 ^ 40 * 2533605 * 2
def baseEnd_2533605 : Nat := 1300957153634664992485669

theorem tailTrace_2533605 : CollatzResearch.WordTrace tailWord_2533605 prefixEnd_2533605 1300957153634664992485669 := by
  unfold tailWord_2533605
  simp only [CollatzResearch.WordTrace]
  refine ⟨92408165986189265129682269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61605443990792843419788179 92408165986189265129682269)
  ·
    refine ⟨34653062244820974423630851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92408165986189265129682269 34653062244820974423630851)
    ·
      refine ⟨51979593367231461635446277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34653062244820974423630851 51979593367231461635446277)
      ·
        refine ⟨9746173756355899056646177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51979593367231461635446277 9746173756355899056646177)
        ·
          refine ⟨7309630317266924292484633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9746173756355899056646177 7309630317266924292484633)
          ·
            refine ⟨5482222737950193219363475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7309630317266924292484633 5482222737950193219363475)
            ·
              refine ⟨8223334106925289829045213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482222737950193219363475 8223334106925289829045213)
              ·
                refine ⟨3083750290096983685891955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8223334106925289829045213 3083750290096983685891955)
                ·
                  refine ⟨4625625435145475528837933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083750290096983685891955 4625625435145475528837933)
                  ·
                    refine ⟨1734609538179553323314225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4625625435145475528837933 1734609538179553323314225)
                    ·
                      refine ⟨1300957153634664992485669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734609538179553323314225 1300957153634664992485669)
                      ·
                        rfl

theorem cell23_2533605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_2533605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533605 prefixEnd_2533605 := by exact prefixLift 2533605
  have htrace : WordTrace (prefixWord ++ tailWord_2533605) baseStart_2533605 baseEnd_2533605 := by
    simpa [prefixWord, tailWord_2533605, baseEnd_2533605] using wordTrace_append hprefix tailTrace_2533605
  have hstable : (prefixWord ++ tailWord_2533605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533605).length < 2 ^ (prefixWord ++ tailWord_2533605).sum := by decide
  have hdescent : baseEnd_2533605 < baseStart_2533605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533708 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2533708 : Nat := 118140960795 + 2533708 * 2 ^ 59
def prefixEnd_2533708 : Nat := 4983230072969 + 3 ^ 40 * 2533708 * 2
def baseEnd_2533708 : Nat := 1301010042142078089497695

theorem tailTrace_2533708 : CollatzResearch.WordTrace tailWord_2533708 prefixEnd_2533708 1301010042142078089497695 := by
  unfold tailWord_2533708
  simp only [CollatzResearch.WordTrace]
  refine ⟨46205961352408056860340889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61607948469877409147121185 46205961352408056860340889)
  ·
    refine ⟨34654471014306042645255667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46205961352408056860340889 34654471014306042645255667)
    ·
      refine ⟨51981706521459063967883501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34654471014306042645255667 51981706521459063967883501)
      ·
        refine ⟨19493139945547148987956313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51981706521459063967883501 19493139945547148987956313)
        ·
          refine ⟨14619854959160361740967235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19493139945547148987956313 14619854959160361740967235)
          ·
            refine ⟨21929782438740542611450853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14619854959160361740967235 21929782438740542611450853)
            ·
              refine ⟨4111834207263851739647035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21929782438740542611450853 4111834207263851739647035)
              ·
                refine ⟨6167751310895777609470553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111834207263851739647035 6167751310895777609470553)
                ·
                  refine ⟨4625813483171833207102915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6167751310895777609470553 4625813483171833207102915)
                  ·
                    refine ⟨6938720224757749810654373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4625813483171833207102915 6938720224757749810654373)
                    ·
                      refine ⟨1301010042142078089497695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6938720224757749810654373 1301010042142078089497695)
                      ·
                        rfl

theorem cell23_2533708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2533708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533708 prefixEnd_2533708 := by exact prefixLift 2533708
  have htrace : WordTrace (prefixWord ++ tailWord_2533708) baseStart_2533708 baseEnd_2533708 := by
    simpa [prefixWord, tailWord_2533708, baseEnd_2533708] using wordTrace_append hprefix tailTrace_2533708
  have hstable : (prefixWord ++ tailWord_2533708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533708).length < 2 ^ (prefixWord ++ tailWord_2533708).sum := by decide
  have hdescent : baseEnd_2533708 < baseStart_2533708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533726 : List Nat := [4, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2533726 : Nat := 118140960795 + 2533726 * 2 ^ 59
def prefixEnd_2533726 : Nat := 4983230072969 + 3 ^ 40 * 2533726 * 2
def baseEnd_2533726 : Nat := 144557698310428779896957

theorem tailTrace_2533726 : CollatzResearch.WordTrace tailWord_2533726 prefixEnd_2533726 144557698310428779896957 := by
  unfold tailWord_2533726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11551572402343862849354629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61608386145833935196558021 11551572402343862849354629)
  ·
    refine ⟨2165919825439474284253993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11551572402343862849354629 2165919825439474284253993)
    ·
      refine ⟨1624439869079605713190495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2165919825439474284253993 1624439869079605713190495)
      ·
        refine ⟨2436659803619408569785743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624439869079605713190495 2436659803619408569785743)
        ·
          refine ⟨3654989705429112854678615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436659803619408569785743 3654989705429112854678615)
          ·
            refine ⟨5482484558143669282017923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654989705429112854678615 5482484558143669282017923)
            ·
              refine ⟨8223726837215503923026885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482484558143669282017923 8223726837215503923026885)
              ·
                refine ⟨1541948781977906985567541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8223726837215503923026885 1541948781977906985567541)
                ·
                  refine ⟨144557698310428779896957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1541948781977906985567541 144557698310428779896957)
                  ·
                    rfl

theorem cell23_2533726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2533726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533726 prefixEnd_2533726 := by exact prefixLift 2533726
  have htrace : WordTrace (prefixWord ++ tailWord_2533726) baseStart_2533726 baseEnd_2533726 := by
    simpa [prefixWord, tailWord_2533726, baseEnd_2533726] using wordTrace_append hprefix tailTrace_2533726
  have hstable : (prefixWord ++ tailWord_2533726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533726).length < 2 ^ (prefixWord ++ tailWord_2533726).sum := by decide
  have hdescent : baseEnd_2533726 < baseStart_2533726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533762 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2533762 : Nat := 118140960795 + 2533762 * 2 ^ 59
def prefixEnd_2533762 : Nat := 4983230072969 + 3 ^ 40 * 2533762 * 2
def baseEnd_2533762 : Nat := 1301037770097420878222447

theorem tailTrace_2533762 : CollatzResearch.WordTrace tailWord_2533762 prefixEnd_2533762 1301037770097420878222447 := by
  unfold tailWord_2533762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23103473061655120235786885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61609261497746987295431693 23103473061655120235786885)
  ·
    refine ⟨4331901199060335044210041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23103473061655120235786885 4331901199060335044210041)
    ·
      refine ⟨3248925899295251283157531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4331901199060335044210041 3248925899295251283157531)
      ·
        refine ⟨4873388848942876924736297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3248925899295251283157531 4873388848942876924736297)
        ·
          refine ⟨3655041636707157693552223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4873388848942876924736297 3655041636707157693552223)
          ·
            refine ⟨5482562455060736540328335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655041636707157693552223 5482562455060736540328335)
            ·
              refine ⟨8223843682591104810492503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482562455060736540328335 8223843682591104810492503)
              ·
                refine ⟨12335765523886657215738755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8223843682591104810492503 12335765523886657215738755)
                ·
                  refine ⟨18503648285829985823608133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12335765523886657215738755 18503648285829985823608133)
                  ·
                    refine ⟨3469434053593122341926525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18503648285829985823608133 3469434053593122341926525)
                    ·
                      refine ⟨1301037770097420878222447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3469434053593122341926525 1301037770097420878222447)
                      ·
                        rfl

theorem cell23_2533762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2533762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533762 prefixEnd_2533762 := by exact prefixLift 2533762
  have htrace : WordTrace (prefixWord ++ tailWord_2533762) baseStart_2533762 baseEnd_2533762 := by
    simpa [prefixWord, tailWord_2533762, baseEnd_2533762] using wordTrace_append hprefix tailTrace_2533762
  have hstable : (prefixWord ++ tailWord_2533762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533762).length < 2 ^ (prefixWord ++ tailWord_2533762).sum := by decide
  have hdescent : baseEnd_2533762 < baseStart_2533762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533792 : List Nat := [2, 1, 1, 4, 1, 3, 2, 4, 1, 1, 3]
def baseStart_2533792 : Nat := 118140960795 + 2533792 * 2 ^ 59
def prefixEnd_2533792 : Nat := 4983230072969 + 3 ^ 40 * 2533792 * 2
def baseEnd_2533792 : Nat := 1301053174517055760847309

theorem tailTrace_2533792 : CollatzResearch.WordTrace tailWord_2533792 prefixEnd_2533792 1301053174517055760847309 := by
  unfold tailWord_2533792
  simp only [CollatzResearch.WordTrace]
  refine ⟨46207493218255898033369815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61609990957674530711159753 46207493218255898033369815)
  ·
    refine ⟨69311239827383847050054723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46207493218255898033369815 69311239827383847050054723)
    ·
      refine ⟨103966859741075770575082085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69311239827383847050054723 103966859741075770575082085)
      ·
        refine ⟨19493786201451706982827891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103966859741075770575082085 19493786201451706982827891)
        ·
          refine ⟨29240679302177560474241837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19493786201451706982827891 29240679302177560474241837)
          ·
            refine ⟨10965254738316585177840689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29240679302177560474241837 10965254738316585177840689)
            ·
              refine ⟨8223941053737438883380517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10965254738316585177840689 8223941053737438883380517)
              ·
                refine ⟨1541988947575769790633847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8223941053737438883380517 1541988947575769790633847)
                ·
                  refine ⟨2312983421363654685950771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541988947575769790633847 2312983421363654685950771)
                  ·
                    refine ⟨3469475132045482028926157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2312983421363654685950771 3469475132045482028926157)
                    ·
                      refine ⟨1301053174517055760847309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3469475132045482028926157 1301053174517055760847309)
                      ·
                        rfl

theorem cell23_2533792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_2533792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533792 prefixEnd_2533792 := by exact prefixLift 2533792
  have htrace : WordTrace (prefixWord ++ tailWord_2533792) baseStart_2533792 baseEnd_2533792 := by
    simpa [prefixWord, tailWord_2533792, baseEnd_2533792] using wordTrace_append hprefix tailTrace_2533792
  have hstable : (prefixWord ++ tailWord_2533792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533792).length < 2 ^ (prefixWord ++ tailWord_2533792).sum := by decide
  have hdescent : baseEnd_2533792 < baseStart_2533792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533815 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_2533815 : Nat := 118140960795 + 2533815 * 2 ^ 59
def prefixEnd_2533815 : Nat := 4983230072969 + 3 ^ 40 * 2533815 * 2
def baseEnd_2533815 : Nat := 1301064984572109170859703

theorem tailTrace_2533815 : CollatzResearch.WordTrace tailWord_2533815 prefixEnd_2533815 1301064984572109170859703 := by
  unfold tailWord_2533815
  simp only [CollatzResearch.WordTrace]
  refine ⟨92415825315428470994826899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61610550210285647329884599 92415825315428470994826899)
  ·
    refine ⟨138623737973142706492240349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92415825315428470994826899 138623737973142706492240349)
    ·
      refine ⟨51983901739928514934590131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138623737973142706492240349 51983901739928514934590131)
      ·
        refine ⟨77975852609892772401885197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51983901739928514934590131 77975852609892772401885197)
        ·
          refine ⟨29240944728709789650706949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77975852609892772401885197 29240944728709789650706949)
          ·
            refine ⟨5482677136633085559507553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29240944728709789650706949 5482677136633085559507553)
            ·
              refine ⟨4112007852474814169630665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5482677136633085559507553 4112007852474814169630665)
              ·
                refine ⟨3084005889356110627222999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4112007852474814169630665 3084005889356110627222999)
                ·
                  refine ⟨4626008834034165940834499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084005889356110627222999 4626008834034165940834499)
                  ·
                    refine ⟨6939013251051248911251749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4626008834034165940834499 6939013251051248911251749)
                    ·
                      refine ⟨1301064984572109170859703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6939013251051248911251749 1301064984572109170859703)
                      ·
                        rfl

theorem cell23_2533815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_2533815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533815 prefixEnd_2533815 := by exact prefixLift 2533815
  have htrace : WordTrace (prefixWord ++ tailWord_2533815) baseStart_2533815 baseEnd_2533815 := by
    simpa [prefixWord, tailWord_2533815, baseEnd_2533815] using wordTrace_append hprefix tailTrace_2533815
  have hstable : (prefixWord ++ tailWord_2533815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533815).length < 2 ^ (prefixWord ++ tailWord_2533815).sum := by decide
  have hdescent : baseEnd_2533815 < baseStart_2533815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533818 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_2533818 : Nat := 118140960795 + 2533818 * 2 ^ 59
def prefixEnd_2533818 : Nat := 4983230072969 + 3 ^ 40 * 2533818 * 2
def baseEnd_2533818 : Nat := 1301066525014072659122189

theorem tailTrace_2533818 : CollatzResearch.WordTrace tailWord_2533818 prefixEnd_2533818 1301066525014072659122189 := by
  unfold tailWord_2533818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23103983683604400626796527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61610623156278401671457405 23103983683604400626796527)
  ·
    refine ⟨34655975525406600940194791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23103983683604400626796527 34655975525406600940194791)
    ·
      refine ⟨51983963288109901410292187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34655975525406600940194791 51983963288109901410292187)
      ·
        refine ⟨77975944932164852115438281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51983963288109901410292187 77975944932164852115438281)
        ·
          refine ⟨58481958699123639086578711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77975944932164852115438281 58481958699123639086578711)
          ·
            refine ⟨87722938048685458629868067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58481958699123639086578711 87722938048685458629868067)
            ·
              refine ⟨131584407073028187944802101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87722938048685458629868067 131584407073028187944802101)
              ·
                refine ⟨12336038163096392619825197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131584407073028187944802101 12336038163096392619825197)
                ·
                  refine ⟨4626014311161147232434449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12336038163096392619825197 4626014311161147232434449)
                  ·
                    refine ⟨3469510733370860424325837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626014311161147232434449 3469510733370860424325837)
                    ·
                      refine ⟨1301066525014072659122189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3469510733370860424325837 1301066525014072659122189)
                      ·
                        rfl

theorem cell23_2533818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_2533818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533818 prefixEnd_2533818 := by exact prefixLift 2533818
  have htrace : WordTrace (prefixWord ++ tailWord_2533818) baseStart_2533818 baseEnd_2533818 := by
    simpa [prefixWord, tailWord_2533818, baseEnd_2533818] using wordTrace_append hprefix tailTrace_2533818
  have hstable : (prefixWord ++ tailWord_2533818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533818).length < 2 ^ (prefixWord ++ tailWord_2533818).sum := by decide
  have hdescent : baseEnd_2533818 < baseStart_2533818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533859 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 2, 4]
def baseStart_2533859 : Nat := 118140960795 + 2533859 * 2 ^ 59
def prefixEnd_2533859 : Nat := 4983230072969 + 3 ^ 40 * 2533859 * 2
def baseEnd_2533859 : Nat := 433695859240302332903167

theorem tailTrace_2533859 : CollatzResearch.WordTrace tailWord_2533859 prefixEnd_2533859 433695859240302332903167 := by
  unfold tailWord_2533859
  simp only [CollatzResearch.WordTrace]
  refine ⟨92417430127269066509428631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61611620084846044339619087 92417430127269066509428631)
  ·
    refine ⟨138626145190903599764142947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92417430127269066509428631 138626145190903599764142947)
    ·
      refine ⟨207939217786355399646214421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138626145190903599764142947 207939217786355399646214421)
      ·
        refine ⟨9747150833735409358416301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 207939217786355399646214421 9747150833735409358416301)
        ·
          refine ⟨3655181562650778509406113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9747150833735409358416301 3655181562650778509406113)
          ·
            refine ⟨2741386171988083882054585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3655181562650778509406113 2741386171988083882054585)
            ·
              refine ⟨2056039628991062911540939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2741386171988083882054585 2056039628991062911540939)
              ·
                refine ⟨3084059443486594367311409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056039628991062911540939 3084059443486594367311409)
                ·
                  refine ⟨2313044582614945775483557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3084059443486594367311409 2313044582614945775483557)
                  ·
                    refine ⟨433695859240302332903167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2313044582614945775483557 433695859240302332903167)
                    ·
                      rfl

theorem cell23_2533859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 2, 4].length) (baseStart_2533859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533859 prefixEnd_2533859 := by exact prefixLift 2533859
  have htrace : WordTrace (prefixWord ++ tailWord_2533859) baseStart_2533859 baseEnd_2533859 := by
    simpa [prefixWord, tailWord_2533859, baseEnd_2533859] using wordTrace_append hprefix tailTrace_2533859
  have hstable : (prefixWord ++ tailWord_2533859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533859).length < 2 ^ (prefixWord ++ tailWord_2533859).sum := by decide
  have hdescent : baseEnd_2533859 < baseStart_2533859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533869 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2533869 : Nat := 118140960795 + 2533869 * 2 ^ 59
def prefixEnd_2533869 : Nat := 4983230072969 + 3 ^ 40 * 2533869 * 2
def baseEnd_2533869 : Nat := 1301092712527451959584455

theorem tailTrace_2533869 : CollatzResearch.WordTrace tailWord_2533869 prefixEnd_2533869 1301092712527451959584455 := by
  unfold tailWord_2533869
  simp only [CollatzResearch.WordTrace]
  refine ⟨92417794857232838217292661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61611863238155225478195107 92417794857232838217292661)
  ·
    refine ⟨8664168267865578582871187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92417794857232838217292661 8664168267865578582871187)
    ·
      refine ⟨12996252401798367874306781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8664168267865578582871187 12996252401798367874306781)
      ·
        refine ⟨4873594650674387952865043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12996252401798367874306781 4873594650674387952865043)
        ·
          refine ⟨7310391976011581929297565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873594650674387952865043 7310391976011581929297565)
          ·
            refine ⟨2741396991004343223486587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7310391976011581929297565 2741396991004343223486587)
            ·
              refine ⟨4112095486506514835229881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741396991004343223486587 4112095486506514835229881)
              ·
                refine ⟨3084071614879886126422411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4112095486506514835229881 3084071614879886126422411)
                ·
                  refine ⟨4626107422319829189633617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084071614879886126422411 4626107422319829189633617)
                  ·
                    refine ⟨3469580566739871892225213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626107422319829189633617 3469580566739871892225213)
                    ·
                      refine ⟨1301092712527451959584455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3469580566739871892225213 1301092712527451959584455)
                      ·
                        rfl

theorem cell23_2533869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2533869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533869 prefixEnd_2533869 := by exact prefixLift 2533869
  have htrace : WordTrace (prefixWord ++ tailWord_2533869) baseStart_2533869 baseEnd_2533869 := by
    simpa [prefixWord, tailWord_2533869, baseEnd_2533869] using wordTrace_append hprefix tailTrace_2533869
  have hstable : (prefixWord ++ tailWord_2533869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533869).length < 2 ^ (prefixWord ++ tailWord_2533869).sum := by decide
  have hdescent : baseEnd_2533869 < baseStart_2533869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533871 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_2533871 : Nat := 118140960795 + 2533871 * 2 ^ 59
def prefixEnd_2533871 : Nat := 4983230072969 + 3 ^ 40 * 2533871 * 2
def baseEnd_2533871 : Nat := 1301093739488760951759445

theorem tailTrace_2533871 : CollatzResearch.WordTrace tailWord_2533871 prefixEnd_2533871 1301093739488760951759445 := by
  unfold tailWord_2533871
  simp only [CollatzResearch.WordTrace]
  refine ⟨92417867803225592558865467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61611911868817061705910311 92417867803225592558865467)
  ·
    refine ⟨138626801704838388838298201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92417867803225592558865467 138626801704838388838298201)
    ·
      refine ⟨103970101278628791628723651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138626801704838388838298201 103970101278628791628723651)
      ·
        refine ⟨155955151917943187443085477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103970101278628791628723651 155955151917943187443085477)
        ·
          refine ⟨29241590984614347645578527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 155955151917943187443085477 29241590984614347645578527)
          ·
            refine ⟨43862386476921521468367791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29241590984614347645578527 43862386476921521468367791)
            ·
              refine ⟨65793579715382282202551687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43862386476921521468367791 65793579715382282202551687)
              ·
                refine ⟨98690369573073423303827531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65793579715382282202551687 98690369573073423303827531)
                ·
                  refine ⟨148035554359610134955741297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98690369573073423303827531 148035554359610134955741297)
                  ·
                    refine ⟨111026665769707601216805973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 148035554359610134955741297 111026665769707601216805973)
                    ·
                      refine ⟨1301093739488760951759445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 111026665769707601216805973 1301093739488760951759445)
                      ·
                        rfl

theorem cell23_2533871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_2533871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533871 prefixEnd_2533871 := by exact prefixLift 2533871
  have htrace : WordTrace (prefixWord ++ tailWord_2533871) baseStart_2533871 baseEnd_2533871 := by
    simpa [prefixWord, tailWord_2533871, baseEnd_2533871] using wordTrace_append hprefix tailTrace_2533871
  have hstable : (prefixWord ++ tailWord_2533871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533871).length < 2 ^ (prefixWord ++ tailWord_2533871).sum := by decide
  have hdescent : baseEnd_2533871 < baseStart_2533871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533875 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 3, 3, 2]
def baseStart_2533875 : Nat := 118140960795 + 2533875 * 2 ^ 59
def prefixEnd_2533875 : Nat := 4983230072969 + 3 ^ 40 * 2533875 * 2
def baseEnd_2533875 : Nat := 1301095793411378936109427

theorem tailTrace_2533875 : CollatzResearch.WordTrace tailWord_2533875 prefixEnd_2533875 1301095793411378936109427 := by
  unfold tailWord_2533875
  simp only [CollatzResearch.WordTrace]
  refine ⟨92418013695211101242011079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61612009130140734161340719 92418013695211101242011079)
  ·
    refine ⟨138627020542816651863016619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92418013695211101242011079 138627020542816651863016619)
    ·
      refine ⟨207940530814224977794524929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138627020542816651863016619 207940530814224977794524929)
      ·
        refine ⟨155955398110668733345893697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207940530814224977794524929 155955398110668733345893697)
        ·
          refine ⟨116966548583001550009420273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155955398110668733345893697 116966548583001550009420273)
          ·
            refine ⟨87724911437251162507065205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116966548583001550009420273 87724911437251162507065205)
            ·
              refine ⟨8224210447242296485037363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87724911437251162507065205 8224210447242296485037363)
              ·
                refine ⟨12336315670863444727556045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8224210447242296485037363 12336315670863444727556045)
                ·
                  refine ⟨4626118376573791772833517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12336315670863444727556045 4626118376573791772833517)
                  ·
                    refine ⟨1734794391215171914812569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4626118376573791772833517 1734794391215171914812569)
                    ·
                      refine ⟨1301095793411378936109427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734794391215171914812569 1301095793411378936109427)
                      ·
                        rfl

theorem cell23_2533875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 3, 2].length) (baseStart_2533875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533875 prefixEnd_2533875 := by exact prefixLift 2533875
  have htrace : WordTrace (prefixWord ++ tailWord_2533875) baseStart_2533875 baseEnd_2533875 := by
    simpa [prefixWord, tailWord_2533875, baseEnd_2533875] using wordTrace_append hprefix tailTrace_2533875
  have hstable : (prefixWord ++ tailWord_2533875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533875).length < 2 ^ (prefixWord ++ tailWord_2533875).sum := by decide
  have hdescent : baseEnd_2533875 < baseStart_2533875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533898 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_2533898 : Nat := 118140960795 + 2533898 * 2 ^ 59
def prefixEnd_2533898 : Nat := 4983230072969 + 3 ^ 40 * 2533898 * 2
def baseEnd_2533898 : Nat := 433702534488810782040607

theorem tailTrace_2533898 : CollatzResearch.WordTrace tailWord_2533898 prefixEnd_2533898 433702534488810782040607 := by
  unfold tailWord_2533898
  simp only [CollatzResearch.WordTrace]
  refine ⟨23104713143531944042524587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61612568382751850780065565 23104713143531944042524587)
  ·
    refine ⟨34657069715297916063786881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23104713143531944042524587 34657069715297916063786881)
    ·
      refine ⟨25992802286473437047840161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34657069715297916063786881 25992802286473437047840161)
      ·
        refine ⟨19494601714855077785880121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25992802286473437047840161 19494601714855077785880121)
        ·
          refine ⟨14620951286141308339410091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19494601714855077785880121 14620951286141308339410091)
          ·
            refine ⟨21931426929211962509115137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14620951286141308339410091 21931426929211962509115137)
            ·
              refine ⟨16448570196908971881836353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21931426929211962509115137 16448570196908971881836353)
              ·
                refine ⟨12336427647681728911377265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16448570196908971881836353 12336427647681728911377265)
                ·
                  refine ⟨9252320735761296683532949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12336427647681728911377265 9252320735761296683532949)
                  ·
                    refine ⟨433702534488810782040607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9252320735761296683532949 433702534488810782040607)
                    ·
                      rfl

theorem cell23_2533898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_2533898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533898 prefixEnd_2533898 := by exact prefixLift 2533898
  have htrace : WordTrace (prefixWord ++ tailWord_2533898) baseStart_2533898 baseEnd_2533898 := by
    simpa [prefixWord, tailWord_2533898, baseEnd_2533898] using wordTrace_append hprefix tailTrace_2533898
  have hstable : (prefixWord ++ tailWord_2533898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533898).length < 2 ^ (prefixWord ++ tailWord_2533898).sum := by decide
  have hdescent : baseEnd_2533898 < baseStart_2533898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533922 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 6, 2, 2]
def baseStart_2533922 : Nat := 118140960795 + 2533922 * 2 ^ 59
def prefixEnd_2533922 : Nat := 4983230072969 + 3 ^ 40 * 2533922 * 2
def baseEnd_2533922 : Nat := 1301119927002140252221711

theorem tailTrace_2533922 : CollatzResearch.WordTrace tailWord_2533922 prefixEnd_2533922 1301119927002140252221711 := by
  unfold tailWord_2533922
  simp only [CollatzResearch.WordTrace]
  refine ⟨23104931981510207067243005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61613151950693885512648013 23104931981510207067243005)
  ·
    refine ⟨8664349493066327650216127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23104931981510207067243005 8664349493066327650216127)
    ·
      refine ⟨12996524239599491475324191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8664349493066327650216127 12996524239599491475324191)
      ·
        refine ⟨19494786359399237212986287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12996524239599491475324191 19494786359399237212986287)
        ·
          refine ⟨29242179539098855819479431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19494786359399237212986287 29242179539098855819479431)
          ·
            refine ⟨43863269308648283729219147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29242179539098855819479431 43863269308648283729219147)
            ·
              refine ⟨65794903962972425593828721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43863269308648283729219147 65794903962972425593828721)
              ·
                refine ⟨49346177972229319195371541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65794903962972425593828721 49346177972229319195371541)
                ·
                  refine ⟨2313102092448249337283041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49346177972229319195371541 2313102092448249337283041)
                  ·
                    refine ⟨1734826569336187002962281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2313102092448249337283041 1734826569336187002962281)
                    ·
                      refine ⟨1301119927002140252221711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734826569336187002962281 1301119927002140252221711)
                      ·
                        rfl

theorem cell23_2533922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_2533922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533922 prefixEnd_2533922 := by exact prefixLift 2533922
  have htrace : WordTrace (prefixWord ++ tailWord_2533922) baseStart_2533922 baseEnd_2533922 := by
    simpa [prefixWord, tailWord_2533922, baseEnd_2533922] using wordTrace_append hprefix tailTrace_2533922
  have hstable : (prefixWord ++ tailWord_2533922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533922).length < 2 ^ (prefixWord ++ tailWord_2533922).sum := by decide
  have hdescent : baseEnd_2533922 < baseStart_2533922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533988 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_2533988 : Nat := 118140960795 + 2533988 * 2 ^ 59
def prefixEnd_2533988 : Nat := 4983230072969 + 3 ^ 40 * 2533988 * 2
def baseEnd_2533988 : Nat := 433717938908445664665469

theorem tailTrace_2533988 : CollatzResearch.WordTrace tailWord_2533988 prefixEnd_2533988 433717938908445664665469 := by
  unfold tailWord_2533988
  simp only [CollatzResearch.WordTrace]
  refine ⟨46211067571900860770437309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61614756762534481027249745 46211067571900860770437309)
  ·
    refine ⟨17329150339462822788913991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46211067571900860770437309 17329150339462822788913991)
    ·
      refine ⟨25993725509194234183370987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17329150339462822788913991 25993725509194234183370987)
      ·
        refine ⟨38990588263791351275056481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25993725509194234183370987 38990588263791351275056481)
        ·
          refine ⟨29242941197843513456292361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38990588263791351275056481 29242941197843513456292361)
          ·
            refine ⟨21932205898382635092219271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29242941197843513456292361 21932205898382635092219271)
            ·
              refine ⟨32898308847573952638328907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21932205898382635092219271 32898308847573952638328907)
              ·
                refine ⟨49347463271360928957493361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32898308847573952638328907 49347463271360928957493361)
                ·
                  refine ⟨37010597453520696718120021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49347463271360928957493361 37010597453520696718120021)
                  ·
                    refine ⟨433717938908445664665469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37010597453520696718120021 433717938908445664665469)
                    ·
                      rfl

theorem cell23_2533988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_2533988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533988 prefixEnd_2533988 := by exact prefixLift 2533988
  have htrace : WordTrace (prefixWord ++ tailWord_2533988) baseStart_2533988 baseEnd_2533988 := by
    simpa [prefixWord, tailWord_2533988, baseEnd_2533988] using wordTrace_append hprefix tailTrace_2533988
  have hstable : (prefixWord ++ tailWord_2533988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533988).length < 2 ^ (prefixWord ++ tailWord_2533988).sum := by decide
  have hdescent : baseEnd_2533988 < baseStart_2533988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533995 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 4, 4, 2]
def baseStart_2533995 : Nat := 118140960795 + 2533995 * 2 ^ 59
def prefixEnd_2533995 : Nat := 4983230072969 + 3 ^ 40 * 2533995 * 2
def baseEnd_2533995 : Nat := 1301157411089918466608875

theorem tailTrace_2533995 : CollatzResearch.WordTrace tailWord_2533995 prefixEnd_2533995 1301157411089918466608875 := by
  unfold tailWord_2533995
  simp only [CollatzResearch.WordTrace]
  refine ⟨92422390454776361736379439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61614926969850907824252959 92422390454776361736379439)
  ·
    refine ⟨138633585682164542604569159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92422390454776361736379439 138633585682164542604569159)
    ·
      refine ⟨207950378523246813906853739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138633585682164542604569159 207950378523246813906853739)
      ·
        refine ⟨311925567784870220860280609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207950378523246813906853739 311925567784870220860280609)
        ·
          refine ⟨233944175838652665645210457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311925567784870220860280609 233944175838652665645210457)
          ·
            refine ⟨175458131878989499233907843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233944175838652665645210457 175458131878989499233907843)
            ·
              refine ⟨263187197818484248850861765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175458131878989499233907843 263187197818484248850861765)
              ·
                refine ⟨49347599590965796659536581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263187197818484248850861765 49347599590965796659536581)
                ·
                  refine ⟨9252674923306086873663109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49347599590965796659536581 9252674923306086873663109)
                  ·
                    refine ⟨1734876548119891288811833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9252674923306086873663109 1734876548119891288811833)
                    ·
                      refine ⟨1301157411089918466608875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734876548119891288811833 1301157411089918466608875)
                      ·
                        rfl

theorem cell23_2533995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 4, 2].length) (baseStart_2533995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2533995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2533995 prefixEnd_2533995 := by exact prefixLift 2533995
  have htrace : WordTrace (prefixWord ++ tailWord_2533995) baseStart_2533995 baseEnd_2533995 := by
    simpa [prefixWord, tailWord_2533995, baseEnd_2533995] using wordTrace_append hprefix tailTrace_2533995
  have hstable : (prefixWord ++ tailWord_2533995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533995).length < 2 ^ (prefixWord ++ tailWord_2533995).sum := by decide
  have hdescent : baseEnd_2533995 < baseStart_2533995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534008 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2534008 : Nat := 118140960795 + 2534008 * 2 ^ 59
def prefixEnd_2534008 : Nat := 4983230072969 + 3 ^ 40 * 2534008 * 2
def baseEnd_2534008 : Nat := 1301164086338426915746315

theorem tailTrace_2534008 : CollatzResearch.WordTrace tailWord_2534008 prefixEnd_2534008 1301164086338426915746315 := by
  unfold tailWord_2534008
  simp only [CollatzResearch.WordTrace]
  refine ⟨46211432301864632478301339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61615243069152843304401785 46211432301864632478301339)
  ·
    refine ⟨69317148452796948717452009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46211432301864632478301339 69317148452796948717452009)
    ·
      refine ⟨51987861339597711538089007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69317148452796948717452009 51987861339597711538089007)
      ·
        refine ⟨77981792009396567307133511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51987861339597711538089007 77981792009396567307133511)
        ·
          refine ⟨116972688014094850960700267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77981792009396567307133511 116972688014094850960700267)
          ·
            refine ⟨175459032021142276441050401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116972688014094850960700267 175459032021142276441050401)
            ·
              refine ⟨131594274015856707330787801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175459032021142276441050401 131594274015856707330787801)
              ·
                refine ⟨98695705511892530498090851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131594274015856707330787801 98695705511892530498090851)
                ·
                  refine ⟨148043558267838795747136277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98695705511892530498090851 148043558267838795747136277)
                  ·
                    refine ⟨6939541793804943550647013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148043558267838795747136277 6939541793804943550647013)
                    ·
                      refine ⟨1301164086338426915746315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6939541793804943550647013 1301164086338426915746315)
                      ·
                        rfl

theorem cell23_2534008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2534008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534008 prefixEnd_2534008 := by exact prefixLift 2534008
  have htrace : WordTrace (prefixWord ++ tailWord_2534008) baseStart_2534008 baseEnd_2534008 := by
    simpa [prefixWord, tailWord_2534008, baseEnd_2534008] using wordTrace_append hprefix tailTrace_2534008
  have hstable : (prefixWord ++ tailWord_2534008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534008).length < 2 ^ (prefixWord ++ tailWord_2534008).sum := by decide
  have hdescent : baseEnd_2534008 < baseStart_2534008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534045 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_2534045 : Nat := 118140960795 + 2534045 * 2 ^ 59
def prefixEnd_2534045 : Nat := 4983230072969 + 3 ^ 40 * 2534045 * 2
def baseEnd_2534045 : Nat := 1301183085122643270983645

theorem tailTrace_2534045 : CollatzResearch.WordTrace tailWord_2534045 prefixEnd_2534045 1301183085122643270983645 := by
  unfold tailWord_2534045
  simp only [CollatzResearch.WordTrace]
  refine ⟨92424214104595220275699589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61616142736396813517133059 92424214104595220275699589)
  ·
    refine ⟨17329540144611603801693673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92424214104595220275699589 17329540144611603801693673)
    ·
      refine ⟨12997155108458702851270255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17329540144611603801693673 12997155108458702851270255)
      ·
        refine ⟨19495732662688054276905383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12997155108458702851270255 19495732662688054276905383)
        ·
          refine ⟨29243598994032081415358075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19495732662688054276905383 29243598994032081415358075)
          ·
            refine ⟨43865398491048122123037113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29243598994032081415358075 43865398491048122123037113)
            ·
              refine ⟨32899048868286091592277835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43865398491048122123037113 32899048868286091592277835)
              ·
                refine ⟨49348573302429137388416753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32899048868286091592277835 49348573302429137388416753)
                ·
                  refine ⟨37011429976821853041312565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49348573302429137388416753 37011429976821853041312565)
                  ·
                    refine ⟨3469821560327048722623053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37011429976821853041312565 3469821560327048722623053)
                    ·
                      refine ⟨1301183085122643270983645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3469821560327048722623053 1301183085122643270983645)
                      ·
                        rfl

theorem cell23_2534045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_2534045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534045 prefixEnd_2534045 := by exact prefixLift 2534045
  have htrace : WordTrace (prefixWord ++ tailWord_2534045) baseStart_2534045 baseEnd_2534045 := by
    simpa [prefixWord, tailWord_2534045, baseEnd_2534045] using wordTrace_append hprefix tailTrace_2534045
  have hstable : (prefixWord ++ tailWord_2534045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534045).length < 2 ^ (prefixWord ++ tailWord_2534045).sum := by decide
  have hdescent : baseEnd_2534045 < baseStart_2534045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534049 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2534049 : Nat := 118140960795 + 2534049 * 2 ^ 59
def prefixEnd_2534049 : Nat := 4983230072969 + 3 ^ 40 * 2534049 * 2
def baseEnd_2534049 : Nat := 1301185139045261255333627

theorem tailTrace_2534049 : CollatzResearch.WordTrace tailWord_2534049 prefixEnd_2534049 1301185139045261255333627 := by
  unfold tailWord_2534049
  simp only [CollatzResearch.WordTrace]
  refine ⟨92424359996580728958845201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61616239997720485972563467 92424359996580728958845201)
  ·
    refine ⟨69318269997435546719133901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92424359996580728958845201 69318269997435546719133901)
    ·
      refine ⟨25994351249038330019675213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69318269997435546719133901 25994351249038330019675213)
      ·
        refine ⟨9747881718389373757378205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25994351249038330019675213 9747881718389373757378205)
        ·
          refine ⟨3655455644396015159016827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9747881718389373757378205 3655455644396015159016827)
          ·
            refine ⟨5483183466594022738525241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655455644396015159016827 5483183466594022738525241)
            ·
              refine ⟨4112387599945517053893931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483183466594022738525241 4112387599945517053893931)
              ·
                refine ⟨6168581399918275580840897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112387599945517053893931 6168581399918275580840897)
                ·
                  refine ⟨4626436049938706685630673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6168581399918275580840897 4626436049938706685630673)
                  ·
                    refine ⟨3469827037454030014223005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4626436049938706685630673 3469827037454030014223005)
                    ·
                      refine ⟨1301185139045261255333627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3469827037454030014223005 1301185139045261255333627)
                      ·
                        rfl

theorem cell23_2534049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2534049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534049 prefixEnd_2534049 := by exact prefixLift 2534049
  have htrace : WordTrace (prefixWord ++ tailWord_2534049) baseStart_2534049 baseEnd_2534049 := by
    simpa [prefixWord, tailWord_2534049, baseEnd_2534049] using wordTrace_append hprefix tailTrace_2534049
  have hstable : (prefixWord ++ tailWord_2534049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534049).length < 2 ^ (prefixWord ++ tailWord_2534049).sum := by decide
  have hdescent : baseEnd_2534049 < baseStart_2534049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534095 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 8, 4]
def baseStart_2534095 : Nat := 118140960795 + 2534095 * 2 ^ 59
def prefixEnd_2534095 : Nat := 4983230072969 + 3 ^ 40 * 2534095 * 2
def baseEnd_2534095 : Nat := 433736253051789358452805

theorem tailTrace_2534095 : CollatzResearch.WordTrace tailWord_2534095 prefixEnd_2534095 433736253051789358452805 := by
  unfold tailWord_2534095
  simp only [CollatzResearch.WordTrace]
  refine ⟨92426037754414078815019739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61617358502942719210013159 92426037754414078815019739)
  ·
    refine ⟨138639056631621118222529609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92426037754414078815019739 138639056631621118222529609)
    ·
      refine ⟨103979292473715838666897207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138639056631621118222529609 103979292473715838666897207)
      ·
        refine ⟨155968938710573758000345811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103979292473715838666897207 155968938710573758000345811)
        ·
          refine ⟨233953408065860637000518717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155968938710573758000345811 233953408065860637000518717)
          ·
            refine ⟨87732528024697738875194519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233953408065860637000518717 87732528024697738875194519)
            ·
              refine ⟨131598792037046608312791779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87732528024697738875194519 131598792037046608312791779)
              ·
                refine ⟨197398188055569912469187669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131598792037046608312791779 197398188055569912469187669)
                ·
                  refine ⟨2313260016276209911748293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 197398188055569912469187669 2313260016276209911748293)
                  ·
                    refine ⟨433736253051789358452805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2313260016276209911748293 433736253051789358452805)
                    ·
                      rfl

theorem cell23_2534095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 8, 4].length) (baseStart_2534095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534095 prefixEnd_2534095 := by exact prefixLift 2534095
  have htrace : WordTrace (prefixWord ++ tailWord_2534095) baseStart_2534095 baseEnd_2534095 := by
    simpa [prefixWord, tailWord_2534095, baseEnd_2534095] using wordTrace_append hprefix tailTrace_2534095
  have hstable : (prefixWord ++ tailWord_2534095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534095).length < 2 ^ (prefixWord ++ tailWord_2534095).sum := by decide
  have hdescent : baseEnd_2534095 < baseStart_2534095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534125 : List Nat := [1, 5, 1, 2, 1, 1, 12]
def baseStart_2534125 : Nat := 118140960795 + 2534125 * 2 ^ 59
def prefixEnd_2534125 : Nat := 4983230072969 + 3 ^ 40 * 2534125 * 2
def baseEnd_2534125 : Nat := 16064495846604974789917

theorem tailTrace_2534125 : CollatzResearch.WordTrace tailWord_2534125 prefixEnd_2534125 16064495846604974789917 := by
  unfold tailWord_2534125
  simp only [CollatzResearch.WordTrace]
  refine ⟨92427131944305393938611829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61618087962870262625741219 92427131944305393938611829)
  ·
    refine ⟨8665043619778630681744859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92427131944305393938611829 8665043619778630681744859)
    ·
      refine ⟨12997565429667946022617289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8665043619778630681744859 12997565429667946022617289)
      ·
        refine ⟨9748174072250959516962967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12997565429667946022617289 9748174072250959516962967)
        ·
          refine ⟨14622261108376439275444451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9748174072250959516962967 14622261108376439275444451)
          ·
            refine ⟨21933391662564658913166677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14622261108376439275444451 21933391662564658913166677)
            ·
              refine ⟨16064495846604974789917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 21933391662564658913166677 16064495846604974789917)
              ·
                rfl

theorem cell23_2534125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 12].length) (baseStart_2534125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534125 prefixEnd_2534125 := by exact prefixLift 2534125
  have htrace : WordTrace (prefixWord ++ tailWord_2534125) baseStart_2534125 baseEnd_2534125 := by
    simpa [prefixWord, tailWord_2534125, baseEnd_2534125] using wordTrace_append hprefix tailTrace_2534125
  have hstable : (prefixWord ++ tailWord_2534125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534125).length < 2 ^ (prefixWord ++ tailWord_2534125).sum := by decide
  have hdescent : baseEnd_2534125 < baseStart_2534125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534136 : List Nat := [2, 1, 2, 1, 1, 2, 3, 6, 1, 2, 2]
def baseStart_2534136 : Nat := 118140960795 + 2534136 * 2 ^ 59
def prefixEnd_2534136 : Nat := 4983230072969 + 3 ^ 40 * 2534136 * 2
def baseEnd_2534136 : Nat := 1301229811862202414945727

theorem tailTrace_2534136 : CollatzResearch.WordTrace tailWord_2534136 prefixEnd_2534136 1301229811862202414945727 := by
  unfold tailWord_2534136
  simp only [CollatzResearch.WordTrace]
  refine ⟨46213766573632771408631131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61618355431510361878174841 46213766573632771408631131)
  ·
    refine ⟨69320649860449157112946697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46213766573632771408631131 69320649860449157112946697)
    ·
      refine ⟨51990487395336867834710023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69320649860449157112946697 51990487395336867834710023)
      ·
        refine ⟨77985731093005301752065035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51990487395336867834710023 77985731093005301752065035)
        ·
          refine ⟨116978596639507952628097553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77985731093005301752065035 116978596639507952628097553)
          ·
            refine ⟨87733947479630964471073165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116978596639507952628097553 87733947479630964471073165)
            ·
              refine ⟨32900230304861611676652437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87733947479630964471073165 32900230304861611676652437)
              ·
                refine ⟨1542198295540388047343083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32900230304861611676652437 1542198295540388047343083)
                ·
                  refine ⟨2313297443310582071014625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542198295540388047343083 2313297443310582071014625)
                  ·
                    refine ⟨1734973082482936553260969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2313297443310582071014625 1734973082482936553260969)
                    ·
                      refine ⟨1301229811862202414945727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1734973082482936553260969 1301229811862202414945727)
                      ·
                        rfl

theorem cell23_2534136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_2534136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534136 prefixEnd_2534136 := by exact prefixLift 2534136
  have htrace : WordTrace (prefixWord ++ tailWord_2534136) baseStart_2534136 baseEnd_2534136 := by
    simpa [prefixWord, tailWord_2534136, baseEnd_2534136] using wordTrace_append hprefix tailTrace_2534136
  have hstable : (prefixWord ++ tailWord_2534136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534136).length < 2 ^ (prefixWord ++ tailWord_2534136).sum := by decide
  have hdescent : baseEnd_2534136 < baseStart_2534136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534165 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_2534165 : Nat := 118140960795 + 2534165 * 2 ^ 59
def prefixEnd_2534165 : Nat := 4983230072969 + 3 ^ 40 * 2534165 * 2
def baseEnd_2534165 : Nat := 1301244702801182801483093

theorem tailTrace_2534165 : CollatzResearch.WordTrace tailWord_2534165 prefixEnd_2534165 1301244702801182801483093 := by
  unfold tailWord_2534165
  simp only [CollatzResearch.WordTrace]
  refine ⟨92428590864160480770067949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61619060576106987180045299 92428590864160480770067949)
  ·
    refine ⟨34660721574060180288775481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92428590864160480770067949 34660721574060180288775481)
    ·
      refine ⟨25995541180545135216581611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34660721574060180288775481 25995541180545135216581611)
      ·
        refine ⟨38993311770817702824872417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25995541180545135216581611 38993311770817702824872417)
        ·
          refine ⟨29244983828113277118654313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38993311770817702824872417 29244983828113277118654313)
          ·
            refine ⟨21933737871084957838990735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29244983828113277118654313 21933737871084957838990735)
            ·
              refine ⟨32900606806627436758486103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21933737871084957838990735 32900606806627436758486103)
              ·
                refine ⟨49350910209941155137729155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32900606806627436758486103 49350910209941155137729155)
                ·
                  refine ⟨74026365314911732706593733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49350910209941155137729155 74026365314911732706593733)
                  ·
                    refine ⟨13879943496545949882486325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74026365314911732706593733 13879943496545949882486325)
                    ·
                      refine ⟨1301244702801182801483093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13879943496545949882486325 1301244702801182801483093)
                      ·
                        rfl

theorem cell23_2534165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_2534165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534165 prefixEnd_2534165 := by exact prefixLift 2534165
  have htrace : WordTrace (prefixWord ++ tailWord_2534165) baseStart_2534165 baseEnd_2534165 := by
    simpa [prefixWord, tailWord_2534165, baseEnd_2534165] using wordTrace_append hprefix tailTrace_2534165
  have hstable : (prefixWord ++ tailWord_2534165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534165).length < 2 ^ (prefixWord ++ tailWord_2534165).sum := by decide
  have hdescent : baseEnd_2534165 < baseStart_2534165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534215 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 9]
def baseStart_2534215 : Nat := 118140960795 + 2534215 * 2 ^ 59
def prefixEnd_2534215 : Nat := 4983230072969 + 3 ^ 40 * 2534215 * 2
def baseEnd_2534215 : Nat := 144585597425989733984207

theorem tailTrace_2534215 : CollatzResearch.WordTrace tailWord_2534215 prefixEnd_2534215 144585597425989733984207 := by
  unfold tailWord_2534215
  simp only [CollatzResearch.WordTrace]
  refine ⟨92430414513979339309388099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61620276342652892872925399 92430414513979339309388099)
  ·
    refine ⟨138645621770969008964082149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92430414513979339309388099 138645621770969008964082149)
    ·
      refine ⟨25996054082056689180765403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138645621770969008964082149 25996054082056689180765403)
      ·
        refine ⟨38994081123085033771148105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25996054082056689180765403 38994081123085033771148105)
        ·
          refine ⟨29245560842313775328361079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38994081123085033771148105 29245560842313775328361079)
          ·
            refine ⟨43868341263470662992541619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29245560842313775328361079 43868341263470662992541619)
            ·
              refine ⟨65802511895205994488812429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43868341263470662992541619 65802511895205994488812429)
              ·
                refine ⟨24675941960702247933304661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65802511895205994488812429 24675941960702247933304661)
                ·
                  refine ⟨144585597425989733984207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24675941960702247933304661 144585597425989733984207)
                  ·
                    rfl

theorem cell23_2534215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 9].length) (baseStart_2534215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534215 prefixEnd_2534215 := by exact prefixLift 2534215
  have htrace : WordTrace (prefixWord ++ tailWord_2534215) baseStart_2534215 baseEnd_2534215 := by
    simpa [prefixWord, tailWord_2534215, baseEnd_2534215] using wordTrace_append hprefix tailTrace_2534215
  have hstable : (prefixWord ++ tailWord_2534215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534215).length < 2 ^ (prefixWord ++ tailWord_2534215).sum := by decide
  have hdescent : baseEnd_2534215 < baseStart_2534215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534243 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 2, 2, 2]
def baseStart_2534243 : Nat := 118140960795 + 2534243 * 2 ^ 59
def prefixEnd_2534243 : Nat := 4983230072969 + 3 ^ 40 * 2534243 * 2
def baseEnd_2534243 : Nat := 1301284754292233496307735

theorem tailTrace_2534243 : CollatzResearch.WordTrace tailWord_2534243 prefixEnd_2534243 1301284754292233496307735 := by
  unfold tailWord_2534243
  simp only [CollatzResearch.WordTrace]
  refine ⟨92431435757877900091407383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61620957171918600060938255 92431435757877900091407383)
  ·
    refine ⟨138647153636816850137111075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92431435757877900091407383 138647153636816850137111075)
    ·
      refine ⟨207970730455225275205666613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138647153636816850137111075 207970730455225275205666613)
      ·
        refine ⟨19497255980177369550531245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207970730455225275205666613 19497255980177369550531245)
        ·
          refine ⟨7311470992566513581449217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19497255980177369550531245 7311470992566513581449217)
          ·
            refine ⟨5483603244424885186086913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7311470992566513581449217 5483603244424885186086913)
            ·
              refine ⟨4112702433318663889565185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483603244424885186086913 4112702433318663889565185)
              ·
                refine ⟨3084526824988997917173889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4112702433318663889565185 3084526824988997917173889)
                ·
                  refine ⟨2313395118741748437880417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3084526824988997917173889 2313395118741748437880417)
                  ·
                    refine ⟨1735046339056311328410313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2313395118741748437880417 1735046339056311328410313)
                    ·
                      refine ⟨1301284754292233496307735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735046339056311328410313 1301284754292233496307735)
                      ·
                        rfl

theorem cell23_2534243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_2534243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534243 prefixEnd_2534243 := by exact prefixLift 2534243
  have htrace : WordTrace (prefixWord ++ tailWord_2534243) baseStart_2534243 baseEnd_2534243 := by
    simpa [prefixWord, tailWord_2534243, baseEnd_2534243] using wordTrace_append hprefix tailTrace_2534243
  have hstable : (prefixWord ++ tailWord_2534243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534243).length < 2 ^ (prefixWord ++ tailWord_2534243).sum := by decide
  have hdescent : baseEnd_2534243 < baseStart_2534243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534279 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 2, 5]
def baseStart_2534279 : Nat := 118140960795 + 2534279 * 2 ^ 59
def prefixEnd_2534279 : Nat := 4983230072969 + 3 ^ 40 * 2534279 * 2
def baseEnd_2534279 : Nat := 433767746531931785152523

theorem tailTrace_2534279 : CollatzResearch.WordTrace tailWord_2534279 prefixEnd_2534279 433767746531931785152523 := by
  unfold tailWord_2534279
  simp only [CollatzResearch.WordTrace]
  refine ⟨92432748785747478239717891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61621832523831652159811927 92432748785747478239717891)
  ·
    refine ⟨138649123178621217359576837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92432748785747478239717891 138649123178621217359576837)
    ·
      refine ⟨25996710595991478254920657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138649123178621217359576837 25996710595991478254920657)
      ·
        refine ⟨19497532946993608691190493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25996710595991478254920657 19497532946993608691190493)
        ·
          refine ⟨7311574855122603259196435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19497532946993608691190493 7311574855122603259196435)
          ·
            refine ⟨10967362282683904888794653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7311574855122603259196435 10967362282683904888794653)
            ·
              refine ⟨4112760856006464333297995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10967362282683904888794653 4112760856006464333297995)
              ·
                refine ⟨6169141284009696499946993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112760856006464333297995 6169141284009696499946993)
                ·
                  refine ⟨4626855963007272374960245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6169141284009696499946993 4626855963007272374960245)
                  ·
                    refine ⟨433767746531931785152523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4626855963007272374960245 433767746531931785152523)
                    ·
                      rfl

theorem cell23_2534279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_2534279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534279 prefixEnd_2534279 := by exact prefixLift 2534279
  have htrace : WordTrace (prefixWord ++ tailWord_2534279) baseStart_2534279 baseEnd_2534279 := by
    simpa [prefixWord, tailWord_2534279, baseEnd_2534279] using wordTrace_append hprefix tailTrace_2534279
  have hstable : (prefixWord ++ tailWord_2534279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534279).length < 2 ^ (prefixWord ++ tailWord_2534279).sum := by decide
  have hdescent : baseEnd_2534279 < baseStart_2534279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534294 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2534294 : Nat := 118140960795 + 2534294 * 2 ^ 59
def prefixEnd_2534294 : Nat := 4983230072969 + 3 ^ 40 * 2534294 * 2
def baseEnd_2534294 : Nat := 1301310941805612796770001

theorem tailTrace_2534294 : CollatzResearch.WordTrace tailWord_2534294 prefixEnd_2534294 1301310941805612796770001 := by
  unfold tailWord_2534294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777080992543320987594621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61622197253795423867675957 5777080992543320987594621)
  ·
    refine ⟨2166405372203745370347983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5777080992543320987594621 2166405372203745370347983)
    ·
      refine ⟨3249608058305618055521975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166405372203745370347983 3249608058305618055521975)
      ·
        refine ⟨4874412087458427083282963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249608058305618055521975 4874412087458427083282963)
        ·
          refine ⟨7311618131187640624924445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874412087458427083282963 7311618131187640624924445)
          ·
            refine ⟨2741856799195365234346667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7311618131187640624924445 2741856799195365234346667)
            ·
              refine ⟨4112785198793047851520001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741856799195365234346667 4112785198793047851520001)
              ·
                refine ⟨3084588899094785888640001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4112785198793047851520001 3084588899094785888640001)
                ·
                  refine ⟨2313441674321089416480001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3084588899094785888640001 2313441674321089416480001)
                  ·
                    refine ⟨1735081255740817062360001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2313441674321089416480001 1735081255740817062360001)
                    ·
                      refine ⟨1301310941805612796770001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735081255740817062360001 1301310941805612796770001)
                      ·
                        rfl

theorem cell23_2534294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2534294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534294 prefixEnd_2534294 := by exact prefixLift 2534294
  have htrace : WordTrace (prefixWord ++ tailWord_2534294) baseStart_2534294 baseEnd_2534294 := by
    simpa [prefixWord, tailWord_2534294, baseEnd_2534294] using wordTrace_append hprefix tailTrace_2534294
  have hstable : (prefixWord ++ tailWord_2534294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534294).length < 2 ^ (prefixWord ++ tailWord_2534294).sum := by decide
  have hdescent : baseEnd_2534294 < baseStart_2534294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534352 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 5, 5]
def baseStart_2534352 : Nat := 118140960795 + 2534352 * 2 ^ 59
def prefixEnd_2534352 : Nat := 4983230072969 + 3 ^ 40 * 2534352 * 2
def baseEnd_2534352 : Nat := 433780241227857856614911

theorem tailTrace_2534352 : CollatzResearch.WordTrace tailWord_2534352 prefixEnd_2534352 433780241227857856614911 := by
  unfold tailWord_2534352
  simp only [CollatzResearch.WordTrace]
  refine ⟨46217705657241505853562655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61623607542988674471416873 46217705657241505853562655)
  ·
    refine ⟨69326558485862258780343983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46217705657241505853562655 69326558485862258780343983)
    ·
      refine ⟨103989837728793388170515975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69326558485862258780343983 103989837728793388170515975)
      ·
        refine ⟨155984756593190082255773963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103989837728793388170515975 155984756593190082255773963)
        ·
          refine ⟨233977134889785123383660945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155984756593190082255773963 233977134889785123383660945)
          ·
            refine ⟨175482851167338842537745709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233977134889785123383660945 175482851167338842537745709)
            ·
              refine ⟨65806069187752065951654641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175482851167338842537745709 65806069187752065951654641)
              ·
                refine ⟨49354551890814049463740981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65806069187752065951654641 49354551890814049463740981)
                ·
                  refine ⟨4626989239763817137225717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49354551890814049463740981 4626989239763817137225717)
                  ·
                    refine ⟨433780241227857856614911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4626989239763817137225717 433780241227857856614911)
                    ·
                      rfl

theorem cell23_2534352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_2534352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534352 prefixEnd_2534352 := by exact prefixLift 2534352
  have htrace : WordTrace (prefixWord ++ tailWord_2534352) baseStart_2534352 baseEnd_2534352 := by
    simpa [prefixWord, tailWord_2534352, baseEnd_2534352] using wordTrace_append hprefix tailTrace_2534352
  have hstable : (prefixWord ++ tailWord_2534352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534352).length < 2 ^ (prefixWord ++ tailWord_2534352).sum := by decide
  have hdescent : baseEnd_2534352 < baseStart_2534352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534359 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 3, 5, 2]
def baseStart_2534359 : Nat := 118140960795 + 2534359 * 2 ^ 59
def prefixEnd_2534359 : Nat := 4983230072969 + 3 ^ 40 * 2534359 * 2
def baseEnd_2534359 : Nat := 1301344318048155042457201

theorem tailTrace_2534359 : CollatzResearch.WordTrace tailWord_2534359 prefixEnd_2534359 1301344318048155042457201 := by
  unfold tailWord_2534359
  simp only [CollatzResearch.WordTrace]
  refine ⟨92435666625457651902630131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61623777750305101268420087 92435666625457651902630131)
  ·
    refine ⟨138653499938186477853945197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92435666625457651902630131 138653499938186477853945197)
    ·
      refine ⟨51995062476819929195229449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138653499938186477853945197 51995062476819929195229449)
      ·
        refine ⟨38996296857614946896422087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51995062476819929195229449 38996296857614946896422087)
        ·
          refine ⟨58494445286422420344633131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38996296857614946896422087 58494445286422420344633131)
          ·
            refine ⟨87741667929633630516949697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58494445286422420344633131 87741667929633630516949697)
            ·
              refine ⟨65806250947225222887712273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87741667929633630516949697 65806250947225222887712273)
              ·
                refine ⟨49354688210418917165784205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65806250947225222887712273 49354688210418917165784205)
                ·
                  refine ⟨18508008078907093937169077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49354688210418917165784205 18508008078907093937169077)
                  ·
                    refine ⟨1735125757397540056609601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18508008078907093937169077 1735125757397540056609601)
                    ·
                      refine ⟨1301344318048155042457201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735125757397540056609601 1301344318048155042457201)
                      ·
                        rfl

theorem cell23_2534359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_2534359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534359 prefixEnd_2534359 := by exact prefixLift 2534359
  have htrace : WordTrace (prefixWord ++ tailWord_2534359) baseStart_2534359 baseEnd_2534359 := by
    simpa [prefixWord, tailWord_2534359, baseEnd_2534359] using wordTrace_append hprefix tailTrace_2534359
  have hstable : (prefixWord ++ tailWord_2534359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534359).length < 2 ^ (prefixWord ++ tailWord_2534359).sum := by decide
  have hdescent : baseEnd_2534359 < baseStart_2534359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534412 : List Nat := [2, 2, 1, 2, 3, 13]
def baseStart_2534412 : Nat := 118140960795 + 2534412 * 2 ^ 59
def prefixEnd_2534412 : Nat := 4983230072969 + 3 ^ 40 * 2534412 * 2
def baseEnd_2534412 : Nat := 5355438405443799732899

theorem tailTrace_2534412 : CollatzResearch.WordTrace tailWord_2534412 prefixEnd_2534412 5355438405443799732899 := by
  unfold tailWord_2534412
  simp only [CollatzResearch.WordTrace]
  refine ⟨46218799847132820977154745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61625066462843761302872993 46218799847132820977154745)
  ·
    refine ⟨34664099885349615732866059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46218799847132820977154745 34664099885349615732866059)
    ·
      refine ⟨51996149828024423599299089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34664099885349615732866059 51996149828024423599299089)
      ·
        refine ⟨38997112371018317699474317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51996149828024423599299089 38997112371018317699474317)
        ·
          refine ⟨14623917139131869137302869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38997112371018317699474317 14623917139131869137302869)
          ·
            refine ⟨5355438405443799732899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 14623917139131869137302869 5355438405443799732899)
            ·
              rfl

theorem cell23_2534412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 13].length) (baseStart_2534412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534412 prefixEnd_2534412 := by exact prefixLift 2534412
  have htrace : WordTrace (prefixWord ++ tailWord_2534412) baseStart_2534412 baseEnd_2534412 := by
    simpa [prefixWord, tailWord_2534412, baseEnd_2534412] using wordTrace_append hprefix tailTrace_2534412
  have hstable : (prefixWord ++ tailWord_2534412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534412).length < 2 ^ (prefixWord ++ tailWord_2534412).sum := by decide
  have hdescent : baseEnd_2534412 < baseStart_2534412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534436 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2534436 : Nat := 118140960795 + 2534436 * 2 ^ 59
def prefixEnd_2534436 : Nat := 4983230072969 + 3 ^ 40 * 2534436 * 2
def baseEnd_2534436 : Nat := 1301383856058551241194347

theorem tailTrace_2534436 : CollatzResearch.WordTrace tailWord_2534436 prefixEnd_2534436 1301383856058551241194347 := by
  unfold tailWord_2534436
  simp only [CollatzResearch.WordTrace]
  refine ⟨46219237523089347026591581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61625650030785796035455441 46219237523089347026591581)
  ·
    refine ⟨17332214071158505134971843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46219237523089347026591581 17332214071158505134971843)
    ·
      refine ⟨25998321106737757702457765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17332214071158505134971843 25998321106737757702457765)
      ·
        refine ⟨4874685207513329569210831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25998321106737757702457765 4874685207513329569210831)
        ·
          refine ⟨7312027811269994353816247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874685207513329569210831 7312027811269994353816247)
          ·
            refine ⟨10968041716904991530724371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312027811269994353816247 10968041716904991530724371)
            ·
              refine ⟨16452062575357487296086557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10968041716904991530724371 16452062575357487296086557)
              ·
                refine ⟨6169523465759057736032459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16452062575357487296086557 6169523465759057736032459)
                ·
                  refine ⟨9254285198638586604048689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169523465759057736032459 9254285198638586604048689)
                  ·
                    refine ⟨6940713898978939953036517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9254285198638586604048689 6940713898978939953036517)
                    ·
                      refine ⟨1301383856058551241194347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6940713898978939953036517 1301383856058551241194347)
                      ·
                        rfl

theorem cell23_2534436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2534436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534436 prefixEnd_2534436 := by exact prefixLift 2534436
  have htrace : WordTrace (prefixWord ++ tailWord_2534436) baseStart_2534436 baseEnd_2534436 := by
    simpa [prefixWord, tailWord_2534436, baseEnd_2534436] using wordTrace_append hprefix tailTrace_2534436
  have hstable : (prefixWord ++ tailWord_2534436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534436).length < 2 ^ (prefixWord ++ tailWord_2534436).sum := by decide
  have hdescent : baseEnd_2534436 < baseStart_2534436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534446 : List Nat := [4, 1, 3, 1, 1, 1, 5, 7]
def baseStart_2534446 : Nat := 118140960795 + 2534446 * 2 ^ 59
def prefixEnd_2534446 : Nat := 4983230072969 + 3 ^ 40 * 2534446 * 2
def baseEnd_2534446 : Nat := 48199592254262822298863

theorem tailTrace_2534446 : CollatzResearch.WordTrace tailWord_2534446 prefixEnd_2534446 48199592254262822298863 := by
  unfold tailWord_2534446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11554854972017808220130899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61625893184094977174031461 11554854972017808220130899)
  ·
    refine ⟨17332282458026712330196349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11554854972017808220130899 17332282458026712330196349)
    ·
      refine ⟨6499605921760017123823631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17332282458026712330196349 6499605921760017123823631)
      ·
        refine ⟨9749408882640025685735447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6499605921760017123823631 9749408882640025685735447)
        ·
          refine ⟨14624113323960038528603171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9749408882640025685735447 14624113323960038528603171)
          ·
            refine ⟨21936169985940057792904757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14624113323960038528603171 21936169985940057792904757)
            ·
              refine ⟨2056515936181880418084821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21936169985940057792904757 2056515936181880418084821)
              ·
                refine ⟨48199592254262822298863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2056515936181880418084821 48199592254262822298863)
                ·
                  rfl

theorem cell23_2534446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_2534446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534446 prefixEnd_2534446 := by exact prefixLift 2534446
  have htrace : WordTrace (prefixWord ++ tailWord_2534446) baseStart_2534446 baseEnd_2534446 := by
    simpa [prefixWord, tailWord_2534446, baseEnd_2534446] using wordTrace_append hprefix tailTrace_2534446
  have hstable : (prefixWord ++ tailWord_2534446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534446).length < 2 ^ (prefixWord ++ tailWord_2534446).sum := by decide
  have hdescent : baseEnd_2534446 < baseStart_2534446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534456 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_2534456 : Nat := 118140960795 + 2534456 * 2 ^ 59
def prefixEnd_2534456 : Nat := 4983230072969 + 3 ^ 40 * 2534456 * 2
def baseEnd_2534456 : Nat := 1301394125671641162944255

theorem tailTrace_2534456 : CollatzResearch.WordTrace tailWord_2534456 prefixEnd_2534456 1301394125671641162944255 := by
  unfold tailWord_2534456
  simp only [CollatzResearch.WordTrace]
  refine ⟨46219602253053118734455611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61626136337404158312607481 46219602253053118734455611)
  ·
    refine ⟨69329403379579678101683417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46219602253053118734455611 69329403379579678101683417)
    ·
      refine ⟨51997052534684758576262563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69329403379579678101683417 51997052534684758576262563)
      ·
        refine ⟨77995578802027137864393845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51997052534684758576262563 77995578802027137864393845)
        ·
          refine ⟨7312085512690044174786923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77995578802027137864393845 7312085512690044174786923)
          ·
            refine ⟨10968128269035066262180385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312085512690044174786923 10968128269035066262180385)
            ·
              refine ⟨8226096201776299696635289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10968128269035066262180385 8226096201776299696635289)
              ·
                refine ⟨6169572151332224772476467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8226096201776299696635289 6169572151332224772476467)
                ·
                  refine ⟨9254358226998337158714701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6169572151332224772476467 9254358226998337158714701)
                  ·
                    refine ⟨3470384335124376434518013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9254358226998337158714701 3470384335124376434518013)
                    ·
                      refine ⟨1301394125671641162944255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3470384335124376434518013 1301394125671641162944255)
                      ·
                        rfl

theorem cell23_2534456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_2534456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534456 prefixEnd_2534456 := by exact prefixLift 2534456
  have htrace : WordTrace (prefixWord ++ tailWord_2534456) baseStart_2534456 baseEnd_2534456 := by
    simpa [prefixWord, tailWord_2534456, baseEnd_2534456] using wordTrace_append hprefix tailTrace_2534456
  have hstable : (prefixWord ++ tailWord_2534456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534456).length < 2 ^ (prefixWord ++ tailWord_2534456).sum := by decide
  have hdescent : baseEnd_2534456 < baseStart_2534456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534457 : List Nat := [1, 2, 1, 5, 2, 2, 2, 3, 1, 2, 2]
def baseStart_2534457 : Nat := 118140960795 + 2534457 * 2 ^ 59
def prefixEnd_2534457 : Nat := 4983230072969 + 3 ^ 40 * 2534457 * 2
def baseEnd_2534457 : Nat := 1301394639152295659031751

theorem tailTrace_2534457 : CollatzResearch.WordTrace tailWord_2534457 prefixEnd_2534457 1301394639152295659031751 := by
  unfold tailWord_2534457
  simp only [CollatzResearch.WordTrace]
  refine ⟨92439240979102614639697625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61626160652735076426465083 92439240979102614639697625)
  ·
    refine ⟨69329430734326960979773219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92439240979102614639697625 69329430734326960979773219)
    ·
      refine ⟨103994146101490441469659829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69329430734326960979773219 103994146101490441469659829)
      ·
        refine ⟨9749451197014728887780609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103994146101490441469659829 9749451197014728887780609)
        ·
          refine ⟨7312088397761046665835457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9749451197014728887780609 7312088397761046665835457)
          ·
            refine ⟨5484066298320784999376593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7312088397761046665835457 5484066298320784999376593)
            ·
              refine ⟨4113049723740588749532445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5484066298320784999376593 4113049723740588749532445)
              ·
                refine ⟨1542393646402720781074667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4113049723740588749532445 1542393646402720781074667)
                ·
                  refine ⟨2313590469604081171612001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542393646402720781074667 2313590469604081171612001)
                  ·
                    refine ⟨1735192852203060878709001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2313590469604081171612001 1735192852203060878709001)
                    ·
                      refine ⟨1301394639152295659031751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735192852203060878709001 1301394639152295659031751)
                      ·
                        rfl

theorem cell23_2534457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_2534457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534457 prefixEnd_2534457 := by exact prefixLift 2534457
  have htrace : WordTrace (prefixWord ++ tailWord_2534457) baseStart_2534457 baseEnd_2534457 := by
    simpa [prefixWord, tailWord_2534457, baseEnd_2534457] using wordTrace_append hprefix tailTrace_2534457
  have hstable : (prefixWord ++ tailWord_2534457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534457).length < 2 ^ (prefixWord ++ tailWord_2534457).sum := by decide
  have hdescent : baseEnd_2534457 < baseStart_2534457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534460 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_2534460 : Nat := 118140960795 + 2534460 * 2 ^ 59
def prefixEnd_2534460 : Nat := 4983230072969 + 3 ^ 40 * 2534460 * 2
def baseEnd_2534460 : Nat := 1301396179594259147294237

theorem tailTrace_2534460 : CollatzResearch.WordTrace tailWord_2534460 prefixEnd_2534460 1301396179594259147294237 := by
  unfold tailWord_2534460
  simp only [CollatzResearch.WordTrace]
  refine ⟨46219675199045873076028417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61626233598727830768037889 46219675199045873076028417)
  ·
    refine ⟨34664756399284404807021313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46219675199045873076028417 34664756399284404807021313)
    ·
      refine ⟨25998567299463303605265985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34664756399284404807021313 25998567299463303605265985)
      ·
        refine ⟨19498925474597477703949489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25998567299463303605265985 19498925474597477703949489)
        ·
          refine ⟨14624194105948108277962117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19498925474597477703949489 14624194105948108277962117)
          ·
            refine ⟨2742036394865270302117897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14624194105948108277962117 2742036394865270302117897)
            ·
              refine ⟨2056527296148952726588423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742036394865270302117897 2056527296148952726588423)
              ·
                refine ⟨3084790944223429089882635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056527296148952726588423 3084790944223429089882635)
                ·
                  refine ⟨4627186416335143634823953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084790944223429089882635 4627186416335143634823953)
                  ·
                    refine ⟨3470389812251357726117965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4627186416335143634823953 3470389812251357726117965)
                    ·
                      refine ⟨1301396179594259147294237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3470389812251357726117965 1301396179594259147294237)
                      ·
                        rfl

theorem cell23_2534460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_2534460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534460 prefixEnd_2534460 := by exact prefixLift 2534460
  have htrace : WordTrace (prefixWord ++ tailWord_2534460) baseStart_2534460 baseEnd_2534460 := by
    simpa [prefixWord, tailWord_2534460, baseEnd_2534460] using wordTrace_append hprefix tailTrace_2534460
  have hstable : (prefixWord ++ tailWord_2534460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534460).length < 2 ^ (prefixWord ++ tailWord_2534460).sum := by decide
  have hdescent : baseEnd_2534460 < baseStart_2534460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534499 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2534499 : Nat := 118140960795 + 2534499 * 2 ^ 59
def prefixEnd_2534499 : Nat := 4983230072969 + 3 ^ 40 * 2534499 * 2
def baseEnd_2534499 : Nat := 1301416205339784494706557

theorem tailTrace_2534499 : CollatzResearch.WordTrace tailWord_2534499 prefixEnd_2534499 1301416205339784494706557 := by
  unfold tailWord_2534499
  simp only [CollatzResearch.WordTrace]
  refine ⟨92440772844950455812726551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61627181896633637208484367 92440772844950455812726551)
  ·
    refine ⟨138661159267425683719089827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92440772844950455812726551 138661159267425683719089827)
    ·
      refine ⟨207991738901138525578634741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138661159267425683719089827 207991738901138525578634741)
      ·
        refine ⟨19499225521981736772997007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 207991738901138525578634741 19499225521981736772997007)
        ·
          refine ⟨29248838282972605159495511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19499225521981736772997007 29248838282972605159495511)
          ·
            refine ⟨43873257424458907739243267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29248838282972605159495511 43873257424458907739243267)
            ·
              refine ⟨65809886136688361608864901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43873257424458907739243267 65809886136688361608864901)
              ·
                refine ⟨12339353650629067801662169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65809886136688361608864901 12339353650629067801662169)
                ·
                  refine ⟨9254515237971800851246627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12339353650629067801662169 9254515237971800851246627)
                  ·
                    refine ⟨13881772856957701276869941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9254515237971800851246627 13881772856957701276869941)
                    ·
                      refine ⟨1301416205339784494706557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13881772856957701276869941 1301416205339784494706557)
                      ·
                        rfl

theorem cell23_2534499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2534499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534499 prefixEnd_2534499 := by exact prefixLift 2534499
  have htrace : WordTrace (prefixWord ++ tailWord_2534499) baseStart_2534499 baseEnd_2534499 := by
    simpa [prefixWord, tailWord_2534499, baseEnd_2534499] using wordTrace_append hprefix tailTrace_2534499
  have hstable : (prefixWord ++ tailWord_2534499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534499).length < 2 ^ (prefixWord ++ tailWord_2534499).sum := by decide
  have hdescent : baseEnd_2534499 < baseStart_2534499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534549 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_2534549 : Nat := 118140960795 + 2534549 * 2 ^ 59
def prefixEnd_2534549 : Nat := 4983230072969 + 3 ^ 40 * 2534549 * 2
def baseEnd_2534549 : Nat := 433813959790836433027109

theorem tailTrace_2534549 : CollatzResearch.WordTrace tailWord_2534549 prefixEnd_2534549 433813959790836433027109 := by
  unfold tailWord_2534549
  simp only [CollatzResearch.WordTrace]
  refine ⟨92442596494769314352046701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61628397663179542901364467 92442596494769314352046701)
  ·
    refine ⟨34665973685538492882017513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92442596494769314352046701 34665973685538492882017513)
    ·
      refine ⟨25999480264153869661513135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34665973685538492882017513 25999480264153869661513135)
      ·
        refine ⟨38999220396230804492269703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25999480264153869661513135 38999220396230804492269703)
        ·
          refine ⟨58498830594346206738404555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38999220396230804492269703 58498830594346206738404555)
          ·
            refine ⟨87748245891519310107606833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58498830594346206738404555 87748245891519310107606833)
            ·
              refine ⟨65811184418639482580705125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87748245891519310107606833 65811184418639482580705125)
              ·
                refine ⟨12339597078494902983882211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65811184418639482580705125 12339597078494902983882211)
                ·
                  refine ⟨18509395617742354475823317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12339597078494902983882211 18509395617742354475823317)
                  ·
                    refine ⟨433813959790836433027109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18509395617742354475823317 433813959790836433027109)
                    ·
                      rfl

theorem cell23_2534549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_2534549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534549 prefixEnd_2534549 := by exact prefixLift 2534549
  have htrace : WordTrace (prefixWord ++ tailWord_2534549) baseStart_2534549 baseEnd_2534549 := by
    simpa [prefixWord, tailWord_2534549, baseEnd_2534549] using wordTrace_append hprefix tailTrace_2534549
  have hstable : (prefixWord ++ tailWord_2534549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534549).length < 2 ^ (prefixWord ++ tailWord_2534549).sum := by decide
  have hdescent : baseEnd_2534549 < baseStart_2534549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534593 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2534593 : Nat := 118140960795 + 2534593 * 2 ^ 59
def prefixEnd_2534593 : Nat := 4983230072969 + 3 ^ 40 * 2534593 * 2
def baseEnd_2534593 : Nat := 1301464472521307126931125

theorem tailTrace_2534593 : CollatzResearch.WordTrace tailWord_2534593 prefixEnd_2534593 1301464472521307126931125 := by
  unfold tailWord_2534593
  simp only [CollatzResearch.WordTrace]
  refine ⟨92444201306609909866648433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61629467537739939911098955 92444201306609909866648433)
  ·
    refine ⟨69333150979957432399986325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92444201306609909866648433 69333150979957432399986325)
    ·
      refine ⟨3249991452185504643749359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69333150979957432399986325 3249991452185504643749359)
      ·
        refine ⟨4874987178278256965624039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249991452185504643749359 4874987178278256965624039)
        ·
          refine ⟨7312480767417385448436059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874987178278256965624039 7312480767417385448436059)
          ·
            refine ⟨10968721151126078172654089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312480767417385448436059 10968721151126078172654089)
            ·
              refine ⟨8226540863344558629490567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10968721151126078172654089 8226540863344558629490567)
              ·
                refine ⟨12339811295016837944235851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8226540863344558629490567 12339811295016837944235851)
                ·
                  refine ⟨18509716942525256916353777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12339811295016837944235851 18509716942525256916353777)
                  ·
                    refine ⟨13882287706893942687265333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18509716942525256916353777 13882287706893942687265333)
                    ·
                      refine ⟨1301464472521307126931125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13882287706893942687265333 1301464472521307126931125)
                      ·
                        rfl

theorem cell23_2534593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2534593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534593 prefixEnd_2534593 := by exact prefixLift 2534593
  have htrace : WordTrace (prefixWord ++ tailWord_2534593) baseStart_2534593 baseEnd_2534593 := by
    simpa [prefixWord, tailWord_2534593, baseEnd_2534593] using wordTrace_append hprefix tailTrace_2534593
  have hstable : (prefixWord ++ tailWord_2534593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534593).length < 2 ^ (prefixWord ++ tailWord_2534593).sum := by decide
  have hdescent : baseEnd_2534593 < baseStart_2534593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534609 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 10]
def baseStart_2534609 : Nat := 118140960795 + 2534609 * 2 ^ 59
def prefixEnd_2534609 : Nat := 4983230072969 + 3 ^ 40 * 2534609 * 2
def baseEnd_2534609 : Nat := 144608076467975451592339

theorem tailTrace_2534609 : CollatzResearch.WordTrace tailWord_2534609 prefixEnd_2534609 144608076467975451592339 := by
  unfold tailWord_2534609
  simp only [CollatzResearch.WordTrace]
  refine ⟨92444784874551944599230881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61629856583034629732820587 92444784874551944599230881)
  ·
    refine ⟨69333588655913958449423161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92444784874551944599230881 69333588655913958449423161)
    ·
      refine ⟨52000191491935468837067371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69333588655913958449423161 52000191491935468837067371)
      ·
        refine ⟨78000287237903203255601057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52000191491935468837067371 78000287237903203255601057)
        ·
          refine ⟨58500215428427402441700793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78000287237903203255601057 58500215428427402441700793)
          ·
            refine ⟨43875161571320551831275595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58500215428427402441700793 43875161571320551831275595)
            ·
              refine ⟨65812742356980827746913393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43875161571320551831275595 65812742356980827746913393)
              ·
                refine ⟨49359556767735620810185045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65812742356980827746913393 49359556767735620810185045)
                ·
                  refine ⟨144608076467975451592339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 49359556767735620810185045 144608076467975451592339)
                  ·
                    rfl

theorem cell23_2534609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 10].length) (baseStart_2534609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534609 prefixEnd_2534609 := by exact prefixLift 2534609
  have htrace : WordTrace (prefixWord ++ tailWord_2534609) baseStart_2534609 baseEnd_2534609 := by
    simpa [prefixWord, tailWord_2534609, baseEnd_2534609] using wordTrace_append hprefix tailTrace_2534609
  have hstable : (prefixWord ++ tailWord_2534609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534609).length < 2 ^ (prefixWord ++ tailWord_2534609).sum := by decide
  have hdescent : baseEnd_2534609 < baseStart_2534609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534613 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2534613 : Nat := 118140960795 + 2534613 * 2 ^ 59
def prefixEnd_2534613 : Nat := 4983230072969 + 3 ^ 40 * 2534613 * 2
def baseEnd_2534613 : Nat := 433824914044799016227011

theorem tailTrace_2534613 : CollatzResearch.WordTrace tailWord_2534613 prefixEnd_2534613 433824914044799016227011 := by
  unfold tailWord_2534613
  simp only [CollatzResearch.WordTrace]
  refine ⟨92444930766537453282376493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61629953844358302188250995 92444930766537453282376493)
  ·
    refine ⟨34666849037451544980891185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92444930766537453282376493 34666849037451544980891185)
    ·
      refine ⟨26000136778088658735668389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34666849037451544980891185 26000136778088658735668389)
      ·
        refine ⟨4875025645891623512937823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26000136778088658735668389 4875025645891623512937823)
        ·
          refine ⟨7312538468837435269406735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4875025645891623512937823 7312538468837435269406735)
          ·
            refine ⟨10968807703256152904110103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312538468837435269406735 10968807703256152904110103)
            ·
              refine ⟨16453211554884229356165155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10968807703256152904110103 16453211554884229356165155)
              ·
                refine ⟨24679817332326344034247733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16453211554884229356165155 24679817332326344034247733)
                ·
                  refine ⟨2313732874905594753210725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24679817332326344034247733 2313732874905594753210725)
                  ·
                    refine ⟨433824914044799016227011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2313732874905594753210725 433824914044799016227011)
                    ·
                      rfl

theorem cell23_2534613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2534613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534613 prefixEnd_2534613 := by exact prefixLift 2534613
  have htrace : WordTrace (prefixWord ++ tailWord_2534613) baseStart_2534613 baseEnd_2534613 := by
    simpa [prefixWord, tailWord_2534613, baseEnd_2534613] using wordTrace_append hprefix tailTrace_2534613
  have hstable : (prefixWord ++ tailWord_2534613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534613).length < 2 ^ (prefixWord ++ tailWord_2534613).sum := by decide
  have hdescent : baseEnd_2534613 < baseStart_2534613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534623 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 3]
def baseStart_2534623 : Nat := 118140960795 + 2534623 * 2 ^ 59
def prefixEnd_2534623 : Nat := 4983230072969 + 3 ^ 40 * 2534623 * 2
def baseEnd_2534623 : Nat := 1301479876940942009555987

theorem tailTrace_2534623 : CollatzResearch.WordTrace tailWord_2534623 prefixEnd_2534623 1301479876940942009555987 := by
  unfold tailWord_2534623
  simp only [CollatzResearch.WordTrace]
  refine ⟨92445295496501224990240523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61630196997667483326827015 92445295496501224990240523)
  ·
    refine ⟨138667943244751837485360785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92445295496501224990240523 138667943244751837485360785)
    ·
      refine ⟨104000957433563878114020589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138667943244751837485360785 104000957433563878114020589)
      ·
        refine ⟨39000359037586454292757721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104000957433563878114020589 39000359037586454292757721)
        ·
          refine ⟨29250269278189840719568291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39000359037586454292757721 29250269278189840719568291)
          ·
            refine ⟨43875403917284761079352437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29250269278189840719568291 43875403917284761079352437)
            ·
              refine ⟨4113319117245446351189291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43875403917284761079352437 4113319117245446351189291)
              ·
                refine ⟨6169978675868169526783937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113319117245446351189291 6169978675868169526783937)
                ·
                  refine ⟨4627484006901127145087953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6169978675868169526783937 4627484006901127145087953)
                  ·
                    refine ⟨3470613005175845358815965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4627484006901127145087953 3470613005175845358815965)
                    ·
                      refine ⟨1301479876940942009555987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3470613005175845358815965 1301479876940942009555987)
                      ·
                        rfl

theorem cell23_2534623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_2534623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534623 prefixEnd_2534623 := by exact prefixLift 2534623
  have htrace : WordTrace (prefixWord ++ tailWord_2534623) baseStart_2534623 baseEnd_2534623 := by
    simpa [prefixWord, tailWord_2534623, baseEnd_2534623] using wordTrace_append hprefix tailTrace_2534623
  have hstable : (prefixWord ++ tailWord_2534623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534623).length < 2 ^ (prefixWord ++ tailWord_2534623).sum := by decide
  have hdescent : baseEnd_2534623 < baseStart_2534623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534643 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 6]
def baseStart_2534643 : Nat := 118140960795 + 2534643 * 2 ^ 59
def prefixEnd_2534643 : Nat := 4983230072969 + 3 ^ 40 * 2534643 * 2
def baseEnd_2534643 : Nat := 144610016283781325700655

theorem tailTrace_2534643 : CollatzResearch.WordTrace tailWord_2534643 prefixEnd_2534643 144610016283781325700655 := by
  unfold tailWord_2534643
  simp only [CollatzResearch.WordTrace]
  refine ⟨92446024956428768405968583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61630683304285845603979055 92446024956428768405968583)
  ·
    refine ⟨138669037434643152608952875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92446024956428768405968583 138669037434643152608952875)
    ·
      refine ⟨208003556151964728913429313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138669037434643152608952875 208003556151964728913429313)
      ·
        refine ⟨156002667113973546685071985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208003556151964728913429313 156002667113973546685071985)
        ·
          refine ⟨117002000335480160013803989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156002667113973546685071985 117002000335480160013803989)
          ·
            refine ⟨2742234382862816250323531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 117002000335480160013803989 2742234382862816250323531)
            ·
              refine ⟨4113351574294224375485297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742234382862816250323531 4113351574294224375485297)
              ·
                refine ⟨3085013680720668281613973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4113351574294224375485297 3085013680720668281613973)
                ·
                  refine ⟨144610016283781325700655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3085013680720668281613973 144610016283781325700655)
                  ·
                    rfl

theorem cell23_2534643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 6].length) (baseStart_2534643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534643 prefixEnd_2534643 := by exact prefixLift 2534643
  have htrace : WordTrace (prefixWord ++ tailWord_2534643) baseStart_2534643 baseEnd_2534643 := by
    simpa [prefixWord, tailWord_2534643, baseEnd_2534643] using wordTrace_append hprefix tailTrace_2534643
  have hstable : (prefixWord ++ tailWord_2534643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534643).length < 2 ^ (prefixWord ++ tailWord_2534643).sum := by decide
  have hdescent : baseEnd_2534643 < baseStart_2534643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534660 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 6]
def baseStart_2534660 : Nat := 118140960795 + 2534660 * 2 ^ 59
def prefixEnd_2534660 : Nat := 4983230072969 + 3 ^ 40 * 2534660 * 2
def baseEnd_2534660 : Nat := 144610986191684262754813

theorem tailTrace_2534660 : CollatzResearch.WordTrace tailWord_2534660 prefixEnd_2534660 144610986191684262754813 := by
  unfold tailWord_2534660
  simp only [CollatzResearch.WordTrace]
  refine ⟨46223322498683590154668717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61631096664911453539558289 46223322498683590154668717)
  ·
    refine ⟨17333745937006346308000769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46223322498683590154668717 17333745937006346308000769)
    ·
      refine ⟨13000309452754759731000577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17333745937006346308000769 13000309452754759731000577)
      ·
        refine ⟨9750232089566069798250433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13000309452754759731000577 9750232089566069798250433)
        ·
          refine ⟨7312674067174552348687825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9750232089566069798250433 7312674067174552348687825)
          ·
            refine ⟨5484505550380914261515869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7312674067174552348687825 5484505550380914261515869)
            ·
              refine ⟨2056689581392842848068451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5484505550380914261515869 2056689581392842848068451)
              ·
                refine ⟨3085034372089264272102677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056689581392842848068451 3085034372089264272102677)
                ·
                  refine ⟨144610986191684262754813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3085034372089264272102677 144610986191684262754813)
                  ·
                    rfl

theorem cell23_2534660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_2534660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534660 prefixEnd_2534660 := by exact prefixLift 2534660
  have htrace : WordTrace (prefixWord ++ tailWord_2534660) baseStart_2534660 baseEnd_2534660 := by
    simpa [prefixWord, tailWord_2534660, baseEnd_2534660] using wordTrace_append hprefix tailTrace_2534660
  have hstable : (prefixWord ++ tailWord_2534660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534660).length < 2 ^ (prefixWord ++ tailWord_2534660).sum := by decide
  have hdescent : baseEnd_2534660 < baseStart_2534660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534670 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2534670 : Nat := 118140960795 + 2534670 * 2 ^ 59
def prefixEnd_2534670 : Nat := 4983230072969 + 3 ^ 40 * 2534670 * 2
def baseEnd_2534670 : Nat := 1301504010531703325668271

theorem tailTrace_2534670 : CollatzResearch.WordTrace tailWord_2534670 prefixEnd_2534670 1301504010531703325668271 := by
  unfold tailWord_2534670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11555876215916369002150183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61631339818220634678134309 11555876215916369002150183)
  ·
    refine ⟨17333814323874553503225275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11555876215916369002150183 17333814323874553503225275)
    ·
      refine ⟨26000721485811830254837913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17333814323874553503225275 26000721485811830254837913)
      ·
        refine ⟨19500541114358872691128435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26000721485811830254837913 19500541114358872691128435)
        ·
          refine ⟨29250811671538309036692653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19500541114358872691128435 29250811671538309036692653)
          ·
            refine ⟨10969054376826865888759745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29250811671538309036692653 10969054376826865888759745)
            ·
              refine ⟨8226790782620149416569809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10969054376826865888759745 8226790782620149416569809)
              ·
                refine ⟨6170093086965112062427357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8226790782620149416569809 6170093086965112062427357)
                ·
                  refine ⟨2313784907611917023410259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6170093086965112062427357 2313784907611917023410259)
                  ·
                    refine ⟨3470677361417875535115389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2313784907611917023410259 3470677361417875535115389)
                    ·
                      refine ⟨1301504010531703325668271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3470677361417875535115389 1301504010531703325668271)
                      ·
                        rfl

theorem cell23_2534670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2534670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534670 prefixEnd_2534670 := by exact prefixLift 2534670
  have htrace : WordTrace (prefixWord ++ tailWord_2534670) baseStart_2534670 baseEnd_2534670 := by
    simpa [prefixWord, tailWord_2534670, baseEnd_2534670] using wordTrace_append hprefix tailTrace_2534670
  have hstable : (prefixWord ++ tailWord_2534670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534670).length < 2 ^ (prefixWord ++ tailWord_2534670).sum := by decide
  have hdescent : baseEnd_2534670 < baseStart_2534670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534673 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 1, 5]
def baseStart_2534673 : Nat := 118140960795 + 2534673 * 2 ^ 59
def prefixEnd_2534673 : Nat := 4983230072969 + 3 ^ 40 * 2534673 * 2
def baseEnd_2534673 : Nat := 433835183657888937976919

theorem tailTrace_2534673 : CollatzResearch.WordTrace tailWord_2534673 prefixEnd_2534673 433835183657888937976919 := by
  unfold tailWord_2534673
  simp only [CollatzResearch.WordTrace]
  refine ⟨92447119146320083529560673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61631412764213389019707115 92447119146320083529560673)
  ·
    refine ⟨69335339359740062647170505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92447119146320083529560673 69335339359740062647170505)
    ·
      refine ⟨52001504519805046985377879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69335339359740062647170505 52001504519805046985377879)
      ·
        refine ⟨78002256779707570478066819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52001504519805046985377879 78002256779707570478066819)
        ·
          refine ⟨117003385169561355717100229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78002256779707570478066819 117003385169561355717100229)
          ·
            refine ⟨21938134719292754196956293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117003385169561355717100229 21938134719292754196956293)
            ·
              refine ⟨4113400259867391411929305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21938134719292754196956293 4113400259867391411929305)
              ·
                refine ⟨3085050194900543558946979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4113400259867391411929305 3085050194900543558946979)
                ·
                  refine ⟨4627575292350815338420469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085050194900543558946979 4627575292350815338420469)
                  ·
                    refine ⟨433835183657888937976919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4627575292350815338420469 433835183657888937976919)
                    ·
                      rfl

theorem cell23_2534673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_2534673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534673 prefixEnd_2534673 := by exact prefixLift 2534673
  have htrace : WordTrace (prefixWord ++ tailWord_2534673) baseStart_2534673 baseEnd_2534673 := by
    simpa [prefixWord, tailWord_2534673, baseEnd_2534673] using wordTrace_append hprefix tailTrace_2534673
  have hstable : (prefixWord ++ tailWord_2534673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534673).length < 2 ^ (prefixWord ++ tailWord_2534673).sum := by decide
  have hdescent : baseEnd_2534673 < baseStart_2534673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534703 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 2, 4]
def baseStart_2534703 : Nat := 118140960795 + 2534703 * 2 ^ 59
def prefixEnd_2534703 : Nat := 4983230072969 + 3 ^ 40 * 2534703 * 2
def baseEnd_2534703 : Nat := 433840318464433898851873

theorem tailTrace_2534703 : CollatzResearch.WordTrace tailWord_2534703 prefixEnd_2534703 433840318464433898851873 := by
  unfold tailWord_2534703
  simp only [CollatzResearch.WordTrace]
  refine ⟨92448213336211398653152763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61632142224140932435435175 92448213336211398653152763)
  ·
    refine ⟨138672320004317097979729145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92448213336211398653152763 138672320004317097979729145)
    ·
      refine ⟨104004240003237823484796859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138672320004317097979729145 104004240003237823484796859)
      ·
        refine ⟨156006360004856735227195289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104004240003237823484796859 156006360004856735227195289)
        ·
          refine ⟨117004770003642551420396467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156006360004856735227195289 117004770003642551420396467)
          ·
            refine ⟨175507155005463827130594701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117004770003642551420396467 175507155005463827130594701)
            ·
              refine ⟨65815183127048935173973013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175507155005463827130594701 65815183127048935173973013)
              ·
                refine ⟨3085086709080418836279985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65815183127048935173973013 3085086709080418836279985)
                ·
                  refine ⟨2313815031810314127209989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3085086709080418836279985 2313815031810314127209989)
                  ·
                    refine ⟨433840318464433898851873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2313815031810314127209989 433840318464433898851873)
                    ·
                      rfl

theorem cell23_2534703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 4].length) (baseStart_2534703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534703 prefixEnd_2534703 := by exact prefixLift 2534703
  have htrace : WordTrace (prefixWord ++ tailWord_2534703) baseStart_2534703 baseEnd_2534703 := by
    simpa [prefixWord, tailWord_2534703, baseEnd_2534703] using wordTrace_append hprefix tailTrace_2534703
  have hstable : (prefixWord ++ tailWord_2534703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534703).length < 2 ^ (prefixWord ++ tailWord_2534703).sum := by decide
  have hdescent : baseEnd_2534703 < baseStart_2534703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534716 : List Nat := [2, 2, 2, 2, 1, 3, 1, 10]
def baseStart_2534716 : Nat := 118140960795 + 2534716 * 2 ^ 59
def prefixEnd_2534716 : Nat := 4983230072969 + 3 ^ 40 * 2534716 * 2
def baseEnd_2534716 : Nat := 48204727060807783173817

theorem tailTrace_2534716 : CollatzResearch.WordTrace tailWord_2534716 prefixEnd_2534716 48204727060807783173817 := by
  unfold tailWord_2534716
  simp only [CollatzResearch.WordTrace]
  refine ⟨46224343742582150936688001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61632458323442867915584001 46224343742582150936688001)
  ·
    refine ⟨34668257806936613202516001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46224343742582150936688001 34668257806936613202516001)
    ·
      refine ⟨26001193355202459901887001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34668257806936613202516001 26001193355202459901887001)
      ·
        refine ⟨19500895016401844926415251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26001193355202459901887001 19500895016401844926415251)
        ·
          refine ⟨29251342524602767389622877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19500895016401844926415251 29251342524602767389622877)
          ·
            refine ⟨10969253446726037771108579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29251342524602767389622877 10969253446726037771108579)
            ·
              refine ⟨16453880170089056656662869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10969253446726037771108579 16453880170089056656662869)
              ·
                refine ⟨48204727060807783173817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16453880170089056656662869 48204727060807783173817)
                ·
                  rfl

theorem cell23_2534716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 10].length) (baseStart_2534716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534716 prefixEnd_2534716 := by exact prefixLift 2534716
  have htrace : WordTrace (prefixWord ++ tailWord_2534716) baseStart_2534716 baseEnd_2534716 := by
    simpa [prefixWord, tailWord_2534716, baseEnd_2534716] using wordTrace_append hprefix tailTrace_2534716
  have hstable : (prefixWord ++ tailWord_2534716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534716).length < 2 ^ (prefixWord ++ tailWord_2534716).sum := by decide
  have hdescent : baseEnd_2534716 < baseStart_2534716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534743 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_2534743 : Nat := 118140960795 + 2534743 * 2 ^ 59
def prefixEnd_2534743 : Nat := 4983230072969 + 3 ^ 40 * 2534743 * 2
def baseEnd_2534743 : Nat := 1301541494619481540055435

theorem tailTrace_2534743 : CollatzResearch.WordTrace tailWord_2534743 prefixEnd_2534743 1301541494619481540055435 := by
  unfold tailWord_2534743
  simp only [CollatzResearch.WordTrace]
  refine ⟨92449672256066485484608883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61633114837377656989739255 92449672256066485484608883)
  ·
    refine ⟨138674508384099728226913325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92449672256066485484608883 138674508384099728226913325)
    ·
      refine ⟨52002940644037398085092497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138674508384099728226913325 52002940644037398085092497)
      ·
        refine ⟨39002205483028048563819373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52002940644037398085092497 39002205483028048563819373)
        ·
          refine ⟨14625827056135518211432265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39002205483028048563819373 14625827056135518211432265)
          ·
            refine ⟨10969370292101638658574199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14625827056135518211432265 10969370292101638658574199)
            ·
              refine ⟨16454055438152457987861299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10969370292101638658574199 16454055438152457987861299)
              ·
                refine ⟨24681083157228686981791949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16454055438152457987861299 24681083157228686981791949)
                ·
                  refine ⟨9255406183960757618171981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24681083157228686981791949 9255406183960757618171981)
                  ·
                    refine ⟨3470777318985284106814493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9255406183960757618171981 3470777318985284106814493)
                    ·
                      refine ⟨1301541494619481540055435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3470777318985284106814493 1301541494619481540055435)
                      ·
                        rfl

theorem cell23_2534743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_2534743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534743 prefixEnd_2534743 := by exact prefixLift 2534743
  have htrace : WordTrace (prefixWord ++ tailWord_2534743) baseStart_2534743 baseEnd_2534743 := by
    simpa [prefixWord, tailWord_2534743, baseEnd_2534743] using wordTrace_append hprefix tailTrace_2534743
  have hstable : (prefixWord ++ tailWord_2534743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534743).length < 2 ^ (prefixWord ++ tailWord_2534743).sum := by decide
  have hdescent : baseEnd_2534743 < baseStart_2534743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534750 : List Nat := [4, 4, 2, 13]
def baseStart_2534750 : Nat := 118140960795 + 2534750 * 2 ^ 59
def prefixEnd_2534750 : Nat := 4983230072969 + 3 ^ 40 * 2534750 * 2
def baseEnd_2534750 : Nat := 595128069951560591069

theorem tailTrace_2534750 : CollatzResearch.WordTrace tailWord_2534750 prefixEnd_2534750 595128069951560591069 := by
  unfold tailWord_2534750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11556240945880140710014213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61633285044694083786742469 11556240945880140710014213)
  ·
    refine ⟨2166795177352526383127665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11556240945880140710014213 2166795177352526383127665)
    ·
      refine ⟨1625096383014394787345749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2166795177352526383127665 1625096383014394787345749)
      ·
        refine ⟨595128069951560591069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1625096383014394787345749 595128069951560591069)
        ·
          rfl

theorem cell23_2534750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 13].length) (baseStart_2534750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534750 prefixEnd_2534750 := by exact prefixLift 2534750
  have htrace : WordTrace (prefixWord ++ tailWord_2534750) baseStart_2534750 baseEnd_2534750 := by
    simpa [prefixWord, tailWord_2534750, baseEnd_2534750] using wordTrace_append hprefix tailTrace_2534750
  have hstable : (prefixWord ++ tailWord_2534750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534750).length < 2 ^ (prefixWord ++ tailWord_2534750).sum := by decide
  have hdescent : baseEnd_2534750 < baseStart_2534750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534770 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_2534770 : Nat := 118140960795 + 2534770 * 2 ^ 59
def prefixEnd_2534770 : Nat := 4983230072969 + 3 ^ 40 * 2534770 * 2
def baseEnd_2534770 : Nat := 1301555358597152934417811

theorem tailTrace_2534770 : CollatzResearch.WordTrace tailWord_2534770 prefixEnd_2534770 1301555358597152934417811 := by
  unfold tailWord_2534770
  simp only [CollatzResearch.WordTrace]
  refine ⟨23112664256742167273960441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61633771351312446063894509 23112664256742167273960441)
  ·
    refine ⟨17334498192556625455470331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23112664256742167273960441 17334498192556625455470331)
    ·
      refine ⟨26001747288834938183205497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17334498192556625455470331 26001747288834938183205497)
      ·
        refine ⟨19501310466626203637404123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26001747288834938183205497 19501310466626203637404123)
        ·
          refine ⟨29251965699939305456106185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19501310466626203637404123 29251965699939305456106185)
          ·
            refine ⟨21938974274954479092079639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29251965699939305456106185 21938974274954479092079639)
            ·
              refine ⟨32908461412431718638119459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21938974274954479092079639 32908461412431718638119459)
              ·
                refine ⟨49362692118647577957179189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32908461412431718638119459 49362692118647577957179189)
                ·
                  refine ⟨4627752386123210433485549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49362692118647577957179189 4627752386123210433485549)
                  ·
                    refine ⟨1735407144796203912557081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4627752386123210433485549 1735407144796203912557081)
                    ·
                      refine ⟨1301555358597152934417811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735407144796203912557081 1301555358597152934417811)
                      ·
                        rfl

theorem cell23_2534770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_2534770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534770 prefixEnd_2534770 := by exact prefixLift 2534770
  have htrace : WordTrace (prefixWord ++ tailWord_2534770) baseStart_2534770 baseEnd_2534770 := by
    simpa [prefixWord, tailWord_2534770, baseEnd_2534770] using wordTrace_append hprefix tailTrace_2534770
  have hstable : (prefixWord ++ tailWord_2534770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534770).length < 2 ^ (prefixWord ++ tailWord_2534770).sum := by decide
  have hdescent : baseEnd_2534770 < baseStart_2534770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534804 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_2534804 : Nat := 118140960795 + 2534804 * 2 ^ 59
def prefixEnd_2534804 : Nat := 4983230072969 + 3 ^ 40 * 2534804 * 2
def baseEnd_2534804 : Nat := 1301572816939405801392655

theorem tailTrace_2534804 : CollatzResearch.WordTrace tailWord_2534804 prefixEnd_2534804 1301572816939405801392655 := by
  unfold tailWord_2534804
  simp only [CollatzResearch.WordTrace]
  refine ⟨46225948554422746451289733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61634598072563661935052977 46225948554422746451289733)
  ·
    refine ⟨8667365353954264959616825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46225948554422746451289733 8667365353954264959616825)
    ·
      refine ⟨6500524015465698719712619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8667365353954264959616825 6500524015465698719712619)
      ·
        refine ⟨9750786023198548079568929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6500524015465698719712619 9750786023198548079568929)
        ·
          refine ⟨7313089517398911059676697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9750786023198548079568929 7313089517398911059676697)
          ·
            refine ⟨5484817138049183294757523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7313089517398911059676697 5484817138049183294757523)
            ·
              refine ⟨8227225707073774942136285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5484817138049183294757523 8227225707073774942136285)
              ·
                refine ⟨3085209640152665603301107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8227225707073774942136285 3085209640152665603301107)
                ·
                  refine ⟨4627814460228998404951661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085209640152665603301107 4627814460228998404951661)
                  ·
                    refine ⟨1735430422585874401856873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4627814460228998404951661 1735430422585874401856873)
                    ·
                      refine ⟨1301572816939405801392655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735430422585874401856873 1301572816939405801392655)
                      ·
                        rfl

theorem cell23_2534804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_2534804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534804 prefixEnd_2534804 := by exact prefixLift 2534804
  have htrace : WordTrace (prefixWord ++ tailWord_2534804) baseStart_2534804 baseEnd_2534804 := by
    simpa [prefixWord, tailWord_2534804, baseEnd_2534804] using wordTrace_append hprefix tailTrace_2534804
  have hstable : (prefixWord ++ tailWord_2534804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534804).length < 2 ^ (prefixWord ++ tailWord_2534804).sum := by decide
  have hdescent : baseEnd_2534804 < baseStart_2534804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534917 : List Nat := [1, 3, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_2534917 : Nat := 118140960795 + 2534917 * 2 ^ 59
def prefixEnd_2534917 : Nat := 4983230072969 + 3 ^ 40 * 2534917 * 2
def baseEnd_2534917 : Nat := 433876946751121286426545

theorem tailTrace_2534917 : CollatzResearch.WordTrace tailWord_2534917 prefixEnd_2534917 433876946751121286426545 := by
  unfold tailWord_2534917
  simp only [CollatzResearch.WordTrace]
  refine ⟨92456018557436113201443005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61637345704957408800962003 92456018557436113201443005)
  ·
    refine ⟨34671006959038542450541127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92456018557436113201443005 34671006959038542450541127)
    ·
      refine ⟨52006510438557813675811691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34671006959038542450541127 52006510438557813675811691)
      ·
        refine ⟨78009765657836720513717537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52006510438557813675811691 78009765657836720513717537)
        ·
          refine ⟨58507324243377540385288153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78009765657836720513717537 58507324243377540385288153)
          ·
            refine ⟨43880493182533155288966115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58507324243377540385288153 43880493182533155288966115)
            ·
              refine ⟨65820739773799732933449173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43880493182533155288966115 65820739773799732933449173)
              ·
                refine ⟨1542673588448431240627715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65820739773799732933449173 1542673588448431240627715)
                ·
                  refine ⟨2314010382672646860941573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542673588448431240627715 2314010382672646860941573)
                  ·
                    refine ⟨433876946751121286426545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2314010382672646860941573 433876946751121286426545)
                    ·
                      rfl

theorem cell23_2534917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_2534917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534917 prefixEnd_2534917 := by exact prefixLift 2534917
  have htrace : WordTrace (prefixWord ++ tailWord_2534917) baseStart_2534917 baseEnd_2534917 := by
    simpa [prefixWord, tailWord_2534917, baseEnd_2534917] using wordTrace_append hprefix tailTrace_2534917
  have hstable : (prefixWord ++ tailWord_2534917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534917).length < 2 ^ (prefixWord ++ tailWord_2534917).sum := by decide
  have hdescent : baseEnd_2534917 < baseStart_2534917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534925 : List Nat := [1, 7, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2534925 : Nat := 118140960795 + 2534925 * 2 ^ 59
def prefixEnd_2534925 : Nat := 4983230072969 + 3 ^ 40 * 2534925 * 2
def baseEnd_2534925 : Nat := 144626105344288869775511

theorem tailTrace_2534925 : CollatzResearch.WordTrace tailWord_2534925 prefixEnd_2534925 144626105344288869775511 := by
  unfold tailWord_2534925
  simp only [CollatzResearch.WordTrace]
  refine ⟨92456310341407130567734229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61637540227604753711822819 92456310341407130567734229)
  ·
    refine ⟨2166944773626729622681271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 92456310341407130567734229 2166944773626729622681271)
    ·
      refine ⟨3250417160440094434021907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166944773626729622681271 3250417160440094434021907)
      ·
        refine ⟨4875625740660141651032861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250417160440094434021907 4875625740660141651032861)
        ·
          refine ⟨1828359652747553119137323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4875625740660141651032861 1828359652747553119137323)
          ·
            refine ⟨2742539479121329678705985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828359652747553119137323 2742539479121329678705985)
            ·
              refine ⟨2056904609340997259029489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742539479121329678705985 2056904609340997259029489)
              ·
                refine ⟨1542678457005747944272117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2056904609340997259029489 1542678457005747944272117)
                ·
                  refine ⟨144626105344288869775511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1542678457005747944272117 144626105344288869775511)
                  ·
                    rfl

theorem cell23_2534925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2534925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534925 prefixEnd_2534925 := by exact prefixLift 2534925
  have htrace : WordTrace (prefixWord ++ tailWord_2534925) baseStart_2534925 baseEnd_2534925 := by
    simpa [prefixWord, tailWord_2534925, baseEnd_2534925] using wordTrace_append hprefix tailTrace_2534925
  have hstable : (prefixWord ++ tailWord_2534925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534925).length < 2 ^ (prefixWord ++ tailWord_2534925).sum := by decide
  have hdescent : baseEnd_2534925 < baseStart_2534925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534960 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 1, 5]
def baseStart_2534960 : Nat := 118140960795 + 2534960 * 2 ^ 59
def prefixEnd_2534960 : Nat := 4983230072969 + 3 ^ 40 * 2534960 * 2
def baseEnd_2534960 : Nat := 433884306640502397013979

theorem tailTrace_2534960 : CollatzResearch.WordTrace tailWord_2534960 prefixEnd_2534960 433884306640502397013979 := by
  unfold tailWord_2534960
  simp only [CollatzResearch.WordTrace]
  refine ⟨46228793448140165772629167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61638391264186887696838889 46228793448140165772629167)
  ·
    refine ⟨69343190172210248658943751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46228793448140165772629167 69343190172210248658943751)
    ·
      refine ⟨104014785258315372988415627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69343190172210248658943751 104014785258315372988415627)
      ·
        refine ⟨156022177887473059482623441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104014785258315372988415627 156022177887473059482623441)
        ·
          refine ⟨117016633415604794611967581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156022177887473059482623441 117016633415604794611967581)
          ·
            refine ⟨43881237530851797979487843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117016633415604794611967581 43881237530851797979487843)
            ·
              refine ⟨65821856296277696969231765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43881237530851797979487843 65821856296277696969231765)
              ·
                refine ⟨3085399513888017045432739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65821856296277696969231765 3085399513888017045432739)
                ·
                  refine ⟨4628099270832025568149109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085399513888017045432739 4628099270832025568149109)
                  ·
                    refine ⟨433884306640502397013979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4628099270832025568149109 433884306640502397013979)
                    ·
                      rfl

theorem cell23_2534960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_2534960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534960 prefixEnd_2534960 := by exact prefixLift 2534960
  have htrace : WordTrace (prefixWord ++ tailWord_2534960) baseStart_2534960 baseEnd_2534960 := by
    simpa [prefixWord, tailWord_2534960, baseEnd_2534960] using wordTrace_append hprefix tailTrace_2534960
  have hstable : (prefixWord ++ tailWord_2534960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534960).length < 2 ^ (prefixWord ++ tailWord_2534960).sum := by decide
  have hdescent : baseEnd_2534960 < baseStart_2534960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534967 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 1, 5, 2]
def baseStart_2534967 : Nat := 118140960795 + 2534967 * 2 ^ 59
def prefixEnd_2534967 : Nat := 4983230072969 + 3 ^ 40 * 2534967 * 2
def baseEnd_2534967 : Nat := 1301656514286088663654405

theorem tailTrace_2534967 : CollatzResearch.WordTrace tailWord_2534967 prefixEnd_2534967 1301656514286088663654405 := by
  unfold tailWord_2534967
  simp only [CollatzResearch.WordTrace]
  refine ⟨92457842207254971740763155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61638561471503314493842103 92457842207254971740763155)
  ·
    refine ⟨138686763310882457611144733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92457842207254971740763155 138686763310882457611144733)
    ·
      refine ⟨52007536241580921604179275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138686763310882457611144733 52007536241580921604179275)
      ·
        refine ⟨78011304362371382406268913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52007536241580921604179275 78011304362371382406268913)
        ·
          refine ⟨58508478271778536804701685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78011304362371382406268913 58508478271778536804701685)
          ·
            refine ⟨5485169837979237825440783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58508478271778536804701685 5485169837979237825440783)
            ·
              refine ⟨8227754756968856738161175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5485169837979237825440783 8227754756968856738161175)
              ·
                refine ⟨12341632135453285107241763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8227754756968856738161175 12341632135453285107241763)
                ·
                  refine ⟨18512448203179927660862645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12341632135453285107241763 18512448203179927660862645)
                  ·
                    refine ⟨1735542019048118218205873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18512448203179927660862645 1735542019048118218205873)
                    ·
                      refine ⟨1301656514286088663654405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735542019048118218205873 1301656514286088663654405)
                      ·
                        rfl

theorem cell23_2534967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_2534967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534967 prefixEnd_2534967 := by exact prefixLift 2534967
  have htrace : WordTrace (prefixWord ++ tailWord_2534967) baseStart_2534967 baseEnd_2534967 := by
    simpa [prefixWord, tailWord_2534967, baseEnd_2534967] using wordTrace_append hprefix tailTrace_2534967
  have hstable : (prefixWord ++ tailWord_2534967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534967).length < 2 ^ (prefixWord ++ tailWord_2534967).sum := by decide
  have hdescent : baseEnd_2534967 < baseStart_2534967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534977 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2534977 : Nat := 118140960795 + 2534977 * 2 ^ 59
def prefixEnd_2534977 : Nat := 4983230072969 + 3 ^ 40 * 2534977 * 2
def baseEnd_2534977 : Nat := 433887216364211208176453

theorem tailTrace_2534977 : CollatzResearch.WordTrace tailWord_2534977 prefixEnd_2534977 433887216364211208176453 := by
  unfold tailWord_2534977
  simp only [CollatzResearch.WordTrace]
  refine ⟨92458206937218743448627185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61638804624812495632418123 92458206937218743448627185)
  ·
    refine ⟨69343655202914057586470389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92458206937218743448627185 69343655202914057586470389)
    ·
      refine ⟨6500967675273192898731599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69343655202914057586470389 6500967675273192898731599)
      ·
        refine ⟨9751451512909789348097399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6500967675273192898731599 9751451512909789348097399)
        ·
          refine ⟨14627177269364684022146099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9751451512909789348097399 14627177269364684022146099)
          ·
            refine ⟨21940765904047026033219149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14627177269364684022146099 21940765904047026033219149)
            ·
              refine ⟨8227787214017634762457181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21940765904047026033219149 8227787214017634762457181)
              ·
                refine ⟨3085420205256613035921443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8227787214017634762457181 3085420205256613035921443)
                ·
                  refine ⟨4628130307884919553882165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085420205256613035921443 4628130307884919553882165)
                  ·
                    refine ⟨433887216364211208176453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4628130307884919553882165 433887216364211208176453)
                    ·
                      rfl

theorem cell23_2534977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2534977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534977 prefixEnd_2534977 := by exact prefixLift 2534977
  have htrace : WordTrace (prefixWord ++ tailWord_2534977) baseStart_2534977 baseEnd_2534977 := by
    simpa [prefixWord, tailWord_2534977, baseEnd_2534977] using wordTrace_append hprefix tailTrace_2534977
  have hstable : (prefixWord ++ tailWord_2534977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534977).length < 2 ^ (prefixWord ++ tailWord_2534977).sum := by decide
  have hdescent : baseEnd_2534977 < baseStart_2534977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534998 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2534998 : Nat := 118140960795 + 2534998 * 2 ^ 59
def prefixEnd_2534998 : Nat := 4983230072969 + 3 ^ 40 * 2534998 * 2
def baseEnd_2534998 : Nat := 144630270242930893596307

theorem tailTrace_2534998 : CollatzResearch.WordTrace tailWord_2534998 prefixEnd_2534998 144630270242930893596307 := by
  unfold tailWord_2534998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5778685804383916502196353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61639315246761776023427765 5778685804383916502196353)
  ·
    refine ⟨4334014353287937376647265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5778685804383916502196353 4334014353287937376647265)
    ·
      refine ⟨3250510764965953032485449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4334014353287937376647265 3250510764965953032485449)
      ·
        refine ⟨2437883073724464774364087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3250510764965953032485449 2437883073724464774364087)
        ·
          refine ⟨3656824610586697161546131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2437883073724464774364087 3656824610586697161546131)
          ·
            refine ⟨5485236915880045742319197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3656824610586697161546131 5485236915880045742319197)
            ·
              refine ⟨2056963843455017153369699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5485236915880045742319197 2056963843455017153369699)
              ·
                refine ⟨3085445765182525730054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056963843455017153369699 3085445765182525730054549)
                ·
                  refine ⟨144630270242930893596307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3085445765182525730054549 144630270242930893596307)
                  ·
                    rfl

theorem cell23_2534998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2534998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2534998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2534998 prefixEnd_2534998 := by exact prefixLift 2534998
  have htrace : WordTrace (prefixWord ++ tailWord_2534998) baseStart_2534998 baseEnd_2534998 := by
    simpa [prefixWord, tailWord_2534998, baseEnd_2534998] using wordTrace_append hprefix tailTrace_2534998
  have hstable : (prefixWord ++ tailWord_2534998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534998).length < 2 ^ (prefixWord ++ tailWord_2534998).sum := by decide
  have hdescent : baseEnd_2534998 < baseStart_2534998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535017 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 3]
def baseStart_2535017 : Nat := 118140960795 + 2535017 * 2 ^ 59
def prefixEnd_2535017 : Nat := 4983230072969 + 3 ^ 40 * 2535017 * 2
def baseEnd_2535017 : Nat := 1301682188318813468029175

theorem tailTrace_2535017 : CollatzResearch.WordTrace tailWord_2535017 prefixEnd_2535017 1301682188318813468029175 := by
  unfold tailWord_2535017
  simp only [CollatzResearch.WordTrace]
  refine ⟨92459665857073830280083305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61639777238049220186722203 92459665857073830280083305)
  ·
    refine ⟨69344749392805372710062479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92459665857073830280083305 69344749392805372710062479)
    ·
      refine ⟨104017124089208059065093719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69344749392805372710062479 104017124089208059065093719)
      ·
        refine ⟨156025686133812088597640579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104017124089208059065093719 156025686133812088597640579)
        ·
          refine ⟨234038529200718132896460869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156025686133812088597640579 234038529200718132896460869)
          ·
            refine ⟨43882224225134649918086413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234038529200718132896460869 43882224225134649918086413)
            ·
              refine ⟨16455834084425493719282405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43882224225134649918086413 16455834084425493719282405)
              ·
                refine ⟨3085468890829780072365451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16455834084425493719282405 3085468890829780072365451)
                ·
                  refine ⟨4628203336244670108548177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085468890829780072365451 4628203336244670108548177)
                  ·
                    refine ⟨3471152502183502581411133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4628203336244670108548177 3471152502183502581411133)
                    ·
                      refine ⟨1301682188318813468029175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3471152502183502581411133 1301682188318813468029175)
                      ·
                        rfl

theorem cell23_2535017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 3].length) (baseStart_2535017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535017 prefixEnd_2535017 := by exact prefixLift 2535017
  have htrace : WordTrace (prefixWord ++ tailWord_2535017) baseStart_2535017 baseEnd_2535017 := by
    simpa [prefixWord, tailWord_2535017, baseEnd_2535017] using wordTrace_append hprefix tailTrace_2535017
  have hstable : (prefixWord ++ tailWord_2535017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535017).length < 2 ^ (prefixWord ++ tailWord_2535017).sum := by decide
  have hdescent : baseEnd_2535017 < baseStart_2535017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535058 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_2535058 : Nat := 118140960795 + 2535058 * 2 ^ 59
def prefixEnd_2535058 : Nat := 4983230072969 + 3 ^ 40 * 2535058 * 2
def baseEnd_2535058 : Nat := 433901080341882602538829

theorem tailTrace_2535058 : CollatzResearch.WordTrace tailWord_2535058 prefixEnd_2535058 433901080341882602538829 := by
  unfold tailWord_2535058
  simp only [CollatzResearch.WordTrace]
  refine ⟨23115290312481323570581457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61640774166616862854883885 23115290312481323570581457)
  ·
    refine ⟨17336467734360992677936093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23115290312481323570581457 17336467734360992677936093)
    ·
      refine ⟨6501175400385372254226035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17336467734360992677936093 6501175400385372254226035)
      ·
        refine ⟨9751763100578058381339053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501175400385372254226035 9751763100578058381339053)
        ·
          refine ⟨3656911162716771893002145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9751763100578058381339053 3656911162716771893002145)
          ·
            refine ⟨2742683372037578919751609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3656911162716771893002145 2742683372037578919751609)
            ·
              refine ⟨2057012529028184189813707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742683372037578919751609 2057012529028184189813707)
              ·
                refine ⟨3085518793542276284720561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057012529028184189813707 3085518793542276284720561)
                ·
                  refine ⟨2314139095156707213540421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3085518793542276284720561 2314139095156707213540421)
                  ·
                    refine ⟨433901080341882602538829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2314139095156707213540421 433901080341882602538829)
                    ·
                      rfl

theorem cell23_2535058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_2535058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535058 prefixEnd_2535058 := by exact prefixLift 2535058
  have htrace : WordTrace (prefixWord ++ tailWord_2535058) baseStart_2535058 baseEnd_2535058 := by
    simpa [prefixWord, tailWord_2535058, baseEnd_2535058] using wordTrace_append hprefix tailTrace_2535058
  have hstable : (prefixWord ++ tailWord_2535058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535058).length < 2 ^ (prefixWord ++ tailWord_2535058).sum := by decide
  have hdescent : baseEnd_2535058 < baseStart_2535058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535068 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_2535068 : Nat := 118140960795 + 2535068 * 2 ^ 59
def prefixEnd_2535068 : Nat := 4983230072969 + 3 ^ 40 * 2535068 * 2
def baseEnd_2535068 : Nat := 1301708375832192768491441

theorem tailTrace_2535068 : CollatzResearch.WordTrace tailWord_2535068 prefixEnd_2535068 1301708375832192768491441 := by
  unfold tailWord_2535068
  simp only [CollatzResearch.WordTrace]
  refine ⟨46230762989944532995094929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61641017319926043993459905 46230762989944532995094929)
  ·
    refine ⟨34673072242458399746321197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46230762989944532995094929 34673072242458399746321197)
    ·
      refine ⟨13002402090921899904870449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34673072242458399746321197 13002402090921899904870449)
      ·
        refine ⟨9751801568191424928652837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13002402090921899904870449 9751801568191424928652837)
        ·
          refine ⟨1828462794035892174122407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9751801568191424928652837 1828462794035892174122407)
          ·
            refine ⟨2742694191053838261183611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828462794035892174122407 2742694191053838261183611)
            ·
              refine ⟨4114041286580757391775417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2742694191053838261183611 4114041286580757391775417)
              ·
                refine ⟨3085530964935568043831563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114041286580757391775417 3085530964935568043831563)
                ·
                  refine ⟨4628296447403352065747345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085530964935568043831563 4628296447403352065747345)
                  ·
                    refine ⟨3471222335552514049310509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4628296447403352065747345 3471222335552514049310509)
                    ·
                      refine ⟨1301708375832192768491441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3471222335552514049310509 1301708375832192768491441)
                      ·
                        rfl

theorem cell23_2535068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_2535068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535068 prefixEnd_2535068 := by exact prefixLift 2535068
  have htrace : WordTrace (prefixWord ++ tailWord_2535068) baseStart_2535068 baseEnd_2535068 := by
    simpa [prefixWord, tailWord_2535068, baseEnd_2535068] using wordTrace_append hprefix tailTrace_2535068
  have hstable : (prefixWord ++ tailWord_2535068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535068).length < 2 ^ (prefixWord ++ tailWord_2535068).sum := by decide
  have hdescent : baseEnd_2535068 < baseStart_2535068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535091 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 1, 3, 2]
def baseStart_2535091 : Nat := 118140960795 + 2535091 * 2 ^ 59
def prefixEnd_2535091 : Nat := 4983230072969 + 3 ^ 40 * 2535091 * 2
def baseEnd_2535091 : Nat := 1301720185887246178503835

theorem tailTrace_2535091 : CollatzResearch.WordTrace tailWord_2535091 prefixEnd_2535091 1301720185887246178503835 := by
  unfold tailWord_2535091
  simp only [CollatzResearch.WordTrace]
  refine ⟨92462364858805740918277127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61641576572537160612184751 92462364858805740918277127)
  ·
    refine ⟨138693547288208611377415691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92462364858805740918277127 138693547288208611377415691)
    ·
      refine ⟨208040320932312917066123537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138693547288208611377415691 208040320932312917066123537)
      ·
        refine ⟨156030240699234687799592653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208040320932312917066123537 156030240699234687799592653)
        ·
          refine ⟨58511340262213007924847245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156030240699234687799592653 58511340262213007924847245)
          ·
            refine ⟨21941752598329877971817717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58511340262213007924847245 21941752598329877971817717)
            ·
              refine ⟨2057039306093426059857911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21941752598329877971817717 2057039306093426059857911)
              ·
                refine ⟨3085558959140139089786867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057039306093426059857911 3085558959140139089786867)
                ·
                  refine ⟨4628338438710208634680301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3085558959140139089786867 4628338438710208634680301)
                  ·
                    refine ⟨1735626914516328238005113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4628338438710208634680301 1735626914516328238005113)
                    ·
                      refine ⟨1301720185887246178503835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735626914516328238005113 1301720185887246178503835)
                      ·
                        rfl

theorem cell23_2535091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 3, 2].length) (baseStart_2535091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535091 prefixEnd_2535091 := by exact prefixLift 2535091
  have htrace : WordTrace (prefixWord ++ tailWord_2535091) baseStart_2535091 baseEnd_2535091 := by
    simpa [prefixWord, tailWord_2535091, baseEnd_2535091] using wordTrace_append hprefix tailTrace_2535091
  have hstable : (prefixWord ++ tailWord_2535091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535091).length < 2 ^ (prefixWord ++ tailWord_2535091).sum := by decide
  have hdescent : baseEnd_2535091 < baseStart_2535091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535121 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 2, 2, 2]
def baseStart_2535121 : Nat := 118140960795 + 2535121 * 2 ^ 59
def prefixEnd_2535121 : Nat := 4983230072969 + 3 ^ 40 * 2535121 * 2
def baseEnd_2535121 : Nat := 1301735590306881061128697

theorem tailTrace_2535121 : CollatzResearch.WordTrace tailWord_2535121 prefixEnd_2535121 1301735590306881061128697 := by
  unfold tailWord_2535121
  simp only [CollatzResearch.WordTrace]
  refine ⟨92463459048697056041869217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61642306032464704027912811 92463459048697056041869217)
  ·
    refine ⟨69347594286522792031401913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92463459048697056041869217 69347594286522792031401913)
    ·
      refine ⟨52010695714892094023551435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69347594286522792031401913 52010695714892094023551435)
      ·
        refine ⟨78016043572338141035327153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52010695714892094023551435 78016043572338141035327153)
        ·
          refine ⟨58512032679253605776495365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78016043572338141035327153 58512032679253605776495365)
          ·
            refine ⟨10971006127360051083092881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58512032679253605776495365 10971006127360051083092881)
            ·
              refine ⟨8228254595520038312319661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10971006127360051083092881 8228254595520038312319661)
              ·
                refine ⟨3085595473320014367119873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8228254595520038312319661 3085595473320014367119873)
                ·
                  refine ⟨2314196604990010775339905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3085595473320014367119873 2314196604990010775339905)
                  ·
                    refine ⟨1735647453742508081504929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2314196604990010775339905 1735647453742508081504929)
                    ·
                      refine ⟨1301735590306881061128697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735647453742508081504929 1301735590306881061128697)
                      ·
                        rfl

theorem cell23_2535121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_2535121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535121 prefixEnd_2535121 := by exact prefixLift 2535121
  have htrace : WordTrace (prefixWord ++ tailWord_2535121) baseStart_2535121 baseEnd_2535121 := by
    simpa [prefixWord, tailWord_2535121, baseEnd_2535121] using wordTrace_append hprefix tailTrace_2535121
  have hstable : (prefixWord ++ tailWord_2535121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535121).length < 2 ^ (prefixWord ++ tailWord_2535121).sum := by decide
  have hdescent : baseEnd_2535121 < baseStart_2535121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535144 : List Nat := [2, 1, 4, 1, 3, 1, 1, 5, 5]
def baseStart_2535144 : Nat := 118140960795 + 2535144 * 2 ^ 59
def prefixEnd_2535144 : Nat := 4983230072969 + 3 ^ 40 * 2535144 * 2
def baseEnd_2535144 : Nat := 144638600040214941237899

theorem tailTrace_2535144 : CollatzResearch.WordTrace tailWord_2535144 prefixEnd_2535144 144638600040214941237899 := by
  unfold tailWord_2535144
  simp only [CollatzResearch.WordTrace]
  refine ⟨46232148963806865484978243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61642865285075820646637657 46232148963806865484978243)
  ·
    refine ⟨69348223445710298227467365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46232148963806865484978243 69348223445710298227467365)
    ·
      refine ⟨13002791896070680917650131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69348223445710298227467365 13002791896070680917650131)
      ·
        refine ⟨19504187844106021376475197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13002791896070680917650131 19504187844106021376475197)
        ·
          refine ⟨7314070441539758016178199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19504187844106021376475197 7314070441539758016178199)
          ·
            refine ⟨10971105662309637024267299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7314070441539758016178199 10971105662309637024267299)
            ·
              refine ⟨16456658493464455536400949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10971105662309637024267299 16456658493464455536400949)
              ·
                refine ⟨1542811733762292706537589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16456658493464455536400949 1542811733762292706537589)
                ·
                  refine ⟨144638600040214941237899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1542811733762292706537589 144638600040214941237899)
                  ·
                    rfl

theorem cell23_2535144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 5].length) (baseStart_2535144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535144 prefixEnd_2535144 := by exact prefixLift 2535144
  have htrace : WordTrace (prefixWord ++ tailWord_2535144) baseStart_2535144 baseEnd_2535144 := by
    simpa [prefixWord, tailWord_2535144, baseEnd_2535144] using wordTrace_append hprefix tailTrace_2535144
  have hstable : (prefixWord ++ tailWord_2535144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535144).length < 2 ^ (prefixWord ++ tailWord_2535144).sum := by decide
  have hdescent : baseEnd_2535144 < baseStart_2535144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535187 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 5, 4]
def baseStart_2535187 : Nat := 118140960795 + 2535187 * 2 ^ 59
def prefixEnd_2535187 : Nat := 4983230072969 + 3 ^ 40 * 2535187 * 2
def baseEnd_2535187 : Nat := 433923160010025934301131

theorem tailTrace_2535187 : CollatzResearch.WordTrace tailWord_2535187 prefixEnd_2535187 433923160010025934301131 := by
  unfold tailWord_2535187
  simp only [CollatzResearch.WordTrace]
  refine ⟨92465866266457949313771815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61643910844305299542514543 92465866266457949313771815)
  ·
    refine ⟨138698799399686923970657723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92465866266457949313771815 138698799399686923970657723)
    ·
      refine ⟨208048199099530385955986585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138698799399686923970657723 208048199099530385955986585)
      ·
        refine ⟨156036149324647789466989939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208048199099530385955986585 156036149324647789466989939)
        ·
          refine ⟨234054223986971684200484909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156036149324647789466989939 234054223986971684200484909)
          ·
            refine ⟨87770333995114381575181841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234054223986971684200484909 87770333995114381575181841)
            ·
              refine ⟨65827750496335786181386381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87770333995114381575181841 65827750496335786181386381)
              ·
                refine ⟨24685406436125919818019893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65827750496335786181386381 24685406436125919818019893)
                ·
                  refine ⟨2314256853386804982939365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24685406436125919818019893 2314256853386804982939365)
                  ·
                    refine ⟨433923160010025934301131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2314256853386804982939365 433923160010025934301131)
                    ·
                      rfl

theorem cell23_2535187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 5, 4].length) (baseStart_2535187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535187 prefixEnd_2535187 := by exact prefixLift 2535187
  have htrace : WordTrace (prefixWord ++ tailWord_2535187) baseStart_2535187 baseEnd_2535187 := by
    simpa [prefixWord, tailWord_2535187, baseEnd_2535187] using wordTrace_append hprefix tailTrace_2535187
  have hstable : (prefixWord ++ tailWord_2535187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535187).length < 2 ^ (prefixWord ++ tailWord_2535187).sum := by decide
  have hdescent : baseEnd_2535187 < baseStart_2535187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535217 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 8]
def baseStart_2535217 : Nat := 118140960795 + 2535217 * 2 ^ 59
def prefixEnd_2535217 : Nat := 4983230072969 + 3 ^ 40 * 2535217 * 2
def baseEnd_2535217 : Nat := 144642764938856965058695

theorem tailTrace_2535217 : CollatzResearch.WordTrace tailWord_2535217 prefixEnd_2535217 144642764938856965058695 := by
  unfold tailWord_2535217
  simp only [CollatzResearch.WordTrace]
  refine ⟨92466960456349264437363905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61644640304232842958242603 92466960456349264437363905)
  ·
    refine ⟨69350220342261948328022929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92466960456349264437363905 69350220342261948328022929)
    ·
      refine ⟨52012665256696461246017197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69350220342261948328022929 52012665256696461246017197)
      ·
        refine ⟨19504749471261172967256449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52012665256696461246017197 19504749471261172967256449)
        ·
          refine ⟨14628562103445879725442337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19504749471261172967256449 14628562103445879725442337)
          ·
            refine ⟨10971421577584409794081753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14628562103445879725442337 10971421577584409794081753)
            ·
              refine ⟨8228566183188307345561315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10971421577584409794081753 8228566183188307345561315)
              ·
                refine ⟨12342849274782461018341973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8228566183188307345561315 12342849274782461018341973)
                ·
                  refine ⟨144642764938856965058695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12342849274782461018341973 144642764938856965058695)
                  ·
                    rfl

theorem cell23_2535217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 8].length) (baseStart_2535217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535217 prefixEnd_2535217 := by exact prefixLift 2535217
  have htrace : WordTrace (prefixWord ++ tailWord_2535217) baseStart_2535217 baseEnd_2535217 := by
    simpa [prefixWord, tailWord_2535217, baseEnd_2535217] using wordTrace_append hprefix tailTrace_2535217
  have hstable : (prefixWord ++ tailWord_2535217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535217).length < 2 ^ (prefixWord ++ tailWord_2535217).sum := by decide
  have hdescent : baseEnd_2535217 < baseStart_2535217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535271 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_2535271 : Nat := 118140960795 + 2535271 * 2 ^ 59
def prefixEnd_2535271 : Nat := 4983230072969 + 3 ^ 40 * 2535271 * 2
def baseEnd_2535271 : Nat := 1301812612405055474253007

theorem tailTrace_2535271 : CollatzResearch.WordTrace tailWord_2535271 prefixEnd_2535271 1301812612405055474253007 := by
  unfold tailWord_2535271
  simp only [CollatzResearch.WordTrace]
  refine ⟨92468929998153631659829667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61645953332102421106553111 92468929998153631659829667)
  ·
    refine ⟨138703394997230447489744501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92468929998153631659829667 138703394997230447489744501)
    ·
      refine ⟨13003443280990354452163547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138703394997230447489744501 13003443280990354452163547)
      ·
        refine ⟨19505164921485531678245321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13003443280990354452163547 19505164921485531678245321)
        ·
          refine ⟨14628873691114148758683991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19505164921485531678245321 14628873691114148758683991)
          ·
            refine ⟨21943310536671223138025987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14628873691114148758683991 21943310536671223138025987)
            ·
              refine ⟨32914965805006834707038981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21943310536671223138025987 32914965805006834707038981)
              ·
                refine ⟨6171556088438781507569809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32914965805006834707038981 6171556088438781507569809)
                ·
                  refine ⟨4628667066329086130677357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6171556088438781507569809 4628667066329086130677357)
                  ·
                    refine ⟨1735750149873407299004009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4628667066329086130677357 1735750149873407299004009)
                    ·
                      refine ⟨1301812612405055474253007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735750149873407299004009 1301812612405055474253007)
                      ·
                        rfl

theorem cell23_2535271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_2535271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535271 prefixEnd_2535271 := by exact prefixLift 2535271
  have htrace : WordTrace (prefixWord ++ tailWord_2535271) baseStart_2535271 baseEnd_2535271 := by
    simpa [prefixWord, tailWord_2535271, baseEnd_2535271] using wordTrace_append hprefix tailTrace_2535271
  have hstable : (prefixWord ++ tailWord_2535271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535271).length < 2 ^ (prefixWord ++ tailWord_2535271).sum := by decide
  have hdescent : baseEnd_2535271 < baseStart_2535271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535324 : List Nat := [2, 2, 3, 3, 1, 2, 10]
def baseStart_2535324 : Nat := 118140960795 + 2535324 * 2 ^ 59
def prefixEnd_2535324 : Nat := 4983230072969 + 3 ^ 40 * 2535324 * 2
def baseEnd_2535324 : Nat := 16072096628144984776423

theorem tailTrace_2535324 : CollatzResearch.WordTrace tailWord_2535324 prefixEnd_2535324 16072096628144984776423 := by
  unfold tailWord_2535324
  simp only [CollatzResearch.WordTrace]
  refine ⟨46235431533480810855754513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61647242044641081141006017 46235431533480810855754513)
  ·
    refine ⟨34676573650110608141815885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46235431533480810855754513 34676573650110608141815885)
    ·
      refine ⟨13003715118791478053180957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34676573650110608141815885 13003715118791478053180957)
      ·
        refine ⟨4876393169546804269942859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13003715118791478053180957 4876393169546804269942859)
        ·
          refine ⟨7314589754320206404914289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876393169546804269942859 7314589754320206404914289)
          ·
            refine ⟨5485942315740154803685717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314589754320206404914289 5485942315740154803685717)
            ·
              refine ⟨16072096628144984776423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5485942315740154803685717 16072096628144984776423)
              ·
                rfl

theorem cell23_2535324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 10].length) (baseStart_2535324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535324 prefixEnd_2535324 := by exact prefixLift 2535324
  have htrace : WordTrace (prefixWord ++ tailWord_2535324) baseStart_2535324 baseEnd_2535324 := by
    simpa [prefixWord, tailWord_2535324, baseEnd_2535324] using wordTrace_append hprefix tailTrace_2535324
  have hstable : (prefixWord ++ tailWord_2535324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535324).length < 2 ^ (prefixWord ++ tailWord_2535324).sum := by decide
  have hdescent : baseEnd_2535324 < baseStart_2535324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535335 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_2535335 : Nat := 118140960795 + 2535335 * 2 ^ 59
def prefixEnd_2535335 : Nat := 4983230072969 + 3 ^ 40 * 2535335 * 2
def baseEnd_2535335 : Nat := 1301845475166943223852713

theorem tailTrace_2535335 : CollatzResearch.WordTrace tailWord_2535335 prefixEnd_2535335 1301845475166943223852713 := by
  unfold tailWord_2535335
  simp only [CollatzResearch.WordTrace]
  refine ⟨92471264269921770590159459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61647509513281180393439639 92471264269921770590159459)
  ·
    refine ⟨138706896404882655885239189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92471264269921770590159459 138706896404882655885239189)
    ·
      refine ⟨6501885768978874494620587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138706896404882655885239189 6501885768978874494620587)
      ·
        refine ⟨9752828653468311741930881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501885768978874494620587 9752828653468311741930881)
        ·
          refine ⟨7314621490101233806448161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9752828653468311741930881 7314621490101233806448161)
          ·
            refine ⟨5485966117575925354836121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314621490101233806448161 5485966117575925354836121)
            ·
              refine ⟨4114474588181944016127091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5485966117575925354836121 4114474588181944016127091)
              ·
                refine ⟨6171711882272916024190637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114474588181944016127091 6171711882272916024190637)
                ·
                  refine ⟨2314391955852343509071489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6171711882272916024190637 2314391955852343509071489)
                  ·
                    refine ⟨1735793966889257631803617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2314391955852343509071489 1735793966889257631803617)
                    ·
                      refine ⟨1301845475166943223852713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1735793966889257631803617 1301845475166943223852713)
                      ·
                        rfl

theorem cell23_2535335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_2535335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535335 prefixEnd_2535335 := by exact prefixLift 2535335
  have htrace : WordTrace (prefixWord ++ tailWord_2535335) baseStart_2535335 baseEnd_2535335 := by
    simpa [prefixWord, tailWord_2535335, baseEnd_2535335] using wordTrace_append hprefix tailTrace_2535335
  have hstable : (prefixWord ++ tailWord_2535335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535335).length < 2 ^ (prefixWord ++ tailWord_2535335).sum := by decide
  have hdescent : baseEnd_2535335 < baseStart_2535335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535337 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 2, 7]
def baseStart_2535337 : Nat := 118140960795 + 2535337 * 2 ^ 59
def prefixEnd_2535337 : Nat := 4983230072969 + 3 ^ 40 * 2535337 * 2
def baseEnd_2535337 : Nat := 433948834042750738675901

theorem tailTrace_2535337 : CollatzResearch.WordTrace tailWord_2535337 prefixEnd_2535337 433948834042750738675901 := by
  unfold tailWord_2535337
  simp only [CollatzResearch.WordTrace]
  refine ⟨92471337215914524931732265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61647558143943016621154843 92471337215914524931732265)
  ·
    refine ⟨69353502911935893698799199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92471337215914524931732265 69353502911935893698799199)
    ·
      refine ⟨104030254367903840548198799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69353502911935893698799199 104030254367903840548198799)
      ·
        refine ⟨156045381551855760822298199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104030254367903840548198799 156045381551855760822298199)
        ·
          refine ⟨234068072327783641233447299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156045381551855760822298199 234068072327783641233447299)
          ·
            refine ⟨351102108491675461850170949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234068072327783641233447299 351102108491675461850170949)
            ·
              refine ⟨65831645342189149096907053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 351102108491675461850170949 65831645342189149096907053)
              ·
                refine ⟨24686867003320930911340145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65831645342189149096907053 24686867003320930911340145)
                ·
                  refine ⟨18515150252490698183505109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24686867003320930911340145 18515150252490698183505109)
                  ·
                    refine ⟨433948834042750738675901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18515150252490698183505109 433948834042750738675901)
                    ·
                      rfl

theorem cell23_2535337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_2535337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535337 prefixEnd_2535337 := by exact prefixLift 2535337
  have htrace : WordTrace (prefixWord ++ tailWord_2535337) baseStart_2535337 baseEnd_2535337 := by
    simpa [prefixWord, tailWord_2535337, baseEnd_2535337] using wordTrace_append hprefix tailTrace_2535337
  have hstable : (prefixWord ++ tailWord_2535337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535337).length < 2 ^ (prefixWord ++ tailWord_2535337).sum := by decide
  have hdescent : baseEnd_2535337 < baseStart_2535337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535348 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2535348 : Nat := 118140960795 + 2535348 * 2 ^ 59
def prefixEnd_2535348 : Nat := 4983230072969 + 3 ^ 40 * 2535348 * 2
def baseEnd_2535348 : Nat := 1301852150415451672990153

theorem tailTrace_2535348 : CollatzResearch.WordTrace tailWord_2535348 prefixEnd_2535348 1301852150415451672990153 := by
  unfold tailWord_2535348
  simp only [CollatzResearch.WordTrace]
  refine ⟨46235869209437336905191349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61647825612583115873588465 46235869209437336905191349)
  ·
    refine ⟨4334612738384750334861689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46235869209437336905191349 4334612738384750334861689)
    ·
      refine ⟨3250959553788562751146267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4334612738384750334861689 3250959553788562751146267)
      ·
        refine ⟨4876439330682844126719401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250959553788562751146267 4876439330682844126719401)
        ·
          refine ⟨3657329498012133095039551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4876439330682844126719401 3657329498012133095039551)
          ·
            refine ⟨5485994247018199642559327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657329498012133095039551 5485994247018199642559327)
            ·
              refine ⟨8228991370527299463838991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5485994247018199642559327 8228991370527299463838991)
              ·
                refine ⟨12343487055790949195758487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8228991370527299463838991 12343487055790949195758487)
                ·
                  refine ⟨18515230583686423793637731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12343487055790949195758487 18515230583686423793637731)
                  ·
                    refine ⟨27772845875529635690456597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18515230583686423793637731 27772845875529635690456597)
                    ·
                      refine ⟨1301852150415451672990153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27772845875529635690456597 1301852150415451672990153)
                      ·
                        rfl

theorem cell23_2535348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2535348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535348 prefixEnd_2535348 := by exact prefixLift 2535348
  have htrace : WordTrace (prefixWord ++ tailWord_2535348) baseStart_2535348 baseEnd_2535348 := by
    simpa [prefixWord, tailWord_2535348, baseEnd_2535348] using wordTrace_append hprefix tailTrace_2535348
  have hstable : (prefixWord ++ tailWord_2535348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535348).length < 2 ^ (prefixWord ++ tailWord_2535348).sum := by decide
  have hdescent : baseEnd_2535348 < baseStart_2535348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535387 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 12]
def baseStart_2535387 : Nat := 118140960795 + 2535387 * 2 ^ 59
def prefixEnd_2535387 : Nat := 4983230072969 + 3 ^ 40 * 2535387 * 2
def baseEnd_2535387 : Nat := 1301872176160977020402473

theorem tailTrace_2535387 : CollatzResearch.WordTrace tailWord_2535387 prefixEnd_2535387 1301872176160977020402473 := by
  unfold tailWord_2535387
  simp only [CollatzResearch.WordTrace]
  refine ⟨92473160865733383471052415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61648773910488922314034943 92473160865733383471052415)
  ·
    refine ⟨138709741298600075206578623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92473160865733383471052415 138709741298600075206578623)
    ·
      refine ⟨208064611947900112809867935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138709741298600075206578623 208064611947900112809867935)
      ·
        refine ⟨312096917921850169214801903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208064611947900112809867935 312096917921850169214801903)
        ·
          refine ⟨468145376882775253822202855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312096917921850169214801903 468145376882775253822202855)
          ·
            refine ⟨702218065324162880733304283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468145376882775253822202855 702218065324162880733304283)
            ·
              refine ⟨1053327097986244321099956425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702218065324162880733304283 1053327097986244321099956425)
              ·
                refine ⟨789995323489683240824967319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053327097986244321099956425 789995323489683240824967319)
                ·
                  refine ⟨1184992985234524861237450979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789995323489683240824967319 1184992985234524861237450979)
                  ·
                    refine ⟨1777489477851787291856176469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1184992985234524861237450979 1777489477851787291856176469)
                    ·
                      refine ⟨1301872176160977020402473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 1777489477851787291856176469 1301872176160977020402473)
                      ·
                        rfl

theorem cell23_2535387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_2535387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535387 prefixEnd_2535387 := by exact prefixLift 2535387
  have htrace : WordTrace (prefixWord ++ tailWord_2535387) baseStart_2535387 baseEnd_2535387 := by
    simpa [prefixWord, tailWord_2535387, baseEnd_2535387] using wordTrace_append hprefix tailTrace_2535387
  have hstable : (prefixWord ++ tailWord_2535387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535387).length < 2 ^ (prefixWord ++ tailWord_2535387).sum := by decide
  have hdescent : baseEnd_2535387 < baseStart_2535387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535404 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_2535404 : Nat := 118140960795 + 2535404 * 2 ^ 59
def prefixEnd_2535404 : Nat := 4983230072969 + 3 ^ 40 * 2535404 * 2
def baseEnd_2535404 : Nat := 1301880905332103453889895

theorem tailTrace_2535404 : CollatzResearch.WordTrace tailWord_2535404 prefixEnd_2535404 1301880905332103453889895 := by
  unfold tailWord_2535404
  simp only [CollatzResearch.WordTrace]
  refine ⟨46236890453335897687210633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61649187271114530249614177 46236890453335897687210633)
  ·
    refine ⟨34677667840001923265407975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46236890453335897687210633 34677667840001923265407975)
    ·
      refine ⟨52016501760002884898111963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34677667840001923265407975 52016501760002884898111963)
      ·
        refine ⟨78024752640004327347167945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52016501760002884898111963 78024752640004327347167945)
        ·
          refine ⟨58518564480003245510375959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78024752640004327347167945 58518564480003245510375959)
          ·
            refine ⟨87777846720004868265563939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58518564480003245510375959 87777846720004868265563939)
            ·
              refine ⟨131666770080007302398345909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87777846720004868265563939 131666770080007302398345909)
              ·
                refine ⟨12343759695000684599844929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131666770080007302398345909 12343759695000684599844929)
                ·
                  refine ⟨9257819771250513449883697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12343759695000684599844929 9257819771250513449883697)
                  ·
                    refine ⟨6943364828437885087412773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9257819771250513449883697 6943364828437885087412773)
                    ·
                      refine ⟨1301880905332103453889895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6943364828437885087412773 1301880905332103453889895)
                      ·
                        rfl

theorem cell23_2535404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_2535404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535404 prefixEnd_2535404 := by exact prefixLift 2535404
  have htrace : WordTrace (prefixWord ++ tailWord_2535404) baseStart_2535404 baseEnd_2535404 := by
    simpa [prefixWord, tailWord_2535404, baseEnd_2535404] using wordTrace_append hprefix tailTrace_2535404
  have hstable : (prefixWord ++ tailWord_2535404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535404).length < 2 ^ (prefixWord ++ tailWord_2535404).sum := by decide
  have hdescent : baseEnd_2535404 < baseStart_2535404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535424 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 3]
def baseStart_2535424 : Nat := 118140960795 + 2535424 * 2 ^ 59
def prefixEnd_2535424 : Nat := 4983230072969 + 3 ^ 40 * 2535424 * 2
def baseEnd_2535424 : Nat := 1301891174945193375639803

theorem tailTrace_2535424 : CollatzResearch.WordTrace tailWord_2535424 prefixEnd_2535424 1301891174945193375639803 := by
  unfold tailWord_2535424
  simp only [CollatzResearch.WordTrace]
  refine ⟨46237255183299669395074663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61649673577732892526766217 46237255183299669395074663)
  ·
    refine ⟨69355882774949504092611995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46237255183299669395074663 69355882774949504092611995)
    ·
      refine ⟨104033824162424256138917993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69355882774949504092611995 104033824162424256138917993)
      ·
        refine ⟨78025368121818192104188495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104033824162424256138917993 78025368121818192104188495)
        ·
          refine ⟨117038052182727288156282743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78025368121818192104188495 117038052182727288156282743)
          ·
            refine ⟨175557078274090932234424115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117038052182727288156282743 175557078274090932234424115)
            ·
              refine ⟨263335617411136398351636173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175557078274090932234424115 263335617411136398351636173)
              ·
                refine ⟨98750856529176149381863565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263335617411136398351636173 98750856529176149381863565)
                ·
                  refine ⟨37031571198441056018198837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98750856529176149381863565 37031571198441056018198837)
                  ·
                    refine ⟨3471709799853849001706141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37031571198441056018198837 3471709799853849001706141)
                    ·
                      refine ⟨1301891174945193375639803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3471709799853849001706141 1301891174945193375639803)
                      ·
                        rfl

theorem cell23_2535424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_2535424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535424 prefixEnd_2535424 := by exact prefixLift 2535424
  have htrace : WordTrace (prefixWord ++ tailWord_2535424) baseStart_2535424 baseEnd_2535424 := by
    simpa [prefixWord, tailWord_2535424, baseEnd_2535424] using wordTrace_append hprefix tailTrace_2535424
  have hstable : (prefixWord ++ tailWord_2535424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535424).length < 2 ^ (prefixWord ++ tailWord_2535424).sum := by decide
  have hdescent : baseEnd_2535424 < baseStart_2535424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535542 : List Nat := [5, 1, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_2535542 : Nat := 118140960795 + 2535542 * 2 ^ 59
def prefixEnd_2535542 : Nat := 4983230072969 + 3 ^ 40 * 2535542 * 2
def baseEnd_2535542 : Nat := 433983921887474637988087

theorem tailTrace_2535542 : CollatzResearch.WordTrace tailWord_2535542 prefixEnd_2535542 433983921887474637988087 := by
  unfold tailWord_2535542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779925886260740308934055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61652542786781229961963253 5779925886260740308934055)
  ·
    refine ⟨8669888829391110463401083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5779925886260740308934055 8669888829391110463401083)
    ·
      refine ⟨13004833244086665695101625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8669888829391110463401083 13004833244086665695101625)
      ·
        refine ⟨9753624933064999271326219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13004833244086665695101625 9753624933064999271326219)
        ·
          refine ⟨14630437399597498906989329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9753624933064999271326219 14630437399597498906989329)
          ·
            refine ⟨10972828049698124180241997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14630437399597498906989329 10972828049698124180241997)
            ·
              refine ⟨4114810518636796567590749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10972828049698124180241997 4114810518636796567590749)
              ·
                refine ⟨1543053944488798712846531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4114810518636796567590749 1543053944488798712846531)
                ·
                  refine ⟨2314580916733198069269797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543053944488798712846531 2314580916733198069269797)
                  ·
                    refine ⟨433983921887474637988087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2314580916733198069269797 433983921887474637988087)
                    ·
                      rfl

theorem cell23_2535542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_2535542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535542 prefixEnd_2535542 := by exact prefixLift 2535542
  have htrace : WordTrace (prefixWord ++ tailWord_2535542) baseStart_2535542 baseEnd_2535542 := by
    simpa [prefixWord, tailWord_2535542, baseEnd_2535542] using wordTrace_append hprefix tailTrace_2535542
  have hstable : (prefixWord ++ tailWord_2535542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535542).length < 2 ^ (prefixWord ++ tailWord_2535542).sum := by decide
  have hdescent : baseEnd_2535542 < baseStart_2535542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535571 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 4]
def baseStart_2535571 : Nat := 118140960795 + 2535571 * 2 ^ 59
def prefixEnd_2535571 : Nat := 4983230072969 + 3 ^ 40 * 2535571 * 2
def baseEnd_2535571 : Nat := 1301966656601404300501627

theorem tailTrace_2535571 : CollatzResearch.WordTrace tailWord_2535571 prefixEnd_2535571 1301966656601404300501627 := by
  unfold tailWord_2535571
  simp only [CollatzResearch.WordTrace]
  refine ⟨92479871897066782895750567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61653247931377855263833711 92479871897066782895750567)
  ·
    refine ⟨138719807845600174343625851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92479871897066782895750567 138719807845600174343625851)
    ·
      refine ⟨208079711768400261515438777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138719807845600174343625851 208079711768400261515438777)
      ·
        refine ⟨156059783826300196136579083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208079711768400261515438777 156059783826300196136579083)
        ·
          refine ⟨234089675739450294204868625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156059783826300196136579083 234089675739450294204868625)
          ·
            refine ⟨175567256804587720653651469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234089675739450294204868625 175567256804587720653651469)
            ·
              refine ⟨65837721301720395245119301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175567256804587720653651469 65837721301720395245119301)
              ·
                refine ⟨12344572744072574108459869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65837721301720395245119301 12344572744072574108459869)
                ·
                  refine ⟨4629214779027215290672451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12344572744072574108459869 4629214779027215290672451)
                  ·
                    refine ⟨6943822168540822936008677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4629214779027215290672451 6943822168540822936008677)
                    ·
                      refine ⟨1301966656601404300501627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6943822168540822936008677 1301966656601404300501627)
                      ·
                        rfl

theorem cell23_2535571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_2535571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535571 prefixEnd_2535571 := by exact prefixLift 2535571
  have htrace : WordTrace (prefixWord ++ tailWord_2535571) baseStart_2535571 baseEnd_2535571 := by
    simpa [prefixWord, tailWord_2535571, baseEnd_2535571] using wordTrace_append hprefix tailTrace_2535571
  have hstable : (prefixWord ++ tailWord_2535571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535571).length < 2 ^ (prefixWord ++ tailWord_2535571).sum := by decide
  have hdescent : baseEnd_2535571 < baseStart_2535571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535585 : List Nat := [1, 2, 3, 3, 1, 4, 1, 2, 1, 5]
def baseStart_2535585 : Nat := 118140960795 + 2535585 * 2 ^ 59
def prefixEnd_2535585 : Nat := 4983230072969 + 3 ^ 40 * 2535585 * 2
def baseEnd_2535585 : Nat := 433991281776855748575521

theorem tailTrace_2535585 : CollatzResearch.WordTrace tailWord_2535585 prefixEnd_2535585 433991281776855748575521 := by
  unfold tailWord_2535585
  simp only [CollatzResearch.WordTrace]
  refine ⟨92480382519016063286760209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61653588346010708857840139 92480382519016063286760209)
  ·
    refine ⟨69360286889262047465070157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92480382519016063286760209 69360286889262047465070157)
    ·
      refine ⟨26010107583473267799401309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69360286889262047465070157 26010107583473267799401309)
      ·
        refine ⟨9753790343802475424775491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26010107583473267799401309 9753790343802475424775491)
        ·
          refine ⟨14630685515703713137163237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9753790343802475424775491 14630685515703713137163237)
          ·
            refine ⟨2743253534194446213218107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14630685515703713137163237 2743253534194446213218107)
            ·
              refine ⟨4114880301291669319827161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743253534194446213218107 4114880301291669319827161)
              ·
                refine ⟨3086160225968751989870371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4114880301291669319827161 3086160225968751989870371)
                ·
                  refine ⟨4629240338953127984805557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3086160225968751989870371 4629240338953127984805557)
                  ·
                    refine ⟨433991281776855748575521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4629240338953127984805557 433991281776855748575521)
                    ·
                      rfl

theorem cell23_2535585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_2535585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535585 prefixEnd_2535585 := by exact prefixLift 2535585
  have htrace : WordTrace (prefixWord ++ tailWord_2535585) baseStart_2535585 baseEnd_2535585 := by
    simpa [prefixWord, tailWord_2535585, baseEnd_2535585] using wordTrace_append hprefix tailTrace_2535585
  have hstable : (prefixWord ++ tailWord_2535585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535585).length < 2 ^ (prefixWord ++ tailWord_2535585).sum := by decide
  have hdescent : baseEnd_2535585 < baseStart_2535585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535645 : List Nat := [1, 4, 3, 2, 1, 2, 3, 7]
def baseStart_2535645 : Nat := 118140960795 + 2535645 * 2 ^ 59
def prefixEnd_2535645 : Nat := 4983230072969 + 3 ^ 40 * 2535645 * 2
def baseEnd_2535645 : Nat := 48222394598882852258381

theorem tailTrace_2535645 : CollatzResearch.WordTrace tailWord_2535645 prefixEnd_2535645 48222394598882852258381 := by
  unfold tailWord_2535645
  simp only [CollatzResearch.WordTrace]
  refine ⟨92482570898798693533944389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61655047265865795689296259 92482570898798693533944389)
  ·
    refine ⟨17340482043524755037614573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92482570898798693533944389 17340482043524755037614573)
    ·
      refine ⟨6502680766321783139105465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17340482043524755037614573 6502680766321783139105465)
      ·
        refine ⟨4877010574741337354329099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6502680766321783139105465 4877010574741337354329099)
        ·
          refine ⟨7315515862112006031493649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4877010574741337354329099 7315515862112006031493649)
          ·
            refine ⟨5486636896584004523620237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7315515862112006031493649 5486636896584004523620237)
            ·
              refine ⟨2057488836219001696357589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5486636896584004523620237 2057488836219001696357589)
              ·
                refine ⟨48222394598882852258381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2057488836219001696357589 48222394598882852258381)
                ·
                  rfl

theorem cell23_2535645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 7].length) (baseStart_2535645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535645 prefixEnd_2535645 := by exact prefixLift 2535645
  have htrace : WordTrace (prefixWord ++ tailWord_2535645) baseStart_2535645 baseEnd_2535645 := by
    simpa [prefixWord, tailWord_2535645, baseEnd_2535645] using wordTrace_append hprefix tailTrace_2535645
  have hstable : (prefixWord ++ tailWord_2535645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535645).length < 2 ^ (prefixWord ++ tailWord_2535645).sum := by decide
  have hdescent : baseEnd_2535645 < baseStart_2535645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535655 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2535655 : Nat := 118140960795 + 2535655 * 2 ^ 59
def prefixEnd_2535655 : Nat := 4983230072969 + 3 ^ 40 * 2535655 * 2
def baseEnd_2535655 : Nat := 1302009788976381971851241

theorem tailTrace_2535655 : CollatzResearch.WordTrace tailWord_2535655 prefixEnd_2535655 1302009788976381971851241 := by
  unfold tailWord_2535655
  simp only [CollatzResearch.WordTrace]
  refine ⟨92482935628762465241808419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61655290419174976827872279 92482935628762465241808419)
  ·
    refine ⟨138724403443143697862712629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92482935628762465241808419 138724403443143697862712629)
    ·
      refine ⟨13005412822794721674629309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138724403443143697862712629 13005412822794721674629309)
      ·
        refine ⟨4877029808548020627985991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13005412822794721674629309 4877029808548020627985991)
        ·
          refine ⟨7315544712822030941978987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4877029808548020627985991 7315544712822030941978987)
          ·
            refine ⟨10973317069233046412968481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7315544712822030941978987 10973317069233046412968481)
            ·
              refine ⟨8229987801924784809726361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10973317069233046412968481 8229987801924784809726361)
              ·
                refine ⟨6172490851443588607294771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8229987801924784809726361 6172490851443588607294771)
                ·
                  refine ⟨9258736277165382910942157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6172490851443588607294771 9258736277165382910942157)
                  ·
                    refine ⟨3472026103937018591603309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9258736277165382910942157 3472026103937018591603309)
                    ·
                      refine ⟨1302009788976381971851241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3472026103937018591603309 1302009788976381971851241)
                      ·
                        rfl

theorem cell23_2535655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2535655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535655 prefixEnd_2535655 := by exact prefixLift 2535655
  have htrace : WordTrace (prefixWord ++ tailWord_2535655) baseStart_2535655 baseEnd_2535655 := by
    simpa [prefixWord, tailWord_2535655, baseEnd_2535655] using wordTrace_append hprefix tailTrace_2535655
  have hstable : (prefixWord ++ tailWord_2535655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535655).length < 2 ^ (prefixWord ++ tailWord_2535655).sum := by decide
  have hdescent : baseEnd_2535655 < baseStart_2535655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535688 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 2, 6]
def baseStart_2535688 : Nat := 118140960795 + 2535688 * 2 ^ 59
def prefixEnd_2535688 : Nat := 4983230072969 + 3 ^ 40 * 2535688 * 2
def baseEnd_2535688 : Nat := 434008911279326780912863

theorem tailTrace_2535688 : CollatzResearch.WordTrace tailWord_2535688 prefixEnd_2535688 434008911279326780912863 := by
  unfold tailWord_2535688
  simp only [CollatzResearch.WordTrace]
  refine ⟨46242069618821455938879859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61656092825095274585173145 46242069618821455938879859)
  ·
    refine ⟨69363104428232183908319789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46242069618821455938879859 69363104428232183908319789)
    ·
      refine ⟨26011164160587068965619921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69363104428232183908319789 26011164160587068965619921)
      ·
        refine ⟨19508373120440301724214941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26011164160587068965619921 19508373120440301724214941)
        ·
          refine ⟨7315639920165113146580603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19508373120440301724214941 7315639920165113146580603)
          ·
            refine ⟨10973459880247669719870905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7315639920165113146580603 10973459880247669719870905)
            ·
              refine ⟨8230094910185752289903179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10973459880247669719870905 8230094910185752289903179)
              ·
                refine ⟨12345142365278628434854769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8230094910185752289903179 12345142365278628434854769)
                ·
                  refine ⟨9258856773958971326141077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12345142365278628434854769 9258856773958971326141077)
                  ·
                    refine ⟨434008911279326780912863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9258856773958971326141077 434008911279326780912863)
                    ·
                      rfl

theorem cell23_2535688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_2535688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535688 prefixEnd_2535688 := by exact prefixLift 2535688
  have htrace : WordTrace (prefixWord ++ tailWord_2535688) baseStart_2535688 baseEnd_2535688 := by
    simpa [prefixWord, tailWord_2535688, baseEnd_2535688] using wordTrace_append hprefix tailTrace_2535688
  have hstable : (prefixWord ++ tailWord_2535688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535688).length < 2 ^ (prefixWord ++ tailWord_2535688).sum := by decide
  have hdescent : baseEnd_2535688 < baseStart_2535688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535712 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 4, 2, 2]
def baseStart_2535712 : Nat := 118140960795 + 2535712 * 2 ^ 59
def prefixEnd_2535712 : Nat := 4983230072969 + 3 ^ 40 * 2535712 * 2
def baseEnd_2535712 : Nat := 1302039057373688248838479

theorem tailTrace_2535712 : CollatzResearch.WordTrace tailWord_2535712 prefixEnd_2535712 1302039057373688248838479 := by
  unfold tailWord_2535712
  simp only [CollatzResearch.WordTrace]
  refine ⟨46242507294777981988316695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61656676393037309317755593 46242507294777981988316695)
  ·
    refine ⟨69363760942166972982475043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46242507294777981988316695 69363760942166972982475043)
    ·
      refine ⟨104045641413250459473712565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69363760942166972982475043 104045641413250459473712565)
      ·
        refine ⟨9754278882492230575660553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104045641413250459473712565 9754278882492230575660553)
        ·
          refine ⟨7315709161869172931745415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9754278882492230575660553 7315709161869172931745415)
          ·
            refine ⟨10973563742803759397618123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7315709161869172931745415 10973563742803759397618123)
            ·
              refine ⟨16460345614205639096427185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10973563742803759397618123 16460345614205639096427185)
              ·
                refine ⟨12345259210654229322320389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16460345614205639096427185 12345259210654229322320389)
                ·
                  refine ⟨2314736101997667997935073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12345259210654229322320389 2314736101997667997935073)
                  ·
                    refine ⟨1736052076498250998451305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2314736101997667997935073 1736052076498250998451305)
                    ·
                      refine ⟨1302039057373688248838479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736052076498250998451305 1302039057373688248838479)
                      ·
                        rfl

theorem cell23_2535712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_2535712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535712 prefixEnd_2535712 := by exact prefixLift 2535712
  have htrace : WordTrace (prefixWord ++ tailWord_2535712) baseStart_2535712 baseEnd_2535712 := by
    simpa [prefixWord, tailWord_2535712, baseEnd_2535712] using wordTrace_append hprefix tailTrace_2535712
  have hstable : (prefixWord ++ tailWord_2535712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535712).length < 2 ^ (prefixWord ++ tailWord_2535712).sum := by decide
  have hdescent : baseEnd_2535712 < baseStart_2535712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535728 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 3]
def baseStart_2535728 : Nat := 118140960795 + 2535728 * 2 ^ 59
def prefixEnd_2535728 : Nat := 4983230072969 + 3 ^ 40 * 2535728 * 2
def baseEnd_2535728 : Nat := 1302047273064160186238405

theorem tailTrace_2535728 : CollatzResearch.WordTrace tailWord_2535728 prefixEnd_2535728 1302047273064160186238405 := by
  unfold tailWord_2535728
  simp only [CollatzResearch.WordTrace]
  refine ⟨46242799078748999354607919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61657065438331999139477225 46242799078748999354607919)
  ·
    refine ⟨69364198618123499031911879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46242799078748999354607919 69364198618123499031911879)
    ·
      refine ⟨104046297927185248547867819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69364198618123499031911879 104046297927185248547867819)
      ·
        refine ⟨156069446890777872821801729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104046297927185248547867819 156069446890777872821801729)
        ·
          refine ⟨117052085168083404616351297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156069446890777872821801729 117052085168083404616351297)
          ·
            refine ⟨87789063876062553462263473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117052085168083404616351297 87789063876062553462263473)
            ·
              refine ⟨65841797907046915096697605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87789063876062553462263473 65841797907046915096697605)
              ·
                refine ⟨12345337107571296580630801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65841797907046915096697605 12345337107571296580630801)
                ·
                  refine ⟨9259002830678472435473101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12345337107571296580630801 9259002830678472435473101)
                  ·
                    refine ⟨3472126061504427163302413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9259002830678472435473101 3472126061504427163302413)
                    ·
                      refine ⟨1302047273064160186238405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3472126061504427163302413 1302047273064160186238405)
                      ·
                        rfl

theorem cell23_2535728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_2535728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535728 prefixEnd_2535728 := by exact prefixLift 2535728
  have htrace : WordTrace (prefixWord ++ tailWord_2535728) baseStart_2535728 baseEnd_2535728 := by
    simpa [prefixWord, tailWord_2535728, baseEnd_2535728] using wordTrace_append hprefix tailTrace_2535728
  have hstable : (prefixWord ++ tailWord_2535728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535728).length < 2 ^ (prefixWord ++ tailWord_2535728).sum := by decide
  have hdescent : baseEnd_2535728 < baseStart_2535728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535785 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 2, 4, 2]
def baseStart_2535785 : Nat := 118140960795 + 2535785 * 2 ^ 59
def prefixEnd_2535785 : Nat := 4983230072969 + 3 ^ 40 * 2535785 * 2
def baseEnd_2535785 : Nat := 1302076541461466463225643

theorem tailTrace_2535785 : CollatzResearch.WordTrace tailWord_2535785 prefixEnd_2535785 1302076541461466463225643 := by
  unfold tailWord_2535785
  simp only [CollatzResearch.WordTrace]
  refine ⟨92487677118291497444040809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61658451412194331629360539 92487677118291497444040809)
  ·
    refine ⟨69365757838718623083030607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92487677118291497444040809 69365757838718623083030607)
    ·
      refine ⟨104048636758077934624545911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69365757838718623083030607 104048636758077934624545911)
      ·
        refine ⟨156072955137116901936818867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104048636758077934624545911 156072955137116901936818867)
        ·
          refine ⟨234109432705675352905228301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156072955137116901936818867 234109432705675352905228301)
          ·
            refine ⟨87791037264628257339460613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234109432705675352905228301 87791037264628257339460613)
            ·
              refine ⟨16460819487117798251148865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87791037264628257339460613 16460819487117798251148865)
              ·
                refine ⟨12345614615338348688361649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16460819487117798251148865 12345614615338348688361649)
                ·
                  refine ⟨9259210961503761516271237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12345614615338348688361649 9259210961503761516271237)
                  ·
                    refine ⟨1736102055281955284300857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9259210961503761516271237 1736102055281955284300857)
                    ·
                      refine ⟨1302076541461466463225643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736102055281955284300857 1302076541461466463225643)
                      ·
                        rfl

theorem cell23_2535785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 4, 2].length) (baseStart_2535785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535785 prefixEnd_2535785 := by exact prefixLift 2535785
  have htrace : WordTrace (prefixWord ++ tailWord_2535785) baseStart_2535785 baseEnd_2535785 := by
    simpa [prefixWord, tailWord_2535785, baseEnd_2535785] using wordTrace_append hprefix tailTrace_2535785
  have hstable : (prefixWord ++ tailWord_2535785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535785).length < 2 ^ (prefixWord ++ tailWord_2535785).sum := by decide
  have hdescent : baseEnd_2535785 < baseStart_2535785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535822 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2535822 : Nat := 118140960795 + 2535822 * 2 ^ 59
def prefixEnd_2535822 : Nat := 4983230072969 + 3 ^ 40 * 2535822 * 2
def baseEnd_2535822 : Nat := 1302095540245682818462973

theorem tailTrace_2535822 : CollatzResearch.WordTrace tailWord_2535822 prefixEnd_2535822 1302095540245682818462973 := by
  unfold tailWord_2535822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561128327394681595392215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61659351079438301842091813 11561128327394681595392215)
  ·
    refine ⟨17341692491092022393088323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11561128327394681595392215 17341692491092022393088323)
    ·
      refine ⟨26012538736638033589632485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17341692491092022393088323 26012538736638033589632485)
      ·
        refine ⟨4877351013119631298056091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26012538736638033589632485 4877351013119631298056091)
        ·
          refine ⟨7316026519679446947084137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4877351013119631298056091 7316026519679446947084137)
          ·
            refine ⟨5487019889759585210313103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7316026519679446947084137 5487019889759585210313103)
            ·
              refine ⟨8230529834639377815469655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5487019889759585210313103 8230529834639377815469655)
              ·
                refine ⟨12345794751959066723204483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8230529834639377815469655 12345794751959066723204483)
                ·
                  refine ⟨18518692127938600084806725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12345794751959066723204483 18518692127938600084806725)
                  ·
                    refine ⟨3472254773988487515901261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18518692127938600084806725 3472254773988487515901261)
                    ·
                      refine ⟨1302095540245682818462973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3472254773988487515901261 1302095540245682818462973)
                      ·
                        rfl

theorem cell23_2535822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2535822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535822 prefixEnd_2535822 := by exact prefixLift 2535822
  have htrace : WordTrace (prefixWord ++ tailWord_2535822) baseStart_2535822 baseEnd_2535822 := by
    simpa [prefixWord, tailWord_2535822, baseEnd_2535822] using wordTrace_append hprefix tailTrace_2535822
  have hstable : (prefixWord ++ tailWord_2535822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535822).length < 2 ^ (prefixWord ++ tailWord_2535822).sum := by decide
  have hdescent : baseEnd_2535822 < baseStart_2535822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535875 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 8, 2]
def baseStart_2535875 : Nat := 118140960795 + 2535875 * 2 ^ 59
def prefixEnd_2535875 : Nat := 4983230072969 + 3 ^ 40 * 2535875 * 2
def baseEnd_2535875 : Nat := 1302122754720371111100229

theorem tailTrace_2535875 : CollatzResearch.WordTrace tailWord_2535875 prefixEnd_2535875 1302122754720371111100229 := by
  unfold tailWord_2535875
  simp only [CollatzResearch.WordTrace]
  refine ⟨92490959687965442814817079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61660639791976961876544719 92490959687965442814817079)
  ·
    refine ⟨138736439531948164222225619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92490959687965442814817079 138736439531948164222225619)
    ·
      refine ⟨208104659297922246333338429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138736439531948164222225619 208104659297922246333338429)
      ·
        refine ⟨78039247236720842375001911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208104659297922246333338429 78039247236720842375001911)
        ·
          refine ⟨117058870855081263562502867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78039247236720842375001911 117058870855081263562502867)
          ·
            refine ⟨175588306282621895343754301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117058870855081263562502867 175588306282621895343754301)
            ·
              refine ⟨65845614855983210753907863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175588306282621895343754301 65845614855983210753907863)
              ·
                refine ⟨98768422283974816130861795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65845614855983210753907863 98768422283974816130861795)
                ·
                  refine ⟨148152633425962224196292693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98768422283974816130861795 148152633425962224196292693)
                  ·
                    refine ⟨1736163672960494814800305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 148152633425962224196292693 1736163672960494814800305)
                    ·
                      refine ⟨1302122754720371111100229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736163672960494814800305 1302122754720371111100229)
                      ·
                        rfl

theorem cell23_2535875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_2535875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535875 prefixEnd_2535875 := by exact prefixLift 2535875
  have htrace : WordTrace (prefixWord ++ tailWord_2535875) baseStart_2535875 baseEnd_2535875 := by
    simpa [prefixWord, tailWord_2535875, baseEnd_2535875] using wordTrace_append hprefix tailTrace_2535875
  have hstable : (prefixWord ++ tailWord_2535875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535875).length < 2 ^ (prefixWord ++ tailWord_2535875).sum := by decide
  have hdescent : baseEnd_2535875 < baseStart_2535875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535888 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_2535888 : Nat := 118140960795 + 2535888 * 2 ^ 59
def prefixEnd_2535888 : Nat := 4983230072969 + 3 ^ 40 * 2535888 * 2
def baseEnd_2535888 : Nat := 1302129429968879560237669

theorem tailTrace_2535888 : CollatzResearch.WordTrace tailWord_2535888 prefixEnd_2535888 1302129429968879560237669 := by
  unfold tailWord_2535888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46245716918459173017520159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61660955891278897356693545 46245716918459173017520159)
  ·
    refine ⟨69368575377688759526280239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46245716918459173017520159 69368575377688759526280239)
    ·
      refine ⟨104052863066533139289420359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69368575377688759526280239 104052863066533139289420359)
      ·
        refine ⟨156079294599799708934130539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104052863066533139289420359 156079294599799708934130539)
        ·
          refine ⟨234118941899699563401195809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156079294599799708934130539 234118941899699563401195809)
          ·
            refine ⟨175589206424774672550896857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234118941899699563401195809 175589206424774672550896857)
            ·
              refine ⟨131691904818581004413172643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175589206424774672550896857 131691904818581004413172643)
              ·
                refine ⟨197537857227871506619758965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131691904818581004413172643 197537857227871506619758965)
                ·
                  refine ⟨18519174115112953745602403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197537857227871506619758965 18519174115112953745602403)
                  ·
                    refine ⟨27778761172669430618403605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18519174115112953745602403 27778761172669430618403605)
                    ·
                      refine ⟨1302129429968879560237669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27778761172669430618403605 1302129429968879560237669)
                      ·
                        rfl

theorem cell23_2535888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_2535888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535888 prefixEnd_2535888 := by exact prefixLift 2535888
  have htrace : WordTrace (prefixWord ++ tailWord_2535888) baseStart_2535888 baseEnd_2535888 := by
    simpa [prefixWord, tailWord_2535888, baseEnd_2535888] using wordTrace_append hprefix tailTrace_2535888
  have hstable : (prefixWord ++ tailWord_2535888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535888).length < 2 ^ (prefixWord ++ tailWord_2535888).sum := by decide
  have hdescent : baseEnd_2535888 < baseStart_2535888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535895 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_2535895 : Nat := 118140960795 + 2535895 * 2 ^ 59
def prefixEnd_2535895 : Nat := 4983230072969 + 3 ^ 40 * 2535895 * 2
def baseEnd_2535895 : Nat := 1302133024333461032850137

theorem tailTrace_2535895 : CollatzResearch.WordTrace tailWord_2535895 prefixEnd_2535895 1302133024333461032850137 := by
  unfold tailWord_2535895
  simp only [CollatzResearch.WordTrace]
  refine ⟨92491689147892986230545139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61661126098595324153696759 92491689147892986230545139)
  ·
    refine ⟨138737533721839479345817709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92491689147892986230545139 138737533721839479345817709)
    ·
      refine ⟨52026575145689804754681641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138737533721839479345817709 52026575145689804754681641)
      ·
        refine ⟨39019931359267353566011231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52026575145689804754681641 39019931359267353566011231)
        ·
          refine ⟨58529897038901030349016847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39019931359267353566011231 58529897038901030349016847)
          ·
            refine ⟨87794845558351545523525271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58529897038901030349016847 87794845558351545523525271)
            ·
              refine ⟨131692268337527318285287907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87794845558351545523525271 131692268337527318285287907)
              ·
                refine ⟨197538402506290977427931861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131692268337527318285287907 197538402506290977427931861)
                ·
                  refine ⟨4629806308741194783467153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 197538402506290977427931861 4629806308741194783467153)
                  ·
                    refine ⟨3472354731555896087600365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4629806308741194783467153 3472354731555896087600365)
                    ·
                      refine ⟨1302133024333461032850137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3472354731555896087600365 1302133024333461032850137)
                      ·
                        rfl

theorem cell23_2535895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_2535895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535895 prefixEnd_2535895 := by exact prefixLift 2535895
  have htrace : WordTrace (prefixWord ++ tailWord_2535895) baseStart_2535895 baseEnd_2535895 := by
    simpa [prefixWord, tailWord_2535895, baseEnd_2535895] using wordTrace_append hprefix tailTrace_2535895
  have hstable : (prefixWord ++ tailWord_2535895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535895).length < 2 ^ (prefixWord ++ tailWord_2535895).sum := by decide
  have hdescent : baseEnd_2535895 < baseStart_2535895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535960 : List Nat := [2, 1, 2, 3, 3, 3, 2, 2, 1, 2, 2]
def baseStart_2535960 : Nat := 118140960795 + 2535960 * 2 ^ 59
def prefixEnd_2535960 : Nat := 4983230072969 + 3 ^ 40 * 2535960 * 2
def baseEnd_2535960 : Nat := 1302166400576003278537339

theorem tailTrace_2535960 : CollatzResearch.WordTrace tailWord_2535960 prefixEnd_2535960 1302166400576003278537339 := by
  unfold tailWord_2535960
  simp only [CollatzResearch.WordTrace]
  refine ⟨46247029946328751165830667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61662706595105001554440889 46247029946328751165830667)
  ·
    refine ⟨69370544919493126748746001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46247029946328751165830667 69370544919493126748746001)
    ·
      refine ⟨52027908689619845061559501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69370544919493126748746001 52027908689619845061559501)
      ·
        refine ⟨19510465758607441898084813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52027908689619845061559501 19510465758607441898084813)
        ·
          refine ⟨7316424659477790711781805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19510465758607441898084813 7316424659477790711781805)
          ·
            refine ⟨2743659247304171516918177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7316424659477790711781805 2743659247304171516918177)
            ·
              refine ⟨2057744435478128637688633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2743659247304171516918177 2057744435478128637688633)
              ·
                refine ⟨1543308326608596478266475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057744435478128637688633 1543308326608596478266475)
                ·
                  refine ⟨2314962489912894717399713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543308326608596478266475 2314962489912894717399713)
                  ·
                    refine ⟨1736221867434671038049785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2314962489912894717399713 1736221867434671038049785)
                    ·
                      refine ⟨1302166400576003278537339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736221867434671038049785 1302166400576003278537339)
                      ·
                        rfl

theorem cell23_2535960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_2535960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535960 prefixEnd_2535960 := by exact prefixLift 2535960
  have htrace : WordTrace (prefixWord ++ tailWord_2535960) baseStart_2535960 baseEnd_2535960 := by
    simpa [prefixWord, tailWord_2535960, baseEnd_2535960] using wordTrace_append hprefix tailTrace_2535960
  have hstable : (prefixWord ++ tailWord_2535960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535960).length < 2 ^ (prefixWord ++ tailWord_2535960).sum := by decide
  have hdescent : baseEnd_2535960 < baseStart_2535960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535976 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2535976 : Nat := 118140960795 + 2535976 * 2 ^ 59
def prefixEnd_2535976 : Nat := 4983230072969 + 3 ^ 40 * 2535976 * 2
def baseEnd_2535976 : Nat := 1302174616266475215937265

theorem tailTrace_2535976 : CollatzResearch.WordTrace tailWord_2535976 prefixEnd_2535976 1302174616266475215937265 := by
  unfold tailWord_2535976
  simp only [CollatzResearch.WordTrace]
  refine ⟨46247321730299768532121891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61663095640399691376162521 46247321730299768532121891)
  ·
    refine ⟨69370982595449652798182837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46247321730299768532121891 69370982595449652798182837)
    ·
      refine ⟨6503529618323404949829641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69370982595449652798182837 6503529618323404949829641)
      ·
        refine ⟨4877647213742553712372231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6503529618323404949829641 4877647213742553712372231)
        ·
          refine ⟨7316470820613830568558347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4877647213742553712372231 7316470820613830568558347)
          ·
            refine ⟨10974706230920745852837521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7316470820613830568558347 10974706230920745852837521)
            ·
              refine ⟨8231029673190559389628141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10974706230920745852837521 8231029673190559389628141)
              ·
                refine ⟨3086636127446459771110553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8231029673190559389628141 3086636127446459771110553)
                ·
                  refine ⟨2314977095584844828332915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3086636127446459771110553 2314977095584844828332915)
                  ·
                    refine ⟨3472465643377267242499373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2314977095584844828332915 3472465643377267242499373)
                    ·
                      refine ⟨1302174616266475215937265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3472465643377267242499373 1302174616266475215937265)
                      ·
                        rfl

theorem cell23_2535976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2535976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535976 prefixEnd_2535976 := by exact prefixLift 2535976
  have htrace : WordTrace (prefixWord ++ tailWord_2535976) baseStart_2535976 baseEnd_2535976 := by
    simpa [prefixWord, tailWord_2535976, baseEnd_2535976] using wordTrace_append hprefix tailTrace_2535976
  have hstable : (prefixWord ++ tailWord_2535976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535976).length < 2 ^ (prefixWord ++ tailWord_2535976).sum := by decide
  have hdescent : baseEnd_2535976 < baseStart_2535976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535985 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2535985 : Nat := 118140960795 + 2535985 * 2 ^ 59
def prefixEnd_2535985 : Nat := 4983230072969 + 3 ^ 40 * 2535985 * 2
def baseEnd_2535985 : Nat := 1302179237592365680724723

theorem tailTrace_2535985 : CollatzResearch.WordTrace tailWord_2535985 prefixEnd_2535985 1302179237592365680724723 := by
  unfold tailWord_2535985
  simp only [CollatzResearch.WordTrace]
  refine ⟨92494971717566931601321409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61663314478377954400880939 92494971717566931601321409)
  ·
    refine ⟨69371228788175198700991057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92494971717566931601321409 69371228788175198700991057)
    ·
      refine ⟨52028421591131399025743293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69371228788175198700991057 52028421591131399025743293)
      ·
        refine ⟨19510658096674274634653735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52028421591131399025743293 19510658096674274634653735)
        ·
          refine ⟨29265987145011411951980603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19510658096674274634653735 29265987145011411951980603)
          ·
            refine ⟨43898980717517117927970905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29265987145011411951980603 43898980717517117927970905)
            ·
              refine ⟨32924235538137838445978179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43898980717517117927970905 32924235538137838445978179)
              ·
                refine ⟨49386353307206757668967269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32924235538137838445978179 49386353307206757668967269)
                ·
                  refine ⟨9259941245101267062931363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49386353307206757668967269 9259941245101267062931363)
                  ·
                    refine ⟨13889911867651900594397045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9259941245101267062931363 13889911867651900594397045)
                    ·
                      refine ⟨1302179237592365680724723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13889911867651900594397045 1302179237592365680724723)
                      ·
                        rfl

theorem cell23_2535985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2535985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535985 prefixEnd_2535985 := by exact prefixLift 2535985
  have htrace : WordTrace (prefixWord ++ tailWord_2535985) baseStart_2535985 baseEnd_2535985 := by
    simpa [prefixWord, tailWord_2535985, baseEnd_2535985] using wordTrace_append hprefix tailTrace_2535985
  have hstable : (prefixWord ++ tailWord_2535985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535985).length < 2 ^ (prefixWord ++ tailWord_2535985).sum := by decide
  have hdescent : baseEnd_2535985 < baseStart_2535985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2535999 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 4, 2, 2]
def baseStart_2535999 : Nat := 118140960795 + 2535999 * 2 ^ 59
def prefixEnd_2535999 : Nat := 4983230072969 + 3 ^ 40 * 2535999 * 2
def baseEnd_2535999 : Nat := 1302186426321528625949659

theorem tailTrace_2535999 : CollatzResearch.WordTrace tailWord_2535999 prefixEnd_2535999 1302186426321528625949659 := by
  unfold tailWord_2535999
  simp only [CollatzResearch.WordTrace]
  refine ⟨92495482339516211992331051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61663654893010807994887367 92495482339516211992331051)
  ·
    refine ⟨138743223509274317988496577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92495482339516211992331051 138743223509274317988496577)
    ·
      refine ⟨104057417631955738491372433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138743223509274317988496577 104057417631955738491372433)
      ·
        refine ⟨78043063223966803868529325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104057417631955738491372433 78043063223966803868529325)
        ·
          refine ⟨29266148708987551450698497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78043063223966803868529325 29266148708987551450698497)
          ·
            refine ⟨21949611531740663588023873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29266148708987551450698497 21949611531740663588023873)
            ·
              refine ⟨16462208648805497691017905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21949611531740663588023873 16462208648805497691017905)
              ·
                refine ⟨12346656486604123268263429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16462208648805497691017905 12346656486604123268263429)
                ·
                  refine ⟨2314998091238273112799393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12346656486604123268263429 2314998091238273112799393)
                  ·
                    refine ⟨1736248568428704834599545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2314998091238273112799393 1736248568428704834599545)
                    ·
                      refine ⟨1302186426321528625949659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736248568428704834599545 1302186426321528625949659)
                      ·
                        rfl

theorem cell23_2535999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_2535999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2535999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2535999 prefixEnd_2535999 := by exact prefixLift 2535999
  have htrace : WordTrace (prefixWord ++ tailWord_2535999) baseStart_2535999 baseEnd_2535999 := by
    simpa [prefixWord, tailWord_2535999, baseEnd_2535999] using wordTrace_append hprefix tailTrace_2535999
  have hstable : (prefixWord ++ tailWord_2535999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2535999).length < 2 ^ (prefixWord ++ tailWord_2535999).sum := by decide
  have hdescent : baseEnd_2535999 < baseStart_2535999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2535999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536032 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 3]
def baseStart_2536032 : Nat := 118140960795 + 2536032 * 2 ^ 59
def prefixEnd_2536032 : Nat := 4983230072969 + 3 ^ 40 * 2536032 * 2
def baseEnd_2536032 : Nat := 1302203371183126996837007

theorem tailTrace_2536032 : CollatzResearch.WordTrace tailWord_2536032 prefixEnd_2536032 1302203371183126996837007 := by
  unfold tailWord_2536032
  simp only [CollatzResearch.WordTrace]
  refine ⟨46248342974198329314141175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61664457298931105752188233 46248342974198329314141175)
  ·
    refine ⟨69372514461297493971211763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46248342974198329314141175 69372514461297493971211763)
    ·
      refine ⟨104058771691946240956817645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69372514461297493971211763 104058771691946240956817645)
      ·
        refine ⟨39022039384479840358806617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104058771691946240956817645 39022039384479840358806617)
        ·
          refine ⟨29266529538359880269104963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39022039384479840358806617 29266529538359880269104963)
          ·
            refine ⟨43899794307539820403657445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29266529538359880269104963 43899794307539820403657445)
            ·
              refine ⟨8231211432663716325685771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43899794307539820403657445 8231211432663716325685771)
              ·
                refine ⟨12346817148995574488528657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8231211432663716325685771 12346817148995574488528657)
                ·
                  refine ⟨9260112861746680866396493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12346817148995574488528657 9260112861746680866396493)
                  ·
                    refine ⟨3472542323155005324898685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9260112861746680866396493 3472542323155005324898685)
                    ·
                      refine ⟨1302203371183126996837007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3472542323155005324898685 1302203371183126996837007)
                      ·
                        rfl

theorem cell23_2536032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_2536032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536032 prefixEnd_2536032 := by exact prefixLift 2536032
  have htrace : WordTrace (prefixWord ++ tailWord_2536032) baseStart_2536032 baseEnd_2536032 := by
    simpa [prefixWord, tailWord_2536032, baseEnd_2536032] using wordTrace_append hprefix tailTrace_2536032
  have hstable : (prefixWord ++ tailWord_2536032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536032).length < 2 ^ (prefixWord ++ tailWord_2536032).sum := by decide
  have hdescent : baseEnd_2536032 < baseStart_2536032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536033 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_2536033 : Nat := 118140960795 + 2536033 * 2 ^ 59
def prefixEnd_2536033 : Nat := 4983230072969 + 3 ^ 40 * 2536033 * 2
def baseEnd_2536033 : Nat := 1302203884663781492924503

theorem tailTrace_2536033 : CollatzResearch.WordTrace tailWord_2536033 prefixEnd_2536033 1302203884663781492924503 := by
  unfold tailWord_2536033
  simp only [CollatzResearch.WordTrace]
  refine ⟨92496722421393035799068753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61664481614262023866045835 92496722421393035799068753)
  ·
    refine ⟨69372541816044776849301565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92496722421393035799068753 69372541816044776849301565)
    ·
      refine ⟨26014703181016791318488087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69372541816044776849301565 26014703181016791318488087)
      ·
        refine ⟨39022054771525186977732131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26014703181016791318488087 39022054771525186977732131)
        ·
          refine ⟨58533082157287780466598197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39022054771525186977732131 58533082157287780466598197)
          ·
            refine ⟨5487476452245729418743581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58533082157287780466598197 5487476452245729418743581)
            ·
              refine ⟨2057803669592148532028843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5487476452245729418743581 2057803669592148532028843)
              ·
                refine ⟨3086705504388222798043265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057803669592148532028843 3086705504388222798043265)
                ·
                  refine ⟨2315029128291167098532449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3086705504388222798043265 2315029128291167098532449)
                  ·
                    refine ⟨1736271846218375323899337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2315029128291167098532449 1736271846218375323899337)
                    ·
                      refine ⟨1302203884663781492924503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736271846218375323899337 1302203884663781492924503)
                      ·
                        rfl

theorem cell23_2536033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_2536033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536033 prefixEnd_2536033 := by exact prefixLift 2536033
  have htrace : WordTrace (prefixWord ++ tailWord_2536033) baseStart_2536033 baseEnd_2536033 := by
    simpa [prefixWord, tailWord_2536033, baseEnd_2536033] using wordTrace_append hprefix tailTrace_2536033
  have hstable : (prefixWord ++ tailWord_2536033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536033).length < 2 ^ (prefixWord ++ tailWord_2536033).sum := by decide
  have hdescent : baseEnd_2536033 < baseStart_2536033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536035 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 3, 7]
def baseStart_2536035 : Nat := 118140960795 + 2536035 * 2 ^ 59
def prefixEnd_2536035 : Nat := 4983230072969 + 3 ^ 40 * 2536035 * 2
def baseEnd_2536035 : Nat := 434068303875030161699831

theorem tailTrace_2536035 : CollatzResearch.WordTrace tailWord_2536035 prefixEnd_2536035 434068303875030161699831 := by
  unfold tailWord_2536035
  simp only [CollatzResearch.WordTrace]
  refine ⟨92496795367385790140641559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61664530244923860093761039 92496795367385790140641559)
  ·
    refine ⟨138745193051078685210962339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92496795367385790140641559 138745193051078685210962339)
    ·
      refine ⟨208117789576618027816443509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138745193051078685210962339 208117789576618027816443509)
      ·
        refine ⟨19511042772807940107791579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208117789576618027816443509 19511042772807940107791579)
        ·
          refine ⟨29266564159211910161687369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19511042772807940107791579 29266564159211910161687369)
          ·
            refine ⟨21949923119408932621265527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29266564159211910161687369 21949923119408932621265527)
            ·
              refine ⟨32924884679113398931898291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21949923119408932621265527 32924884679113398931898291)
              ·
                refine ⟨49387327018670098397847437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32924884679113398931898291 49387327018670098397847437)
                ·
                  refine ⟨18520247632001286899192789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49387327018670098397847437 18520247632001286899192789)
                  ·
                    refine ⟨434068303875030161699831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18520247632001286899192789 434068303875030161699831)
                    ·
                      rfl

theorem cell23_2536035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 7].length) (baseStart_2536035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536035 prefixEnd_2536035 := by exact prefixLift 2536035
  have htrace : WordTrace (prefixWord ++ tailWord_2536035) baseStart_2536035 baseEnd_2536035 := by
    simpa [prefixWord, tailWord_2536035, baseEnd_2536035] using wordTrace_append hprefix tailTrace_2536035
  have hstable : (prefixWord ++ tailWord_2536035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536035).length < 2 ^ (prefixWord ++ tailWord_2536035).sum := by decide
  have hdescent : baseEnd_2536035 < baseStart_2536035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536075 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 5]
def baseStart_2536075 : Nat := 118140960795 + 2536075 * 2 ^ 59
def prefixEnd_2536075 : Nat := 4983230072969 + 3 ^ 40 * 2536075 * 2
def baseEnd_2536075 : Nat := 1302225450851270328599309

theorem tailTrace_2536075 : CollatzResearch.WordTrace tailWord_2536075 prefixEnd_2536075 1302225450851270328599309 := by
  unfold tailWord_2536075
  simp only [CollatzResearch.WordTrace]
  refine ⟨92498254287240876972097679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61665502858160584648065119 92498254287240876972097679)
  ·
    refine ⟨138747381430861315458146519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92498254287240876972097679 138747381430861315458146519)
    ·
      refine ⟨208121072146291973187219779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138747381430861315458146519 208121072146291973187219779)
      ·
        refine ⟨312181608219437959780829669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208121072146291973187219779 312181608219437959780829669)
        ·
          refine ⟨58534051541144617458905563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 312181608219437959780829669 58534051541144617458905563)
          ·
            refine ⟨87801077311716926188358345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58534051541144617458905563 87801077311716926188358345)
            ·
              refine ⟨65850807983787694641268759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87801077311716926188358345 65850807983787694641268759)
              ·
                refine ⟨98776211975681541961903139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65850807983787694641268759 98776211975681541961903139)
                ·
                  refine ⟨148164317963522312942854709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98776211975681541961903139 148164317963522312942854709)
                  ·
                    refine ⟨13890404809080216838392629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 148164317963522312942854709 13890404809080216838392629)
                    ·
                      refine ⟨1302225450851270328599309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13890404809080216838392629 1302225450851270328599309)
                      ·
                        rfl

theorem cell23_2536075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_2536075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536075 prefixEnd_2536075 := by exact prefixLift 2536075
  have htrace : WordTrace (prefixWord ++ tailWord_2536075) baseStart_2536075 baseEnd_2536075 := by
    simpa [prefixWord, tailWord_2536075, baseEnd_2536075] using wordTrace_append hprefix tailTrace_2536075
  have hstable : (prefixWord ++ tailWord_2536075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536075).length < 2 ^ (prefixWord ++ tailWord_2536075).sum := by decide
  have hdescent : baseEnd_2536075 < baseStart_2536075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536180 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2536180 : Nat := 118140960795 + 2536180 * 2 ^ 59
def prefixEnd_2536180 : Nat := 4983230072969 + 3 ^ 40 * 2536180 * 2
def baseEnd_2536180 : Nat := 144697707368888046420703

theorem tailTrace_2536180 : CollatzResearch.WordTrace tailWord_2536180 prefixEnd_2536180 144697707368888046420703 := by
  unfold tailWord_2536180
  simp only [CollatzResearch.WordTrace]
  refine ⟨46251041975930239952334997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61668055967906986603113329 46251041975930239952334997)
  ·
    refine ⟨2168017592621729997765703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46251041975930239952334997 2168017592621729997765703)
    ·
      refine ⟨3252026388932594996648555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2168017592621729997765703 3252026388932594996648555)
      ·
        refine ⟨4878039583398892494972833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252026388932594996648555 4878039583398892494972833)
        ·
          refine ⟨3658529687549169371229625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4878039583398892494972833 3658529687549169371229625)
          ·
            refine ⟨2743897265661877028422219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3658529687549169371229625 2743897265661877028422219)
            ·
              refine ⟨4115845898492815542633329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2743897265661877028422219 4115845898492815542633329)
              ·
                refine ⟨3086884423869611656974997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4115845898492815542633329 3086884423869611656974997)
                ·
                  refine ⟨144697707368888046420703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3086884423869611656974997 144697707368888046420703)
                  ·
                    rfl

theorem cell23_2536180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2536180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536180 prefixEnd_2536180 := by exact prefixLift 2536180
  have htrace : WordTrace (prefixWord ++ tailWord_2536180) baseStart_2536180 baseEnd_2536180 := by
    simpa [prefixWord, tailWord_2536180, baseEnd_2536180] using wordTrace_append hprefix tailTrace_2536180
  have hstable : (prefixWord ++ tailWord_2536180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536180).length < 2 ^ (prefixWord ++ tailWord_2536180).sum := by decide
  have hdescent : baseEnd_2536180 < baseStart_2536180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536189 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_2536189 : Nat := 118140960795 + 2536189 * 2 ^ 59
def prefixEnd_2536189 : Nat := 4983230072969 + 3 ^ 40 * 2536189 * 2
def baseEnd_2536189 : Nat := 434094662548627627524595

theorem tailTrace_2536189 : CollatzResearch.WordTrace tailWord_2536189 prefixEnd_2536189 434094662548627627524595 := by
  unfold tailWord_2536189
  simp only [CollatzResearch.WordTrace]
  refine ⟨92502412208827874441747621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61668274805885249627831747 92502412208827874441747621)
  ·
    refine ⟨17344202289155226457827679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92502412208827874441747621 17344202289155226457827679)
    ·
      refine ⟨26016303433732839686741519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17344202289155226457827679 26016303433732839686741519)
      ·
        refine ⟨39024455150599259530112279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26016303433732839686741519 39024455150599259530112279)
        ·
          refine ⟨58536682725898889295168419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39024455150599259530112279 58536682725898889295168419)
          ·
            refine ⟨87805024088848333942752629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58536682725898889295168419 87805024088848333942752629)
            ·
              refine ⟨8231721008329531307133059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87805024088848333942752629 8231721008329531307133059)
              ·
                refine ⟨12347581512494296960699589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8231721008329531307133059 12347581512494296960699589)
                ·
                  refine ⟨2315171533592680680131173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12347581512494296960699589 2315171533592680680131173)
                  ·
                    refine ⟨434094662548627627524595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2315171533592680680131173 434094662548627627524595)
                    ·
                      rfl

theorem cell23_2536189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_2536189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536189 prefixEnd_2536189 := by exact prefixLift 2536189
  have htrace : WordTrace (prefixWord ++ tailWord_2536189) baseStart_2536189 baseEnd_2536189 := by
    simpa [prefixWord, tailWord_2536189, baseEnd_2536189] using wordTrace_append hprefix tailTrace_2536189
  have hstable : (prefixWord ++ tailWord_2536189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536189).length < 2 ^ (prefixWord ++ tailWord_2536189).sum := by decide
  have hdescent : baseEnd_2536189 < baseStart_2536189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536190 : List Nat := [4, 2, 2, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_2536190 : Nat := 118140960795 + 2536190 * 2 ^ 59
def prefixEnd_2536190 : Nat := 4983230072969 + 3 ^ 40 * 2536190 * 2
def baseEnd_2536190 : Nat := 1302284501126537378661281

theorem tailTrace_2536190 : CollatzResearch.WordTrace tailWord_2536190 prefixEnd_2536190 1302284501126537378661281 := by
  unfold tailWord_2536190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562806085228031451566753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61668299121216167741689349 11562806085228031451566753)
  ·
    refine ⟨8672104563921023588675065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11562806085228031451566753 8672104563921023588675065)
    ·
      refine ⟨6504078422940767691506299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8672104563921023588675065 6504078422940767691506299)
      ·
        refine ⟨9756117634411151537259449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504078422940767691506299 9756117634411151537259449)
        ·
          refine ⟨7317088225808363652944587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9756117634411151537259449 7317088225808363652944587)
          ·
            refine ⟨10975632338712545479416881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317088225808363652944587 10975632338712545479416881)
            ·
              refine ⟨8231724254034409109562661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10975632338712545479416881 8231724254034409109562661)
              ·
                refine ⟨1543448297631451708042999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8231724254034409109562661 1543448297631451708042999)
                ·
                  refine ⟨2315172446447177562064499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543448297631451708042999 2315172446447177562064499)
                  ·
                    refine ⟨3472758669670766343096749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2315172446447177562064499 3472758669670766343096749)
                    ·
                      refine ⟨1302284501126537378661281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3472758669670766343096749 1302284501126537378661281)
                      ·
                        rfl

theorem cell23_2536190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_2536190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536190 prefixEnd_2536190 := by exact prefixLift 2536190
  have htrace : WordTrace (prefixWord ++ tailWord_2536190) baseStart_2536190 baseEnd_2536190 := by
    simpa [prefixWord, tailWord_2536190, baseEnd_2536190] using wordTrace_append hprefix tailTrace_2536190
  have hstable : (prefixWord ++ tailWord_2536190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536190).length < 2 ^ (prefixWord ++ tailWord_2536190).sum := by decide
  have hdescent : baseEnd_2536190 < baseStart_2536190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536199 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2536199 : Nat := 118140960795 + 2536199 * 2 ^ 59
def prefixEnd_2536199 : Nat := 4983230072969 + 3 ^ 40 * 2536199 * 2
def baseEnd_2536199 : Nat := 1302289122452427843448739

theorem tailTrace_2536199 : CollatzResearch.WordTrace tailWord_2536199 prefixEnd_2536199 1302289122452427843448739 := by
  unfold tailWord_2536199
  simp only [CollatzResearch.WordTrace]
  refine ⟨92502776938791646149611651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61668517959194430766407767 92502776938791646149611651)
  ·
    refine ⟨138754165408187469224417477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92502776938791646149611651 138754165408187469224417477)
    ·
      refine ⟨26016406014035150479578277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138754165408187469224417477 26016406014035150479578277)
      ·
        refine ⟨4878076127631590714920927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26016406014035150479578277 4878076127631590714920927)
        ·
          refine ⟨7317114191447386072381391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878076127631590714920927 7317114191447386072381391)
          ·
            refine ⟨10975671287171079108572087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317114191447386072381391 10975671287171079108572087)
            ·
              refine ⟨16463506930756618662858131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10975671287171079108572087 16463506930756618662858131)
              ·
                refine ⟨24695260396134927994287197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16463506930756618662858131 24695260396134927994287197)
                ·
                  refine ⟨9260722648550597997857699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24695260396134927994287197 9260722648550597997857699)
                  ·
                    refine ⟨13891083972825896996786549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9260722648550597997857699 13891083972825896996786549)
                    ·
                      refine ⟨1302289122452427843448739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13891083972825896996786549 1302289122452427843448739)
                      ·
                        rfl

theorem cell23_2536199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2536199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536199 prefixEnd_2536199 := by exact prefixLift 2536199
  have htrace : WordTrace (prefixWord ++ tailWord_2536199) baseStart_2536199 baseEnd_2536199 := by
    simpa [prefixWord, tailWord_2536199, baseEnd_2536199] using wordTrace_append hprefix tailTrace_2536199
  have hstable : (prefixWord ++ tailWord_2536199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536199).length < 2 ^ (prefixWord ++ tailWord_2536199).sum := by decide
  have hdescent : baseEnd_2536199 < baseStart_2536199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536202 : List Nat := [3, 1, 2, 2, 1, 2, 2, 10]
def baseStart_2536202 : Nat := 118140960795 + 2536202 * 2 ^ 59
def prefixEnd_2536202 : Nat := 4983230072969 + 3 ^ 40 * 2536202 * 2
def baseEnd_2536202 : Nat := 48232987514607086359675

theorem tailTrace_2536202 : CollatzResearch.WordTrace tailWord_2536202 prefixEnd_2536202 48232987514607086359675 := by
  unfold tailWord_2536202
  simp only [CollatzResearch.WordTrace]
  refine ⟨23125721589445194415492715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61668590905187185107980573 23125721589445194415492715)
  ·
    refine ⟨34688582384167791623239073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23125721589445194415492715 34688582384167791623239073)
    ·
      refine ⟨26016436788125843717429305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34688582384167791623239073 26016436788125843717429305)
      ·
        refine ⟨19512327591094382788071979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26016436788125843717429305 19512327591094382788071979)
        ·
          refine ⟨29268491386641574182107969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19512327591094382788071979 29268491386641574182107969)
          ·
            refine ⟨21951368539981180636580977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29268491386641574182107969 21951368539981180636580977)
            ·
              refine ⟨16463526404985885477435733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21951368539981180636580977 16463526404985885477435733)
              ·
                refine ⟨48232987514607086359675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16463526404985885477435733 48232987514607086359675)
                ·
                  rfl

theorem cell23_2536202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 10].length) (baseStart_2536202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536202 prefixEnd_2536202 := by exact prefixLift 2536202
  have htrace : WordTrace (prefixWord ++ tailWord_2536202) baseStart_2536202 baseEnd_2536202 := by
    simpa [prefixWord, tailWord_2536202, baseEnd_2536202] using wordTrace_append hprefix tailTrace_2536202
  have hstable : (prefixWord ++ tailWord_2536202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536202).length < 2 ^ (prefixWord ++ tailWord_2536202).sum := by decide
  have hdescent : baseEnd_2536202 < baseStart_2536202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536209 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_2536209 : Nat := 118140960795 + 2536209 * 2 ^ 59
def prefixEnd_2536209 : Nat := 4983230072969 + 3 ^ 40 * 2536209 * 2
def baseEnd_2536209 : Nat := 1302294257258972804323693

theorem tailTrace_2536209 : CollatzResearch.WordTrace tailWord_2536209 prefixEnd_2536209 1302294257258972804323693 := by
  unfold tailWord_2536209
  simp only [CollatzResearch.WordTrace]
  refine ⟨92503141668755417857475681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61668761112503611904983787 92503141668755417857475681)
  ·
    refine ⟨69377356251566563393106761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92503141668755417857475681 69377356251566563393106761)
    ·
      refine ⟨52033017188674922544830071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69377356251566563393106761 52033017188674922544830071)
      ·
        refine ⟨78049525783012383817245107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52033017188674922544830071 78049525783012383817245107)
        ·
          refine ⟨117074288674518575725867661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78049525783012383817245107 117074288674518575725867661)
          ·
            refine ⟨43902858252944465897200373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117074288674518575725867661 43902858252944465897200373)
            ·
              refine ⟨4115892961213543677862535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43902858252944465897200373 4115892961213543677862535)
              ·
                refine ⟨6173839441820315516793803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115892961213543677862535 6173839441820315516793803)
                ·
                  refine ⟨9260759162730473275190705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6173839441820315516793803 9260759162730473275190705)
                  ·
                    refine ⟨6945569372047854956393029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9260759162730473275190705 6945569372047854956393029)
                    ·
                      refine ⟨1302294257258972804323693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6945569372047854956393029 1302294257258972804323693)
                      ·
                        rfl

theorem cell23_2536209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_2536209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536209 prefixEnd_2536209 := by exact prefixLift 2536209
  have htrace : WordTrace (prefixWord ++ tailWord_2536209) baseStart_2536209 baseEnd_2536209 := by
    simpa [prefixWord, tailWord_2536209, baseEnd_2536209] using wordTrace_append hprefix tailTrace_2536209
  have hstable : (prefixWord ++ tailWord_2536209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536209).length < 2 ^ (prefixWord ++ tailWord_2536209).sum := by decide
  have hdescent : baseEnd_2536209 < baseStart_2536209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536229 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_2536229 : Nat := 118140960795 + 2536229 * 2 ^ 59
def prefixEnd_2536229 : Nat := 4983230072969 + 3 ^ 40 * 2536229 * 2
def baseEnd_2536229 : Nat := 1302304526872062726073601

theorem tailTrace_2536229 : CollatzResearch.WordTrace tailWord_2536229 prefixEnd_2536229 1302304526872062726073601 := by
  unfold tailWord_2536229
  simp only [CollatzResearch.WordTrace]
  refine ⟨92503871128682961273203741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61669247419121974182135827 92503871128682961273203741)
  ·
    refine ⟨34688951673256110477451403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92503871128682961273203741 34688951673256110477451403)
    ·
      refine ⟨52033427509884165716177105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34688951673256110477451403 52033427509884165716177105)
      ·
        refine ⟨39025070632413124287132829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52033427509884165716177105 39025070632413124287132829)
        ·
          refine ⟨14634401487154921607674811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39025070632413124287132829 14634401487154921607674811)
          ·
            refine ⟨21951602230732382411512217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14634401487154921607674811 21951602230732382411512217)
            ·
              refine ⟨16463701673049286808634163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21951602230732382411512217 16463701673049286808634163)
              ·
                refine ⟨24695552509573930212951245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16463701673049286808634163 24695552509573930212951245)
                ·
                  refine ⟨9260832191090223829856717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24695552509573930212951245 9260832191090223829856717)
                  ·
                    refine ⟨3472812071658833936196269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9260832191090223829856717 3472812071658833936196269)
                    ·
                      refine ⟨1302304526872062726073601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3472812071658833936196269 1302304526872062726073601)
                      ·
                        rfl

theorem cell23_2536229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_2536229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536229 prefixEnd_2536229 := by exact prefixLift 2536229
  have htrace : WordTrace (prefixWord ++ tailWord_2536229) baseStart_2536229 baseEnd_2536229 := by
    simpa [prefixWord, tailWord_2536229, baseEnd_2536229] using wordTrace_append hprefix tailTrace_2536229
  have hstable : (prefixWord ++ tailWord_2536229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536229).length < 2 ^ (prefixWord ++ tailWord_2536229).sum := by decide
  have hdescent : baseEnd_2536229 < baseStart_2536229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536257 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2536257 : Nat := 118140960795 + 2536257 * 2 ^ 59
def prefixEnd_2536257 : Nat := 4983230072969 + 3 ^ 40 * 2536257 * 2
def baseEnd_2536257 : Nat := 434106301443462872174491

theorem tailTrace_2536257 : CollatzResearch.WordTrace tailWord_2536257 prefixEnd_2536257 434106301443462872174491 := by
  unfold tailWord_2536257
  simp only [CollatzResearch.WordTrace]
  refine ⟨92504892372581522055223025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61669928248387681370148683 92504892372581522055223025)
  ·
    refine ⟨69378669279436141541417269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92504892372581522055223025 69378669279436141541417269)
    ·
      refine ⟨6504250244947138269507869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69378669279436141541417269 6504250244947138269507869)
      ·
        refine ⟨2439093841855176851065451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6504250244947138269507869 2439093841855176851065451)
        ·
          refine ⟨3658640762782765276598177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439093841855176851065451 3658640762782765276598177)
          ·
            refine ⟨2743980572087073957448633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3658640762782765276598177 2743980572087073957448633)
            ·
              refine ⟨2057985429065305468086475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2743980572087073957448633 2057985429065305468086475)
              ·
                refine ⟨3086978143597958202129713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2057985429065305468086475 3086978143597958202129713)
                ·
                  refine ⟨2315233607698468651597285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3086978143597958202129713 2315233607698468651597285)
                  ·
                    refine ⟨434106301443462872174491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2315233607698468651597285 434106301443462872174491)
                    ·
                      rfl

theorem cell23_2536257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2536257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536257 prefixEnd_2536257 := by exact prefixLift 2536257
  have htrace : WordTrace (prefixWord ++ tailWord_2536257) baseStart_2536257 baseEnd_2536257 := by
    simpa [prefixWord, tailWord_2536257, baseEnd_2536257] using wordTrace_append hprefix tailTrace_2536257
  have hstable : (prefixWord ++ tailWord_2536257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536257).length < 2 ^ (prefixWord ++ tailWord_2536257).sum := by decide
  have hdescent : baseEnd_2536257 < baseStart_2536257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536273 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 3, 3, 2]
def baseStart_2536273 : Nat := 118140960795 + 2536273 * 2 ^ 59
def prefixEnd_2536273 : Nat := 4983230072969 + 3 ^ 40 * 2536273 * 2
def baseEnd_2536273 : Nat := 1302327120020860553923399

theorem tailTrace_2536273 : CollatzResearch.WordTrace tailWord_2536273 prefixEnd_2536273 1302327120020860553923399 := by
  unfold tailWord_2536273
  simp only [CollatzResearch.WordTrace]
  refine ⟨92505475940523556787805473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61670317293682371191870315 92505475940523556787805473)
  ·
    refine ⟨69379106955392667590854105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92505475940523556787805473 69379106955392667590854105)
    ·
      refine ⟨52034330216544500693140579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69379106955392667590854105 52034330216544500693140579)
      ·
        refine ⟨78051495324816751039710869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52034330216544500693140579 78051495324816751039710869)
        ·
          refine ⟨3658663843350785204986447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78051495324816751039710869 3658663843350785204986447)
          ·
            refine ⟨5487995765026177807479671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658663843350785204986447 5487995765026177807479671)
            ·
              refine ⟨8231993647539266711219507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5487995765026177807479671 8231993647539266711219507)
              ·
                refine ⟨12347990471308900066829261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8231993647539266711219507 12347990471308900066829261)
                ·
                  refine ⟨4630496426740837525060973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12347990471308900066829261 4630496426740837525060973)
                  ·
                    refine ⟨1736436160027814071897865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4630496426740837525060973 1736436160027814071897865)
                    ·
                      refine ⟨1302327120020860553923399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736436160027814071897865 1302327120020860553923399)
                      ·
                        rfl

theorem cell23_2536273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_2536273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536273 prefixEnd_2536273 := by exact prefixLift 2536273
  have htrace : WordTrace (prefixWord ++ tailWord_2536273) baseStart_2536273 baseEnd_2536273 := by
    simpa [prefixWord, tailWord_2536273, baseEnd_2536273] using wordTrace_append hprefix tailTrace_2536273
  have hstable : (prefixWord ++ tailWord_2536273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536273).length < 2 ^ (prefixWord ++ tailWord_2536273).sum := by decide
  have hdescent : baseEnd_2536273 < baseStart_2536273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536319 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 3]
def baseStart_2536319 : Nat := 118140960795 + 2536319 * 2 ^ 59
def prefixEnd_2536319 : Nat := 4983230072969 + 3 ^ 40 * 2536319 * 2
def baseEnd_2536319 : Nat := 1302350740130967373948187

theorem tailTrace_2536319 : CollatzResearch.WordTrace tailWord_2536319 prefixEnd_2536319 1302350740130967373948187 := by
  unfold tailWord_2536319
  simp only [CollatzResearch.WordTrace]
  refine ⟨92507153698356906643980011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61671435798904604429320007 92507153698356906643980011)
  ·
    refine ⟨138760730547535359965970017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92507153698356906643980011 138760730547535359965970017)
    ·
      refine ⟨104070547910651519974477513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138760730547535359965970017 104070547910651519974477513)
      ·
        refine ⟨78052910932988639980858135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104070547910651519974477513 78052910932988639980858135)
        ·
          refine ⟨117079366399482959971287203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78052910932988639980858135 117079366399482959971287203)
          ·
            refine ⟨175619049599224439956930805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117079366399482959971287203 175619049599224439956930805)
            ·
              refine ⟨16464285899927291245962263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 175619049599224439956930805 16464285899927291245962263)
              ·
                refine ⟨24696428849890936868943395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16464285899927291245962263 24696428849890936868943395)
                ·
                  refine ⟨37044643274836405303415093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24696428849890936868943395 37044643274836405303415093)
                  ·
                    refine ⟨3472935307015912997195165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37044643274836405303415093 3472935307015912997195165)
                    ·
                      refine ⟨1302350740130967373948187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3472935307015912997195165 1302350740130967373948187)
                      ·
                        rfl

theorem cell23_2536319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_2536319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536319 prefixEnd_2536319 := by exact prefixLift 2536319
  have htrace : WordTrace (prefixWord ++ tailWord_2536319) baseStart_2536319 baseEnd_2536319 := by
    simpa [prefixWord, tailWord_2536319, baseEnd_2536319] using wordTrace_append hprefix tailTrace_2536319
  have hstable : (prefixWord ++ tailWord_2536319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536319).length < 2 ^ (prefixWord ++ tailWord_2536319).sum := by decide
  have hdescent : baseEnd_2536319 < baseStart_2536319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536339 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 2, 5]
def baseStart_2536339 : Nat := 118140960795 + 2536339 * 2 ^ 59
def prefixEnd_2536339 : Nat := 4983230072969 + 3 ^ 40 * 2536339 * 2
def baseEnd_2536339 : Nat := 434120336581352431899365

theorem tailTrace_2536339 : CollatzResearch.WordTrace tailWord_2536339 prefixEnd_2536339 434120336581352431899365 := by
  unfold tailWord_2536339
  simp only [CollatzResearch.WordTrace]
  refine ⟨92507883158284450059708071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61671922105522966706472047 92507883158284450059708071)
  ·
    refine ⟨138761824737426675089562107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92507883158284450059708071 138761824737426675089562107)
    ·
      refine ⟨208142737106140012634343161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138761824737426675089562107 208142737106140012634343161)
      ·
        refine ⟨156107052829605009475757371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208142737106140012634343161 156107052829605009475757371)
        ·
          refine ⟨234160579244407514213636057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156107052829605009475757371 234160579244407514213636057)
          ·
            refine ⟨175620434433305635660227043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234160579244407514213636057 175620434433305635660227043)
            ·
              refine ⟨263430651649958453490340565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175620434433305635660227043 263430651649958453490340565)
              ·
                refine ⟨6174155898045901253679857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 263430651649958453490340565 6174155898045901253679857)
                ·
                  refine ⟨4630616923534425940259893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6174155898045901253679857 4630616923534425940259893)
                  ·
                    refine ⟨434120336581352431899365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4630616923534425940259893 434120336581352431899365)
                    ·
                      rfl

theorem cell23_2536339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 5].length) (baseStart_2536339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536339 prefixEnd_2536339 := by exact prefixLift 2536339
  have htrace : WordTrace (prefixWord ++ tailWord_2536339) baseStart_2536339 baseEnd_2536339 := by
    simpa [prefixWord, tailWord_2536339, baseEnd_2536339] using wordTrace_append hprefix tailTrace_2536339
  have hstable : (prefixWord ++ tailWord_2536339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536339).length < 2 ^ (prefixWord ++ tailWord_2536339).sum := by decide
  have hdescent : baseEnd_2536339 < baseStart_2536339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536396 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2536396 : Nat := 118140960795 + 2536396 * 2 ^ 59
def prefixEnd_2536396 : Nat := 4983230072969 + 3 ^ 40 * 2536396 * 2
def baseEnd_2536396 : Nat := 1302390278141363572685333

theorem tailTrace_2536396 : CollatzResearch.WordTrace tailWord_2536396 prefixEnd_2536396 1302390278141363572685333 := by
  unfold tailWord_2536396
  simp only [CollatzResearch.WordTrace]
  refine ⟨46254981059538974397266521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61673308079385299196355361 46254981059538974397266521)
  ·
    refine ⟨34691235794654230797949891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46254981059538974397266521 34691235794654230797949891)
    ·
      refine ⟨52036853691981346196924837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34691235794654230797949891 52036853691981346196924837)
      ·
        refine ⟨9756910067246502411923407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52036853691981346196924837 9756910067246502411923407)
        ·
          refine ⟨14635365100869753617885111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9756910067246502411923407 14635365100869753617885111)
          ·
            refine ⟨21953047651304630426827667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14635365100869753617885111 21953047651304630426827667)
            ·
              refine ⟨32929571476956945640241501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21953047651304630426827667 32929571476956945640241501)
              ·
                refine ⟨12348589303858854615090563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32929571476956945640241501 12348589303858854615090563)
                ·
                  refine ⟨18522883955788281922635845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12348589303858854615090563 18522883955788281922635845)
                  ·
                    refine ⟨3473040741710302860494221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18522883955788281922635845 3473040741710302860494221)
                    ·
                      refine ⟨1302390278141363572685333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3473040741710302860494221 1302390278141363572685333)
                      ·
                        rfl

theorem cell23_2536396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2536396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536396 prefixEnd_2536396 := by exact prefixLift 2536396
  have htrace : WordTrace (prefixWord ++ tailWord_2536396) baseStart_2536396 baseEnd_2536396 := by
    simpa [prefixWord, tailWord_2536396, baseEnd_2536396] using wordTrace_append hprefix tailTrace_2536396
  have hstable : (prefixWord ++ tailWord_2536396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536396).length < 2 ^ (prefixWord ++ tailWord_2536396).sum := by decide
  have hdescent : baseEnd_2536396 < baseStart_2536396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536399 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 8]
def baseStart_2536399 : Nat := 118140960795 + 2536399 * 2 ^ 59
def prefixEnd_2536399 : Nat := 4983230072969 + 3 ^ 40 * 2536399 * 2
def baseEnd_2536399 : Nat := 144710202064814117883091

theorem tailTrace_2536399 : CollatzResearch.WordTrace tailWord_2536399 prefixEnd_2536399 144710202064814117883091 := by
  unfold tailWord_2536399
  simp only [CollatzResearch.WordTrace]
  refine ⟨92510071538067080306892251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61673381025378053537928167 92510071538067080306892251)
  ·
    refine ⟨138765107307100620460338377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92510071538067080306892251 138765107307100620460338377)
    ·
      refine ⟨104073830480325465345253783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138765107307100620460338377 104073830480325465345253783)
      ·
        refine ⟨156110745720488198017880675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104073830480325465345253783 156110745720488198017880675)
        ·
          refine ⟨234166118580732297026821013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156110745720488198017880675 234166118580732297026821013)
          ·
            refine ⟨10976536808471826423132235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 234166118580732297026821013 10976536808471826423132235)
            ·
              refine ⟨16464805212707739634698353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10976536808471826423132235 16464805212707739634698353)
              ·
                refine ⟨12348603909530804726023765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16464805212707739634698353 12348603909530804726023765)
                ·
                  refine ⟨144710202064814117883091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12348603909530804726023765 144710202064814117883091)
                  ·
                    rfl

theorem cell23_2536399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 8].length) (baseStart_2536399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536399 prefixEnd_2536399 := by exact prefixLift 2536399
  have htrace : WordTrace (prefixWord ++ tailWord_2536399) baseStart_2536399 baseEnd_2536399 := by
    simpa [prefixWord, tailWord_2536399, baseEnd_2536399] using wordTrace_append hprefix tailTrace_2536399
  have hstable : (prefixWord ++ tailWord_2536399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536399).length < 2 ^ (prefixWord ++ tailWord_2536399).sum := by decide
  have hdescent : baseEnd_2536399 < baseStart_2536399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536413 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2536413 : Nat := 118140960795 + 2536413 * 2 ^ 59
def prefixEnd_2536413 : Nat := 4983230072969 + 3 ^ 40 * 2536413 * 2
def baseEnd_2536413 : Nat := 1302399007312490006172755

theorem tailTrace_2536413 : CollatzResearch.WordTrace tailWord_2536413 prefixEnd_2536413 1302399007312490006172755 := by
  unfold tailWord_2536413
  simp only [CollatzResearch.WordTrace]
  refine ⟨92510582160016360697901893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61673721440010907131934595 92510582160016360697901893)
  ·
    refine ⟨17345734155003067630856605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92510582160016360697901893 17345734155003067630856605)
    ·
      refine ⟨6504650308126150361571227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17345734155003067630856605 6504650308126150361571227)
      ·
        refine ⟨9756975462189225542356841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6504650308126150361571227 9756975462189225542356841)
        ·
          refine ⟨7317731596641919156767631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9756975462189225542356841 7317731596641919156767631)
          ·
            refine ⟨10976597394962878735151447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317731596641919156767631 10976597394962878735151447)
            ·
              refine ⟨16464896092444318102727171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10976597394962878735151447 16464896092444318102727171)
              ·
                refine ⟨24697344138666477154090757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16464896092444318102727171 24697344138666477154090757)
                ·
                  refine ⟨4630752025999964466392017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24697344138666477154090757 4630752025999964466392017)
                  ·
                    refine ⟨3473064019499973349794013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4630752025999964466392017 3473064019499973349794013)
                    ·
                      refine ⟨1302399007312490006172755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3473064019499973349794013 1302399007312490006172755)
                      ·
                        rfl

theorem cell23_2536413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2536413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536413 prefixEnd_2536413 := by exact prefixLift 2536413
  have htrace : WordTrace (prefixWord ++ tailWord_2536413) baseStart_2536413 baseEnd_2536413 := by
    simpa [prefixWord, tailWord_2536413, baseEnd_2536413] using wordTrace_append hprefix tailTrace_2536413
  have hstable : (prefixWord ++ tailWord_2536413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536413).length < 2 ^ (prefixWord ++ tailWord_2536413).sum := by decide
  have hdescent : baseEnd_2536413 < baseStart_2536413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536433 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 6]
def baseStart_2536433 : Nat := 118140960795 + 2536433 * 2 ^ 59
def prefixEnd_2536433 : Nat := 4983230072969 + 3 ^ 40 * 2536433 * 2
def baseEnd_2536433 : Nat := 144712141880619991991407

theorem tailTrace_2536433 : CollatzResearch.WordTrace tailWord_2536433 prefixEnd_2536433 144712141880619991991407 := by
  unfold tailWord_2536433
  simp only [CollatzResearch.WordTrace]
  refine ⟨92511311619943904113629953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61674207746629269409086635 92511311619943904113629953)
  ·
    refine ⟨69383483714957928085222465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92511311619943904113629953 69383483714957928085222465)
    ·
      refine ⟨52037612786218446063916849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69383483714957928085222465 52037612786218446063916849)
      ·
        refine ⟨39028209589663834547937637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52037612786218446063916849 39028209589663834547937637)
        ·
          refine ⟨7317789298061968977738307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39028209589663834547937637 7317789298061968977738307)
          ·
            refine ⟨10976683947092953466607461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317789298061968977738307 10976683947092953466607461)
            ·
              refine ⟨2058128240079928774988899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10976683947092953466607461 2058128240079928774988899)
              ·
                refine ⟨3087192360119893162483349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058128240079928774988899 3087192360119893162483349)
                ·
                  refine ⟨144712141880619991991407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3087192360119893162483349 144712141880619991991407)
                  ·
                    rfl

theorem cell23_2536433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 6].length) (baseStart_2536433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536433 prefixEnd_2536433 := by exact prefixLift 2536433
  have htrace : WordTrace (prefixWord ++ tailWord_2536433) baseStart_2536433 baseEnd_2536433 := by
    simpa [prefixWord, tailWord_2536433, baseEnd_2536433] using wordTrace_append hprefix tailTrace_2536433
  have hstable : (prefixWord ++ tailWord_2536433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536433).length < 2 ^ (prefixWord ++ tailWord_2536433).sum := by decide
  have hdescent : baseEnd_2536433 < baseStart_2536433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536500 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2536500 : Nat := 118140960795 + 2536500 * 2 ^ 59
def prefixEnd_2536500 : Nat := 4983230072969 + 3 ^ 40 * 2536500 * 2
def baseEnd_2536500 : Nat := 1302443680129431165784855

theorem tailTrace_2536500 : CollatzResearch.WordTrace tailWord_2536500 prefixEnd_2536500 1302443680129431165784855 := by
  unfold tailWord_2536500
  simp only [CollatzResearch.WordTrace]
  refine ⟨46256877655350587278159477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61675836873800783037545969 46256877655350587278159477)
  ·
    refine ⟨4336582280189117557327451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46256877655350587278159477 4336582280189117557327451)
    ·
      refine ⟨6504873420283676335991177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4336582280189117557327451 6504873420283676335991177)
      ·
        refine ⟨4878655065212757251993383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6504873420283676335991177 4878655065212757251993383)
        ·
          refine ⟨7317982597819135877990075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878655065212757251993383 7317982597819135877990075)
          ·
            refine ⟨10976973896728703816985113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7317982597819135877990075 10976973896728703816985113)
            ·
              refine ⟨8232730422546527862738835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10976973896728703816985113 8232730422546527862738835)
              ·
                refine ⟨12349095633819791794108253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8232730422546527862738835 12349095633819791794108253)
                ·
                  refine ⟨4630910862682421922790595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12349095633819791794108253 4630910862682421922790595)
                  ·
                    refine ⟨6946366294023632884185893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4630910862682421922790595 6946366294023632884185893)
                    ·
                      refine ⟨1302443680129431165784855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6946366294023632884185893 1302443680129431165784855)
                      ·
                        rfl

theorem cell23_2536500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2536500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536500 prefixEnd_2536500 := by exact prefixLift 2536500
  have htrace : WordTrace (prefixWord ++ tailWord_2536500) baseStart_2536500 baseEnd_2536500 := by
    simpa [prefixWord, tailWord_2536500, baseEnd_2536500] using wordTrace_append hprefix tailTrace_2536500
  have hstable : (prefixWord ++ tailWord_2536500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536500).length < 2 ^ (prefixWord ++ tailWord_2536500).sum := by decide
  have hdescent : baseEnd_2536500 < baseStart_2536500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536503 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_2536503 : Nat := 118140960795 + 2536503 * 2 ^ 59
def prefixEnd_2536503 : Nat := 4983230072969 + 3 ^ 40 * 2536503 * 2
def baseEnd_2536503 : Nat := 1302445220571394654047341

theorem tailTrace_2536503 : CollatzResearch.WordTrace tailWord_2536503 prefixEnd_2536503 1302445220571394654047341 := by
  unfold tailWord_2536503
  simp only [CollatzResearch.WordTrace]
  refine ⟨92513864729690306068678163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61675909819793537379118775 92513864729690306068678163)
  ·
    refine ⟨138770797094535459103017245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92513864729690306068678163 138770797094535459103017245)
    ·
      refine ⟨52039048910450797163631467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138770797094535459103017245 52039048910450797163631467)
      ·
        refine ⟨78058573365676195745447201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52039048910450797163631467 78058573365676195745447201)
        ·
          refine ⟨58543930024257146809085401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78058573365676195745447201 58543930024257146809085401)
          ·
            refine ⟨43907947518192860106814051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58543930024257146809085401 43907947518192860106814051)
            ·
              refine ⟨65861921277289290160221077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43907947518192860106814051 65861921277289290160221077)
              ·
                refine ⟨3087277559872935476260363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65861921277289290160221077 3087277559872935476260363)
                ·
                  refine ⟨4630916339809403214390545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087277559872935476260363 4630916339809403214390545)
                  ·
                    refine ⟨3473187254857052410792909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4630916339809403214390545 3473187254857052410792909)
                    ·
                      refine ⟨1302445220571394654047341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3473187254857052410792909 1302445220571394654047341)
                      ·
                        rfl

theorem cell23_2536503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_2536503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536503 prefixEnd_2536503 := by exact prefixLift 2536503
  have htrace : WordTrace (prefixWord ++ tailWord_2536503) baseStart_2536503 baseEnd_2536503 := by
    simpa [prefixWord, tailWord_2536503, baseEnd_2536503] using wordTrace_append hprefix tailTrace_2536503
  have hstable : (prefixWord ++ tailWord_2536503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536503).length < 2 ^ (prefixWord ++ tailWord_2536503).sum := by decide
  have hdescent : baseEnd_2536503 < baseStart_2536503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536517 : List Nat := [1, 3, 1, 1, 1, 3, 3, 5, 1, 2, 2]
def baseStart_2536517 : Nat := 118140960795 + 2536517 * 2 ^ 59
def prefixEnd_2536517 : Nat := 4983230072969 + 3 ^ 40 * 2536517 * 2
def baseEnd_2536517 : Nat := 1302452409300557599272277

theorem tailTrace_2536517 : CollatzResearch.WordTrace tailWord_2536517 prefixEnd_2536517 1302452409300557599272277 := by
  unfold tailWord_2536517
  simp only [CollatzResearch.WordTrace]
  refine ⟨92514375351639586459687805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61676250234426390973125203 92514375351639586459687805)
  ·
    refine ⟨34692890756864844922382927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92514375351639586459687805 34692890756864844922382927)
    ·
      refine ⟨52039336135297267383574391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34692890756864844922382927 52039336135297267383574391)
      ·
        refine ⟨78059004202945901075361587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52039336135297267383574391 78059004202945901075361587)
        ·
          refine ⟨117088506304418851613042381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78059004202945901075361587 117088506304418851613042381)
          ·
            refine ⟨43908189864157069354890893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117088506304418851613042381 43908189864157069354890893)
            ·
              refine ⟨16465571199058901008084085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43908189864157069354890893 16465571199058901008084085)
              ·
                refine ⟨1543647299911771969507883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16465571199058901008084085 1543647299911771969507883)
                ·
                  refine ⟨2315470949867657954261825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543647299911771969507883 2315470949867657954261825)
                  ·
                    refine ⟨1736603212400743465696369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2315470949867657954261825 1736603212400743465696369)
                    ·
                      refine ⟨1302452409300557599272277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736603212400743465696369 1302452409300557599272277)
                      ·
                        rfl

theorem cell23_2536517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_2536517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536517 prefixEnd_2536517 := by exact prefixLift 2536517
  have htrace : WordTrace (prefixWord ++ tailWord_2536517) baseStart_2536517 baseEnd_2536517 := by
    simpa [prefixWord, tailWord_2536517, baseEnd_2536517] using wordTrace_append hprefix tailTrace_2536517
  have hstable : (prefixWord ++ tailWord_2536517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536517).length < 2 ^ (prefixWord ++ tailWord_2536517).sum := by decide
  have hdescent : baseEnd_2536517 < baseStart_2536517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
