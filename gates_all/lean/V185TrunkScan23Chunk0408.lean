import V185TrunkScan23Chunk0407

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2412503 : List Nat := [1, 1, 3, 2, 1, 1, 4, 5, 1, 2, 2]
def baseStart_2412503 : Nat := 118140960795 + 2412503 * 2 ^ 59
def prefixEnd_2412503 : Nat := 4983230072969 + 3 ^ 40 * 2412503 * 2
def baseEnd_2412503 : Nat := 1238773619413879804617607

theorem tailTrace_2412503 : CollatzResearch.WordTrace tailWord_2412503 prefixEnd_2412503 1238773619413879804617607 := by
  unfold tailWord_2412503
  simp only [CollatzResearch.WordTrace]
  refine ⟨87991213178921128554706163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58660808785947419036470775 87991213178921128554706163)
  ·
    refine ⟨131986819768381692832059245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87991213178921128554706163 131986819768381692832059245)
    ·
      refine ⟨49495057413143134812022217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131986819768381692832059245 49495057413143134812022217)
      ·
        refine ⟨37121293059857351109016663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49495057413143134812022217 37121293059857351109016663)
        ·
          refine ⟨55681939589786026663524995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37121293059857351109016663 55681939589786026663524995)
          ·
            refine ⟨83522909384679039995287493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55681939589786026663524995 83522909384679039995287493)
            ·
              refine ⟨15660545509627319999116405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83522909384679039995287493 15660545509627319999116405)
              ·
                refine ⟨1468176141527561249917163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15660545509627319999116405 1468176141527561249917163)
                ·
                  refine ⟨2202264212291341874875745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468176141527561249917163 2202264212291341874875745)
                  ·
                    refine ⟨1651698159218506406156809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2202264212291341874875745 1651698159218506406156809)
                    ·
                      refine ⟨1238773619413879804617607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651698159218506406156809 1238773619413879804617607)
                      ·
                        rfl

theorem cell23_2412503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_2412503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412503 prefixEnd_2412503 := by exact prefixLift 2412503
  have htrace : WordTrace (prefixWord ++ tailWord_2412503) baseStart_2412503 baseEnd_2412503 := by
    simpa [prefixWord, tailWord_2412503, baseEnd_2412503] using wordTrace_append hprefix tailTrace_2412503
  have hstable : (prefixWord ++ tailWord_2412503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412503).length < 2 ^ (prefixWord ++ tailWord_2412503).sum := by decide
  have hdescent : baseEnd_2412503 < baseStart_2412503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412506 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_2412506 : Nat := 118140960795 + 2412506 * 2 ^ 59
def prefixEnd_2412506 : Nat := 4983230072969 + 3 ^ 40 * 2412506 * 2
def baseEnd_2412506 : Nat := 1238775159855843292880093

theorem tailTrace_2412506 : CollatzResearch.WordTrace tailWord_2412506 prefixEnd_2412506 1238775159855843292880093 := by
  unfold tailWord_2412506
  simp only [CollatzResearch.WordTrace]
  refine ⟨21997830649477565016766343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58660881731940173378043581 21997830649477565016766343)
  ·
    refine ⟨32996745974216347525149515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21997830649477565016766343 32996745974216347525149515)
    ·
      refine ⟨49495118961324521287724273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32996745974216347525149515 49495118961324521287724273)
      ·
        refine ⟨37121339220993390965793205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49495118961324521287724273 37121339220993390965793205)
        ·
          refine ⟨3480125551968130403043113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37121339220993390965793205 3480125551968130403043113)
          ·
            refine ⟨2610094163976097802282335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480125551968130403043113 2610094163976097802282335)
            ·
              refine ⟨3915141245964146703423503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610094163976097802282335 3915141245964146703423503)
              ·
                refine ⟨5872711868946220055135255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915141245964146703423503 5872711868946220055135255)
                ·
                  refine ⟨8809067803419330082702883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5872711868946220055135255 8809067803419330082702883)
                  ·
                    refine ⟨13213601705128995124054325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8809067803419330082702883 13213601705128995124054325)
                    ·
                      refine ⟨1238775159855843292880093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13213601705128995124054325 1238775159855843292880093)
                      ·
                        rfl

theorem cell23_2412506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_2412506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412506 prefixEnd_2412506 := by exact prefixLift 2412506
  have htrace : WordTrace (prefixWord ++ tailWord_2412506) baseStart_2412506 baseEnd_2412506 := by
    simpa [prefixWord, tailWord_2412506, baseEnd_2412506] using wordTrace_append hprefix tailTrace_2412506
  have hstable : (prefixWord ++ tailWord_2412506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412506).length < 2 ^ (prefixWord ++ tailWord_2412506).sum := by decide
  have hdescent : baseEnd_2412506 < baseStart_2412506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412509 : List Nat := [1, 4, 3, 1, 4, 10]
def baseStart_2412509 : Nat := 118140960795 + 2412509 * 2 ^ 59
def prefixEnd_2412509 : Nat := 4983230072969 + 3 ^ 40 * 2412509 * 2
def baseEnd_2412509 : Nat := 5097846503283155477953

theorem tailTrace_2412509 : CollatzResearch.WordTrace tailWord_2412509 prefixEnd_2412509 5097846503283155477953 := by
  unfold tailWord_2412509
  simp only [CollatzResearch.WordTrace]
  refine ⟨87991432016899391579424581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58660954677932927719616387 87991432016899391579424581)
  ·
    refine ⟨16498393503168635921142109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87991432016899391579424581 16498393503168635921142109)
    ·
      refine ⟨6186897563688238470428291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16498393503168635921142109 6186897563688238470428291)
      ·
        refine ⟨9280346345532357705642437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6186897563688238470428291 9280346345532357705642437)
        ·
          refine ⟨1740064939787317069807957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9280346345532357705642437 1740064939787317069807957)
          ·
            refine ⟨5097846503283155477953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1740064939787317069807957 5097846503283155477953)
            ·
              rfl

theorem cell23_2412509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 10].length) (baseStart_2412509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412509 prefixEnd_2412509 := by exact prefixLift 2412509
  have htrace : WordTrace (prefixWord ++ tailWord_2412509) baseStart_2412509 baseEnd_2412509 := by
    simpa [prefixWord, tailWord_2412509, baseEnd_2412509] using wordTrace_append hprefix tailTrace_2412509
  have hstable : (prefixWord ++ tailWord_2412509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412509).length < 2 ^ (prefixWord ++ tailWord_2412509).sum := by decide
  have hdescent : baseEnd_2412509 < baseStart_2412509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412514 : List Nat := [3, 3, 3, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2412514 : Nat := 118140960795 + 2412514 * 2 ^ 59
def prefixEnd_2412514 : Nat := 4983230072969 + 3 ^ 40 * 2412514 * 2
def baseEnd_2412514 : Nat := 1238779267701079261580057

theorem tailTrace_2412514 : CollatzResearch.WordTrace tailWord_2412514 prefixEnd_2412514 1238779267701079261580057 := by
  unfold tailWord_2412514
  simp only [CollatzResearch.WordTrace]
  refine ⟨21997903595470319358339149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58661076254587518288904397 21997903595470319358339149)
  ·
    refine ⟨8249213848301369759377181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21997903595470319358339149 8249213848301369759377181)
    ·
      refine ⟨3093455193113013659766443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8249213848301369759377181 3093455193113013659766443)
      ·
        refine ⟨4640182789669520489649665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3093455193113013659766443 4640182789669520489649665)
        ·
          refine ⟨3480137092252140367237249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4640182789669520489649665 3480137092252140367237249)
          ·
            refine ⟨2610102819189105275427937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480137092252140367237249 2610102819189105275427937)
            ·
              refine ⟨1957577114391828956570953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2610102819189105275427937 1957577114391828956570953)
              ·
                refine ⟨1468182835793871717428215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957577114391828956570953 1468182835793871717428215)
                ·
                  refine ⟨2202274253690807576142323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468182835793871717428215 2202274253690807576142323)
                  ·
                    refine ⟨3303411380536211364213485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202274253690807576142323 3303411380536211364213485)
                    ·
                      refine ⟨1238779267701079261580057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303411380536211364213485 1238779267701079261580057)
                      ·
                        rfl

theorem cell23_2412514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2412514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412514 prefixEnd_2412514 := by exact prefixLift 2412514
  have htrace : WordTrace (prefixWord ++ tailWord_2412514) baseStart_2412514 baseEnd_2412514 := by
    simpa [prefixWord, tailWord_2412514, baseEnd_2412514] using wordTrace_append hprefix tailTrace_2412514
  have hstable : (prefixWord ++ tailWord_2412514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412514).length < 2 ^ (prefixWord ++ tailWord_2412514).sum := by decide
  have hdescent : baseEnd_2412514 < baseStart_2412514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412522 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_2412522 : Nat := 118140960795 + 2412522 * 2 ^ 59
def prefixEnd_2412522 : Nat := 4983230072969 + 3 ^ 40 * 2412522 * 2
def baseEnd_2412522 : Nat := 412927791848771743426673

theorem tailTrace_2412522 : CollatzResearch.WordTrace tailWord_2412522 prefixEnd_2412522 412927791848771743426673 := by
  unfold tailWord_2412522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21997976541463073699911955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58661270777234863199765213 21997976541463073699911955)
  ·
    refine ⟨32996964812194610549867933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21997976541463073699911955 32996964812194610549867933)
    ·
      refine ⟨12373861804572978956200475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32996964812194610549867933 12373861804572978956200475)
      ·
        refine ⟨18560792706859468434300713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12373861804572978956200475 18560792706859468434300713)
        ·
          refine ⟨13920594530144601325725535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18560792706859468434300713 13920594530144601325725535)
          ·
            refine ⟨20880891795216901988588303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13920594530144601325725535 20880891795216901988588303)
            ·
              refine ⟨31321337692825352982882455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20880891795216901988588303 31321337692825352982882455)
              ·
                refine ⟨46982006539238029474323683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31321337692825352982882455 46982006539238029474323683)
                ·
                  refine ⟨70473009808857044211485525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46982006539238029474323683 70473009808857044211485525)
                  ·
                    refine ⟨412927791848771743426673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 70473009808857044211485525 412927791848771743426673)
                    ·
                      rfl

theorem cell23_2412522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_2412522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412522 prefixEnd_2412522 := by exact prefixLift 2412522
  have htrace : WordTrace (prefixWord ++ tailWord_2412522) baseStart_2412522 baseEnd_2412522 := by
    simpa [prefixWord, tailWord_2412522, baseEnd_2412522] using wordTrace_append hprefix tailTrace_2412522
  have hstable : (prefixWord ++ tailWord_2412522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412522).length < 2 ^ (prefixWord ++ tailWord_2412522).sum := by decide
  have hdescent : baseEnd_2412522 < baseStart_2412522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412536 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_2412536 : Nat := 118140960795 + 2412536 * 2 ^ 59
def prefixEnd_2412536 : Nat := 4983230072969 + 3 ^ 40 * 2412536 * 2
def baseEnd_2412536 : Nat := 1238790564275478175504955

theorem tailTrace_2412536 : CollatzResearch.WordTrace tailWord_2412536 prefixEnd_2412536 1238790564275478175504955 := by
  unfold tailWord_2412536
  simp only [CollatzResearch.WordTrace]
  refine ⟨43996208393900787595328731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58661611191867716793771641 43996208393900787595328731)
  ·
    refine ⟨65994312590851181392993097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43996208393900787595328731 65994312590851181392993097)
    ·
      refine ⟨49495734443138386044744823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65994312590851181392993097 49495734443138386044744823)
      ·
        refine ⟨74243601664707579067117235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49495734443138386044744823 74243601664707579067117235)
        ·
          refine ⟨111365402497061368600675853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74243601664707579067117235 111365402497061368600675853)
          ·
            refine ⟨41762025936398013225253445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111365402497061368600675853 41762025936398013225253445)
            ·
              refine ⟨7830379863074627479735021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41762025936398013225253445 7830379863074627479735021)
              ·
                refine ⟨2936392448652985304900633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7830379863074627479735021 2936392448652985304900633)
                ·
                  refine ⟨2202294336489738978675475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936392448652985304900633 2202294336489738978675475)
                  ·
                    refine ⟨3303441504734608468013213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202294336489738978675475 3303441504734608468013213)
                    ·
                      refine ⟨1238790564275478175504955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303441504734608468013213 1238790564275478175504955)
                      ·
                        rfl

theorem cell23_2412536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_2412536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412536 prefixEnd_2412536 := by exact prefixLift 2412536
  have htrace : WordTrace (prefixWord ++ tailWord_2412536) baseStart_2412536 baseEnd_2412536 := by
    simpa [prefixWord, tailWord_2412536, baseEnd_2412536] using wordTrace_append hprefix tailTrace_2412536
  have hstable : (prefixWord ++ tailWord_2412536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412536).length < 2 ^ (prefixWord ++ tailWord_2412536).sum := by decide
  have hdescent : baseEnd_2412536 < baseStart_2412536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412552 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 1, 8]
def baseStart_2412552 : Nat := 118140960795 + 2412552 * 2 ^ 59
def prefixEnd_2412552 : Nat := 4983230072969 + 3 ^ 40 * 2412552 * 2
def baseEnd_2412552 : Nat := 412932926655316704301627

theorem tailTrace_2412552 : CollatzResearch.WordTrace tailWord_2412552 prefixEnd_2412552 412932926655316704301627 := by
  unfold tailWord_2412552
  simp only [CollatzResearch.WordTrace]
  refine ⟨43996500177871804961619955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58662000237162406615493273 43996500177871804961619955)
  ·
    refine ⟨65994750266807707442429933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43996500177871804961619955 65994750266807707442429933)
    ·
      refine ⟨24748031350052890290911225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65994750266807707442429933 24748031350052890290911225)
      ·
        refine ⟨18561023512539667718183419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24748031350052890290911225 18561023512539667718183419)
        ·
          refine ⟨27841535268809501577275129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18561023512539667718183419 27841535268809501577275129)
          ·
            refine ⟨20881151451607126182956347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27841535268809501577275129 20881151451607126182956347)
            ·
              refine ⟨31321727177410689274434521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20881151451607126182956347 31321727177410689274434521)
              ·
                refine ⟨23491295383058016955825891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31321727177410689274434521 23491295383058016955825891)
                ·
                  refine ⟨35236943074587025433738837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23491295383058016955825891 35236943074587025433738837)
                  ·
                    refine ⟨412932926655316704301627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35236943074587025433738837 412932926655316704301627)
                    ·
                      rfl

theorem cell23_2412552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_2412552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412552 prefixEnd_2412552 := by exact prefixLift 2412552
  have htrace : WordTrace (prefixWord ++ tailWord_2412552) baseStart_2412552 baseEnd_2412552 := by
    simpa [prefixWord, tailWord_2412552, baseEnd_2412552] using wordTrace_append hprefix tailTrace_2412552
  have hstable : (prefixWord ++ tailWord_2412552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412552).length < 2 ^ (prefixWord ++ tailWord_2412552).sum := by decide
  have hdescent : baseEnd_2412552 < baseStart_2412552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412557 : List Nat := [1, 7, 1, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2412557 : Nat := 118140960795 + 2412557 * 2 ^ 59
def prefixEnd_2412557 : Nat := 4983230072969 + 3 ^ 40 * 2412557 * 2
def baseEnd_2412557 : Nat := 1238801347369222593342359

theorem tailTrace_2412557 : CollatzResearch.WordTrace tailWord_2412557 prefixEnd_2412557 1238801347369222593342359 := by
  unfold tailWord_2412557
  simp only [CollatzResearch.WordTrace]
  refine ⟨87993182720725495777171925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58662121813816997184781283 87993182720725495777171925)
  ·
    refine ⟨2062340220017003807277467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 87993182720725495777171925 2062340220017003807277467)
    ·
      refine ⟨3093510330025505710916201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2062340220017003807277467 3093510330025505710916201)
      ·
        refine ⟨2320132747519129283187151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3093510330025505710916201 2320132747519129283187151)
        ·
          refine ⟨3480199121278693924780727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320132747519129283187151 3480199121278693924780727)
          ·
            refine ⟨5220298681918040887171091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480199121278693924780727 5220298681918040887171091)
            ·
              refine ⟨7830448022877061330756637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220298681918040887171091 7830448022877061330756637)
              ·
                refine ⟨2936418008578897999033739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7830448022877061330756637 2936418008578897999033739)
                ·
                  refine ⟨4404627012868346998550609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2936418008578897999033739 4404627012868346998550609)
                  ·
                    refine ⟨3303470259651260248912957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4404627012868346998550609 3303470259651260248912957)
                    ·
                      refine ⟨1238801347369222593342359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303470259651260248912957 1238801347369222593342359)
                      ·
                        rfl

theorem cell23_2412557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2412557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412557 prefixEnd_2412557 := by exact prefixLift 2412557
  have htrace : WordTrace (prefixWord ++ tailWord_2412557) baseStart_2412557 baseEnd_2412557 := by
    simpa [prefixWord, tailWord_2412557, baseEnd_2412557] using wordTrace_append hprefix tailTrace_2412557
  have hstable : (prefixWord ++ tailWord_2412557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412557).length < 2 ^ (prefixWord ++ tailWord_2412557).sum := by decide
  have hdescent : baseEnd_2412557 < baseStart_2412557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412563 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 1, 3, 2]
def baseStart_2412563 : Nat := 118140960795 + 2412563 * 2 ^ 59
def prefixEnd_2412563 : Nat := 4983230072969 + 3 ^ 40 * 2412563 * 2
def baseEnd_2412563 : Nat := 1238804428253149569867331

theorem tailTrace_2412563 : CollatzResearch.WordTrace tailWord_2412563 prefixEnd_2412563 1238804428253149569867331 := by
  unfold tailWord_2412563
  simp only [CollatzResearch.WordTrace]
  refine ⟨87993401558703758801890343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58662267705802505867926895 87993401558703758801890343)
  ·
    refine ⟨131990102338055638202835515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87993401558703758801890343 131990102338055638202835515)
    ·
      refine ⟨197985153507083457304253273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131990102338055638202835515 197985153507083457304253273)
      ·
        refine ⟨148488865130312592978189955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197985153507083457304253273 148488865130312592978189955)
        ·
          refine ⟨222733297695468889467284933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148488865130312592978189955 222733297695468889467284933)
          ·
            refine ⟨41762493317900416775115925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222733297695468889467284933 41762493317900416775115925)
            ·
              refine ⟨1957616874276582036333559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41762493317900416775115925 1957616874276582036333559)
              ·
                refine ⟨2936425311414873054500339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957616874276582036333559 2936425311414873054500339)
                ·
                  refine ⟨4404637967122309581750509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2936425311414873054500339 4404637967122309581750509)
                  ·
                    refine ⟨1651739237670866093156441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4404637967122309581750509 1651739237670866093156441)
                    ·
                      refine ⟨1238804428253149569867331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651739237670866093156441 1238804428253149569867331)
                      ·
                        rfl

theorem cell23_2412563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 3, 2].length) (baseStart_2412563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412563 prefixEnd_2412563 := by exact prefixLift 2412563
  have htrace : WordTrace (prefixWord ++ tailWord_2412563) baseStart_2412563 baseEnd_2412563 := by
    simpa [prefixWord, tailWord_2412563, baseEnd_2412563] using wordTrace_append hprefix tailTrace_2412563
  have hstable : (prefixWord ++ tailWord_2412563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412563).length < 2 ^ (prefixWord ++ tailWord_2412563).sum := by decide
  have hdescent : baseEnd_2412563 < baseStart_2412563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412593 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 1, 4, 2]
def baseStart_2412593 : Nat := 118140960795 + 2412593 * 2 ^ 59
def prefixEnd_2412593 : Nat := 4983230072969 + 3 ^ 40 * 2412593 * 2
def baseEnd_2412593 : Nat := 1238819832672784452492193

theorem tailTrace_2412593 : CollatzResearch.WordTrace tailWord_2412593 prefixEnd_2412593 1238819832672784452492193 := by
  unfold tailWord_2412593
  simp only [CollatzResearch.WordTrace]
  refine ⟨87994495748595073925482433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58662997165730049283654955 87994495748595073925482433)
  ·
    refine ⟨65995871811446305444111825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87994495748595073925482433 65995871811446305444111825)
    ·
      refine ⟨49496903858584729083083869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65995871811446305444111825 49496903858584729083083869)
      ·
        refine ⟨18561338946969273406156451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49496903858584729083083869 18561338946969273406156451)
        ·
          refine ⟨27842008420453910109234677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18561338946969273406156451 27842008420453910109234677)
          ·
            refine ⟨2610188289417554072740751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27842008420453910109234677 2610188289417554072740751)
            ·
              refine ⟨3915282434126331109111127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610188289417554072740751 3915282434126331109111127)
              ·
                refine ⟨5872923651189496663666691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915282434126331109111127 5872923651189496663666691)
                ·
                  refine ⟨8809385476784244995500037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5872923651189496663666691 8809385476784244995500037)
                  ·
                    refine ⟨1651759776897045936656257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8809385476784244995500037 1651759776897045936656257)
                    ·
                      refine ⟨1238819832672784452492193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651759776897045936656257 1238819832672784452492193)
                      ·
                        rfl

theorem cell23_2412593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_2412593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412593 prefixEnd_2412593 := by exact prefixLift 2412593
  have htrace : WordTrace (prefixWord ++ tailWord_2412593) baseStart_2412593 baseEnd_2412593 := by
    simpa [prefixWord, tailWord_2412593, baseEnd_2412593] using wordTrace_append hprefix tailTrace_2412593
  have hstable : (prefixWord ++ tailWord_2412593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412593).length < 2 ^ (prefixWord ++ tailWord_2412593).sum := by decide
  have hdescent : baseEnd_2412593 < baseStart_2412593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412629 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_2412629 : Nat := 118140960795 + 2412629 * 2 ^ 59
def prefixEnd_2412629 : Nat := 4983230072969 + 3 ^ 40 * 2412629 * 2
def baseEnd_2412629 : Nat := 412946105992115437214009

theorem tailTrace_2412629 : CollatzResearch.WordTrace tailWord_2412629 prefixEnd_2412629 412946105992115437214009 := by
  unfold tailWord_2412629
  simp only [CollatzResearch.WordTrace]
  refine ⟨87995808776464652073792941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58663872517643101382528627 87995808776464652073792941)
  ·
    refine ⟨32998428291174244527672353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87995808776464652073792941 32998428291174244527672353)
    ·
      refine ⟨24748821218380683395754265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32998428291174244527672353 24748821218380683395754265)
      ·
        refine ⟨18561615913785512546815699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24748821218380683395754265 18561615913785512546815699)
        ·
          refine ⟨27842423870678268820223549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18561615913785512546815699 27842423870678268820223549)
          ·
            refine ⟨10440908951504350807583831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27842423870678268820223549 10440908951504350807583831)
            ·
              refine ⟨15661363427256526211375747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10440908951504350807583831 15661363427256526211375747)
              ·
                refine ⟨23492045140884789317063621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15661363427256526211375747 23492045140884789317063621)
                ·
                  refine ⟨4404758463915897996949429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23492045140884789317063621 4404758463915897996949429)
                  ·
                    refine ⟨412946105992115437214009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4404758463915897996949429 412946105992115437214009)
                    ·
                      rfl

theorem cell23_2412629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_2412629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412629 prefixEnd_2412629 := by exact prefixLift 2412629
  have htrace : WordTrace (prefixWord ++ tailWord_2412629) baseStart_2412629 baseEnd_2412629 := by
    simpa [prefixWord, tailWord_2412629, baseEnd_2412629] using wordTrace_append hprefix tailTrace_2412629
  have hstable : (prefixWord ++ tailWord_2412629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412629).length < 2 ^ (prefixWord ++ tailWord_2412629).sum := by decide
  have hdescent : baseEnd_2412629 < baseStart_2412629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412649 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_2412649 : Nat := 118140960795 + 2412649 * 2 ^ 59
def prefixEnd_2412649 : Nat := 4983230072969 + 3 ^ 40 * 2412649 * 2
def baseEnd_2412649 : Nat := 1238848587589436233391935

theorem tailTrace_2412649 : CollatzResearch.WordTrace tailWord_2412649 prefixEnd_2412649 1238848587589436233391935 := by
  unfold tailWord_2412649
  simp only [CollatzResearch.WordTrace]
  refine ⟨87996538236392195489521001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58664358824261463659680667 87996538236392195489521001)
  ·
    refine ⟨65997403677294146617140751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87996538236392195489521001 65997403677294146617140751)
    ·
      refine ⟨98996105515941219925711127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65997403677294146617140751 98996105515941219925711127)
      ·
        refine ⟨148494158273911829888566691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98996105515941219925711127 148494158273911829888566691)
        ·
          refine ⟨222741237410867744832850037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148494158273911829888566691 222741237410867744832850037)
          ·
            refine ⟨20881991007268851078079691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222741237410867744832850037 20881991007268851078079691)
            ·
              refine ⟨31322986510903276617119537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20881991007268851078079691 31322986510903276617119537)
              ·
                refine ⟨23492239883177457462839653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31322986510903276617119537 23492239883177457462839653)
                ·
                  refine ⟨4404794978095773274282435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23492239883177457462839653 4404794978095773274282435)
                  ·
                    refine ⟨6607192467143659911423653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4404794978095773274282435 6607192467143659911423653)
                    ·
                      refine ⟨1238848587589436233391935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6607192467143659911423653 1238848587589436233391935)
                      ·
                        rfl

theorem cell23_2412649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_2412649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412649 prefixEnd_2412649 := by exact prefixLift 2412649
  have htrace : WordTrace (prefixWord ++ tailWord_2412649) baseStart_2412649 baseEnd_2412649 := by
    simpa [prefixWord, tailWord_2412649, baseEnd_2412649] using wordTrace_append hprefix tailTrace_2412649
  have hstable : (prefixWord ++ tailWord_2412649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412649).length < 2 ^ (prefixWord ++ tailWord_2412649).sum := by decide
  have hdescent : baseEnd_2412649 < baseStart_2412649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412693 : List Nat := [1, 3, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_2412693 : Nat := 118140960795 + 2412693 * 2 ^ 59
def prefixEnd_2412693 : Nat := 4983230072969 + 3 ^ 40 * 2412693 * 2
def baseEnd_2412693 : Nat := 412957060246078020413911

theorem tailTrace_2412693 : CollatzResearch.WordTrace tailWord_2412693 prefixEnd_2412693 412957060246078020413911 := by
  unfold tailWord_2412693
  simp only [CollatzResearch.WordTrace]
  refine ⟨87998143048232791004122733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58665428698821860669415155 87998143048232791004122733)
  ·
    refine ⟨32999303643087296626546025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87998143048232791004122733 32999303643087296626546025)
    ·
      refine ⟨24749477732315472469909519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32999303643087296626546025 24749477732315472469909519)
      ·
        refine ⟨37124216598473208704864279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24749477732315472469909519 37124216598473208704864279)
        ·
          refine ⟨55686324897709813057296419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37124216598473208704864279 55686324897709813057296419)
          ·
            refine ⟨83529487346564719585944629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55686324897709813057296419 83529487346564719585944629)
            ·
              refine ⟨7830889438740442461182309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83529487346564719585944629 7830889438740442461182309)
              ·
                refine ⟨1468291769763832961471683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7830889438740442461182309 1468291769763832961471683)
                ·
                  refine ⟨2202437654645749442207525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468291769763832961471683 2202437654645749442207525)
                  ·
                    refine ⟨412957060246078020413911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202437654645749442207525 412957060246078020413911)
                    ·
                      rfl

theorem cell23_2412693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_2412693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412693 prefixEnd_2412693 := by exact prefixLift 2412693
  have htrace : WordTrace (prefixWord ++ tailWord_2412693) baseStart_2412693 baseEnd_2412693 := by
    simpa [prefixWord, tailWord_2412693, baseEnd_2412693] using wordTrace_append hprefix tailTrace_2412693
  have hstable : (prefixWord ++ tailWord_2412693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412693).length < 2 ^ (prefixWord ++ tailWord_2412693).sum := by decide
  have hdescent : baseEnd_2412693 < baseStart_2412693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412694 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2412694 : Nat := 118140960795 + 2412694 * 2 ^ 59
def prefixEnd_2412694 : Nat := 4983230072969 + 3 ^ 40 * 2412694 * 2
def baseEnd_2412694 : Nat := 1238871694218888557329229

theorem tailTrace_2412694 : CollatzResearch.WordTrace tailWord_2412694 prefixEnd_2412694 1238871694218888557329229 := by
  unfold tailWord_2412694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5499886220076823010931821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58665453014152778783272757 5499886220076823010931821)
  ·
    refine ⟨2062457332528808629099433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5499886220076823010931821 2062457332528808629099433)
    ·
      refine ⟨1546842999396606471824575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2062457332528808629099433 1546842999396606471824575)
      ·
        refine ⟨2320264499094909707736863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546842999396606471824575 2320264499094909707736863)
        ·
          refine ⟨3480396748642364561605295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320264499094909707736863 3480396748642364561605295)
          ·
            refine ⟨5220595122963546842407943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480396748642364561605295 5220595122963546842407943)
            ·
              refine ⟨7830892684445320263611915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220595122963546842407943 7830892684445320263611915)
              ·
                refine ⟨11746339026667980395417873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7830892684445320263611915 11746339026667980395417873)
                ·
                  refine ⟨8809754270000985296563405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11746339026667980395417873 8809754270000985296563405)
                  ·
                    refine ⟨3303657851250369486211277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8809754270000985296563405 3303657851250369486211277)
                    ·
                      refine ⟨1238871694218888557329229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303657851250369486211277 1238871694218888557329229)
                      ·
                        rfl

theorem cell23_2412694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2412694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412694 prefixEnd_2412694 := by exact prefixLift 2412694
  have htrace : WordTrace (prefixWord ++ tailWord_2412694) baseStart_2412694 baseEnd_2412694 := by
    simpa [prefixWord, tailWord_2412694, baseEnd_2412694] using wordTrace_append hprefix tailTrace_2412694
  have hstable : (prefixWord ++ tailWord_2412694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412694).length < 2 ^ (prefixWord ++ tailWord_2412694).sum := by decide
  have hdescent : baseEnd_2412694 < baseStart_2412694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412750 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_2412750 : Nat := 118140960795 + 2412750 * 2 ^ 59
def prefixEnd_2412750 : Nat := 4983230072969 + 3 ^ 40 * 2412750 * 2
def baseEnd_2412750 : Nat := 1238900449135540338228971

theorem tailTrace_2412750 : CollatzResearch.WordTrace tailWord_2412750 prefixEnd_2412750 1238900449135540338228971 := by
  unfold tailWord_2412750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11000027751128286217368463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58666814672684193159298469 11000027751128286217368463)
  ·
    refine ⟨16500041626692429326052695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11000027751128286217368463 16500041626692429326052695)
    ·
      refine ⟨24750062440038643989079043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16500041626692429326052695 24750062440038643989079043)
      ·
        refine ⟨37125093660057965983618565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24750062440038643989079043 37125093660057965983618565)
        ·
          refine ⟨6960955061260868621928481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37125093660057965983618565 6960955061260868621928481)
          ·
            refine ⟨5220716295945651466446361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6960955061260868621928481 5220716295945651466446361)
            ·
              refine ⟨3915537221959238599834771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5220716295945651466446361 3915537221959238599834771)
              ·
                refine ⟨5873305832938857899752157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915537221959238599834771 5873305832938857899752157)
                ·
                  refine ⟨2202489687352071712407059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5873305832938857899752157 2202489687352071712407059)
                  ·
                    refine ⟨3303734531028107568610589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202489687352071712407059 3303734531028107568610589)
                    ·
                      refine ⟨1238900449135540338228971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303734531028107568610589 1238900449135540338228971)
                      ·
                        rfl

theorem cell23_2412750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_2412750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412750 prefixEnd_2412750 := by exact prefixLift 2412750
  have htrace : WordTrace (prefixWord ++ tailWord_2412750) baseStart_2412750 baseEnd_2412750 := by
    simpa [prefixWord, tailWord_2412750, baseEnd_2412750] using wordTrace_append hprefix tailTrace_2412750
  have hstable : (prefixWord ++ tailWord_2412750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412750).length < 2 ^ (prefixWord ++ tailWord_2412750).sum := by decide
  have hdescent : baseEnd_2412750 < baseStart_2412750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412773 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2412773 : Nat := 118140960795 + 2412773 * 2 ^ 59
def prefixEnd_2412773 : Nat := 4983230072969 + 3 ^ 40 * 2412773 * 2
def baseEnd_2412773 : Nat := 1238912259190593748241365

theorem tailTrace_2412773 : CollatzResearch.WordTrace tailWord_2412773 prefixEnd_2412773 1238912259190593748241365 := by
  unfold tailWord_2412773
  simp only [CollatzResearch.WordTrace]
  refine ⟨88001060887942964667034973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58667373925295309778023315 88001060887942964667034973)
  ·
    refine ⟨33000397832978611750138115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88001060887942964667034973 33000397832978611750138115)
    ·
      refine ⟨49500596749467917625207173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33000397832978611750138115 49500596749467917625207173)
      ·
        refine ⟨9281361890525234554726345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49500596749467917625207173 9281361890525234554726345)
        ·
          refine ⟨6961021417893925916044759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9281361890525234554726345 6961021417893925916044759)
          ·
            refine ⟨10441532126840888874067139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6961021417893925916044759 10441532126840888874067139)
            ·
              refine ⟨15662298190261333311100709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10441532126840888874067139 15662298190261333311100709)
              ·
                refine ⟨2936680910673999995831383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15662298190261333311100709 2936680910673999995831383)
                ·
                  refine ⟨4405021366010999993747075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2936680910673999995831383 4405021366010999993747075)
                  ·
                    refine ⟨6607532049016499990620613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4405021366010999993747075 6607532049016499990620613)
                    ·
                      refine ⟨1238912259190593748241365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6607532049016499990620613 1238912259190593748241365)
                      ·
                        rfl

theorem cell23_2412773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2412773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412773 prefixEnd_2412773 := by exact prefixLift 2412773
  have htrace : WordTrace (prefixWord ++ tailWord_2412773) baseStart_2412773 baseEnd_2412773 := by
    simpa [prefixWord, tailWord_2412773, baseEnd_2412773] using wordTrace_append hprefix tailTrace_2412773
  have hstable : (prefixWord ++ tailWord_2412773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412773).length < 2 ^ (prefixWord ++ tailWord_2412773).sum := by decide
  have hdescent : baseEnd_2412773 < baseStart_2412773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412779 : List Nat := [1, 1, 1, 1, 2, 5, 3, 9]
def baseStart_2412779 : Nat := 118140960795 + 2412779 * 2 ^ 59
def prefixEnd_2412779 : Nat := 4983230072969 + 3 ^ 40 * 2412779 * 2
def baseEnd_2412779 : Nat := 45885753336093360176531

theorem tailTrace_2412779 : CollatzResearch.WordTrace tailWord_2412779 prefixEnd_2412779 45885753336093360176531 := by
  unfold tailWord_2412779
  simp only [CollatzResearch.WordTrace]
  refine ⟨88001279725921227691753391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58667519817280818461168927 88001279725921227691753391)
  ·
    refine ⟨132001919588881841537630087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88001279725921227691753391 132001919588881841537630087)
    ·
      refine ⟨198002879383322762306445131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132001919588881841537630087 198002879383322762306445131)
      ·
        refine ⟨297004319074984143459667697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198002879383322762306445131 297004319074984143459667697)
        ·
          refine ⟨222753239306238107594750773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297004319074984143459667697 222753239306238107594750773)
          ·
            refine ⟨20883116184959822587007885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222753239306238107594750773 20883116184959822587007885)
            ·
              refine ⟨7831168569359933470127957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20883116184959822587007885 7831168569359933470127957)
              ·
                refine ⟨45885753336093360176531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7831168569359933470127957 45885753336093360176531)
                ·
                  rfl

theorem cell23_2412779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 9].length) (baseStart_2412779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412779 prefixEnd_2412779 := by exact prefixLift 2412779
  have htrace : WordTrace (prefixWord ++ tailWord_2412779) baseStart_2412779 baseEnd_2412779 := by
    simpa [prefixWord, tailWord_2412779, baseEnd_2412779] using wordTrace_append hprefix tailTrace_2412779
  have hstable : (prefixWord ++ tailWord_2412779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412779).length < 2 ^ (prefixWord ++ tailWord_2412779).sum := by decide
  have hdescent : baseEnd_2412779 < baseStart_2412779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412790 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2]
def baseStart_2412790 : Nat := 118140960795 + 2412790 * 2 ^ 59
def prefixEnd_2412790 : Nat := 4983230072969 + 3 ^ 40 * 2412790 * 2
def baseEnd_2412790 : Nat := 1238920988361720181728787

theorem tailTrace_2412790 : CollatzResearch.WordTrace tailWord_2412790 prefixEnd_2412790 1238920988361720181728787 := by
  unfold tailWord_2412790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500105058055086035650239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58667787285920917713602549 5500105058055086035650239)
  ·
    refine ⟨8250157587082629053475359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5500105058055086035650239 8250157587082629053475359)
    ·
      refine ⟨12375236380623943580213039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8250157587082629053475359 12375236380623943580213039)
      ·
        refine ⟨18562854570935915370319559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12375236380623943580213039 18562854570935915370319559)
        ·
          refine ⟨27844281856403873055479339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18562854570935915370319559 27844281856403873055479339)
          ·
            refine ⟨41766422784605809583219009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27844281856403873055479339 41766422784605809583219009)
            ·
              refine ⟨31324817088454357187414257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41766422784605809583219009 31324817088454357187414257)
              ·
                refine ⟨23493612816340767890560693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31324817088454357187414257 23493612816340767890560693)
                ·
                  refine ⟨2202526201531946989740065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23493612816340767890560693 2202526201531946989740065)
                  ·
                    refine ⟨1651894651148960242305049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2202526201531946989740065 1651894651148960242305049)
                    ·
                      refine ⟨1238920988361720181728787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651894651148960242305049 1238920988361720181728787)
                      ·
                        rfl

theorem cell23_2412790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_2412790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412790 prefixEnd_2412790 := by exact prefixLift 2412790
  have htrace : WordTrace (prefixWord ++ tailWord_2412790) baseStart_2412790 baseEnd_2412790 := by
    simpa [prefixWord, tailWord_2412790, baseEnd_2412790] using wordTrace_append hprefix tailTrace_2412790
  have hstable : (prefixWord ++ tailWord_2412790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412790).length < 2 ^ (prefixWord ++ tailWord_2412790).sum := by decide
  have hdescent : baseEnd_2412790 < baseStart_2412790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412796 : List Nat := [2, 2, 2, 1, 4, 3, 9]
def baseStart_2412796 : Nat := 118140960795 + 2412796 * 2 ^ 59
def prefixEnd_2412796 : Nat := 4983230072969 + 3 ^ 40 * 2412796 * 2
def baseEnd_2412796 : Nat := 15295358879575890842639

theorem tailTrace_2412796 : CollatzResearch.WordTrace tailWord_2412796 prefixEnd_2412796 15295358879575890842639 := by
  unfold tailWord_2412796
  simp only [CollatzResearch.WordTrace]
  refine ⟨44000949883429819797561121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58667933177906426396748161 44000949883429819797561121)
  ·
    refine ⟨33000712412572364848170841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44000949883429819797561121 33000712412572364848170841)
    ·
      refine ⟨24750534309429273636128131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33000712412572364848170841 24750534309429273636128131)
      ·
        refine ⟨37125801464143910454192197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24750534309429273636128131 37125801464143910454192197)
        ·
          refine ⟨6961087774526983210161037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37125801464143910454192197 6961087774526983210161037)
          ·
            refine ⟨2610407915447618703810389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6961087774526983210161037 2610407915447618703810389)
            ·
              refine ⟨15295358879575890842639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2610407915447618703810389 15295358879575890842639)
              ·
                rfl

theorem cell23_2412796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 9].length) (baseStart_2412796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412796 prefixEnd_2412796 := by exact prefixLift 2412796
  have htrace : WordTrace (prefixWord ++ tailWord_2412796) baseStart_2412796 baseEnd_2412796 := by
    simpa [prefixWord, tailWord_2412796, baseEnd_2412796] using wordTrace_append hprefix tailTrace_2412796
  have hstable : (prefixWord ++ tailWord_2412796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412796).length < 2 ^ (prefixWord ++ tailWord_2412796).sum := by decide
  have hdescent : baseEnd_2412796 < baseStart_2412796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412840 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2412840 : Nat := 118140960795 + 2412840 * 2 ^ 59
def prefixEnd_2412840 : Nat := 4983230072969 + 3 ^ 40 * 2412840 * 2
def baseEnd_2412840 : Nat := 1238946662394444986103557

theorem tailTrace_2412840 : CollatzResearch.WordTrace tailWord_2412840 prefixEnd_2412840 1238946662394444986103557 := by
  unfold tailWord_2412840
  simp only [CollatzResearch.WordTrace]
  refine ⟨44001752289350117554861987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58669003052466823406482649 44001752289350117554861987)
  ·
    refine ⟨66002628434025176332292981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44001752289350117554861987 66002628434025176332292981)
    ·
      refine ⟨6187746415689860281152467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66002628434025176332292981 6187746415689860281152467)
      ·
        refine ⟨9281619623534790421728701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6187746415689860281152467 9281619623534790421728701)
        ·
          refine ⟨3480607358825546408148263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9281619623534790421728701 3480607358825546408148263)
          ·
            refine ⟨5220911038238319612222395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480607358825546408148263 5220911038238319612222395)
            ·
              refine ⟨7831366557357479418333593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220911038238319612222395 7831366557357479418333593)
              ·
                refine ⟨5873524918018109563750195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7831366557357479418333593 5873524918018109563750195)
                ·
                  refine ⟨8810287377027164345625293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5873524918018109563750195 8810287377027164345625293)
                  ·
                    refine ⟨3303857766385186629609485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8810287377027164345625293 3303857766385186629609485)
                    ·
                      refine ⟨1238946662394444986103557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303857766385186629609485 1238946662394444986103557)
                      ·
                        rfl

theorem cell23_2412840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2412840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412840 prefixEnd_2412840 := by exact prefixLift 2412840
  have htrace : WordTrace (prefixWord ++ tailWord_2412840) baseStart_2412840 baseEnd_2412840 := by
    simpa [prefixWord, tailWord_2412840, baseEnd_2412840] using wordTrace_append hprefix tailTrace_2412840
  have hstable : (prefixWord ++ tailWord_2412840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412840).length < 2 ^ (prefixWord ++ tailWord_2412840).sum := by decide
  have hdescent : baseEnd_2412840 < baseStart_2412840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412857 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2412857 : Nat := 118140960795 + 2412857 * 2 ^ 59
def prefixEnd_2412857 : Nat := 4983230072969 + 3 ^ 40 * 2412857 * 2
def baseEnd_2412857 : Nat := 1238955391565571419590979

theorem tailTrace_2412857 : CollatzResearch.WordTrace tailWord_2412857 prefixEnd_2412857 1238955391565571419590979 := by
  unfold tailWord_2412857
  simp only [CollatzResearch.WordTrace]
  refine ⟨88004124619638647013092825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58669416413092431342061883 88004124619638647013092825)
  ·
    refine ⟨66003093464728985259819619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88004124619638647013092825 66003093464728985259819619)
    ·
      refine ⟨99004640197093477889729429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66003093464728985259819619 99004640197093477889729429)
      ·
        refine ⟨4640842509238756776081067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99004640197093477889729429 4640842509238756776081067)
        ·
          refine ⟨6961263763858135164121601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4640842509238756776081067 6961263763858135164121601)
          ·
            refine ⟨5220947822893601373091201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6961263763858135164121601 5220947822893601373091201)
            ·
              refine ⟨3915710867170201029818401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5220947822893601373091201 3915710867170201029818401)
              ·
                refine ⟨2936783150377650772363801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3915710867170201029818401 2936783150377650772363801)
                ·
                  refine ⟨2202587362783238079272851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936783150377650772363801 2202587362783238079272851)
                  ·
                    refine ⟨3303881044174857118909277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202587362783238079272851 3303881044174857118909277)
                    ·
                      refine ⟨1238955391565571419590979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303881044174857118909277 1238955391565571419590979)
                      ·
                        rfl

theorem cell23_2412857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2412857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412857 prefixEnd_2412857 := by exact prefixLift 2412857
  have htrace : WordTrace (prefixWord ++ tailWord_2412857) baseStart_2412857 baseEnd_2412857 := by
    simpa [prefixWord, tailWord_2412857, baseEnd_2412857] using wordTrace_append hprefix tailTrace_2412857
  have hstable : (prefixWord ++ tailWord_2412857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412857).length < 2 ^ (prefixWord ++ tailWord_2412857).sum := by decide
  have hdescent : baseEnd_2412857 < baseStart_2412857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412863 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 3, 4, 2]
def baseStart_2412863 : Nat := 118140960795 + 2412863 * 2 ^ 59
def prefixEnd_2412863 : Nat := 4983230072969 + 3 ^ 40 * 2412863 * 2
def baseEnd_2412863 : Nat := 1238958472449498396115951

theorem tailTrace_2412863 : CollatzResearch.WordTrace tailWord_2412863 prefixEnd_2412863 1238958472449498396115951 := by
  unfold tailWord_2412863
  simp only [CollatzResearch.WordTrace]
  refine ⟨88004343457616910037811243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58669562305077940025207495 88004343457616910037811243)
  ·
    refine ⟨132006515186425365056716865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88004343457616910037811243 132006515186425365056716865)
    ·
      refine ⟨99004886389819023792537649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132006515186425365056716865 99004886389819023792537649)
      ·
        refine ⟨74253664792364267844403237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99004886389819023792537649 74253664792364267844403237)
        ·
          refine ⟨13922562148568300220825607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74253664792364267844403237 13922562148568300220825607)
          ·
            refine ⟨20883843222852450331238411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13922562148568300220825607 20883843222852450331238411)
            ·
              refine ⟨31325764834278675496857617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20883843222852450331238411 31325764834278675496857617)
              ·
                refine ⟨23494323625709006622643213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31325764834278675496857617 23494323625709006622643213)
                ·
                  refine ⟨8810371359640877483491205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23494323625709006622643213 8810371359640877483491205)
                  ·
                    refine ⟨1651944629932664528154601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8810371359640877483491205 1651944629932664528154601)
                    ·
                      refine ⟨1238958472449498396115951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651944629932664528154601 1238958472449498396115951)
                      ·
                        rfl

theorem cell23_2412863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_2412863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412863 prefixEnd_2412863 := by exact prefixLift 2412863
  have htrace : WordTrace (prefixWord ++ tailWord_2412863) baseStart_2412863 baseEnd_2412863 := by
    simpa [prefixWord, tailWord_2412863, baseEnd_2412863] using wordTrace_append hprefix tailTrace_2412863
  have hstable : (prefixWord ++ tailWord_2412863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412863).length < 2 ^ (prefixWord ++ tailWord_2412863).sum := by decide
  have hdescent : baseEnd_2412863 < baseStart_2412863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412880 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 1, 4, 2]
def baseStart_2412880 : Nat := 118140960795 + 2412880 * 2 ^ 59
def prefixEnd_2412880 : Nat := 4983230072969 + 3 ^ 40 * 2412880 * 2
def baseEnd_2412880 : Nat := 1238967201620624829603373

theorem tailTrace_2412880 : CollatzResearch.WordTrace tailWord_2412880 prefixEnd_2412880 1238967201620624829603373 := by
  unfold tailWord_2412880
  simp only [CollatzResearch.WordTrace]
  refine ⟨44002481749277660970590047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58669975665703547960786729 44002481749277660970590047)
  ·
    refine ⟨66003722623916491455885071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44002481749277660970590047 66003722623916491455885071)
    ·
      refine ⟨99005583935874737183827607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66003722623916491455885071 99005583935874737183827607)
      ·
        refine ⟨148508375903812105775741411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99005583935874737183827607 148508375903812105775741411)
        ·
          refine ⟨222762563855718158663612117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148508375903812105775741411 222762563855718158663612117)
          ·
            refine ⟨5220997590368394343678409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 222762563855718158663612117 5220997590368394343678409)
            ·
              refine ⟨3915748192776295757758807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5220997590368394343678409 3915748192776295757758807)
              ·
                refine ⟨5873622289164443636638211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915748192776295757758807 5873622289164443636638211)
                ·
                  refine ⟨8810433433746665454957317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5873622289164443636638211 8810433433746665454957317)
                  ·
                    refine ⟨1651956268827499772804497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8810433433746665454957317 1651956268827499772804497)
                    ·
                      refine ⟨1238967201620624829603373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651956268827499772804497 1238967201620624829603373)
                      ·
                        rfl

theorem cell23_2412880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 4, 2].length) (baseStart_2412880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412880 prefixEnd_2412880 := by exact prefixLift 2412880
  have htrace : WordTrace (prefixWord ++ tailWord_2412880) baseStart_2412880 baseEnd_2412880 := by
    simpa [prefixWord, tailWord_2412880, baseEnd_2412880] using wordTrace_append hprefix tailTrace_2412880
  have hstable : (prefixWord ++ tailWord_2412880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412880).length < 2 ^ (prefixWord ++ tailWord_2412880).sum := by decide
  have hdescent : baseEnd_2412880 < baseStart_2412880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412914 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_2412914 : Nat := 118140960795 + 2412914 * 2 ^ 59
def prefixEnd_2412914 : Nat := 4983230072969 + 3 ^ 40 * 2412914 * 2
def baseEnd_2412914 : Nat := 1238984659962877696578217

theorem tailTrace_2412914 : CollatzResearch.WordTrace tailWord_2412914 prefixEnd_2412914 1238984659962877696578217 := by
  unfold tailWord_2412914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22001550895108036436979449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58670802386954763831945197 22001550895108036436979449)
  ·
    refine ⟨16501163171331027327734587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22001550895108036436979449 16501163171331027327734587)
    ·
      refine ⟨24751744756996540991601881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16501163171331027327734587 24751744756996540991601881)
      ·
        refine ⟨18563808567747405743701411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24751744756996540991601881 18563808567747405743701411)
        ·
          refine ⟨27845712851621108615552117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18563808567747405743701411 27845712851621108615552117)
          ·
            refine ⟨2610535579839478932708011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27845712851621108615552117 2610535579839478932708011)
            ·
              refine ⟨3915803369759218399062017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610535579839478932708011 3915803369759218399062017)
              ·
                refine ⟨2936852527319413799296513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3915803369759218399062017 2936852527319413799296513)
                ·
                  refine ⟨2202639395489560349472385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936852527319413799296513 2202639395489560349472385)
                  ·
                    refine ⟨1651979546617170262104289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2202639395489560349472385 1651979546617170262104289)
                    ·
                      refine ⟨1238984659962877696578217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651979546617170262104289 1238984659962877696578217)
                      ·
                        rfl

theorem cell23_2412914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_2412914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412914 prefixEnd_2412914 := by exact prefixLift 2412914
  have htrace : WordTrace (prefixWord ++ tailWord_2412914) baseStart_2412914 baseEnd_2412914 := by
    simpa [prefixWord, tailWord_2412914, baseEnd_2412914] using wordTrace_append hprefix tailTrace_2412914
  have hstable : (prefixWord ++ tailWord_2412914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412914).length < 2 ^ (prefixWord ++ tailWord_2412914).sum := by decide
  have hdescent : baseEnd_2412914 < baseStart_2412914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412953 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_2412953 : Nat := 118140960795 + 2412953 * 2 ^ 59
def prefixEnd_2412953 : Nat := 4983230072969 + 3 ^ 40 * 2412953 * 2
def baseEnd_2412953 : Nat := 1239004685708403043990537

theorem tailTrace_2412953 : CollatzResearch.WordTrace tailWord_2412953 prefixEnd_2412953 1239004685708403043990537 := by
  unfold tailWord_2412953
  simp only [CollatzResearch.WordTrace]
  refine ⟨88007626027290855408587513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58671750684860570272391675 88007626027290855408587513)
  ·
    refine ⟨66005719520468141556440635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88007626027290855408587513 66005719520468141556440635)
    ·
      refine ⟨99008579280702212334660953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66005719520468141556440635 99008579280702212334660953)
      ·
        refine ⟨74256434460526659250995715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99008579280702212334660953 74256434460526659250995715)
        ·
          refine ⟨111384651690789988876493573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74256434460526659250995715 111384651690789988876493573)
          ·
            refine ⟨20884622192023122914342545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111384651690789988876493573 20884622192023122914342545)
            ·
              refine ⟨15663466644017342185756909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20884622192023122914342545 15663466644017342185756909)
              ·
                refine ⟨5873799991506503319658841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15663466644017342185756909 5873799991506503319658841)
                ·
                  refine ⟨4405349993629877489744131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5873799991506503319658841 4405349993629877489744131)
                  ·
                    refine ⟨6608024990444816234616197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4405349993629877489744131 6608024990444816234616197)
                    ·
                      refine ⟨1239004685708403043990537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6608024990444816234616197 1239004685708403043990537)
                      ·
                        rfl

theorem cell23_2412953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_2412953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412953 prefixEnd_2412953 := by exact prefixLift 2412953
  have htrace : WordTrace (prefixWord ++ tailWord_2412953) baseStart_2412953 baseEnd_2412953 := by
    simpa [prefixWord, tailWord_2412953, baseEnd_2412953] using wordTrace_append hprefix tailTrace_2412953
  have hstable : (prefixWord ++ tailWord_2412953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412953).length < 2 ^ (prefixWord ++ tailWord_2412953).sum := by decide
  have hdescent : baseEnd_2412953 < baseStart_2412953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413014 : List Nat := [5, 2, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2413014 : Nat := 118140960795 + 2413014 * 2 ^ 59
def prefixEnd_2413014 : Nat := 4983230072969 + 3 ^ 40 * 2413014 * 2
def baseEnd_2413014 : Nat := 413012002676109101775919

theorem tailTrace_2413014 : CollatzResearch.WordTrace tailWord_2413014 prefixEnd_2413014 413012002676109101775919 := by
  unfold tailWord_2413014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500615680004366426659881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58673233920046575217705397 5500615680004366426659881)
  ·
    refine ⟨4125461760003274819994911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5500615680004366426659881 4125461760003274819994911)
    ·
      refine ⟨6188192640004912229992367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125461760003274819994911 6188192640004912229992367)
      ·
        refine ⟨9282288960007368344988551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6188192640004912229992367 9282288960007368344988551)
        ·
          refine ⟨13923433440011052517482827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9282288960007368344988551 13923433440011052517482827)
          ·
            refine ⟨20885150160016578776224241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13923433440011052517482827 20885150160016578776224241)
            ·
              refine ⟨15663862620012434082168181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20885150160016578776224241 15663862620012434082168181)
              ·
                refine ⟨1468487120626165695203267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15663862620012434082168181 1468487120626165695203267)
                ·
                  refine ⟨2202730680939248542804901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468487120626165695203267 2202730680939248542804901)
                  ·
                    refine ⟨413012002676109101775919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202730680939248542804901 413012002676109101775919)
                    ·
                      rfl

theorem cell23_2413014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2413014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413014 prefixEnd_2413014 := by exact prefixLift 2413014
  have htrace : WordTrace (prefixWord ++ tailWord_2413014) baseStart_2413014 baseEnd_2413014 := by
    simpa [prefixWord, tailWord_2413014, baseEnd_2413014] using wordTrace_append hprefix tailTrace_2413014
  have hstable : (prefixWord ++ tailWord_2413014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413014).length < 2 ^ (prefixWord ++ tailWord_2413014).sum := by decide
  have hdescent : baseEnd_2413014 < baseStart_2413014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413043 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 4]
def baseStart_2413043 : Nat := 118140960795 + 2413043 * 2 ^ 59
def prefixEnd_2413043 : Nat := 4983230072969 + 3 ^ 40 * 2413043 * 2
def baseEnd_2413043 : Nat := 1239050898967307691865123

theorem tailTrace_2413043 : CollatzResearch.WordTrace tailWord_2413043 prefixEnd_2413043 1239050898967307691865123 := by
  unfold tailWord_2413043
  simp only [CollatzResearch.WordTrace]
  refine ⟨88010908596964800779363783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58673939064643200519575855 88010908596964800779363783)
  ·
    refine ⟨132016362895447201169045675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88010908596964800779363783 132016362895447201169045675)
    ·
      refine ⟨198024544343170801753568513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132016362895447201169045675 198024544343170801753568513)
      ·
        refine ⟨148518408257378101315176385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198024544343170801753568513 148518408257378101315176385)
        ·
          refine ⟨111388806193033575986382289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148518408257378101315176385 111388806193033575986382289)
          ·
            refine ⟨83541604644775181989786717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111388806193033575986382289 83541604644775181989786717)
            ·
              refine ⟨31328101741790693246170019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83541604644775181989786717 31328101741790693246170019)
              ·
                refine ⟨46992152612686039869255029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31328101741790693246170019 46992152612686039869255029)
                ·
                  refine ⟨4405514307439316237742659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46992152612686039869255029 4405514307439316237742659)
                  ·
                    refine ⟨6608271461158974356613989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4405514307439316237742659 6608271461158974356613989)
                    ·
                      refine ⟨1239050898967307691865123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6608271461158974356613989 1239050898967307691865123)
                      ·
                        rfl

theorem cell23_2413043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_2413043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413043 prefixEnd_2413043 := by exact prefixLift 2413043
  have htrace : WordTrace (prefixWord ++ tailWord_2413043) baseStart_2413043 baseEnd_2413043 := by
    simpa [prefixWord, tailWord_2413043, baseEnd_2413043] using wordTrace_append hprefix tailTrace_2413043
  have hstable : (prefixWord ++ tailWord_2413043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413043).length < 2 ^ (prefixWord ++ tailWord_2413043).sum := by decide
  have hdescent : baseEnd_2413043 < baseStart_2413043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413070 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_2413070 : Nat := 118140960795 + 2413070 * 2 ^ 59
def prefixEnd_2413070 : Nat := 4983230072969 + 3 ^ 40 * 2413070 * 2
def baseEnd_2413070 : Nat := 413021587648326362075833

theorem tailTrace_2413070 : CollatzResearch.WordTrace tailWord_2413070 prefixEnd_2413070 413021587648326362075833 := by
  unfold tailWord_2413070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11001486670983373048824583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58674595578577989593731109 11001486670983373048824583)
  ·
    refine ⟨16502230006475059573236875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11001486670983373048824583 16502230006475059573236875)
    ·
      refine ⟨24753345009712589359855313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16502230006475059573236875 24753345009712589359855313)
      ·
        refine ⟨18565008757284442019891485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24753345009712589359855313 18565008757284442019891485)
        ·
          refine ⟨6961878283981665757459307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18565008757284442019891485 6961878283981665757459307)
          ·
            refine ⟨10442817425972498636188961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6961878283981665757459307 10442817425972498636188961)
            ·
              refine ⟨7832113069479373977141721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10442817425972498636188961 7832113069479373977141721)
              ·
                refine ⟨5874084802109530482856291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7832113069479373977141721 5874084802109530482856291)
                ·
                  refine ⟨8811127203164295724284437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5874084802109530482856291 8811127203164295724284437)
                  ·
                    refine ⟨413021587648326362075833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8811127203164295724284437 413021587648326362075833)
                    ·
                      rfl

theorem cell23_2413070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_2413070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413070 prefixEnd_2413070 := by exact prefixLift 2413070
  have htrace : WordTrace (prefixWord ++ tailWord_2413070) baseStart_2413070 baseEnd_2413070 := by
    simpa [prefixWord, tailWord_2413070, baseEnd_2413070] using wordTrace_append hprefix tailTrace_2413070
  have hstable : (prefixWord ++ tailWord_2413070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413070).length < 2 ^ (prefixWord ++ tailWord_2413070).sum := by decide
  have hdescent : baseEnd_2413070 < baseStart_2413070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413073 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_2413073 : Nat := 118140960795 + 2413073 * 2 ^ 59
def prefixEnd_2413073 : Nat := 4983230072969 + 3 ^ 40 * 2413073 * 2
def baseEnd_2413073 : Nat := 1239066303386942574489985

theorem tailTrace_2413073 : CollatzResearch.WordTrace tailWord_2413073 prefixEnd_2413073 1239066303386942574489985 := by
  unfold tailWord_2413073
  simp only [CollatzResearch.WordTrace]
  refine ⟨88012002786856115902955873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58674668524570743935303915 88012002786856115902955873)
  ·
    refine ⟨66009002090142086927216905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88012002786856115902955873 66009002090142086927216905)
    ·
      refine ⟨49506751567606565195412679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66009002090142086927216905 49506751567606565195412679)
      ·
        refine ⟨74260127351409847793119019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49506751567606565195412679 74260127351409847793119019)
        ·
          refine ⟨111390191027114771689678529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74260127351409847793119019 111390191027114771689678529)
          ·
            refine ⟨83542643270336078767258897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111390191027114771689678529 83542643270336078767258897)
            ·
              refine ⟨62656982452752059075444173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83542643270336078767258897 62656982452752059075444173)
              ·
                refine ⟨23496368419782022153291565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62656982452752059075444173 23496368419782022153291565)
                ·
                  refine ⟨8811138157418258307484337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23496368419782022153291565 8811138157418258307484337)
                  ·
                    refine ⟨6608353618063693730613253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8811138157418258307484337 6608353618063693730613253)
                    ·
                      refine ⟨1239066303386942574489985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6608353618063693730613253 1239066303386942574489985)
                      ·
                        rfl

theorem cell23_2413073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_2413073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413073 prefixEnd_2413073 := by exact prefixLift 2413073
  have htrace : WordTrace (prefixWord ++ tailWord_2413073) baseStart_2413073 baseEnd_2413073 := by
    simpa [prefixWord, tailWord_2413073, baseEnd_2413073] using wordTrace_append hprefix tailTrace_2413073
  have hstable : (prefixWord ++ tailWord_2413073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413073).length < 2 ^ (prefixWord ++ tailWord_2413073).sum := by decide
  have hdescent : baseEnd_2413073 < baseStart_2413073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413077 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_2413077 : Nat := 118140960795 + 2413077 * 2 ^ 59
def prefixEnd_2413077 : Nat := 4983230072969 + 3 ^ 40 * 2413077 * 2
def baseEnd_2413077 : Nat := 1239068357309560558839967

theorem tailTrace_2413077 : CollatzResearch.WordTrace tailWord_2413077 prefixEnd_2413077 1239068357309560558839967 := by
  unfold tailWord_2413077
  simp only [CollatzResearch.WordTrace]
  refine ⟨88012148678841624586101485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58674765785894416390734323 88012148678841624586101485)
  ·
    refine ⟨33004555754565609219788057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88012148678841624586101485 33004555754565609219788057)
    ·
      refine ⟨24753416815924206914841043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33004555754565609219788057 24753416815924206914841043)
      ·
        refine ⟨37130125223886310372261565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24753416815924206914841043 37130125223886310372261565)
        ·
          refine ⟨13923796958957366389598087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37130125223886310372261565 13923796958957366389598087)
          ·
            refine ⟨20885695438436049584397131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13923796958957366389598087 20885695438436049584397131)
            ·
              refine ⟨31328543157654074376595697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20885695438436049584397131 31328543157654074376595697)
              ·
                refine ⟨23496407368240555782446773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31328543157654074376595697 23496407368240555782446773)
                ·
                  refine ⟨2202788190772552104604385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23496407368240555782446773 2202788190772552104604385)
                  ·
                    refine ⟨1652091143079414078453289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2202788190772552104604385 1652091143079414078453289)
                    ·
                      refine ⟨1239068357309560558839967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652091143079414078453289 1239068357309560558839967)
                      ·
                        rfl

theorem cell23_2413077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_2413077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413077 prefixEnd_2413077 := by exact prefixLift 2413077
  have htrace : WordTrace (prefixWord ++ tailWord_2413077) baseStart_2413077 baseEnd_2413077 := by
    simpa [prefixWord, tailWord_2413077, baseEnd_2413077] using wordTrace_append hprefix tailTrace_2413077
  have hstable : (prefixWord ++ tailWord_2413077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413077).length < 2 ^ (prefixWord ++ tailWord_2413077).sum := by decide
  have hdescent : baseEnd_2413077 < baseStart_2413077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413117 : List Nat := [1, 4, 1, 3, 2, 3, 2, 7]
def baseStart_2413117 : Nat := 118140960795 + 2413117 * 2 ^ 59
def prefixEnd_2413117 : Nat := 4983230072969 + 3 ^ 40 * 2413117 * 2
def baseEnd_2413117 : Nat := 45892181353175570457029

theorem tailTrace_2413117 : CollatzResearch.WordTrace tailWord_2413117 prefixEnd_2413117 45892181353175570457029 := by
  unfold tailWord_2413117
  simp only [CollatzResearch.WordTrace]
  refine ⟨88013607598696711417557605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58675738399131140945038403 88013607598696711417557605)
  ·
    refine ⟨16502551424755633390792051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88013607598696711417557605 16502551424755633390792051)
    ·
      refine ⟨24753827137133450086188077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16502551424755633390792051 24753827137133450086188077)
      ·
        refine ⟨9282685176425043782320529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24753827137133450086188077 9282685176425043782320529)
        ·
          refine ⟨6962013882318782836740397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9282685176425043782320529 6962013882318782836740397)
          ·
            refine ⟨2610755205869543563777649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6962013882318782836740397 2610755205869543563777649)
            ·
              refine ⟨1958066404402157672833237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2610755205869543563777649 1958066404402157672833237)
              ·
                refine ⟨45892181353175570457029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1958066404402157672833237 45892181353175570457029)
                ·
                  rfl

theorem cell23_2413117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 7].length) (baseStart_2413117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413117 prefixEnd_2413117 := by exact prefixLift 2413117
  have htrace : WordTrace (prefixWord ++ tailWord_2413117) baseStart_2413117 baseEnd_2413117 := by
    simpa [prefixWord, tailWord_2413117, baseEnd_2413117] using wordTrace_append hprefix tailTrace_2413117
  have hstable : (prefixWord ++ tailWord_2413117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413117).length < 2 ^ (prefixWord ++ tailWord_2413117).sum := by decide
  have hdescent : baseEnd_2413117 < baseStart_2413117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413127 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_2413127 : Nat := 118140960795 + 2413127 * 2 ^ 59
def prefixEnd_2413127 : Nat := 4983230072969 + 3 ^ 40 * 2413127 * 2
def baseEnd_2413127 : Nat := 1239094031342285363214737

theorem tailTrace_2413127 : CollatzResearch.WordTrace tailWord_2413127 prefixEnd_2413127 1239094031342285363214737 := by
  unfold tailWord_2413127
  simp only [CollatzResearch.WordTrace]
  refine ⟨88013972328660483125421635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58675981552440322083614423 88013972328660483125421635)
  ·
    refine ⟨132020958492990724688132453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88013972328660483125421635 132020958492990724688132453)
    ·
      refine ⟨24753929717435760879024835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132020958492990724688132453 24753929717435760879024835)
      ·
        refine ⟨37130894576153641318537253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24753929717435760879024835 37130894576153641318537253)
        ·
          refine ⟨6962042733028807747225735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37130894576153641318537253 6962042733028807747225735)
          ·
            refine ⟨10443064099543211620838603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962042733028807747225735 10443064099543211620838603)
            ·
              refine ⟨15664596149314817431257905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10443064099543211620838603 15664596149314817431257905)
              ·
                refine ⟨11748447111986113073443429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15664596149314817431257905 11748447111986113073443429)
                ·
                  refine ⟨2202833833497396201270643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11748447111986113073443429 2202833833497396201270643)
                  ·
                    refine ⟨3304250750246094301905965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202833833497396201270643 3304250750246094301905965)
                    ·
                      refine ⟨1239094031342285363214737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3304250750246094301905965 1239094031342285363214737)
                      ·
                        rfl

theorem cell23_2413127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_2413127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413127 prefixEnd_2413127 := by exact prefixLift 2413127
  have htrace : WordTrace (prefixWord ++ tailWord_2413127) baseStart_2413127 baseEnd_2413127 := by
    simpa [prefixWord, tailWord_2413127, baseEnd_2413127] using wordTrace_append hprefix tailTrace_2413127
  have hstable : (prefixWord ++ tailWord_2413127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413127).length < 2 ^ (prefixWord ++ tailWord_2413127).sum := by decide
  have hdescent : baseEnd_2413127 < baseStart_2413127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413183 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_2413183 : Nat := 118140960795 + 2413183 * 2 ^ 59
def prefixEnd_2413183 : Nat := 4983230072969 + 3 ^ 40 * 2413183 * 2
def baseEnd_2413183 : Nat := 1239122786258937144114479

theorem tailTrace_2413183 : CollatzResearch.WordTrace tailWord_2413183 prefixEnd_2413183 1239122786258937144114479 := by
  unfold tailWord_2413183
  simp only [CollatzResearch.WordTrace]
  refine ⟨88016014816457604689460203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58677343210971736459640135 88016014816457604689460203)
  ·
    refine ⟨132024022224686407034190305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88016014816457604689460203 132024022224686407034190305)
    ·
      refine ⟨99018016668514805275642729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132024022224686407034190305 99018016668514805275642729)
      ·
        refine ⟨74263512501386103956732047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99018016668514805275642729 74263512501386103956732047)
        ·
          refine ⟨111395268752079155935098071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74263512501386103956732047 111395268752079155935098071)
          ·
            refine ⟨167092903128118733902647107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111395268752079155935098071 167092903128118733902647107)
            ·
              refine ⟨250639354692178100853970661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167092903128118733902647107 250639354692178100853970661)
              ·
                refine ⟨46994879004783393910119499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250639354692178100853970661 46994879004783393910119499)
                ·
                  refine ⟨70492318507175090865179249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46994879004783393910119499 70492318507175090865179249)
                  ·
                    refine ⟨52869238880381318148884437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70492318507175090865179249 52869238880381318148884437)
                    ·
                      refine ⟨1239122786258937144114479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52869238880381318148884437 1239122786258937144114479)
                      ·
                        rfl

theorem cell23_2413183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_2413183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413183 prefixEnd_2413183 := by exact prefixLift 2413183
  have htrace : WordTrace (prefixWord ++ tailWord_2413183) baseStart_2413183 baseEnd_2413183 := by
    simpa [prefixWord, tailWord_2413183, baseEnd_2413183] using wordTrace_append hprefix tailTrace_2413183
  have hstable : (prefixWord ++ tailWord_2413183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413183).length < 2 ^ (prefixWord ++ tailWord_2413183).sum := by decide
  have hdescent : baseEnd_2413183 < baseStart_2413183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413207 : List Nat := [1, 1, 3, 3, 2, 1, 3, 4, 5]
def baseStart_2413207 : Nat := 118140960795 + 2413207 * 2 ^ 59
def prefixEnd_2413207 : Nat := 4983230072969 + 3 ^ 40 * 2413207 * 2
def baseEnd_2413207 : Nat := 137681678866071672246041

theorem tailTrace_2413207 : CollatzResearch.WordTrace tailWord_2413207 prefixEnd_2413207 137681678866071672246041 := by
  unfold tailWord_2413207
  simp only [CollatzResearch.WordTrace]
  refine ⟨88016890168370656788333875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58677926778913771192222583 88016890168370656788333875)
  ·
    refine ⟨132025335252555985182500813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88016890168370656788333875 132025335252555985182500813)
    ·
      refine ⟨49509500719708494443437805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132025335252555985182500813 49509500719708494443437805)
      ·
        refine ⟨18566062769890685416289177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49509500719708494443437805 18566062769890685416289177)
        ·
          refine ⟨13924547077418014062216883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18566062769890685416289177 13924547077418014062216883)
          ·
            refine ⟨20886820616127021093325325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13924547077418014062216883 20886820616127021093325325)
            ·
              refine ⟨7832557731047632909996997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20886820616127021093325325 7832557731047632909996997)
              ·
                refine ⟨1468604574571431170624437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7832557731047632909996997 1468604574571431170624437)
                ·
                  refine ⟨137681678866071672246041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1468604574571431170624437 137681678866071672246041)
                  ·
                    rfl

theorem cell23_2413207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 5].length) (baseStart_2413207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413207 prefixEnd_2413207 := by exact prefixLift 2413207
  have htrace : WordTrace (prefixWord ++ tailWord_2413207) baseStart_2413207 baseEnd_2413207 := by
    simpa [prefixWord, tailWord_2413207, baseEnd_2413207] using wordTrace_append hprefix tailTrace_2413207
  have hstable : (prefixWord ++ tailWord_2413207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413207).length < 2 ^ (prefixWord ++ tailWord_2413207).sum := by decide
  have hdescent : baseEnd_2413207 < baseStart_2413207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413220 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_2413220 : Nat := 118140960795 + 2413220 * 2 ^ 59
def prefixEnd_2413220 : Nat := 4983230072969 + 3 ^ 40 * 2413220 * 2
def baseEnd_2413220 : Nat := 413047261681051166450603

theorem tailTrace_2413220 : CollatzResearch.WordTrace tailWord_2413220 prefixEnd_2413220 413047261681051166450603 := by
  unfold tailWord_2413220
  simp only [CollatzResearch.WordTrace]
  refine ⟨44008682158661780004278557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58678242878215706672371409 44008682158661780004278557)
  ·
    refine ⟨16503255809498167501604459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44008682158661780004278557 16503255809498167501604459)
    ·
      refine ⟨24754883714247251252406689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16503255809498167501604459 24754883714247251252406689)
      ·
        refine ⟨18566162785685438439305017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24754883714247251252406689 18566162785685438439305017)
        ·
          refine ⟨13924622089264078829478763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18566162785685438439305017 13924622089264078829478763)
          ·
            refine ⟨20886933133896118244218145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13924622089264078829478763 20886933133896118244218145)
            ·
              refine ⟨15665199850422088683163609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20886933133896118244218145 15665199850422088683163609)
              ·
                refine ⟨11748899887816566512372707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15665199850422088683163609 11748899887816566512372707)
                ·
                  refine ⟨17623349831724849768559061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11748899887816566512372707 17623349831724849768559061)
                  ·
                    refine ⟨413047261681051166450603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17623349831724849768559061 413047261681051166450603)
                    ·
                      rfl

theorem cell23_2413220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_2413220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413220 prefixEnd_2413220 := by exact prefixLift 2413220
  have htrace : WordTrace (prefixWord ++ tailWord_2413220) baseStart_2413220 baseEnd_2413220 := by
    simpa [prefixWord, tailWord_2413220, baseEnd_2413220] using wordTrace_append hprefix tailTrace_2413220
  have hstable : (prefixWord ++ tailWord_2413220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413220).length < 2 ^ (prefixWord ++ tailWord_2413220).sum := by decide
  have hdescent : baseEnd_2413220 < baseStart_2413220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413237 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2413237 : Nat := 118140960795 + 2413237 * 2 ^ 59
def prefixEnd_2413237 : Nat := 4983230072969 + 3 ^ 40 * 2413237 * 2
def baseEnd_2413237 : Nat := 413050171404759977613077

theorem tailTrace_2413237 : CollatzResearch.WordTrace tailWord_2413237 prefixEnd_2413237 413050171404759977613077 := by
  unfold tailWord_2413237
  simp only [CollatzResearch.WordTrace]
  refine ⟨88017984358261971911925965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58678656238841314607950643 88017984358261971911925965)
  ·
    refine ⟨33006744134348239466972237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88017984358261971911925965 33006744134348239466972237)
    ·
      refine ⟨12377529050380589800114589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33006744134348239466972237 12377529050380589800114589)
      ·
        refine ⟨4641573393892721175042971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12377529050380589800114589 4641573393892721175042971)
        ·
          refine ⟨6962360090839081762564457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641573393892721175042971 6962360090839081762564457)
          ·
            refine ⟨5221770068129311321923343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6962360090839081762564457 5221770068129311321923343)
            ·
              refine ⟨7832655102193966982885015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5221770068129311321923343 7832655102193966982885015)
              ·
                refine ⟨11748982653290950474327523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7832655102193966982885015 11748982653290950474327523)
                ·
                  refine ⟨17623473979936425711491285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11748982653290950474327523 17623473979936425711491285)
                  ·
                    refine ⟨413050171404759977613077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17623473979936425711491285 413050171404759977613077)
                    ·
                      rfl

theorem cell23_2413237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2413237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413237 prefixEnd_2413237 := by exact prefixLift 2413237
  have htrace : WordTrace (prefixWord ++ tailWord_2413237) baseStart_2413237 baseEnd_2413237 := by
    simpa [prefixWord, tailWord_2413237, baseEnd_2413237] using wordTrace_append hprefix tailTrace_2413237
  have hstable : (prefixWord ++ tailWord_2413237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413237).length < 2 ^ (prefixWord ++ tailWord_2413237).sum := by decide
  have hdescent : baseEnd_2413237 < baseStart_2413237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413344 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 1, 5]
def baseStart_2413344 : Nat := 118140960795 + 2413344 * 2 ^ 59
def prefixEnd_2413344 : Nat := 4983230072969 + 3 ^ 40 * 2413344 * 2
def baseEnd_2413344 : Nat := 413068485548103671400413

theorem tailTrace_2413344 : CollatzResearch.WordTrace tailWord_2413344 prefixEnd_2413344 413068485548103671400413 := by
  unfold tailWord_2413344
  simp only [CollatzResearch.WordTrace]
  refine ⟨44010943484437164593035543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58681257979249552790714057 44010943484437164593035543)
  ·
    refine ⟨66016415226655746889553315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44010943484437164593035543 66016415226655746889553315)
    ·
      refine ⟨99024622839983620334329973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66016415226655746889553315 99024622839983620334329973)
      ·
        refine ⟨9283558391248464406343435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99024622839983620334329973 9283558391248464406343435)
        ·
          refine ⟨13925337586872696609515153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9283558391248464406343435 13925337586872696609515153)
          ·
            refine ⟨10444003190154522457136365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13925337586872696609515153 10444003190154522457136365)
            ·
              refine ⟨3916501196307945921426137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10444003190154522457136365 3916501196307945921426137)
              ·
                refine ⟨2937375897230959441069603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3916501196307945921426137 2937375897230959441069603)
                ·
                  refine ⟨4406063845846439161604405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937375897230959441069603 4406063845846439161604405)
                  ·
                    refine ⟨413068485548103671400413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4406063845846439161604405 413068485548103671400413)
                    ·
                      rfl

theorem cell23_2413344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_2413344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413344 prefixEnd_2413344 := by exact prefixLift 2413344
  have htrace : WordTrace (prefixWord ++ tailWord_2413344) baseStart_2413344 baseEnd_2413344 := by
    simpa [prefixWord, tailWord_2413344, baseEnd_2413344] using wordTrace_append hprefix tailTrace_2413344
  have hstable : (prefixWord ++ tailWord_2413344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413344).length < 2 ^ (prefixWord ++ tailWord_2413344).sum := by decide
  have hdescent : baseEnd_2413344 < baseStart_2413344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413370 : List Nat := [3, 1, 1, 1, 17]
def baseStart_2413370 : Nat := 118140960795 + 2413370 * 2 ^ 59
def prefixEnd_2413370 : Nat := 4983230072969 + 3 ^ 40 * 2413370 * 2
def baseEnd_2413370 : Nat := 1699888624336526628911

theorem tailTrace_2413370 : CollatzResearch.WordTrace tailWord_2413370 prefixEnd_2413370 1699888624336526628911 := by
  unfold tailWord_2413370
  simp only [CollatzResearch.WordTrace]
  refine ⟨22005708816695033906629391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58681890177853423751011709 22005708816695033906629391)
  ·
    refine ⟨33008563225042550859944087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22005708816695033906629391 33008563225042550859944087)
    ·
      refine ⟨49512844837563826289916131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33008563225042550859944087 49512844837563826289916131)
      ·
        refine ⟨74269267256345739434874197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49512844837563826289916131 74269267256345739434874197)
        ·
          refine ⟨1699888624336526628911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 74269267256345739434874197 1699888624336526628911)
          ·
            rfl

theorem cell23_2413370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 17].length) (baseStart_2413370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413370 prefixEnd_2413370 := by exact prefixLift 2413370
  have htrace : WordTrace (prefixWord ++ tailWord_2413370) baseStart_2413370 baseEnd_2413370 := by
    simpa [prefixWord, tailWord_2413370, baseEnd_2413370] using wordTrace_append hprefix tailTrace_2413370
  have hstable : (prefixWord ++ tailWord_2413370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413370).length < 2 ^ (prefixWord ++ tailWord_2413370).sum := by decide
  have hdescent : baseEnd_2413370 < baseStart_2413370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413375 : List Nat := [1, 1, 2, 2, 5, 3, 2, 2, 1, 1, 3]
def baseStart_2413375 : Nat := 118140960795 + 2413375 * 2 ^ 59
def prefixEnd_2413375 : Nat := 4983230072969 + 3 ^ 40 * 2413375 * 2
def baseEnd_2413375 : Nat := 1239221374544600392913597

theorem tailTrace_2413375 : CollatzResearch.WordTrace tailWord_2413375 prefixEnd_2413375 1239221374544600392913597 := by
  unfold tailWord_2413375
  simp only [CollatzResearch.WordTrace]
  refine ⟨88023017631762021480449579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58682011754508014320299719 88023017631762021480449579)
  ·
    refine ⟨132034526447643032220674369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88023017631762021480449579 132034526447643032220674369)
    ·
      refine ⟨99025894835732274165505777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132034526447643032220674369 99025894835732274165505777)
      ·
        refine ⟨74269421126799205624129333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99025894835732274165505777 74269421126799205624129333)
        ·
          refine ⟨6962758230637425527262125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74269421126799205624129333 6962758230637425527262125)
          ·
            refine ⟨2611034336489034572723297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6962758230637425527262125 2611034336489034572723297)
            ·
              refine ⟨1958275752366775929542473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611034336489034572723297 1958275752366775929542473)
              ·
                refine ⟨1468706814275081947156855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958275752366775929542473 1468706814275081947156855)
                ·
                  refine ⟨2203060221412622920735283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468706814275081947156855 2203060221412622920735283)
                  ·
                    refine ⟨3304590332118934381102925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2203060221412622920735283 3304590332118934381102925)
                    ·
                      refine ⟨1239221374544600392913597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3304590332118934381102925 1239221374544600392913597)
                      ·
                        rfl

theorem cell23_2413375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_2413375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413375 prefixEnd_2413375 := by exact prefixLift 2413375
  have htrace : WordTrace (prefixWord ++ tailWord_2413375) baseStart_2413375 baseEnd_2413375 := by
    simpa [prefixWord, tailWord_2413375, baseEnd_2413375] using wordTrace_append hprefix tailTrace_2413375
  have hstable : (prefixWord ++ tailWord_2413375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413375).length < 2 ^ (prefixWord ++ tailWord_2413375).sum := by decide
  have hdescent : baseEnd_2413375 < baseStart_2413375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413394 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_2413394 : Nat := 118140960795 + 2413394 * 2 ^ 59
def prefixEnd_2413394 : Nat := 4983230072969 + 3 ^ 40 * 2413394 * 2
def baseEnd_2413394 : Nat := 1239231130677035818576009

theorem tailTrace_2413394 : CollatzResearch.WordTrace tailWord_2413394 prefixEnd_2413394 1239231130677035818576009 := by
  unfold tailWord_2413394
  simp only [CollatzResearch.WordTrace]
  refine ⟨22005927654673296931347809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58682473745795458483594157 22005927654673296931347809)
  ·
    refine ⟨16504445741004972698510857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22005927654673296931347809 16504445741004972698510857)
    ·
      refine ⟨12378334305753729523883143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16504445741004972698510857 12378334305753729523883143)
      ·
        refine ⟨18567501458630594285824715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12378334305753729523883143 18567501458630594285824715)
        ·
          refine ⟨27851252187945891428737073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18567501458630594285824715 27851252187945891428737073)
          ·
            refine ⟨20888439140959418571552805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27851252187945891428737073 20888439140959418571552805)
            ·
              refine ⟨3916582338929890982166151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20888439140959418571552805 3916582338929890982166151)
              ·
                refine ⟨5874873508394836473249227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916582338929890982166151 5874873508394836473249227)
                ·
                  refine ⟨8812310262592254709873841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5874873508394836473249227 8812310262592254709873841)
                  ·
                    refine ⟨6609232696944191032405381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8812310262592254709873841 6609232696944191032405381)
                    ·
                      refine ⟨1239231130677035818576009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6609232696944191032405381 1239231130677035818576009)
                      ·
                        rfl

theorem cell23_2413394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_2413394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413394 prefixEnd_2413394 := by exact prefixLift 2413394
  have htrace : WordTrace (prefixWord ++ tailWord_2413394) baseStart_2413394 baseEnd_2413394 := by
    simpa [prefixWord, tailWord_2413394, baseEnd_2413394] using wordTrace_append hprefix tailTrace_2413394
  have hstable : (prefixWord ++ tailWord_2413394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413394).length < 2 ^ (prefixWord ++ tailWord_2413394).sum := by decide
  have hdescent : baseEnd_2413394 < baseStart_2413394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413415 : List Nat := [1, 1, 5, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_2413415 : Nat := 118140960795 + 2413415 * 2 ^ 59
def prefixEnd_2413415 : Nat := 4983230072969 + 3 ^ 40 * 2413415 * 2
def baseEnd_2413415 : Nat := 1239241913770780236413413

theorem tailTrace_2413415 : CollatzResearch.WordTrace tailWord_2413415 prefixEnd_2413415 1239241913770780236413413 := by
  unfold tailWord_2413415
  simp only [CollatzResearch.WordTrace]
  refine ⟨88024476551617108311905699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58682984367744738874603799 88024476551617108311905699)
  ·
    refine ⟨132036714827425662467858549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88024476551617108311905699 132036714827425662467858549)
    ·
      refine ⟨12378442015071155856361739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132036714827425662467858549 12378442015071155856361739)
      ·
        refine ⟨18567663022606733784542609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12378442015071155856361739 18567663022606733784542609)
        ·
          refine ⟨13925747266955050338406957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18567663022606733784542609 13925747266955050338406957)
          ·
            refine ⟨5222155225108143876902609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13925747266955050338406957 5222155225108143876902609)
            ·
              refine ⟨3916616418831107907676957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5222155225108143876902609 3916616418831107907676957)
              ·
                refine ⟨1468731157061665465378859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3916616418831107907676957 1468731157061665465378859)
                ·
                  refine ⟨2203096735592498198068289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468731157061665465378859 2203096735592498198068289)
                  ·
                    refine ⟨1652322551694373648551217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2203096735592498198068289 1652322551694373648551217)
                    ·
                      refine ⟨1239241913770780236413413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652322551694373648551217 1239241913770780236413413)
                      ·
                        rfl

theorem cell23_2413415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_2413415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413415 prefixEnd_2413415 := by exact prefixLift 2413415
  have htrace : WordTrace (prefixWord ++ tailWord_2413415) baseStart_2413415 baseEnd_2413415 := by
    simpa [prefixWord, tailWord_2413415, baseEnd_2413415] using wordTrace_append hprefix tailTrace_2413415
  have hstable : (prefixWord ++ tailWord_2413415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413415).length < 2 ^ (prefixWord ++ tailWord_2413415).sum := by decide
  have hdescent : baseEnd_2413415 < baseStart_2413415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413437 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_2413437 : Nat := 118140960795 + 2413437 * 2 ^ 59
def prefixEnd_2413437 : Nat := 4983230072969 + 3 ^ 40 * 2413437 * 2
def baseEnd_2413437 : Nat := 1239253210345179150338311

theorem tailTrace_2413437 : CollatzResearch.WordTrace tailWord_2413437 prefixEnd_2413437 1239253210345179150338311 := by
  unfold tailWord_2413437
  simp only [CollatzResearch.WordTrace]
  refine ⟨88025278957537406069206565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58683519305024937379471043 88025278957537406069206565)
  ·
    refine ⟨16504739804538263637976231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88025278957537406069206565 16504739804538263637976231)
    ·
      refine ⟨24757109706807395456964347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16504739804538263637976231 24757109706807395456964347)
      ·
        refine ⟨37135664560211093185446521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24757109706807395456964347 37135664560211093185446521)
        ·
          refine ⟨27851748420158319889084891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37135664560211093185446521 27851748420158319889084891)
          ·
            refine ⟨41777622630237479833627337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27851748420158319889084891 41777622630237479833627337)
            ·
              refine ⟨31333216972678109875220503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41777622630237479833627337 31333216972678109875220503)
              ·
                refine ⟨46999825459017164812830755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31333216972678109875220503 46999825459017164812830755)
                ·
                  refine ⟨70499738188525747219246133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46999825459017164812830755 70499738188525747219246133)
                  ·
                    refine ⟨6609350455174288801804325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70499738188525747219246133 6609350455174288801804325)
                    ·
                      refine ⟨1239253210345179150338311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6609350455174288801804325 1239253210345179150338311)
                      ·
                        rfl

theorem cell23_2413437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_2413437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413437 prefixEnd_2413437 := by exact prefixLift 2413437
  have htrace : WordTrace (prefixWord ++ tailWord_2413437) baseStart_2413437 baseEnd_2413437 := by
    simpa [prefixWord, tailWord_2413437, baseEnd_2413437] using wordTrace_append hprefix tailTrace_2413437
  have hstable : (prefixWord ++ tailWord_2413437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413437).length < 2 ^ (prefixWord ++ tailWord_2413437).sum := by decide
  have hdescent : baseEnd_2413437 < baseStart_2413437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413442 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2413442 : Nat := 118140960795 + 2413442 * 2 ^ 59
def prefixEnd_2413442 : Nat := 4983230072969 + 3 ^ 40 * 2413442 * 2
def baseEnd_2413442 : Nat := 413085259249483876925263

theorem tailTrace_2413442 : CollatzResearch.WordTrace tailWord_2413442 prefixEnd_2413442 413085259249483876925263 := by
  unfold tailWord_2413442
  simp only [CollatzResearch.WordTrace]
  refine ⟨22006365330629822980784645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58683640881679527948759053 22006365330629822980784645)
  ·
    refine ⟨4126193499493091808897121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22006365330629822980784645 4126193499493091808897121)
    ·
      refine ⟨3094645124619818856672841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4126193499493091808897121 3094645124619818856672841)
      ·
        refine ⟨2320983843464864142504631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3094645124619818856672841 2320983843464864142504631)
        ·
          refine ⟨3481475765197296213756947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320983843464864142504631 3481475765197296213756947)
          ·
            refine ⟨5222213647795944320635421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3481475765197296213756947 5222213647795944320635421)
            ·
              refine ⟨1958330117923479120238283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5222213647795944320635421 1958330117923479120238283)
              ·
                refine ⟨2937495176885218680357425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958330117923479120238283 2937495176885218680357425)
                ·
                  refine ⟨2203121382663914010268069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2937495176885218680357425 2203121382663914010268069)
                  ·
                    refine ⟨413085259249483876925263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2203121382663914010268069 413085259249483876925263)
                    ·
                      rfl

theorem cell23_2413442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2413442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413442 prefixEnd_2413442 := by exact prefixLift 2413442
  have htrace : WordTrace (prefixWord ++ tailWord_2413442) baseStart_2413442 baseEnd_2413442 := by
    simpa [prefixWord, tailWord_2413442, baseEnd_2413442] using wordTrace_append hprefix tailTrace_2413442
  have hstable : (prefixWord ++ tailWord_2413442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413442).length < 2 ^ (prefixWord ++ tailWord_2413442).sum := by decide
  have hdescent : baseEnd_2413442 < baseStart_2413442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413457 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_2413457 : Nat := 118140960795 + 2413457 * 2 ^ 59
def prefixEnd_2413457 : Nat := 4983230072969 + 3 ^ 40 * 2413457 * 2
def baseEnd_2413457 : Nat := 1239263479958269072088219

theorem tailTrace_2413457 : CollatzResearch.WordTrace tailWord_2413457 prefixEnd_2413457 1239263479958269072088219 := by
  unfold tailWord_2413457
  simp only [CollatzResearch.WordTrace]
  refine ⟨88026008417464949484934625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58684005611643299656623083 88026008417464949484934625)
  ·
    refine ⟨66019506313098712113700969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88026008417464949484934625 66019506313098712113700969)
    ·
      refine ⟨49514629734824034085275727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66019506313098712113700969 49514629734824034085275727)
      ·
        refine ⟨74271944602236051127913591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49514629734824034085275727 74271944602236051127913591)
        ·
          refine ⟨111407916903354076691870387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74271944602236051127913591 111407916903354076691870387)
          ·
            refine ⟨167111875355031115037805581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111407916903354076691870387 167111875355031115037805581)
            ·
              refine ⟨62666953258136668139177093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167111875355031115037805581 62666953258136668139177093)
              ·
                refine ⟨11750053735900625276095705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62666953258136668139177093 11750053735900625276095705)
                ·
                  refine ⟨8812540301925468957071779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11750053735900625276095705 8812540301925468957071779)
                  ·
                    refine ⟨13218810452888203435607669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8812540301925468957071779 13218810452888203435607669)
                    ·
                      refine ⟨1239263479958269072088219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13218810452888203435607669 1239263479958269072088219)
                      ·
                        rfl

theorem cell23_2413457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_2413457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413457 prefixEnd_2413457 := by exact prefixLift 2413457
  have htrace : WordTrace (prefixWord ++ tailWord_2413457) baseStart_2413457 baseEnd_2413457 := by
    simpa [prefixWord, tailWord_2413457, baseEnd_2413457] using wordTrace_append hprefix tailTrace_2413457
  have hstable : (prefixWord ++ tailWord_2413457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413457).length < 2 ^ (prefixWord ++ tailWord_2413457).sum := by decide
  have hdescent : baseEnd_2413457 < baseStart_2413457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413474 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2413474 : Nat := 118140960795 + 2413474 * 2 ^ 59
def prefixEnd_2413474 : Nat := 4983230072969 + 3 ^ 40 * 2413474 * 2
def baseEnd_2413474 : Nat := 1239272209129395505575641

theorem tailTrace_2413474 : CollatzResearch.WordTrace tailWord_2413474 prefixEnd_2413474 1239272209129395505575641 := by
  unfold tailWord_2413474
  simp only [CollatzResearch.WordTrace]
  refine ⟨22006657114600840347075869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58684418972268907592202317 22006657114600840347075869)
  ·
    refine ⟨8252496417975315130153451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22006657114600840347075869 8252496417975315130153451)
    ·
      refine ⟨12378744626962972695230177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8252496417975315130153451 12378744626962972695230177)
      ·
        refine ⟨9284058470222229521422633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12378744626962972695230177 9284058470222229521422633)
        ·
          refine ⟨6963043852666672141066975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9284058470222229521422633 6963043852666672141066975)
          ·
            refine ⟨10444565779000008211600463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6963043852666672141066975 10444565779000008211600463)
            ·
              refine ⟨15666848668500012317400695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10444565779000008211600463 15666848668500012317400695)
              ·
                refine ⟨23500273002750018476101043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15666848668500012317400695 23500273002750018476101043)
                ·
                  refine ⟨35250409504125027714151565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23500273002750018476101043 35250409504125027714151565)
                  ·
                    refine ⟨13218903564046885392806837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35250409504125027714151565 13218903564046885392806837)
                    ·
                      refine ⟨1239272209129395505575641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13218903564046885392806837 1239272209129395505575641)
                      ·
                        rfl

theorem cell23_2413474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2413474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413474 prefixEnd_2413474 := by exact prefixLift 2413474
  have htrace : WordTrace (prefixWord ++ tailWord_2413474) baseStart_2413474 baseEnd_2413474 := by
    simpa [prefixWord, tailWord_2413474, baseEnd_2413474] using wordTrace_append hprefix tailTrace_2413474
  have hstable : (prefixWord ++ tailWord_2413474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413474).length < 2 ^ (prefixWord ++ tailWord_2413474).sum := by decide
  have hdescent : baseEnd_2413474 < baseStart_2413474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413561 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 2, 4, 2]
def baseStart_2413561 : Nat := 118140960795 + 2413561 * 2 ^ 59
def prefixEnd_2413561 : Nat := 4983230072969 + 3 ^ 40 * 2413561 * 2
def baseEnd_2413561 : Nat := 1239316881946336665187741

theorem tailTrace_2413561 : CollatzResearch.WordTrace tailWord_2413561 prefixEnd_2413561 1239316881946336665187741 := by
  unfold tailWord_2413561
  simp only [CollatzResearch.WordTrace]
  refine ⟨88029801609088175246720537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58686534406058783497813691 88029801609088175246720537)
  ·
    refine ⟨66022351206816131435040403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88029801609088175246720537 66022351206816131435040403)
    ·
      refine ⟨99033526810224197152560605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66022351206816131435040403 99033526810224197152560605)
      ·
        refine ⟨37137572553834073932210227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99033526810224197152560605 37137572553834073932210227)
        ·
          refine ⟨55706358830751110898315341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37137572553834073932210227 55706358830751110898315341)
          ·
            refine ⟨20889884561531666586868253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55706358830751110898315341 20889884561531666586868253)
            ·
              refine ⟨7833706710574374970075595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20889884561531666586868253 7833706710574374970075595)
              ·
                refine ⟨11750560065861562455113393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7833706710574374970075595 11750560065861562455113393)
                ·
                  refine ⟨8812920049396171841335045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11750560065861562455113393 8812920049396171841335045)
                  ·
                    refine ⟨1652422509261782220250321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8812920049396171841335045 1652422509261782220250321)
                    ·
                      refine ⟨1239316881946336665187741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652422509261782220250321 1239316881946336665187741)
                      ·
                        rfl

theorem cell23_2413561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_2413561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413561 prefixEnd_2413561 := by exact prefixLift 2413561
  have htrace : WordTrace (prefixWord ++ tailWord_2413561) baseStart_2413561 baseEnd_2413561 := by
    simpa [prefixWord, tailWord_2413561, baseEnd_2413561] using wordTrace_append hprefix tailTrace_2413561
  have hstable : (prefixWord ++ tailWord_2413561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413561).length < 2 ^ (prefixWord ++ tailWord_2413561).sum := by decide
  have hdescent : baseEnd_2413561 < baseStart_2413561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413567 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 12]
def baseStart_2413567 : Nat := 118140960795 + 2413567 * 2 ^ 59
def prefixEnd_2413567 : Nat := 4983230072969 + 3 ^ 40 * 2413567 * 2
def baseEnd_2413567 : Nat := 137702218092251515745857

theorem tailTrace_2413567 : CollatzResearch.WordTrace tailWord_2413567 prefixEnd_2413567 137702218092251515745857 := by
  unfold tailWord_2413567
  simp only [CollatzResearch.WordTrace]
  refine ⟨88030020447066438271438955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58686680298044292180959303 88030020447066438271438955)
  ·
    refine ⟨132045030670599657407158433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88030020447066438271438955 132045030670599657407158433)
    ·
      refine ⟨99033773002949743055368825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132045030670599657407158433 99033773002949743055368825)
      ·
        refine ⟨74275329752212307291526619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99033773002949743055368825 74275329752212307291526619)
        ·
          refine ⟨111412994628318460937289929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74275329752212307291526619 111412994628318460937289929)
          ·
            refine ⟨83559745971238845702967447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111412994628318460937289929 83559745971238845702967447)
            ·
              refine ⟨125339618956858268554451171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83559745971238845702967447 125339618956858268554451171)
              ·
                refine ⟨188009428435287402831676757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125339618956858268554451171 188009428435287402831676757)
                ·
                  refine ⟨137702218092251515745857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 188009428435287402831676757 137702218092251515745857)
                  ·
                    rfl

theorem cell23_2413567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 12].length) (baseStart_2413567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413567 prefixEnd_2413567 := by exact prefixLift 2413567
  have htrace : WordTrace (prefixWord ++ tailWord_2413567) baseStart_2413567 baseEnd_2413567 := by
    simpa [prefixWord, tailWord_2413567, baseEnd_2413567] using wordTrace_append hprefix tailTrace_2413567
  have hstable : (prefixWord ++ tailWord_2413567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413567).length < 2 ^ (prefixWord ++ tailWord_2413567).sum := by decide
  have hdescent : baseEnd_2413567 < baseStart_2413567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413578 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_2413578 : Nat := 118140960795 + 2413578 * 2 ^ 59
def prefixEnd_2413578 : Nat := 4983230072969 + 3 ^ 40 * 2413578 * 2
def baseEnd_2413578 : Nat := 1239325611117463098675163

theorem tailTrace_2413578 : CollatzResearch.WordTrace tailWord_2413578 prefixEnd_2413578 1239325611117463098675163 := by
  unfold tailWord_2413578
  simp only [CollatzResearch.WordTrace]
  refine ⟨22007605412506646787522347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58686947766684391433392925 22007605412506646787522347)
  ·
    refine ⟨33011408118759970181283521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22007605412506646787522347 33011408118759970181283521)
    ·
      refine ⟨24758556089069977635962641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33011408118759970181283521 24758556089069977635962641)
      ·
        refine ⟨18568917066802483226971981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24758556089069977635962641 18568917066802483226971981)
        ·
          refine ⟨6963343900050931210114493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18568917066802483226971981 6963343900050931210114493)
          ·
            refine ⟨2611253962519099203792935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6963343900050931210114493 2611253962519099203792935)
            ·
              refine ⟨3916880943778648805689403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611253962519099203792935 3916880943778648805689403)
              ·
                refine ⟨5875321415667973208534105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916880943778648805689403 5875321415667973208534105)
                ·
                  refine ⟨4406491061750979906400579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5875321415667973208534105 4406491061750979906400579)
                  ·
                    refine ⟨6609736592626469859600869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4406491061750979906400579 6609736592626469859600869)
                    ·
                      refine ⟨1239325611117463098675163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6609736592626469859600869 1239325611117463098675163)
                      ·
                        rfl

theorem cell23_2413578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_2413578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413578 prefixEnd_2413578 := by exact prefixLift 2413578
  have htrace : WordTrace (prefixWord ++ tailWord_2413578) baseStart_2413578 baseEnd_2413578 := by
    simpa [prefixWord, tailWord_2413578, baseEnd_2413578] using wordTrace_append hprefix tailTrace_2413578
  have hstable : (prefixWord ++ tailWord_2413578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413578).length < 2 ^ (prefixWord ++ tailWord_2413578).sum := by decide
  have hdescent : baseEnd_2413578 < baseStart_2413578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413601 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 6]
def baseStart_2413601 : Nat := 118140960795 + 2413601 * 2 ^ 59
def prefixEnd_2413601 : Nat := 4983230072969 + 3 ^ 40 * 2413601 * 2
def baseEnd_2413601 : Nat := 137704157908057389854173

theorem tailTrace_2413601 : CollatzResearch.WordTrace tailWord_2413601 prefixEnd_2413601 137704157908057389854173 := by
  unfold tailWord_2413601
  simp only [CollatzResearch.WordTrace]
  refine ⟨88031260528943262078176657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58687507019295508052117771 88031260528943262078176657)
  ·
    refine ⟨66023445396707446558632493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88031260528943262078176657 66023445396707446558632493)
    ·
      refine ⟨24758792023765292459487185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66023445396707446558632493 24758792023765292459487185)
      ·
        refine ⟨18569094017823969344615389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24758792023765292459487185 18569094017823969344615389)
        ·
          refine ⟨6963410256683988504230771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18569094017823969344615389 6963410256683988504230771)
          ·
            refine ⟨10445115385025982756346157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6963410256683988504230771 10445115385025982756346157)
            ·
              refine ⟨3916918269384743533629809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10445115385025982756346157 3916918269384743533629809)
              ·
                refine ⟨2937688702038557650222357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3916918269384743533629809 2937688702038557650222357)
                ·
                  refine ⟨137704157908057389854173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2937688702038557650222357 137704157908057389854173)
                  ·
                    rfl

theorem cell23_2413601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 6].length) (baseStart_2413601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413601 prefixEnd_2413601 := by exact prefixLift 2413601
  have htrace : WordTrace (prefixWord ++ tailWord_2413601) baseStart_2413601 baseEnd_2413601 := by
    simpa [prefixWord, tailWord_2413601, baseEnd_2413601] using wordTrace_append hprefix tailTrace_2413601
  have hstable : (prefixWord ++ tailWord_2413601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413601).length < 2 ^ (prefixWord ++ tailWord_2413601).sum := by decide
  have hdescent : baseEnd_2413601 < baseStart_2413601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413628 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_2413628 : Nat := 118140960795 + 2413628 * 2 ^ 59
def prefixEnd_2413628 : Nat := 4983230072969 + 3 ^ 40 * 2413628 * 2
def baseEnd_2413628 : Nat := 1239351285150187903049933

theorem tailTrace_2413628 : CollatzResearch.WordTrace tailWord_2413628 prefixEnd_2413628 1239351285150187903049933 := by
  unfold tailWord_2413628
  simp only [CollatzResearch.WordTrace]
  refine ⟨44016122649922722844704769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58688163533230297126273025 44016122649922722844704769)
  ·
    refine ⟨33012091987442042133528577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44016122649922722844704769 33012091987442042133528577)
    ·
      refine ⟨24759068990581531600146433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33012091987442042133528577 24759068990581531600146433)
      ·
        refine ⟨18569301742936148700109825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24759068990581531600146433 18569301742936148700109825)
        ·
          refine ⟨13926976307202111525082369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18569301742936148700109825 13926976307202111525082369)
          ·
            refine ⟨10445232230401583643811777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13926976307202111525082369 10445232230401583643811777)
            ·
              refine ⟨7833924172801187732858833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10445232230401583643811777 7833924172801187732858833)
              ·
                refine ⟨5875443129600890799644125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7833924172801187732858833 5875443129600890799644125)
                ·
                  refine ⟨2203291173600334049866547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5875443129600890799644125 2203291173600334049866547)
                  ·
                    refine ⟨3304936760400501074799821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2203291173600334049866547 3304936760400501074799821)
                    ·
                      refine ⟨1239351285150187903049933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3304936760400501074799821 1239351285150187903049933)
                      ·
                        rfl

theorem cell23_2413628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_2413628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413628 prefixEnd_2413628 := by exact prefixLift 2413628
  have htrace : WordTrace (prefixWord ++ tailWord_2413628) baseStart_2413628 baseEnd_2413628 := by
    simpa [prefixWord, tailWord_2413628, baseEnd_2413628] using wordTrace_append hprefix tailTrace_2413628
  have hstable : (prefixWord ++ tailWord_2413628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413628).length < 2 ^ (prefixWord ++ tailWord_2413628).sum := by decide
  have hdescent : baseEnd_2413628 < baseStart_2413628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413644 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_2413644 : Nat := 118140960795 + 2413644 * 2 ^ 59
def prefixEnd_2413644 : Nat := 4983230072969 + 3 ^ 40 * 2413644 * 2
def baseEnd_2413644 : Nat := 413119833613553280149953

theorem tailTrace_2413644 : CollatzResearch.WordTrace tailWord_2413644 prefixEnd_2413644 413119833613553280149953 := by
  unfold tailWord_2413644
  simp only [CollatzResearch.WordTrace]
  refine ⟨44016414433893740210995993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58688552578524986947994657 44016414433893740210995993)
  ·
    refine ⟨33012310825420305158246995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44016414433893740210995993 33012310825420305158246995)
    ·
      refine ⟨49518466238130457737370493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33012310825420305158246995 49518466238130457737370493)
      ·
        refine ⟨18569424839298921651513935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49518466238130457737370493 18569424839298921651513935)
        ·
          refine ⟨27854137258948382477270903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18569424839298921651513935 27854137258948382477270903)
          ·
            refine ⟨41781205888422573715906355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27854137258948382477270903 41781205888422573715906355)
            ·
              refine ⟨62671808832633860573859533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41781205888422573715906355 62671808832633860573859533)
              ·
                refine ⟨23501928312237697715197325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62671808832633860573859533 23501928312237697715197325)
                ·
                  refine ⟨8813223117089136643198997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23501928312237697715197325 8813223117089136643198997)
                  ·
                    refine ⟨413119833613553280149953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8813223117089136643198997 413119833613553280149953)
                    ·
                      rfl

theorem cell23_2413644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_2413644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413644 prefixEnd_2413644 := by exact prefixLift 2413644
  have htrace : WordTrace (prefixWord ++ tailWord_2413644) baseStart_2413644 baseEnd_2413644 := by
    simpa [prefixWord, tailWord_2413644, baseEnd_2413644] using wordTrace_append hprefix tailTrace_2413644
  have hstable : (prefixWord ++ tailWord_2413644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413644).length < 2 ^ (prefixWord ++ tailWord_2413644).sum := by decide
  have hdescent : baseEnd_2413644 < baseStart_2413644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413664 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2413664 : Nat := 118140960795 + 2413664 * 2 ^ 59
def prefixEnd_2413664 : Nat := 4983230072969 + 3 ^ 40 * 2413664 * 2
def baseEnd_2413664 : Nat := 1239369770453749762199767

theorem tailTrace_2413664 : CollatzResearch.WordTrace tailWord_2413664 prefixEnd_2413664 1239369770453749762199767 := by
  unfold tailWord_2413664
  simp only [CollatzResearch.WordTrace]
  refine ⟨44016779163857511918860023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58689038885143349225146697 44016779163857511918860023)
  ·
    refine ⟨66025168745786267878290035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44016779163857511918860023 66025168745786267878290035)
    ·
      refine ⟨99037753118679401817435053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66025168745786267878290035 99037753118679401817435053)
      ·
        refine ⟨37139157419504775681538145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99037753118679401817435053 37139157419504775681538145)
        ·
          refine ⟨27854368064628581761153609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37139157419504775681538145 27854368064628581761153609)
          ·
            refine ⟨20890776048471436320865207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27854368064628581761153609 20890776048471436320865207)
            ·
              refine ⟨31336164072707154481297811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20890776048471436320865207 31336164072707154481297811)
              ·
                refine ⟨47004246109060731721946717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31336164072707154481297811 47004246109060731721946717)
                ·
                  refine ⟨17626592290897774395730019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47004246109060731721946717 17626592290897774395730019)
                  ·
                    refine ⟨26439888436346661593595029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17626592290897774395730019 26439888436346661593595029)
                    ·
                      refine ⟨1239369770453749762199767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26439888436346661593595029 1239369770453749762199767)
                      ·
                        rfl

theorem cell23_2413664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2413664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413664 prefixEnd_2413664 := by exact prefixLift 2413664
  have htrace : WordTrace (prefixWord ++ tailWord_2413664) baseStart_2413664 baseEnd_2413664 := by
    simpa [prefixWord, tailWord_2413664, baseEnd_2413664] using wordTrace_append hprefix tailTrace_2413664
  have hstable : (prefixWord ++ tailWord_2413664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413664).length < 2 ^ (prefixWord ++ tailWord_2413664).sum := by decide
  have hdescent : baseEnd_2413664 < baseStart_2413664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413671 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2413671 : Nat := 118140960795 + 2413671 * 2 ^ 59
def prefixEnd_2413671 : Nat := 4983230072969 + 3 ^ 40 * 2413671 * 2
def baseEnd_2413671 : Nat := 1239373364818331234812235

theorem tailTrace_2413671 : CollatzResearch.WordTrace tailWord_2413671 prefixEnd_2413671 1239373364818331234812235 := by
  unfold tailWord_2413671
  simp only [CollatzResearch.WordTrace]
  refine ⟨88033813638689664033224867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58689209092459776022149911 88033813638689664033224867)
  ·
    refine ⟨132050720458034496049837301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88033813638689664033224867 132050720458034496049837301)
    ·
      refine ⟨12379755042940734004672247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132050720458034496049837301 12379755042940734004672247)
      ·
        refine ⟨18569632564411101007008371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12379755042940734004672247 18569632564411101007008371)
        ·
          refine ⟨27854448846616651510512557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18569632564411101007008371 27854448846616651510512557)
          ·
            refine ⟨10445418317481244316442209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27854448846616651510512557 10445418317481244316442209)
            ·
              refine ⟨7834063738110933237331657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10445418317481244316442209 7834063738110933237331657)
              ·
                refine ⟨5875547803583199927998743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7834063738110933237331657 5875547803583199927998743)
                ·
                  refine ⟨8813321705374799891998115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5875547803583199927998743 8813321705374799891998115)
                  ·
                    refine ⟨13219982558062199837997173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8813321705374799891998115 13219982558062199837997173)
                    ·
                      refine ⟨1239373364818331234812235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13219982558062199837997173 1239373364818331234812235)
                      ·
                        rfl

theorem cell23_2413671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2413671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413671 prefixEnd_2413671 := by exact prefixLift 2413671
  have htrace : WordTrace (prefixWord ++ tailWord_2413671) baseStart_2413671 baseEnd_2413671 := by
    simpa [prefixWord, tailWord_2413671, baseEnd_2413671] using wordTrace_append hprefix tailTrace_2413671
  have hstable : (prefixWord ++ tailWord_2413671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413671).length < 2 ^ (prefixWord ++ tailWord_2413671).sum := by decide
  have hdescent : baseEnd_2413671 < baseStart_2413671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413685 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2413685 : Nat := 118140960795 + 2413685 * 2 ^ 59
def prefixEnd_2413685 : Nat := 4983230072969 + 3 ^ 40 * 2413685 * 2
def baseEnd_2413685 : Nat := 1239380553547494180037171

theorem tailTrace_2413685 : CollatzResearch.WordTrace tailWord_2413685 prefixEnd_2413685 1239380553547494180037171 := by
  unfold tailWord_2413685
  simp only [CollatzResearch.WordTrace]
  refine ⟨88034324260638944424234509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58689549507092629616156339 88034324260638944424234509)
  ·
    refine ⟨33012871597739604159087941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88034324260638944424234509 33012871597739604159087941)
    ·
      refine ⟨6189913424576175779828989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33012871597739604159087941 6189913424576175779828989)
      ·
        refine ⟨2321217534216065917435871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6189913424576175779828989 2321217534216065917435871)
        ·
          refine ⟨3481826301324098876153807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2321217534216065917435871 3481826301324098876153807)
          ·
            refine ⟨5222739451986148314230711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3481826301324098876153807 5222739451986148314230711)
            ·
              refine ⟨7834109177979222471346067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5222739451986148314230711 7834109177979222471346067)
              ·
                refine ⟨11751163766968833707019101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834109177979222471346067 11751163766968833707019101)
                ·
                  refine ⟨4406686412613312640132163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11751163766968833707019101 4406686412613312640132163)
                  ·
                    refine ⟨6610029618919968960198245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4406686412613312640132163 6610029618919968960198245)
                    ·
                      refine ⟨1239380553547494180037171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6610029618919968960198245 1239380553547494180037171)
                      ·
                        rfl

theorem cell23_2413685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2413685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413685 prefixEnd_2413685 := by exact prefixLift 2413685
  have htrace : WordTrace (prefixWord ++ tailWord_2413685) baseStart_2413685 baseEnd_2413685 := by
    simpa [prefixWord, tailWord_2413685, baseEnd_2413685] using wordTrace_append hprefix tailTrace_2413685
  have hstable : (prefixWord ++ tailWord_2413685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413685).length < 2 ^ (prefixWord ++ tailWord_2413685).sum := by decide
  have hdescent : baseEnd_2413685 < baseStart_2413685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413688 : List Nat := [2, 1, 2, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_2413688 : Nat := 118140960795 + 2413688 * 2 ^ 59
def prefixEnd_2413688 : Nat := 4983230072969 + 3 ^ 40 * 2413688 * 2
def baseEnd_2413688 : Nat := 1239382093989457668299657

theorem tailTrace_2413688 : CollatzResearch.WordTrace tailWord_2413688 prefixEnd_2413688 1239382093989457668299657 := by
  unfold tailWord_2413688
  simp only [CollatzResearch.WordTrace]
  refine ⟨44017216839814037968296859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58689622453085383957729145 44017216839814037968296859)
  ·
    refine ⟨66025825259721056952445289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44017216839814037968296859 66025825259721056952445289)
    ·
      refine ⟨49519368944790792714333967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66025825259721056952445289 49519368944790792714333967)
      ·
        refine ⟨74279053417186189071500951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49519368944790792714333967 74279053417186189071500951)
        ·
          refine ⟨111418580125779283607251427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74279053417186189071500951 111418580125779283607251427)
          ·
            refine ⟨167127870188668925410877141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111418580125779283607251427 167127870188668925410877141)
            ·
              refine ⟨3917059457546927939317433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 167127870188668925410877141 3917059457546927939317433)
              ·
                refine ⟨2937794593160195954488075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3917059457546927939317433 2937794593160195954488075)
                ·
                  refine ⟨4406691889740293931732113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937794593160195954488075 4406691889740293931732113)
                  ·
                    refine ⟨3305018917305220448799085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4406691889740293931732113 3305018917305220448799085)
                    ·
                      refine ⟨1239382093989457668299657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3305018917305220448799085 1239382093989457668299657)
                      ·
                        rfl

theorem cell23_2413688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_2413688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413688 prefixEnd_2413688 := by exact prefixLift 2413688
  have htrace : WordTrace (prefixWord ++ tailWord_2413688) baseStart_2413688 baseEnd_2413688 := by
    simpa [prefixWord, tailWord_2413688, baseEnd_2413688] using wordTrace_append hprefix tailTrace_2413688
  have hstable : (prefixWord ++ tailWord_2413688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413688).length < 2 ^ (prefixWord ++ tailWord_2413688).sum := by decide
  have hdescent : baseEnd_2413688 < baseStart_2413688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413705 : List Nat := [1, 2, 1, 1, 4, 4, 3, 1, 1, 2, 3]
def baseStart_2413705 : Nat := 118140960795 + 2413705 * 2 ^ 59
def prefixEnd_2413705 : Nat := 4983230072969 + 3 ^ 40 * 2413705 * 2
def baseEnd_2413705 : Nat := 1239390823160584101787079

theorem tailTrace_2413705 : CollatzResearch.WordTrace tailWord_2413705 prefixEnd_2413705 1239390823160584101787079 := by
  unfold tailWord_2413705
  simp only [CollatzResearch.WordTrace]
  refine ⟨88035053720566487839962569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58690035813710991893308379 88035053720566487839962569)
  ·
    refine ⟨66026290290424865879971927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88035053720566487839962569 66026290290424865879971927)
    ·
      refine ⟨99039435435637298819957891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66026290290424865879971927 99039435435637298819957891)
      ·
        refine ⟨148559153153455948229936837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99039435435637298819957891 148559153153455948229936837)
        ·
          refine ⟨27854841216272990293113157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148559153153455948229936837 27854841216272990293113157)
          ·
            refine ⟨5222782728051185679958717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27854841216272990293113157 5222782728051185679958717)
            ·
              refine ⟨1958543523019194629984519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5222782728051185679958717 1958543523019194629984519)
              ·
                refine ⟨2937815284528791944976779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958543523019194629984519 2937815284528791944976779)
                ·
                  refine ⟨4406722926793187917465169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937815284528791944976779 4406722926793187917465169)
                  ·
                    refine ⟨3305042195094890938098877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4406722926793187917465169 3305042195094890938098877)
                    ·
                      refine ⟨1239390823160584101787079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3305042195094890938098877 1239390823160584101787079)
                      ·
                        rfl

theorem cell23_2413705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 1, 2, 3].length) (baseStart_2413705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413705 prefixEnd_2413705 := by exact prefixLift 2413705
  have htrace : WordTrace (prefixWord ++ tailWord_2413705) baseStart_2413705 baseEnd_2413705 := by
    simpa [prefixWord, tailWord_2413705, baseEnd_2413705] using wordTrace_append hprefix tailTrace_2413705
  have hstable : (prefixWord ++ tailWord_2413705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413705).length < 2 ^ (prefixWord ++ tailWord_2413705).sum := by decide
  have hdescent : baseEnd_2413705 < baseStart_2413705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413711 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 4, 7, 2]
def baseStart_2413711 : Nat := 118140960795 + 2413711 * 2 ^ 59
def prefixEnd_2413711 : Nat := 4983230072969 + 3 ^ 40 * 2413711 * 2
def baseEnd_2413711 : Nat := 1239393904044511078312051

theorem tailTrace_2413711 : CollatzResearch.WordTrace tailWord_2413711 prefixEnd_2413711 1239393904044511078312051 := by
  unfold tailWord_2413711
  simp only [CollatzResearch.WordTrace]
  refine ⟨88035272558544750864680987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58690181705696500576453991 88035272558544750864680987)
  ·
    refine ⟨132052908837817126297021481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88035272558544750864680987 132052908837817126297021481)
    ·
      refine ⟨99039681628362844722766111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132052908837817126297021481 99039681628362844722766111)
      ·
        refine ⟨148559522442544267084149167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99039681628362844722766111 148559522442544267084149167)
        ·
          refine ⟨222839283663816400626223751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148559522442544267084149167 222839283663816400626223751)
          ·
            refine ⟨334258925495724600939335627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222839283663816400626223751 334258925495724600939335627)
            ·
              refine ⟨501388388243586901409003441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334258925495724600939335627 501388388243586901409003441)
              ·
                refine ⟨376041291182690176056752581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501388388243586901409003441 376041291182690176056752581)
                ·
                  refine ⟨70507742096754408010641109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376041291182690176056752581 70507742096754408010641109)
                  ·
                    refine ⟨1652525205392681437749401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 70507742096754408010641109 1652525205392681437749401)
                    ·
                      refine ⟨1239393904044511078312051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652525205392681437749401 1239393904044511078312051)
                      ·
                        rfl

theorem cell23_2413711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 7, 2].length) (baseStart_2413711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413711 prefixEnd_2413711 := by exact prefixLift 2413711
  have htrace : WordTrace (prefixWord ++ tailWord_2413711) baseStart_2413711 baseEnd_2413711 := by
    simpa [prefixWord, tailWord_2413711, baseEnd_2413711] using wordTrace_append hprefix tailTrace_2413711
  have hstable : (prefixWord ++ tailWord_2413711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413711).length < 2 ^ (prefixWord ++ tailWord_2413711).sum := by decide
  have hdescent : baseEnd_2413711 < baseStart_2413711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413719 : List Nat := [1, 1, 3, 3, 3, 1, 4, 2, 1, 2, 2]
def baseStart_2413719 : Nat := 118140960795 + 2413719 * 2 ^ 59
def prefixEnd_2413719 : Nat := 4983230072969 + 3 ^ 40 * 2413719 * 2
def baseEnd_2413719 : Nat := 1239398011889747047012015

theorem tailTrace_2413719 : CollatzResearch.WordTrace tailWord_2413719 prefixEnd_2413719 1239398011889747047012015 := by
  unfold tailWord_2413719
  simp only [CollatzResearch.WordTrace]
  refine ⟨88035564342515768230972211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58690376228343845487314807 88035564342515768230972211)
  ·
    refine ⟨132053346513773652346458317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88035564342515768230972211 132053346513773652346458317)
    ·
      refine ⟨49520004942665119629921869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132053346513773652346458317 49520004942665119629921869)
      ·
        refine ⟨18570001853499419861220701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49520004942665119629921869 18570001853499419861220701)
        ·
          refine ⟨6963750695062282447957763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18570001853499419861220701 6963750695062282447957763)
          ·
            refine ⟨10445626042593423671936645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6963750695062282447957763 10445626042593423671936645)
            ·
              refine ⟨1958554882986266938488121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10445626042593423671936645 1958554882986266938488121)
              ·
                refine ⟨1468916162239700203866091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958554882986266938488121 1468916162239700203866091)
                ·
                  refine ⟨2203374243359550305799137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468916162239700203866091 2203374243359550305799137)
                  ·
                    refine ⟨1652530682519662729349353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2203374243359550305799137 1652530682519662729349353)
                    ·
                      refine ⟨1239398011889747047012015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652530682519662729349353 1239398011889747047012015)
                      ·
                        rfl

theorem cell23_2413719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_2413719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413719 prefixEnd_2413719 := by exact prefixLift 2413719
  have htrace : WordTrace (prefixWord ++ tailWord_2413719) baseStart_2413719 baseEnd_2413719 := by
    simpa [prefixWord, tailWord_2413719, baseEnd_2413719] using wordTrace_append hprefix tailTrace_2413719
  have hstable : (prefixWord ++ tailWord_2413719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413719).length < 2 ^ (prefixWord ++ tailWord_2413719).sum := by decide
  have hdescent : baseEnd_2413719 < baseStart_2413719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413728 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 5, 3, 2]
def baseStart_2413728 : Nat := 118140960795 + 2413728 * 2 ^ 59
def prefixEnd_2413728 : Nat := 4983230072969 + 3 ^ 40 * 2413728 * 2
def baseEnd_2413728 : Nat := 1239402633215637511799473

theorem tailTrace_2413728 : CollatzResearch.WordTrace tailWord_2413728 prefixEnd_2413728 1239402633215637511799473 := by
  unfold tailWord_2413728
  simp only [CollatzResearch.WordTrace]
  refine ⟨44017946299741581384024919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58690595066322108512033225 44017946299741581384024919)
  ·
    refine ⟨66026919449612372076037379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44017946299741581384024919 66026919449612372076037379)
    ·
      refine ⟨99040379174418558114056069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66026919449612372076037379 99040379174418558114056069)
      ·
        refine ⟨18570071095203479646385513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99040379174418558114056069 18570071095203479646385513)
        ·
          refine ⟨13927553321402609734789135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18570071095203479646385513 13927553321402609734789135)
          ·
            refine ⟨20891329982103914602183703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13927553321402609734789135 20891329982103914602183703)
            ·
              refine ⟨31336994973155871903275555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20891329982103914602183703 31336994973155871903275555)
              ·
                refine ⟨47005492459733807854913333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31336994973155871903275555 47005492459733807854913333)
                ·
                  refine ⟨4406764918100044486398125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47005492459733807854913333 4406764918100044486398125)
                  ·
                    refine ⟨1652536844287516682399297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4406764918100044486398125 1652536844287516682399297)
                    ·
                      refine ⟨1239402633215637511799473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652536844287516682399297 1239402633215637511799473)
                      ·
                        rfl

theorem cell23_2413728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_2413728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413728 prefixEnd_2413728 := by exact prefixLift 2413728
  have htrace : WordTrace (prefixWord ++ tailWord_2413728) baseStart_2413728 baseEnd_2413728 := by
    simpa [prefixWord, tailWord_2413728, baseEnd_2413728] using wordTrace_append hprefix tailTrace_2413728
  have hstable : (prefixWord ++ tailWord_2413728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413728).length < 2 ^ (prefixWord ++ tailWord_2413728).sum := by decide
  have hdescent : baseEnd_2413728 < baseStart_2413728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413735 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2413735 : Nat := 118140960795 + 2413735 * 2 ^ 59
def prefixEnd_2413735 : Nat := 4983230072969 + 3 ^ 40 * 2413735 * 2
def baseEnd_2413735 : Nat := 1239406227580218984411941

theorem tailTrace_2413735 : CollatzResearch.WordTrace tailWord_2413735 prefixEnd_2413735 1239406227580218984411941 := by
  unfold tailWord_2413735
  simp only [CollatzResearch.WordTrace]
  refine ⟨88036147910457802963554659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58690765273638535309036439 88036147910457802963554659)
  ·
    refine ⟨132054221865686704445331989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88036147910457802963554659 132054221865686704445331989)
    ·
      refine ⟨6190041649954064270874937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132054221865686704445331989 6190041649954064270874937)
      ·
        refine ⟨4642531237465548203156203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6190041649954064270874937 4642531237465548203156203)
        ·
          refine ⟨6963796856198322304734305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4642531237465548203156203 6963796856198322304734305)
          ·
            refine ⟨5222847642148741728550729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6963796856198322304734305 5222847642148741728550729)
            ·
              refine ⟨3917135731611556296413047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5222847642148741728550729 3917135731611556296413047)
              ·
                refine ⟨5875703597417334444619571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3917135731611556296413047 5875703597417334444619571)
                ·
                  refine ⟨8813555396126001666929357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5875703597417334444619571 8813555396126001666929357)
                  ·
                    refine ⟨3305083273547250625098509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8813555396126001666929357 3305083273547250625098509)
                    ·
                      refine ⟨1239406227580218984411941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3305083273547250625098509 1239406227580218984411941)
                      ·
                        rfl

theorem cell23_2413735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2413735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413735 prefixEnd_2413735 := by exact prefixLift 2413735
  have htrace : WordTrace (prefixWord ++ tailWord_2413735) baseStart_2413735 baseEnd_2413735 := by
    simpa [prefixWord, tailWord_2413735, baseEnd_2413735] using wordTrace_append hprefix tailTrace_2413735
  have hstable : (prefixWord ++ tailWord_2413735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413735).length < 2 ^ (prefixWord ++ tailWord_2413735).sum := by decide
  have hdescent : baseEnd_2413735 < baseStart_2413735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413745 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2413745 : Nat := 118140960795 + 2413745 * 2 ^ 59
def prefixEnd_2413745 : Nat := 4983230072969 + 3 ^ 40 * 2413745 * 2
def baseEnd_2413745 : Nat := 1239411362386763945286895

theorem tailTrace_2413745 : CollatzResearch.WordTrace tailWord_2413745 prefixEnd_2413745 1239411362386763945286895 := by
  unfold tailWord_2413745
  simp only [CollatzResearch.WordTrace]
  refine ⟨88036512640421574671418689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58691008426947716447612459 88036512640421574671418689)
  ·
    refine ⟨66027384480316181003564017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88036512640421574671418689 66027384480316181003564017)
    ·
      refine ⟨49520538360237135752673013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66027384480316181003564017 49520538360237135752673013)
      ·
        refine ⟨4642550471272231476813095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49520538360237135752673013 4642550471272231476813095)
        ·
          refine ⟨6963825706908347215219643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4642550471272231476813095 6963825706908347215219643)
          ·
            refine ⟨10445738560362520822829465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6963825706908347215219643 10445738560362520822829465)
            ·
              refine ⟨7834303920271890617122099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10445738560362520822829465 7834303920271890617122099)
              ·
                refine ⟨11751455880407835925683149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834303920271890617122099 11751455880407835925683149)
                ·
                  refine ⟨4406795955152938472131181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11751455880407835925683149 4406795955152938472131181)
                  ·
                    refine ⟨1652548483182351927049193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4406795955152938472131181 1652548483182351927049193)
                    ·
                      refine ⟨1239411362386763945286895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652548483182351927049193 1239411362386763945286895)
                      ·
                        rfl

theorem cell23_2413745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2413745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413745 prefixEnd_2413745 := by exact prefixLift 2413745
  have htrace : WordTrace (prefixWord ++ tailWord_2413745) baseStart_2413745 baseEnd_2413745 := by
    simpa [prefixWord, tailWord_2413745, baseEnd_2413745] using wordTrace_append hprefix tailTrace_2413745
  have hstable : (prefixWord ++ tailWord_2413745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413745).length < 2 ^ (prefixWord ++ tailWord_2413745).sum := by decide
  have hdescent : baseEnd_2413745 < baseStart_2413745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413775 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 2, 2, 2]
def baseStart_2413775 : Nat := 118140960795 + 2413775 * 2 ^ 59
def prefixEnd_2413775 : Nat := 4983230072969 + 3 ^ 40 * 2413775 * 2
def baseEnd_2413775 : Nat := 1239426766806398827911757

theorem tailTrace_2413775 : CollatzResearch.WordTrace tailWord_2413775 prefixEnd_2413775 1239426766806398827911757 := by
  unfold tailWord_2413775
  simp only [CollatzResearch.WordTrace]
  refine ⟨88037606830312889795010779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58691737886875259863340519 88037606830312889795010779)
  ·
    refine ⟨132056410245469334692516169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88037606830312889795010779 132056410245469334692516169)
    ·
      refine ⟨99042307684102001019387127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132056410245469334692516169 99042307684102001019387127)
      ·
        refine ⟨148563461526153001529080691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99042307684102001019387127 148563461526153001529080691)
        ·
          refine ⟨222845192289229502293621037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148563461526153001529080691 222845192289229502293621037)
          ·
            refine ⟨83566947108461063360107889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222845192289229502293621037 83566947108461063360107889)
            ·
              refine ⟨62675210331345797520080917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83566947108461063360107889 62675210331345797520080917)
              ·
                refine ⟨2937900484281834258753793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62675210331345797520080917 2937900484281834258753793)
                ·
                  refine ⟨2203425363211375694065345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2937900484281834258753793 2203425363211375694065345)
                  ·
                    refine ⟨1652569022408531770549009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2203425363211375694065345 1652569022408531770549009)
                    ·
                      refine ⟨1239426766806398827911757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652569022408531770549009 1239426766806398827911757)
                      ·
                        rfl

theorem cell23_2413775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 2, 2, 2].length) (baseStart_2413775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413775 prefixEnd_2413775 := by exact prefixLift 2413775
  have htrace : WordTrace (prefixWord ++ tailWord_2413775) baseStart_2413775 baseEnd_2413775 := by
    simpa [prefixWord, tailWord_2413775, baseEnd_2413775] using wordTrace_append hprefix tailTrace_2413775
  have hstable : (prefixWord ++ tailWord_2413775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413775).length < 2 ^ (prefixWord ++ tailWord_2413775).sum := by decide
  have hdescent : baseEnd_2413775 < baseStart_2413775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413811 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 1, 7]
def baseStart_2413811 : Nat := 118140960795 + 2413811 * 2 ^ 59
def prefixEnd_2413811 : Nat := 4983230072969 + 3 ^ 40 * 2413811 * 2
def baseEnd_2413811 : Nat := 413148417369986895687197

theorem tailTrace_2413811 : CollatzResearch.WordTrace tailWord_2413811 prefixEnd_2413811 413148417369986895687197 := by
  unfold tailWord_2413811
  simp only [CollatzResearch.WordTrace]
  refine ⟨88038919858182467943321287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58692613238788311962214191 88038919858182467943321287)
  ·
    refine ⟨132058379787273701914981931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88038919858182467943321287 132058379787273701914981931)
    ·
      refine ⟨198087569680910552872472897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132058379787273701914981931 198087569680910552872472897)
      ·
        refine ⟨148565677260682914654354673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198087569680910552872472897 148565677260682914654354673)
        ·
          refine ⟨111424257945512185990766005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148565677260682914654354673 111424257945512185990766005)
          ·
            refine ⟨10446024182391767436634313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111424257945512185990766005 10446024182391767436634313)
            ·
              refine ⟨7834518136793825577475735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10446024182391767436634313 7834518136793825577475735)
              ·
                refine ⟨11751777205190738366213603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834518136793825577475735 11751777205190738366213603)
                ·
                  refine ⟨17627665807786107549320405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11751777205190738366213603 17627665807786107549320405)
                  ·
                    refine ⟨413148417369986895687197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17627665807786107549320405 413148417369986895687197)
                    ·
                      rfl

theorem cell23_2413811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 7].length) (baseStart_2413811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413811 prefixEnd_2413811 := by exact prefixLift 2413811
  have htrace : WordTrace (prefixWord ++ tailWord_2413811) baseStart_2413811 baseEnd_2413811 := by
    simpa [prefixWord, tailWord_2413811, baseEnd_2413811] using wordTrace_append hprefix tailTrace_2413811
  have hstable : (prefixWord ++ tailWord_2413811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413811).length < 2 ^ (prefixWord ++ tailWord_2413811).sum := by decide
  have hdescent : baseEnd_2413811 < baseStart_2413811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413828 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_2413828 : Nat := 118140960795 + 2413828 * 2 ^ 59
def prefixEnd_2413828 : Nat := 4983230072969 + 3 ^ 40 * 2413828 * 2
def baseEnd_2413828 : Nat := 413151327093695706849671

theorem tailTrace_2413828 : CollatzResearch.WordTrace tailWord_2413828 prefixEnd_2413828 413151327093695706849671 := by
  unfold tailWord_2413828
  simp only [CollatzResearch.WordTrace]
  refine ⟨44019769949560439923345069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58693026599413919897793425 44019769949560439923345069)
  ·
    refine ⟨16507413731085164971254401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44019769949560439923345069 16507413731085164971254401)
    ·
      refine ⟨12380560298313873728440801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16507413731085164971254401 12380560298313873728440801)
      ·
        refine ⟨9285420223735405296330601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12380560298313873728440801 9285420223735405296330601)
        ·
          refine ⟨6964065167801553972247951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9285420223735405296330601 6964065167801553972247951)
          ·
            refine ⟨10446097751702330958371927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6964065167801553972247951 10446097751702330958371927)
            ·
              refine ⟨15669146627553496437557891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10446097751702330958371927 15669146627553496437557891)
              ·
                refine ⟨23503719941330244656336837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15669146627553496437557891 23503719941330244656336837)
                ·
                  refine ⟨4406947488999420873063157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23503719941330244656336837 4406947488999420873063157)
                  ·
                    refine ⟨413151327093695706849671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4406947488999420873063157 413151327093695706849671)
                    ·
                      rfl

theorem cell23_2413828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_2413828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413828 prefixEnd_2413828 := by exact prefixLift 2413828
  have htrace : WordTrace (prefixWord ++ tailWord_2413828) baseStart_2413828 baseEnd_2413828 := by
    simpa [prefixWord, tailWord_2413828, baseEnd_2413828] using wordTrace_append hprefix tailTrace_2413828
  have hstable : (prefixWord ++ tailWord_2413828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413828).length < 2 ^ (prefixWord ++ tailWord_2413828).sum := by decide
  have hdescent : baseEnd_2413828 < baseStart_2413828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413832 : List Nat := [2, 1, 3, 2, 4, 1, 3, 2, 5]
def baseStart_2413832 : Nat := 118140960795 + 2413832 * 2 ^ 59
def prefixEnd_2413832 : Nat := 4983230072969 + 3 ^ 40 * 2413832 * 2
def baseEnd_2413832 : Nat := 137717337244856122766555

theorem tailTrace_2413832 : CollatzResearch.WordTrace tailWord_2413832 prefixEnd_2413832 137717337244856122766555 := by
  unfold tailWord_2413832
  simp only [CollatzResearch.WordTrace]
  refine ⟨44019842895553194264917875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58693123860737592353223833 44019842895553194264917875)
  ·
    refine ⟨66029764343329791397376813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44019842895553194264917875 66029764343329791397376813)
    ·
      refine ⟨24761161628748671774016305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66029764343329791397376813 24761161628748671774016305)
      ·
        refine ⟨18570871221561503830512229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24761161628748671774016305 18570871221561503830512229)
        ·
          refine ⟨3482038354042781968221043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18570871221561503830512229 3482038354042781968221043)
          ·
            refine ⟨5223057531064172952331565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3482038354042781968221043 5223057531064172952331565)
            ·
              refine ⟨1958646574149064857124337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5223057531064172952331565 1958646574149064857124337)
              ·
                refine ⟨1468984930611798642843253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958646574149064857124337 1468984930611798642843253)
                ·
                  refine ⟨137717337244856122766555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1468984930611798642843253 137717337244856122766555)
                  ·
                    rfl

theorem cell23_2413832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 5].length) (baseStart_2413832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413832 prefixEnd_2413832 := by exact prefixLift 2413832
  have htrace : WordTrace (prefixWord ++ tailWord_2413832) baseStart_2413832 baseEnd_2413832 := by
    simpa [prefixWord, tailWord_2413832, baseEnd_2413832] using wordTrace_append hprefix tailTrace_2413832
  have hstable : (prefixWord ++ tailWord_2413832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413832).length < 2 ^ (prefixWord ++ tailWord_2413832).sum := by decide
  have hdescent : baseEnd_2413832 < baseStart_2413832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413838 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2413838 : Nat := 118140960795 + 2413838 * 2 ^ 59
def prefixEnd_2413838 : Nat := 4983230072969 + 3 ^ 40 * 2413838 * 2
def baseEnd_2413838 : Nat := 1239459116087632081423967

theorem tailTrace_2413838 : CollatzResearch.WordTrace tailWord_2413838 prefixEnd_2413838 1239459116087632081423967 := by
  unfold tailWord_2413838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11004988078635581444319271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58693269752723101036369445 11004988078635581444319271)
  ·
    refine ⟨16507482117953372166478907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11004988078635581444319271 16507482117953372166478907)
    ·
      refine ⟨24761223176930058249718361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16507482117953372166478907 24761223176930058249718361)
      ·
        refine ⟨18570917382697543687288771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24761223176930058249718361 18570917382697543687288771)
        ·
          refine ⟨27856376074046315530933157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18570917382697543687288771 27856376074046315530933157)
          ·
            refine ⟨5223070513883684162049967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27856376074046315530933157 5223070513883684162049967)
            ·
              refine ⟨7834605770825526243074951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5223070513883684162049967 7834605770825526243074951)
              ·
                refine ⟨11751908656238289364612427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834605770825526243074951 11751908656238289364612427)
                ·
                  refine ⟨17627862984357434046918641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11751908656238289364612427 17627862984357434046918641)
                  ·
                    refine ⟨13220897238268075535188981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17627862984357434046918641 13220897238268075535188981)
                    ·
                      refine ⟨1239459116087632081423967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13220897238268075535188981 1239459116087632081423967)
                      ·
                        rfl

theorem cell23_2413838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2413838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413838 prefixEnd_2413838 := by exact prefixLift 2413838
  have htrace : WordTrace (prefixWord ++ tailWord_2413838) baseStart_2413838 baseEnd_2413838 := by
    simpa [prefixWord, tailWord_2413838, baseEnd_2413838] using wordTrace_append hprefix tailTrace_2413838
  have hstable : (prefixWord ++ tailWord_2413838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413838).length < 2 ^ (prefixWord ++ tailWord_2413838).sum := by decide
  have hdescent : baseEnd_2413838 < baseStart_2413838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413888 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 6]
def baseStart_2413888 : Nat := 118140960795 + 2413888 * 2 ^ 59
def prefixEnd_2413888 : Nat := 4983230072969 + 3 ^ 40 * 2413888 * 2
def baseEnd_2413888 : Nat := 137720532235595209533193

theorem tailTrace_2413888 : CollatzResearch.WordTrace tailWord_2413888 prefixEnd_2413888 137720532235595209533193 := by
  unfold tailWord_2413888
  simp only [CollatzResearch.WordTrace]
  refine ⟨44020864139451755046937159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58694485519269006729249545 44020864139451755046937159)
  ·
    refine ⟨66031296209177632570405739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44020864139451755046937159 66031296209177632570405739)
    ·
      refine ⟨99046944313766448855608609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66031296209177632570405739 99046944313766448855608609)
      ·
        refine ⟨74285208235324836641706457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99046944313766448855608609 74285208235324836641706457)
        ·
          refine ⟨55713906176493627481279843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74285208235324836641706457 55713906176493627481279843)
          ·
            refine ⟨83570859264740441221919765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55713906176493627481279843 83570859264740441221919765)
            ·
              refine ⟨3917384028034708182277489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83570859264740441221919765 3917384028034708182277489)
              ·
                refine ⟨2938038021026031136708117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3917384028034708182277489 2938038021026031136708117)
                ·
                  refine ⟨137720532235595209533193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2938038021026031136708117 137720532235595209533193)
                  ·
                    rfl

theorem cell23_2413888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 6].length) (baseStart_2413888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413888 prefixEnd_2413888 := by exact prefixLift 2413888
  have htrace : WordTrace (prefixWord ++ tailWord_2413888) baseStart_2413888 baseEnd_2413888 := by
    simpa [prefixWord, tailWord_2413888, baseEnd_2413888] using wordTrace_append hprefix tailTrace_2413888
  have hstable : (prefixWord ++ tailWord_2413888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413888).length < 2 ^ (prefixWord ++ tailWord_2413888).sum := by decide
  have hdescent : baseEnd_2413888 < baseStart_2413888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413891 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 6]
def baseStart_2413891 : Nat := 118140960795 + 2413891 * 2 ^ 59
def prefixEnd_2413891 : Nat := 4983230072969 + 3 ^ 40 * 2413891 * 2
def baseEnd_2413891 : Nat := 1239486330562320374061223

theorem tailTrace_2413891 : CollatzResearch.WordTrace tailWord_2413891 prefixEnd_2413891 1239486330562320374061223 := by
  unfold tailWord_2413891
  simp only [CollatzResearch.WordTrace]
  refine ⟨88041837697892641606233527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58694558465261761070822351 88041837697892641606233527)
  ·
    refine ⟨132062756546838962409350291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88041837697892641606233527 132062756546838962409350291)
    ·
      refine ⟨198094134820258443614025437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132062756546838962409350291 198094134820258443614025437)
      ·
        refine ⟨74285300557596916355259539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198094134820258443614025437 74285300557596916355259539)
        ·
          refine ⟨111427950836395374532889309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74285300557596916355259539 111427950836395374532889309)
          ·
            refine ⟨41785481563648265449833491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111427950836395374532889309 41785481563648265449833491)
            ·
              refine ⟨62678222345472398174750237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41785481563648265449833491 62678222345472398174750237)
              ·
                refine ⟨23504333379552149315531339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62678222345472398174750237 23504333379552149315531339)
                ·
                  refine ⟨35256500069328223973297009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23504333379552149315531339 35256500069328223973297009)
                  ·
                    refine ⟨26442375051996167979972757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35256500069328223973297009 26442375051996167979972757)
                    ·
                      refine ⟨1239486330562320374061223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26442375051996167979972757 1239486330562320374061223)
                      ·
                        rfl

theorem cell23_2413891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_2413891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413891 prefixEnd_2413891 := by exact prefixLift 2413891
  have htrace : WordTrace (prefixWord ++ tailWord_2413891) baseStart_2413891 baseEnd_2413891 := by
    simpa [prefixWord, tailWord_2413891, baseEnd_2413891] using wordTrace_append hprefix tailTrace_2413891
  have hstable : (prefixWord ++ tailWord_2413891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413891).length < 2 ^ (prefixWord ++ tailWord_2413891).sum := by decide
  have hdescent : baseEnd_2413891 < baseStart_2413891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413925 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 1, 5, 2]
def baseStart_2413925 : Nat := 118140960795 + 2413925 * 2 ^ 59
def prefixEnd_2413925 : Nat := 4983230072969 + 3 ^ 40 * 2413925 * 2
def baseEnd_2413925 : Nat := 1239503788904573241036067

theorem tailTrace_2413925 : CollatzResearch.WordTrace tailWord_2413925 prefixEnd_2413925 1239503788904573241036067 := by
  unfold tailWord_2413925
  simp only [CollatzResearch.WordTrace]
  refine ⟨88043077779769465412971229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58695385186512976941980819 88043077779769465412971229)
  ·
    refine ⟨33016154167413549529864211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88043077779769465412971229 33016154167413549529864211)
    ·
      refine ⟨49524231251120324294796317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33016154167413549529864211 49524231251120324294796317)
      ·
        refine ⟨18571586719170121610548619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49524231251120324294796317 18571586719170121610548619)
        ·
          refine ⟨27857380078755182415822929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18571586719170121610548619 27857380078755182415822929)
          ·
            refine ⟨20893035059066386811867197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27857380078755182415822929 20893035059066386811867197)
            ·
              refine ⟨7834888147149895054450199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20893035059066386811867197 7834888147149895054450199)
              ·
                refine ⟨11752332220724842581675299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7834888147149895054450199 11752332220724842581675299)
                ·
                  refine ⟨17628498331087263872512949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11752332220724842581675299 17628498331087263872512949)
                  ·
                    refine ⟨1652671718539430988048089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17628498331087263872512949 1652671718539430988048089)
                    ·
                      refine ⟨1239503788904573241036067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652671718539430988048089 1239503788904573241036067)
                      ·
                        rfl

theorem cell23_2413925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_2413925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413925 prefixEnd_2413925 := by exact prefixLift 2413925
  have htrace : WordTrace (prefixWord ++ tailWord_2413925) baseStart_2413925 baseEnd_2413925 := by
    simpa [prefixWord, tailWord_2413925, baseEnd_2413925] using wordTrace_append hprefix tailTrace_2413925
  have hstable : (prefixWord ++ tailWord_2413925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413925).length < 2 ^ (prefixWord ++ tailWord_2413925).sum := by decide
  have hdescent : baseEnd_2413925 < baseStart_2413925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413972 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2413972 : Nat := 118140960795 + 2413972 * 2 ^ 59
def prefixEnd_2413972 : Nat := 4983230072969 + 3 ^ 40 * 2413972 * 2
def baseEnd_2413972 : Nat := 1239527922495334557148351

theorem tailTrace_2413972 : CollatzResearch.WordTrace tailWord_2413972 prefixEnd_2413972 1239527922495334557148351 := by
  unfold tailWord_2413972
  simp only [CollatzResearch.WordTrace]
  refine ⟨44022396005299596219966085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58696528007066128293288113 44022396005299596219966085)
  ·
    refine ⟨8254199250993674291243641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44022396005299596219966085 8254199250993674291243641)
    ·
      refine ⟨6190649438245255718432731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8254199250993674291243641 6190649438245255718432731)
      ·
        refine ⟨9285974157367883577649097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6190649438245255718432731 9285974157367883577649097)
        ·
          refine ⟨6964480618025912683236823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9285974157367883577649097 6964480618025912683236823)
          ·
            refine ⟨10446720927038869024855235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6964480618025912683236823 10446720927038869024855235)
            ·
              refine ⟨15670081390558303537282853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10446720927038869024855235 15670081390558303537282853)
              ·
                refine ⟨2938140260729681913240535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15670081390558303537282853 2938140260729681913240535)
                ·
                  refine ⟨4407210391094522869860803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938140260729681913240535 4407210391094522869860803)
                  ·
                    refine ⟨6610815586641784304791205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4407210391094522869860803 6610815586641784304791205)
                    ·
                      refine ⟨1239527922495334557148351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6610815586641784304791205 1239527922495334557148351)
                      ·
                        rfl

theorem cell23_2413972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2413972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413972 prefixEnd_2413972 := by exact prefixLift 2413972
  have htrace : WordTrace (prefixWord ++ tailWord_2413972) baseStart_2413972 baseEnd_2413972 := by
    simpa [prefixWord, tailWord_2413972, baseEnd_2413972] using wordTrace_append hprefix tailTrace_2413972
  have hstable : (prefixWord ++ tailWord_2413972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413972).length < 2 ^ (prefixWord ++ tailWord_2413972).sum := by decide
  have hdescent : baseEnd_2413972 < baseStart_2413972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413978 : List Nat := [3, 1, 1, 4, 1, 1, 3, 9]
def baseStart_2413978 : Nat := 118140960795 + 2413978 * 2 ^ 59
def prefixEnd_2413978 : Nat := 4983230072969 + 3 ^ 40 * 2413978 * 2
def baseEnd_2413978 : Nat := 45908555680713390136049

theorem tailTrace_2413978 : CollatzResearch.WordTrace tailWord_2413978 prefixEnd_2413978 45908555680713390136049 := by
  unfold tailWord_2413978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22011252712144363866162647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58696673899051636976433725 22011252712144363866162647)
  ·
    refine ⟨33016879068216545799243971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22011252712144363866162647 33016879068216545799243971)
    ·
      refine ⟨49525318602324818698865957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33016879068216545799243971 49525318602324818698865957)
      ·
        refine ⟨9285997237935903506037367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49525318602324818698865957 9285997237935903506037367)
        ·
          refine ⟨13928995856903855259056051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9285997237935903506037367 13928995856903855259056051)
          ·
            refine ⟨20893493785355782888584077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13928995856903855259056051 20893493785355782888584077)
            ·
              refine ⟨7835060169508418583219029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20893493785355782888584077 7835060169508418583219029)
              ·
                refine ⟨45908555680713390136049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7835060169508418583219029 45908555680713390136049)
                ·
                  rfl

theorem cell23_2413978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 9].length) (baseStart_2413978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413978 prefixEnd_2413978 := by exact prefixLift 2413978
  have htrace : WordTrace (prefixWord ++ tailWord_2413978) baseStart_2413978 baseEnd_2413978 := by
    simpa [prefixWord, tailWord_2413978, baseEnd_2413978] using wordTrace_append hprefix tailTrace_2413978
  have hstable : (prefixWord ++ tailWord_2413978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413978).length < 2 ^ (prefixWord ++ tailWord_2413978).sum := by decide
  have hdescent : baseEnd_2413978 < baseStart_2413978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2413989 : List Nat := [1, 3, 1, 2, 1, 1, 2, 7, 1, 2, 2]
def baseStart_2413989 : Nat := 118140960795 + 2413989 * 2 ^ 59
def prefixEnd_2413989 : Nat := 4983230072969 + 3 ^ 40 * 2413989 * 2
def baseEnd_2413989 : Nat := 1239536651666460990635773

theorem tailTrace_2413989 : CollatzResearch.WordTrace tailWord_2413989 prefixEnd_2413989 1239536651666460990635773 := by
  unfold tailWord_2413989
  simp only [CollatzResearch.WordTrace]
  refine ⟨88045412051537604343301021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58696941367691736228867347 88045412051537604343301021)
  ·
    refine ⟨33017029519326601628737883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88045412051537604343301021 33017029519326601628737883)
    ·
      refine ⟨49525544278989902443106825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33017029519326601628737883 49525544278989902443106825)
      ·
        refine ⟨37144158209242426832330119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49525544278989902443106825 37144158209242426832330119)
        ·
          refine ⟨55716237313863640248495179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37144158209242426832330119 55716237313863640248495179)
          ·
            refine ⟨83574355970795460372742769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55716237313863640248495179 83574355970795460372742769)
            ·
              refine ⟨62680766978096595279557077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83574355970795460372742769 62680766978096595279557077)
              ·
                refine ⟨1469080476049138951864619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62680766978096595279557077 1469080476049138951864619)
                ·
                  refine ⟨2203620714073708427796929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469080476049138951864619 2203620714073708427796929)
                  ·
                    refine ⟨1652715535555281320847697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2203620714073708427796929 1652715535555281320847697)
                    ·
                      refine ⟨1239536651666460990635773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652715535555281320847697 1239536651666460990635773)
                      ·
                        rfl

theorem cell23_2413989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_2413989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2413989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2413989 prefixEnd_2413989 := by exact prefixLift 2413989
  have htrace : WordTrace (prefixWord ++ tailWord_2413989) baseStart_2413989 baseEnd_2413989 := by
    simpa [prefixWord, tailWord_2413989, baseEnd_2413989] using wordTrace_append hprefix tailTrace_2413989
  have hstable : (prefixWord ++ tailWord_2413989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2413989).length < 2 ^ (prefixWord ++ tailWord_2413989).sum := by decide
  have hdescent : baseEnd_2413989 < baseStart_2413989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2413989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414048 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2414048 : Nat := 118140960795 + 2414048 * 2 ^ 59
def prefixEnd_2414048 : Nat := 4983230072969 + 3 ^ 40 * 2414048 * 2
def baseEnd_2414048 : Nat := 1239566947025076259798001

theorem tailTrace_2414048 : CollatzResearch.WordTrace tailWord_2414048 prefixEnd_2414048 1239566947025076259798001 := by
  unfold tailWord_2414048
  simp only [CollatzResearch.WordTrace]
  refine ⟨44023781979161928709849399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58698375972215904946465865 44023781979161928709849399)
  ·
    refine ⟨66035672968742893064774099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44023781979161928709849399 66035672968742893064774099)
    ·
      refine ⟨99053509453114339597161149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66035672968742893064774099 99053509453114339597161149)
      ·
        refine ⟨37145066044917877348935431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99053509453114339597161149 37145066044917877348935431)
        ·
          refine ⟨55717599067376816023403147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37145066044917877348935431 55717599067376816023403147)
          ·
            refine ⟨83576398601065224035104721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55717599067376816023403147 83576398601065224035104721)
            ·
              refine ⟨62682298950798918026328541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83576398601065224035104721 62682298950798918026328541)
              ·
                refine ⟨23505862106549594259873203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62682298950798918026328541 23505862106549594259873203)
                ·
                  refine ⟨35258793159824391389809805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23505862106549594259873203 35258793159824391389809805)
                  ·
                    refine ⟨13222047434934146771178677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35258793159824391389809805 13222047434934146771178677)
                    ·
                      refine ⟨1239566947025076259798001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13222047434934146771178677 1239566947025076259798001)
                      ·
                        rfl

theorem cell23_2414048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2414048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414048 prefixEnd_2414048 := by exact prefixLift 2414048
  have htrace : WordTrace (prefixWord ++ tailWord_2414048) baseStart_2414048 baseEnd_2414048 := by
    simpa [prefixWord, tailWord_2414048, baseEnd_2414048] using wordTrace_append hprefix tailTrace_2414048
  have hstable : (prefixWord ++ tailWord_2414048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414048).length < 2 ^ (prefixWord ++ tailWord_2414048).sum := by decide
  have hdescent : baseEnd_2414048 < baseStart_2414048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414062 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_2414062 : Nat := 118140960795 + 2414062 * 2 ^ 59
def prefixEnd_2414062 : Nat := 4983230072969 + 3 ^ 40 * 2414062 * 2
def baseEnd_2414062 : Nat := 1239574135754239205022937

theorem tailTrace_2414062 : CollatzResearch.WordTrace tailWord_2414062 prefixEnd_2414062 1239574135754239205022937 := by
  unfold tailWord_2414062
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006009322534142226338555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58698716386848758540472293 11006009322534142226338555)
  ·
    refine ⟨16509013983801213339507833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11006009322534142226338555 16509013983801213339507833)
    ·
      refine ⟨12381760487850910004630875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16509013983801213339507833 12381760487850910004630875)
      ·
        refine ⟨18572640731776365006946313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12381760487850910004630875 18572640731776365006946313)
        ·
          refine ⟨13929480548832273755209735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18572640731776365006946313 13929480548832273755209735)
          ·
            refine ⟨20894220823248410632814603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13929480548832273755209735 20894220823248410632814603)
            ·
              refine ⟨31341331234872615949221905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20894220823248410632814603 31341331234872615949221905)
              ·
                refine ⟨23505998426154461961916429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31341331234872615949221905 23505998426154461961916429)
                ·
                  refine ⟨8814749409807923235718661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23505998426154461961916429 8814749409807923235718661)
                  ·
                    refine ⟨1652765514338985606697249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8814749409807923235718661 1652765514338985606697249)
                    ·
                      refine ⟨1239574135754239205022937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652765514338985606697249 1239574135754239205022937)
                      ·
                        rfl

theorem cell23_2414062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_2414062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414062 prefixEnd_2414062 := by exact prefixLift 2414062
  have htrace : WordTrace (prefixWord ++ tailWord_2414062) baseStart_2414062 baseEnd_2414062 := by
    simpa [prefixWord, tailWord_2414062, baseEnd_2414062] using wordTrace_append hprefix tailTrace_2414062
  have hstable : (prefixWord ++ tailWord_2414062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414062).length < 2 ^ (prefixWord ++ tailWord_2414062).sum := by decide
  have hdescent : baseEnd_2414062 < baseStart_2414062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414065 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_2414065 : Nat := 118140960795 + 2414065 * 2 ^ 59
def prefixEnd_2414065 : Nat := 4983230072969 + 3 ^ 40 * 2414065 * 2
def baseEnd_2414065 : Nat := 1239575676196202693285423

theorem tailTrace_2414065 : CollatzResearch.WordTrace tailWord_2414065 prefixEnd_2414065 1239575676196202693285423 := by
  unfold tailWord_2414065
  simp only [CollatzResearch.WordTrace]
  refine ⟨88048183999262269323067649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58698789332841512882045099 88048183999262269323067649)
  ·
    refine ⟨66036137999446701992300737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88048183999262269323067649 66036137999446701992300737)
    ·
      refine ⟨49527103499585026494225553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66036137999446701992300737 49527103499585026494225553)
      ·
        refine ⟨37145327624688769870669165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49527103499585026494225553 37145327624688769870669165)
        ·
          refine ⟨13929497859258288701500937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37145327624688769870669165 13929497859258288701500937)
          ·
            refine ⟨10447123394443716526125703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13929497859258288701500937 10447123394443716526125703)
            ·
              refine ⟨15670685091665574789188555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10447123394443716526125703 15670685091665574789188555)
              ·
                refine ⟨23506027637498362183782833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15670685091665574789188555 23506027637498362183782833)
                ·
                  refine ⟨17629520728123771637837125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23506027637498362183782833 17629520728123771637837125)
                  ·
                    refine ⟨3305535136523207182094461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17629520728123771637837125 3305535136523207182094461)
                    ·
                      refine ⟨1239575676196202693285423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3305535136523207182094461 1239575676196202693285423)
                      ·
                        rfl

theorem cell23_2414065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_2414065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414065 prefixEnd_2414065 := by exact prefixLift 2414065
  have htrace : WordTrace (prefixWord ++ tailWord_2414065) baseStart_2414065 baseEnd_2414065 := by
    simpa [prefixWord, tailWord_2414065, baseEnd_2414065] using wordTrace_append hprefix tailTrace_2414065
  have hstable : (prefixWord ++ tailWord_2414065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414065).length < 2 ^ (prefixWord ++ tailWord_2414065).sum := by decide
  have hdescent : baseEnd_2414065 < baseStart_2414065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414100 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2414100 : Nat := 118140960795 + 2414100 * 2 ^ 59
def prefixEnd_2414100 : Nat := 4983230072969 + 3 ^ 40 * 2414100 * 2
def baseEnd_2414100 : Nat := 1239593648019110056347763

theorem tailTrace_2414100 : CollatzResearch.WordTrace tailWord_2414100 prefixEnd_2414100 1239593648019110056347763 := by
  unfold tailWord_2414100
  simp only [CollatzResearch.WordTrace]
  refine ⟨44024730277067735150295877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58699640369423646867061169 44024730277067735150295877)
  ·
    refine ⟨8254636926950200340680477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44024730277067735150295877 8254636926950200340680477)
    ·
      refine ⟨3095488847606325127755179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8254636926950200340680477 3095488847606325127755179)
      ·
        refine ⟨4643233271409487691632769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3095488847606325127755179 4643233271409487691632769)
        ·
          refine ⟨3482424953557115768724577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4643233271409487691632769 3482424953557115768724577)
          ·
            refine ⟨2611818715167836826543433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3482424953557115768724577 2611818715167836826543433)
            ·
              refine ⟨1958864036375877619907575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611818715167836826543433 1958864036375877619907575)
              ·
                refine ⟨2938296054563816429861363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958864036375877619907575 2938296054563816429861363)
                ·
                  refine ⟨4407444081845724644792045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938296054563816429861363 4407444081845724644792045)
                  ·
                    refine ⟨1652791530692146741797017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4407444081845724644792045 1652791530692146741797017)
                    ·
                      refine ⟨1239593648019110056347763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652791530692146741797017 1239593648019110056347763)
                      ·
                        rfl

theorem cell23_2414100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2414100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414100 prefixEnd_2414100 := by exact prefixLift 2414100
  have htrace : WordTrace (prefixWord ++ tailWord_2414100) baseStart_2414100 baseEnd_2414100 := by
    simpa [prefixWord, tailWord_2414100, baseEnd_2414100] using wordTrace_append hprefix tailTrace_2414100
  have hstable : (prefixWord ++ tailWord_2414100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414100).length < 2 ^ (prefixWord ++ tailWord_2414100).sum := by decide
  have hdescent : baseEnd_2414100 < baseStart_2414100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414112 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2414112 : Nat := 118140960795 + 2414112 * 2 ^ 59
def prefixEnd_2414112 : Nat := 4983230072969 + 3 ^ 40 * 2414112 * 2
def baseEnd_2414112 : Nat := 1239599809786964009397707

theorem tailTrace_2414112 : CollatzResearch.WordTrace tailWord_2414112 prefixEnd_2414112 1239599809786964009397707 := by
  unfold tailWord_2414112
  simp only [CollatzResearch.WordTrace]
  refine ⟨44024949115045998175014295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58699932153394664233352393 44024949115045998175014295)
  ·
    refine ⟨66037423672568997262521443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44024949115045998175014295 66037423672568997262521443)
    ·
      refine ⟨99056135508853495893782165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66037423672568997262521443 99056135508853495893782165)
      ·
        refine ⟨4643256351977507620021039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99056135508853495893782165 4643256351977507620021039)
        ·
          refine ⟨6964884527966261430031559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4643256351977507620021039 6964884527966261430031559)
          ·
            refine ⟨10447326791949392145047339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6964884527966261430031559 10447326791949392145047339)
            ·
              refine ⟨15670990187924088217571009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10447326791949392145047339 15670990187924088217571009)
              ·
                refine ⟨11753242640943066163178257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15670990187924088217571009 11753242640943066163178257)
                ·
                  refine ⟨8814931980707299622383693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11753242640943066163178257 8814931980707299622383693)
                  ·
                    refine ⟨3305599492765237358393885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8814931980707299622383693 3305599492765237358393885)
                    ·
                      refine ⟨1239599809786964009397707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3305599492765237358393885 1239599809786964009397707)
                      ·
                        rfl

theorem cell23_2414112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2414112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414112 prefixEnd_2414112 := by exact prefixLift 2414112
  have htrace : WordTrace (prefixWord ++ tailWord_2414112) baseStart_2414112 baseEnd_2414112 := by
    simpa [prefixWord, tailWord_2414112, baseEnd_2414112] using wordTrace_append hprefix tailTrace_2414112
  have hstable : (prefixWord ++ tailWord_2414112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414112).length < 2 ^ (prefixWord ++ tailWord_2414112).sum := by decide
  have hdescent : baseEnd_2414112 < baseStart_2414112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414135 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_2414135 : Nat := 118140960795 + 2414135 * 2 ^ 59
def prefixEnd_2414135 : Nat := 4983230072969 + 3 ^ 40 * 2414135 * 2
def baseEnd_2414135 : Nat := 1239611619842017419410101

theorem tailTrace_2414135 : CollatzResearch.WordTrace tailWord_2414135 prefixEnd_2414135 1239611619842017419410101 := by
  unfold tailWord_2414135
  simp only [CollatzResearch.WordTrace]
  refine ⟨88050737109008671278115859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58700491406005780852077239 88050737109008671278115859)
  ·
    refine ⟨132076105663513006917173789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88050737109008671278115859 132076105663513006917173789)
    ·
      refine ⟨49528539623817377593940171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132076105663513006917173789 49528539623817377593940171)
      ·
        refine ⟨74292809435726066390910257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49528539623817377593940171 74292809435726066390910257)
        ·
          refine ⟨55719607076794549793182693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74292809435726066390910257 55719607076794549793182693)
          ·
            refine ⟨10447426326898978086221755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55719607076794549793182693 10447426326898978086221755)
            ·
              refine ⟨15671139490348467129332633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10447426326898978086221755 15671139490348467129332633)
              ·
                refine ⟨11753354617761350346999475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15671139490348467129332633 11753354617761350346999475)
                ·
                  refine ⟨17630031926642025520499213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11753354617761350346999475 17630031926642025520499213)
                  ·
                    refine ⟨6611261972490759570187205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17630031926642025520499213 6611261972490759570187205)
                    ·
                      refine ⟨1239611619842017419410101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6611261972490759570187205 1239611619842017419410101)
                      ·
                        rfl

theorem cell23_2414135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_2414135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414135 prefixEnd_2414135 := by exact prefixLift 2414135
  have htrace : WordTrace (prefixWord ++ tailWord_2414135) baseStart_2414135 baseEnd_2414135 := by
    simpa [prefixWord, tailWord_2414135, baseEnd_2414135] using wordTrace_append hprefix tailTrace_2414135
  have hstable : (prefixWord ++ tailWord_2414135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414135).length < 2 ^ (prefixWord ++ tailWord_2414135).sum := by decide
  have hdescent : baseEnd_2414135 < baseStart_2414135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414145 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2414145 : Nat := 118140960795 + 2414145 * 2 ^ 59
def prefixEnd_2414145 : Nat := 4983230072969 + 3 ^ 40 * 2414145 * 2
def baseEnd_2414145 : Nat := 413205584882854126761685

theorem tailTrace_2414145 : CollatzResearch.WordTrace tailWord_2414145 prefixEnd_2414145 413205584882854126761685 := by
  unfold tailWord_2414145
  simp only [CollatzResearch.WordTrace]
  refine ⟨88051101838972442985979889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58700734559314961990653259 88051101838972442985979889)
  ·
    refine ⟨66038326379229332239484917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88051101838972442985979889 66038326379229332239484917)
    ·
      refine ⟨6191093098052749897451711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66038326379229332239484917 6191093098052749897451711)
      ·
        refine ⟨9286639647079124846177567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6191093098052749897451711 9286639647079124846177567)
        ·
          refine ⟨13929959470618687269266351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9286639647079124846177567 13929959470618687269266351)
          ·
            refine ⟨20894939205928030903899527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13929959470618687269266351 20894939205928030903899527)
            ·
              refine ⟨31342408808892046355849291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20894939205928030903899527 31342408808892046355849291)
              ·
                refine ⟨47013613213338069533773937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31342408808892046355849291 47013613213338069533773937)
                ·
                  refine ⟨35260209910003552150330453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47013613213338069533773937 35260209910003552150330453)
                  ·
                    refine ⟨413205584882854126761685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35260209910003552150330453 413205584882854126761685)
                    ·
                      rfl

theorem cell23_2414145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2414145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414145 prefixEnd_2414145 := by exact prefixLift 2414145
  have htrace : WordTrace (prefixWord ++ tailWord_2414145) baseStart_2414145 baseEnd_2414145 := by
    simpa [prefixWord, tailWord_2414145, baseEnd_2414145] using wordTrace_append hprefix tailTrace_2414145
  have hstable : (prefixWord ++ tailWord_2414145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414145).length < 2 ^ (prefixWord ++ tailWord_2414145).sum := by decide
  have hdescent : baseEnd_2414145 < baseStart_2414145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414179 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 3, 4]
def baseStart_2414179 : Nat := 118140960795 + 2414179 * 2 ^ 59
def prefixEnd_2414179 : Nat := 4983230072969 + 3 ^ 40 * 2414179 * 2
def baseEnd_2414179 : Nat := 413211404330271749086633

theorem tailTrace_2414179 : CollatzResearch.WordTrace tailWord_2414179 prefixEnd_2414179 413211404330271749086633 := by
  unfold tailWord_2414179
  simp only [CollatzResearch.WordTrace]
  refine ⟨88052341920849266792717591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58701561280566177861811727 88052341920849266792717591)
  ·
    refine ⟨132078512881273900189076387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88052341920849266792717591 132078512881273900189076387)
    ·
      refine ⟨198117769321910850283614581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132078512881273900189076387 198117769321910850283614581)
      ·
        refine ⟨18573540873929142214088867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198117769321910850283614581 18573540873929142214088867)
        ·
          refine ⟨27860311310893713321133301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18573540873929142214088867 27860311310893713321133301)
          ·
            refine ⟨2611904185396285623856247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27860311310893713321133301 2611904185396285623856247)
            ·
              refine ⟨3917856278094428435784371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611904185396285623856247 3917856278094428435784371)
              ·
                refine ⟨5876784417141642653676557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3917856278094428435784371 5876784417141642653676557)
                ·
                  refine ⟨2203794156428115995128709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5876784417141642653676557 2203794156428115995128709)
                  ·
                    refine ⟨413211404330271749086633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2203794156428115995128709 413211404330271749086633)
                    ·
                      rfl

theorem cell23_2414179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 4].length) (baseStart_2414179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414179 prefixEnd_2414179 := by exact prefixLift 2414179
  have htrace : WordTrace (prefixWord ++ tailWord_2414179) baseStart_2414179 baseEnd_2414179 := by
    simpa [prefixWord, tailWord_2414179, baseEnd_2414179] using wordTrace_append hprefix tailTrace_2414179
  have hstable : (prefixWord ++ tailWord_2414179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414179).length < 2 ^ (prefixWord ++ tailWord_2414179).sum := by decide
  have hdescent : baseEnd_2414179 < baseStart_2414179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414192 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 6]
def baseStart_2414192 : Nat := 118140960795 + 2414192 * 2 ^ 59
def prefixEnd_2414192 : Nat := 4983230072969 + 3 ^ 40 * 2414192 * 2
def baseEnd_2414192 : Nat := 137737876471035966266371

theorem tailTrace_2414192 : CollatzResearch.WordTrace tailWord_2414192 prefixEnd_2414192 137737876471035966266371 := by
  unfold tailWord_2414192
  simp only [CollatzResearch.WordTrace]
  refine ⟨44026408034901085006470415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58701877379868113341960553 44026408034901085006470415)
  ·
    refine ⟨66039612052351627509705623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44026408034901085006470415 66039612052351627509705623)
    ·
      refine ⟨99059418078527441264558435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66039612052351627509705623 99059418078527441264558435)
      ·
        refine ⟨148589127117791161896837653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99059418078527441264558435 148589127117791161896837653)
        ·
          refine ⟨6965115333646460713914265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 148589127117791161896837653 6965115333646460713914265)
          ·
            refine ⟨5223836500234845535435699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6965115333646460713914265 5223836500234845535435699)
            ·
              refine ⟨7835754750352268303153549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5223836500234845535435699 7835754750352268303153549)
              ·
                refine ⟨2938408031382100613682581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7835754750352268303153549 2938408031382100613682581)
                ·
                  refine ⟨137737876471035966266371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2938408031382100613682581 137737876471035966266371)
                  ·
                    rfl

theorem cell23_2414192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 6].length) (baseStart_2414192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414192 prefixEnd_2414192 := by exact prefixLift 2414192
  have htrace : WordTrace (prefixWord ++ tailWord_2414192) baseStart_2414192 baseEnd_2414192 := by
    simpa [prefixWord, tailWord_2414192, baseEnd_2414192] using wordTrace_append hprefix tailTrace_2414192
  have hstable : (prefixWord ++ tailWord_2414192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414192).length < 2 ^ (prefixWord ++ tailWord_2414192).sum := by decide
  have hdescent : baseEnd_2414192 < baseStart_2414192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414265 : List Nat := [1, 2, 1, 4, 1, 1, 2, 11]
def baseStart_2414265 : Nat := 118140960795 + 2414265 * 2 ^ 59
def prefixEnd_2414265 : Nat := 4983230072969 + 3 ^ 40 * 2414265 * 2
def baseEnd_2414265 : Nat := 45914013789892663362389

theorem tailTrace_2414265 : CollatzResearch.WordTrace tailWord_2414265 prefixEnd_2414265 45914013789892663362389 := by
  unfold tailWord_2414265
  simp only [CollatzResearch.WordTrace]
  refine ⟨88055478598537703480348249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58703652399025135653565499 88055478598537703480348249)
  ·
    refine ⟨66041608948903277610261187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88055478598537703480348249 66041608948903277610261187)
    ·
      refine ⟨99062413423354916415391781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66041608948903277610261187 99062413423354916415391781)
      ·
        refine ⟨18574202516879046827885959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99062413423354916415391781 18574202516879046827885959)
        ·
          refine ⟨27861303775318570241828939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18574202516879046827885959 27861303775318570241828939)
          ·
            refine ⟨41791955662977855362743409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27861303775318570241828939 41791955662977855362743409)
            ·
              refine ⟨31343966747233391522057557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41791955662977855362743409 31343966747233391522057557)
              ·
                refine ⟨45914013789892663362389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 31343966747233391522057557 45914013789892663362389)
                ·
                  rfl

theorem cell23_2414265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 11].length) (baseStart_2414265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414265 prefixEnd_2414265 := by exact prefixLift 2414265
  have htrace : WordTrace (prefixWord ++ tailWord_2414265) baseStart_2414265 baseEnd_2414265 := by
    simpa [prefixWord, tailWord_2414265, baseEnd_2414265] using wordTrace_append hprefix tailTrace_2414265
  have hstable : (prefixWord ++ tailWord_2414265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414265).length < 2 ^ (prefixWord ++ tailWord_2414265).sum := by decide
  have hdescent : baseEnd_2414265 < baseStart_2414265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414272 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_2414272 : Nat := 118140960795 + 2414272 * 2 ^ 59
def prefixEnd_2414272 : Nat := 4983230072969 + 3 ^ 40 * 2414272 * 2
def baseEnd_2414272 : Nat := 1239681966691683383396971

theorem tailTrace_2414272 : CollatzResearch.WordTrace tailWord_2414272 prefixEnd_2414272 1239681966691683383396971 := by
  unfold tailWord_2414272
  simp only [CollatzResearch.WordTrace]
  refine ⟨44027866954756171837926535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58703822606341562450568713 44027866954756171837926535)
  ·
    refine ⟨66041800432134257756889803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44027866954756171837926535 66041800432134257756889803)
    ·
      refine ⟨99062700648201386635334705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66041800432134257756889803 99062700648201386635334705)
      ·
        refine ⟨74297025486151039976501029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99062700648201386635334705 74297025486151039976501029)
        ·
          refine ⟨13930692278653319995593943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74297025486151039976501029 13930692278653319995593943)
          ·
            refine ⟨20896038417979979993390915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13930692278653319995593943 20896038417979979993390915)
            ·
              refine ⟨31344057626969969990086373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20896038417979979993390915 31344057626969969990086373)
              ·
                refine ⟨5877010805056869373141195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31344057626969969990086373 5877010805056869373141195)
                ·
                  refine ⟨8815516207585304059711793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5877010805056869373141195 8815516207585304059711793)
                  ·
                    refine ⟨6611637155688978044783845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8815516207585304059711793 6611637155688978044783845)
                    ·
                      refine ⟨1239681966691683383396971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6611637155688978044783845 1239681966691683383396971)
                      ·
                        rfl

theorem cell23_2414272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_2414272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414272 prefixEnd_2414272 := by exact prefixLift 2414272
  have htrace : WordTrace (prefixWord ++ tailWord_2414272) baseStart_2414272 baseEnd_2414272 := by
    simpa [prefixWord, tailWord_2414272, baseEnd_2414272] using wordTrace_append hprefix tailTrace_2414272
  have hstable : (prefixWord ++ tailWord_2414272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414272).length < 2 ^ (prefixWord ++ tailWord_2414272).sum := by decide
  have hdescent : baseEnd_2414272 < baseStart_2414272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414276 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_2414276 : Nat := 118140960795 + 2414276 * 2 ^ 59
def prefixEnd_2414276 : Nat := 4983230072969 + 3 ^ 40 * 2414276 * 2
def baseEnd_2414276 : Nat := 1239684020614301367746953

theorem tailTrace_2414276 : CollatzResearch.WordTrace tailWord_2414276 prefixEnd_2414276 1239684020614301367746953 := by
  unfold tailWord_2414276
  simp only [CollatzResearch.WordTrace]
  refine ⟨44027939900748926179499341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58703919867665234905999121 44027939900748926179499341)
  ·
    refine ⟨16510477462780847317312253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44027939900748926179499341 16510477462780847317312253)
    ·
      refine ⟨6191429048542817743992095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16510477462780847317312253 6191429048542817743992095)
      ·
        refine ⟨9287143572814226615988143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6191429048542817743992095 9287143572814226615988143)
        ·
          refine ⟨13930715359221339923982215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9287143572814226615988143 13930715359221339923982215)
          ·
            refine ⟨20896073038832009885973323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13930715359221339923982215 20896073038832009885973323)
            ·
              refine ⟨31344109558248014828959985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20896073038832009885973323 31344109558248014828959985)
              ·
                refine ⟨23508082168686011121719989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31344109558248014828959985 23508082168686011121719989)
                ·
                  refine ⟨2203882703314313542661249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23508082168686011121719989 2203882703314313542661249)
                  ·
                    refine ⟨1652912027485735156995937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2203882703314313542661249 1652912027485735156995937)
                    ·
                      refine ⟨1239684020614301367746953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1652912027485735156995937 1239684020614301367746953)
                      ·
                        rfl

theorem cell23_2414276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_2414276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414276 prefixEnd_2414276 := by exact prefixLift 2414276
  have htrace : WordTrace (prefixWord ++ tailWord_2414276) baseStart_2414276 baseEnd_2414276 := by
    simpa [prefixWord, tailWord_2414276, baseEnd_2414276] using wordTrace_append hprefix tailTrace_2414276
  have hstable : (prefixWord ++ tailWord_2414276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414276).length < 2 ^ (prefixWord ++ tailWord_2414276).sum := by decide
  have hdescent : baseEnd_2414276 < baseStart_2414276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414279 : List Nat := [1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 3]
def baseStart_2414279 : Nat := 118140960795 + 2414279 * 2 ^ 59
def prefixEnd_2414279 : Nat := 4983230072969 + 3 ^ 40 * 2414279 * 2
def baseEnd_2414279 : Nat := 1239685561056264856009439

theorem tailTrace_2414279 : CollatzResearch.WordTrace tailWord_2414279 prefixEnd_2414279 1239685561056264856009439 := by
  unfold tailWord_2414279
  simp only [CollatzResearch.WordTrace]
  refine ⟨88055989220486983871357891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58703992813657989247571927 88055989220486983871357891)
  ·
    refine ⟨132083983830730475807036837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88055989220486983871357891 132083983830730475807036837)
    ·
      refine ⟨24765746968261964213819407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132083983830730475807036837 24765746968261964213819407)
      ·
        refine ⟨37148620452392946320729111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24765746968261964213819407 37148620452392946320729111)
        ·
          refine ⟨55722930678589419481093667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37148620452392946320729111 55722930678589419481093667)
          ·
            refine ⟨83584396017884129221640501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55722930678589419481093667 83584396017884129221640501)
            ·
              refine ⟨7836037126676637114528797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83584396017884129221640501 7836037126676637114528797)
              ·
                refine ⟨2938513922503738917948299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7836037126676637114528797 2938513922503738917948299)
                ·
                  refine ⟨4407770883755608376922449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938513922503738917948299 4407770883755608376922449)
                  ·
                    refine ⟨3305828162816706282691837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4407770883755608376922449 3305828162816706282691837)
                    ·
                      refine ⟨1239685561056264856009439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3305828162816706282691837 1239685561056264856009439)
                      ·
                        rfl

theorem cell23_2414279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_2414279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414279 prefixEnd_2414279 := by exact prefixLift 2414279
  have htrace : WordTrace (prefixWord ++ tailWord_2414279) baseStart_2414279 baseEnd_2414279 := by
    simpa [prefixWord, tailWord_2414279, baseEnd_2414279] using wordTrace_append hprefix tailTrace_2414279
  have hstable : (prefixWord ++ tailWord_2414279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414279).length < 2 ^ (prefixWord ++ tailWord_2414279).sum := by decide
  have hdescent : baseEnd_2414279 < baseStart_2414279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414282 : List Nat := [3, 1, 2, 1, 5, 1, 10]
def baseStart_2414282 : Nat := 118140960795 + 2414282 * 2 ^ 59
def prefixEnd_2414282 : Nat := 4983230072969 + 3 ^ 40 * 2414282 * 2
def baseEnd_2414282 : Nat := 15304779030842325237925

theorem tailTrace_2414282 : CollatzResearch.WordTrace tailWord_2414282 prefixEnd_2414282 15304779030842325237925 := by
  unfold tailWord_2414282
  simp only [CollatzResearch.WordTrace]
  refine ⟨22014024659869028845929275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58704065759650743589144733 22014024659869028845929275)
  ·
    refine ⟨33021036989803543268893913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22014024659869028845929275 33021036989803543268893913)
    ·
      refine ⟨24765777742352657451670435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33021036989803543268893913 24765777742352657451670435)
      ·
        refine ⟨37148666613528986177505653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24765777742352657451670435 37148666613528986177505653)
        ·
          refine ⟨3482687495018342454141155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37148666613528986177505653 3482687495018342454141155)
          ·
            refine ⟨5224031242527513681211733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3482687495018342454141155 5224031242527513681211733)
            ·
              refine ⟨15304779030842325237925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5224031242527513681211733 15304779030842325237925)
              ·
                rfl

theorem cell23_2414282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 10].length) (baseStart_2414282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414282 prefixEnd_2414282 := by exact prefixLift 2414282
  have htrace : WordTrace (prefixWord ++ tailWord_2414282) baseStart_2414282 baseEnd_2414282 := by
    simpa [prefixWord, tailWord_2414282, baseEnd_2414282] using wordTrace_append hprefix tailTrace_2414282
  have hstable : (prefixWord ++ tailWord_2414282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414282).length < 2 ^ (prefixWord ++ tailWord_2414282).sum := by decide
  have hdescent : baseEnd_2414282 < baseStart_2414282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414322 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2414322 : Nat := 118140960795 + 2414322 * 2 ^ 59
def prefixEnd_2414322 : Nat := 4983230072969 + 3 ^ 40 * 2414322 * 2
def baseEnd_2414322 : Nat := 1239707640724408187771741

theorem tailTrace_2414322 : CollatzResearch.WordTrace tailWord_2414322 prefixEnd_2414322 1239707640724408187771741 := by
  unfold tailWord_2414322
  simp only [CollatzResearch.WordTrace]
  refine ⟨22014389389832800553793305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58705038372887468143448813 22014389389832800553793305)
  ·
    refine ⟨16510792042374600415344979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22014389389832800553793305 16510792042374600415344979)
    ·
      refine ⟨24766188063561900623017469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16510792042374600415344979 24766188063561900623017469)
      ·
        refine ⟨9287320523835712733631551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24766188063561900623017469 9287320523835712733631551)
        ·
          refine ⟨13930980785753569100447327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9287320523835712733631551 13930980785753569100447327)
          ·
            refine ⟨20896471178630353650670991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13930980785753569100447327 20896471178630353650670991)
            ·
              refine ⟨31344706767945530476006487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20896471178630353650670991 31344706767945530476006487)
              ·
                refine ⟨47017060151918295714009731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31344706767945530476006487 47017060151918295714009731)
                ·
                  refine ⟨70525590227877443571014597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47017060151918295714009731 70525590227877443571014597)
                  ·
                    refine ⟨13223548167727020669565237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70525590227877443571014597 13223548167727020669565237)
                    ·
                      refine ⟨1239707640724408187771741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13223548167727020669565237 1239707640724408187771741)
                      ·
                        rfl

theorem cell23_2414322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2414322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414322 prefixEnd_2414322 := by exact prefixLift 2414322
  have htrace : WordTrace (prefixWord ++ tailWord_2414322) baseStart_2414322 baseEnd_2414322 := by
    simpa [prefixWord, tailWord_2414322, baseEnd_2414322] using wordTrace_append hprefix tailTrace_2414322
  have hstable : (prefixWord ++ tailWord_2414322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414322).length < 2 ^ (prefixWord ++ tailWord_2414322).sum := by decide
  have hdescent : baseEnd_2414322 < baseStart_2414322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414326 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2414326 : Nat := 118140960795 + 2414326 * 2 ^ 59
def prefixEnd_2414326 : Nat := 4983230072969 + 3 ^ 40 * 2414326 * 2
def baseEnd_2414326 : Nat := 1239709694647026172121723

theorem tailTrace_2414326 : CollatzResearch.WordTrace tailWord_2414326 prefixEnd_2414326 1239709694647026172121723 := by
  unfold tailWord_2414326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503606465707294431144927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58705135634211140598879221 5503606465707294431144927)
  ·
    refine ⟨8255409698560941646717391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5503606465707294431144927 8255409698560941646717391)
    ·
      refine ⟨12383114547841412470076087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8255409698560941646717391 12383114547841412470076087)
      ·
        refine ⟨18574671821762118705114131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12383114547841412470076087 18574671821762118705114131)
        ·
          refine ⟨27862007732643178057671197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18574671821762118705114131 27862007732643178057671197)
          ·
            refine ⟨10448252899741191771626699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27862007732643178057671197 10448252899741191771626699)
            ·
              refine ⟨15672379349611787657440049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10448252899741191771626699 15672379349611787657440049)
              ·
                refine ⟨11754284512208840743080037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15672379349611787657440049 11754284512208840743080037)
                ·
                  refine ⟨2203928346039157639327507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11754284512208840743080037 2203928346039157639327507)
                  ·
                    refine ⟨3305892519058736458991261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2203928346039157639327507 3305892519058736458991261)
                    ·
                      refine ⟨1239709694647026172121723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3305892519058736458991261 1239709694647026172121723)
                      ·
                        rfl

theorem cell23_2414326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2414326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414326 prefixEnd_2414326 := by exact prefixLift 2414326
  have htrace : WordTrace (prefixWord ++ tailWord_2414326) baseStart_2414326 baseEnd_2414326 := by
    simpa [prefixWord, tailWord_2414326, baseEnd_2414326] using wordTrace_append hprefix tailTrace_2414326
  have hstable : (prefixWord ++ tailWord_2414326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414326).length < 2 ^ (prefixWord ++ tailWord_2414326).sum := by decide
  have hdescent : baseEnd_2414326 < baseStart_2414326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414409 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 1, 7, 2]
def baseStart_2414409 : Nat := 118140960795 + 2414409 * 2 ^ 59
def prefixEnd_2414409 : Nat := 4983230072969 + 3 ^ 40 * 2414409 * 2
def baseEnd_2414409 : Nat := 1239752313541349347383841

theorem tailTrace_2414409 : CollatzResearch.WordTrace tailWord_2414409 prefixEnd_2414409 1239752313541349347383841 := by
  unfold tailWord_2414409
  simp only [CollatzResearch.WordTrace]
  refine ⟨88060730710016016073590281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58707153806677344049060187 88060730710016016073590281)
  ·
    refine ⟨66045548032512012055192711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88060730710016016073590281 66045548032512012055192711)
    ·
      refine ⟨99068322048768018082789067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66045548032512012055192711 99068322048768018082789067)
      ·
        refine ⟨148602483073152027124183601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99068322048768018082789067 148602483073152027124183601)
        ·
          refine ⟨111451862304864020343137701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148602483073152027124183601 111451862304864020343137701)
          ·
            refine ⟨20897224182162003814338319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111451862304864020343137701 20897224182162003814338319)
            ·
              refine ⟨31345836273243005721507479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20897224182162003814338319 31345836273243005721507479)
              ·
                refine ⟨47018754409864508582261219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31345836273243005721507479 47018754409864508582261219)
                ·
                  refine ⟨70528131614796762873391829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47018754409864508582261219 70528131614796762873391829)
                  ·
                    refine ⟨1653003084721799129845121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 70528131614796762873391829 1653003084721799129845121)
                    ·
                      refine ⟨1239752313541349347383841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653003084721799129845121 1239752313541349347383841)
                      ·
                        rfl

theorem cell23_2414409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 7, 2].length) (baseStart_2414409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414409 prefixEnd_2414409 := by exact prefixLift 2414409
  have htrace : WordTrace (prefixWord ++ tailWord_2414409) baseStart_2414409 baseEnd_2414409 := by
    simpa [prefixWord, tailWord_2414409, baseEnd_2414409] using wordTrace_append hprefix tailTrace_2414409
  have hstable : (prefixWord ++ tailWord_2414409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414409).length < 2 ^ (prefixWord ++ tailWord_2414409).sum := by decide
  have hdescent : baseEnd_2414409 < baseStart_2414409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414439 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2414439 : Nat := 118140960795 + 2414439 * 2 ^ 59
def prefixEnd_2414439 : Nat := 4983230072969 + 3 ^ 40 * 2414439 * 2
def baseEnd_2414439 : Nat := 1239767717960984230008703

theorem tailTrace_2414439 : CollatzResearch.WordTrace tailWord_2414439 prefixEnd_2414439 1239767717960984230008703 := by
  unfold tailWord_2414439
  simp only [CollatzResearch.WordTrace]
  refine ⟨88061824899907331197182371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58707883266604887464788247 88061824899907331197182371)
  ·
    refine ⟨132092737349860996795773557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88061824899907331197182371 132092737349860996795773557)
    ·
      refine ⟨12383694126549468449603771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132092737349860996795773557 12383694126549468449603771)
      ·
        refine ⟨18575541189824202674405657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12383694126549468449603771 18575541189824202674405657)
        ·
          refine ⟨13931655892368152005804243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18575541189824202674405657 13931655892368152005804243)
          ·
            refine ⟨20897483838552228008706365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13931655892368152005804243 20897483838552228008706365)
            ·
              refine ⟨7836556439457085503264887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20897483838552228008706365 7836556439457085503264887)
              ·
                refine ⟨11754834659185628254897331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7836556439457085503264887 11754834659185628254897331)
                ·
                  refine ⟨17632251988778442382345997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11754834659185628254897331 17632251988778442382345997)
                  ·
                    refine ⟨6612094495791915893379749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17632251988778442382345997 6612094495791915893379749)
                    ·
                      refine ⟨1239767717960984230008703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6612094495791915893379749 1239767717960984230008703)
                      ·
                        rfl

theorem cell23_2414439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2414439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414439 prefixEnd_2414439 := by exact prefixLift 2414439
  have htrace : WordTrace (prefixWord ++ tailWord_2414439) baseStart_2414439 baseEnd_2414439 := by
    simpa [prefixWord, tailWord_2414439, baseEnd_2414439] using wordTrace_append hprefix tailTrace_2414439
  have hstable : (prefixWord ++ tailWord_2414439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414439).length < 2 ^ (prefixWord ++ tailWord_2414439).sum := by decide
  have hdescent : baseEnd_2414439 < baseStart_2414439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414449 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 5, 4]
def baseStart_2414449 : Nat := 118140960795 + 2414449 * 2 ^ 59
def prefixEnd_2414449 : Nat := 4983230072969 + 3 ^ 40 * 2414449 * 2
def baseEnd_2414449 : Nat := 413257617589176396961219

theorem tailTrace_2414449 : CollatzResearch.WordTrace tailWord_2414449 prefixEnd_2414449 413257617589176396961219 := by
  unfold tailWord_2414449
  simp only [CollatzResearch.WordTrace]
  refine ⟨88062189629871102905046401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58708126419914068603364267 88062189629871102905046401)
  ·
    refine ⟨66046642222403327178784801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88062189629871102905046401 66046642222403327178784801)
    ·
      refine ⟨49534981666802495384088601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66046642222403327178784801 49534981666802495384088601)
      ·
        refine ⟨37151236250101871538066451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49534981666802495384088601 37151236250101871538066451)
        ·
          refine ⟨55726854375152807307099677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37151236250101871538066451 55726854375152807307099677)
          ·
            refine ⟨20897570390682302740162379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55726854375152807307099677 20897570390682302740162379)
            ·
              refine ⟨31346355586023454110243569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20897570390682302740162379 31346355586023454110243569)
              ·
                refine ⟨23509766689517590582682677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31346355586023454110243569 23509766689517590582682677)
                ·
                  refine ⟨2204040627142274117126501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23509766689517590582682677 2204040627142274117126501)
                  ·
                    refine ⟨413257617589176396961219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2204040627142274117126501 413257617589176396961219)
                    ·
                      rfl

theorem cell23_2414449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_2414449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414449 prefixEnd_2414449 := by exact prefixLift 2414449
  have htrace : WordTrace (prefixWord ++ tailWord_2414449) baseStart_2414449 baseEnd_2414449 := by
    simpa [prefixWord, tailWord_2414449, baseEnd_2414449] using wordTrace_append hprefix tailTrace_2414449
  have hstable : (prefixWord ++ tailWord_2414449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414449).length < 2 ^ (prefixWord ++ tailWord_2414449).sum := by decide
  have hdescent : baseEnd_2414449 < baseStart_2414449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414459 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 3]
def baseStart_2414459 : Nat := 118140960795 + 2414459 * 2 ^ 59
def prefixEnd_2414459 : Nat := 4983230072969 + 3 ^ 40 * 2414459 * 2
def baseEnd_2414459 : Nat := 1239777987574074151758611

theorem tailTrace_2414459 : CollatzResearch.WordTrace tailWord_2414459 prefixEnd_2414459 1239777987574074151758611 := by
  unfold tailWord_2414459
  simp only [CollatzResearch.WordTrace]
  refine ⟨88062554359834874612910431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58708369573223249741940287 88062554359834874612910431)
  ·
    refine ⟨132093831539752311919365647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88062554359834874612910431 132093831539752311919365647)
    ·
      refine ⟨198140747309628467879048471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132093831539752311919365647 198140747309628467879048471)
      ·
        refine ⟨297211120964442701818572707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198140747309628467879048471 297211120964442701818572707)
        ·
          refine ⟨445816681446664052727859061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297211120964442701818572707 445816681446664052727859061)
          ·
            refine ⟨41795313885624754943236787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 445816681446664052727859061 41795313885624754943236787)
            ·
              refine ⟨62692970828437132414855181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41795313885624754943236787 62692970828437132414855181)
              ·
                refine ⟨23509864060663924655570693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62692970828437132414855181 23509864060663924655570693)
                ·
                  refine ⟨4408099511374485872919505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23509864060663924655570693 4408099511374485872919505)
                  ·
                    refine ⟨3306074633530864404689629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4408099511374485872919505 3306074633530864404689629)
                    ·
                      refine ⟨1239777987574074151758611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3306074633530864404689629 1239777987574074151758611)
                      ·
                        rfl

theorem cell23_2414459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 3].length) (baseStart_2414459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414459 prefixEnd_2414459 := by exact prefixLift 2414459
  have htrace : WordTrace (prefixWord ++ tailWord_2414459) baseStart_2414459 baseEnd_2414459 := by
    simpa [prefixWord, tailWord_2414459, baseEnd_2414459] using wordTrace_append hprefix tailTrace_2414459
  have hstable : (prefixWord ++ tailWord_2414459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414459).length < 2 ^ (prefixWord ++ tailWord_2414459).sum := by decide
  have hdescent : baseEnd_2414459 < baseStart_2414459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414500 : List Nat := [2, 3, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_2414500 : Nat := 118140960795 + 2414500 * 2 ^ 59
def prefixEnd_2414500 : Nat := 4983230072969 + 3 ^ 40 * 2414500 * 2
def baseEnd_2414500 : Nat := 413266346760302830448641

theorem tailTrace_2414500 : CollatzResearch.WordTrace tailWord_2414500 prefixEnd_2414500 413266346760302830448641 := by
  unfold tailWord_2414500
  simp only [CollatzResearch.WordTrace]
  refine ⟨44032024876343169307576477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58709366501790892410101969 44032024876343169307576477)
  ·
    refine ⟨16512009328628688490341179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44032024876343169307576477 16512009328628688490341179)
    ·
      refine ⟨24768013992943032735511769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16512009328628688490341179 24768013992943032735511769)
      ·
        refine ⟨18576010494707274551633827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24768013992943032735511769 18576010494707274551633827)
        ·
          refine ⟨27864015742060911827450741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18576010494707274551633827 27864015742060911827450741)
          ·
            refine ⟨2612251475818210483823507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27864015742060911827450741 2612251475818210483823507)
            ·
              refine ⟨3918377213727315725735261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612251475818210483823507 3918377213727315725735261)
              ·
                refine ⟨1469391455147743397150723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3918377213727315725735261 1469391455147743397150723)
                ·
                  refine ⟨2204087182721615095726085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469391455147743397150723 2204087182721615095726085)
                  ·
                    refine ⟨413266346760302830448641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2204087182721615095726085 413266346760302830448641)
                    ·
                      rfl

theorem cell23_2414500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_2414500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414500 prefixEnd_2414500 := by exact prefixLift 2414500
  have htrace : WordTrace (prefixWord ++ tailWord_2414500) baseStart_2414500 baseEnd_2414500 := by
    simpa [prefixWord, tailWord_2414500, baseEnd_2414500] using wordTrace_append hprefix tailTrace_2414500
  have hstable : (prefixWord ++ tailWord_2414500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414500).length < 2 ^ (prefixWord ++ tailWord_2414500).sum := by decide
  have hdescent : baseEnd_2414500 < baseStart_2414500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414539 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 1, 6]
def baseStart_2414539 : Nat := 118140960795 + 2414539 * 2 ^ 59
def prefixEnd_2414539 : Nat := 4983230072969 + 3 ^ 40 * 2414539 * 2
def baseEnd_2414539 : Nat := 413273022008811279586081

theorem tailTrace_2414539 : CollatzResearch.WordTrace tailWord_2414539 prefixEnd_2414539 413273022008811279586081 := by
  unfold tailWord_2414539
  simp only [CollatzResearch.WordTrace]
  refine ⟨88065472199545048275822671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58710314799696698850548447 88065472199545048275822671)
  ·
    refine ⟨132098208299317572413734007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88065472199545048275822671 132098208299317572413734007)
    ·
      refine ⟨198147312448976358620601011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132098208299317572413734007 198147312448976358620601011)
      ·
        refine ⟨297220968673464537930901517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198147312448976358620601011 297220968673464537930901517)
        ·
          refine ⟨111457863252549201724088069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297220968673464537930901517 111457863252549201724088069)
          ·
            refine ⟨20898349359852975323266513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111457863252549201724088069 20898349359852975323266513)
            ·
              refine ⟨15673762019889731492449885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20898349359852975323266513 15673762019889731492449885)
              ·
                refine ⟨5877660757458649309668707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15673762019889731492449885 5877660757458649309668707)
                ·
                  refine ⟨8816491136187973964503061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5877660757458649309668707 8816491136187973964503061)
                  ·
                    refine ⟨413273022008811279586081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8816491136187973964503061 413273022008811279586081)
                    ·
                      rfl

theorem cell23_2414539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 6].length) (baseStart_2414539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414539 prefixEnd_2414539 := by exact prefixLift 2414539
  have htrace : WordTrace (prefixWord ++ tailWord_2414539) baseStart_2414539 baseEnd_2414539 := by
    simpa [prefixWord, tailWord_2414539, baseEnd_2414539] using wordTrace_append hprefix tailTrace_2414539
  have hstable : (prefixWord ++ tailWord_2414539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414539).length < 2 ^ (prefixWord ++ tailWord_2414539).sum := by decide
  have hdescent : baseEnd_2414539 < baseStart_2414539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414574 : List Nat := [4, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_2414574 : Nat := 118140960795 + 2414574 * 2 ^ 59
def prefixEnd_2414574 : Nat := 4983230072969 + 3 ^ 40 * 2414574 * 2
def baseEnd_2414574 : Nat := 1239837037849341201820583

theorem tailTrace_2414574 : CollatzResearch.WordTrace tailWord_2414574 prefixEnd_2414574 1239837037849341201820583 := by
  unfold tailWord_2414574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11008343594302281156668347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58711165836278832835564517 11008343594302281156668347)
  ·
    refine ⟨16512515391453421735002521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11008343594302281156668347 16512515391453421735002521)
    ·
      refine ⟨12384386543590066301251891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16512515391453421735002521 12384386543590066301251891)
      ·
        refine ⟨18576579815385099451877837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12384386543590066301251891 18576579815385099451877837)
        ·
          refine ⟨6966217430769412294454189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18576579815385099451877837 6966217430769412294454189)
          ·
            refine ⟨2612331536538529610420321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6966217430769412294454189 2612331536538529610420321)
            ·
              refine ⟨1959248652403897207815241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2612331536538529610420321 1959248652403897207815241)
              ·
                refine ⟨1469436489302922905861431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1959248652403897207815241 1469436489302922905861431)
                ·
                  refine ⟨2204154733954384358792147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469436489302922905861431 2204154733954384358792147)
                  ·
                    refine ⟨3306232100931576538188221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2204154733954384358792147 3306232100931576538188221)
                    ·
                      refine ⟨1239837037849341201820583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3306232100931576538188221 1239837037849341201820583)
                      ·
                        rfl

theorem cell23_2414574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_2414574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414574 prefixEnd_2414574 := by exact prefixLift 2414574
  have htrace : WordTrace (prefixWord ++ tailWord_2414574) baseStart_2414574 baseEnd_2414574 := by
    simpa [prefixWord, tailWord_2414574, baseEnd_2414574] using wordTrace_append hprefix tailTrace_2414574
  have hstable : (prefixWord ++ tailWord_2414574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414574).length < 2 ^ (prefixWord ++ tailWord_2414574).sum := by decide
  have hdescent : baseEnd_2414574 < baseStart_2414574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414589 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_2414589 : Nat := 118140960795 + 2414589 * 2 ^ 59
def prefixEnd_2414589 : Nat := 4983230072969 + 3 ^ 40 * 2414589 * 2
def baseEnd_2414589 : Nat := 1239844740059158643133013

theorem tailTrace_2414589 : CollatzResearch.WordTrace tailWord_2414589 prefixEnd_2414589 1239844740059158643133013 := by
  unfold tailWord_2414589
  simp only [CollatzResearch.WordTrace]
  refine ⟨88067295849363906815142821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58711530566242604543428547 88067295849363906815142821)
  ·
    refine ⟨16512617971755732527839279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88067295849363906815142821 16512617971755732527839279)
    ·
      refine ⟨24768926957633598791758919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16512617971755732527839279 24768926957633598791758919)
      ·
        refine ⟨37153390436450398187638379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24768926957633598791758919 37153390436450398187638379)
        ·
          refine ⟨55730085654675597281457569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37153390436450398187638379 55730085654675597281457569)
          ·
            refine ⟨41797564241006697961093177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55730085654675597281457569 41797564241006697961093177)
            ·
              refine ⟨31348173180755023470819883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41797564241006697961093177 31348173180755023470819883)
              ·
                refine ⟨47022259771132535206229825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31348173180755023470819883 47022259771132535206229825)
                ·
                  refine ⟨35266694828349401404672369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47022259771132535206229825 35266694828349401404672369)
                  ·
                    refine ⟨26450021121262051053504277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35266694828349401404672369 26450021121262051053504277)
                    ·
                      refine ⟨1239844740059158643133013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26450021121262051053504277 1239844740059158643133013)
                      ·
                        rfl

theorem cell23_2414589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_2414589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414589 prefixEnd_2414589 := by exact prefixLift 2414589
  have htrace : WordTrace (prefixWord ++ tailWord_2414589) baseStart_2414589 baseEnd_2414589 := by
    simpa [prefixWord, tailWord_2414589, baseEnd_2414589] using wordTrace_append hprefix tailTrace_2414589
  have hstable : (prefixWord ++ tailWord_2414589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414589).length < 2 ^ (prefixWord ++ tailWord_2414589).sum := by decide
  have hdescent : baseEnd_2414589 < baseStart_2414589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414590 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2414590 : Nat := 118140960795 + 2414590 * 2 ^ 59
def prefixEnd_2414590 : Nat := 4983230072969 + 3 ^ 40 * 2414590 * 2
def baseEnd_2414590 : Nat := 413281751179937713073503

theorem tailTrace_2414590 : CollatzResearch.WordTrace tailWord_2414590 prefixEnd_2414590 413281751179937713073503 := by
  unfold tailWord_2414590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11008416540295035498241153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58711554881573522657286149 11008416540295035498241153)
  ·
    refine ⟨8256312405221276623680865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11008416540295035498241153 8256312405221276623680865)
    ·
      refine ⟨6192234303915957467760649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8256312405221276623680865 6192234303915957467760649)
      ·
        refine ⟨4644175727936968100820487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6192234303915957467760649 4644175727936968100820487)
        ·
          refine ⟨6966263591905452151230731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4644175727936968100820487 6966263591905452151230731)
          ·
            refine ⟨10449395387858178226846097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6966263591905452151230731 10449395387858178226846097)
            ·
              refine ⟨7837046540893633670134573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10449395387858178226846097 7837046540893633670134573)
              ·
                refine ⟨2938892452835112626300465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7837046540893633670134573 2938892452835112626300465)
                ·
                  refine ⟨2204169339626334469725349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2938892452835112626300465 2204169339626334469725349)
                  ·
                    refine ⟨413281751179937713073503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2204169339626334469725349 413281751179937713073503)
                    ·
                      rfl

theorem cell23_2414590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2414590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414590 prefixEnd_2414590 := by exact prefixLift 2414590
  have htrace : WordTrace (prefixWord ++ tailWord_2414590) baseStart_2414590 baseEnd_2414590 := by
    simpa [prefixWord, tailWord_2414590, baseEnd_2414590] using wordTrace_append hprefix tailTrace_2414590
  have hstable : (prefixWord ++ tailWord_2414590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414590).length < 2 ^ (prefixWord ++ tailWord_2414590).sum := by decide
  have hdescent : baseEnd_2414590 < baseStart_2414590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414619 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 4]
def baseStart_2414619 : Nat := 118140960795 + 2414619 * 2 ^ 59
def prefixEnd_2414619 : Nat := 4983230072969 + 3 ^ 40 * 2414619 * 2
def baseEnd_2414619 : Nat := 1239860144478793525757875

theorem tailTrace_2414619 : CollatzResearch.WordTrace tailWord_2414619 prefixEnd_2414619 1239860144478793525757875 := by
  unfold tailWord_2414619
  simp only [CollatzResearch.WordTrace]
  refine ⟨88068390039255221938734911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58712260026170147959156607 88068390039255221938734911)
  ·
    refine ⟨132102585058882832908102367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88068390039255221938734911 132102585058882832908102367)
    ·
      refine ⟨198153877588324249362153551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132102585058882832908102367 198153877588324249362153551)
      ·
        refine ⟨297230816382486374043230327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198153877588324249362153551 297230816382486374043230327)
        ·
          refine ⟨445846224573729561064845491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297230816382486374043230327 445846224573729561064845491)
          ·
            refine ⟨668769336860594341597268237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445846224573729561064845491 668769336860594341597268237)
            ·
              refine ⟨250788501322722878098975589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 668769336860594341597268237 250788501322722878098975589)
              ·
                refine ⟨47022843998010539643557923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250788501322722878098975589 47022843998010539643557923)
                ·
                  refine ⟨70534265997015809465336885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47022843998010539643557923 70534265997015809465336885)
                  ·
                    refine ⟨6612587437220232137375333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70534265997015809465336885 6612587437220232137375333)
                    ·
                      refine ⟨1239860144478793525757875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6612587437220232137375333 1239860144478793525757875)
                      ·
                        rfl

theorem cell23_2414619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 4].length) (baseStart_2414619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414619 prefixEnd_2414619 := by exact prefixLift 2414619
  have htrace : WordTrace (prefixWord ++ tailWord_2414619) baseStart_2414619 baseEnd_2414619 := by
    simpa [prefixWord, tailWord_2414619, baseEnd_2414619] using wordTrace_append hprefix tailTrace_2414619
  have hstable : (prefixWord ++ tailWord_2414619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414619).length < 2 ^ (prefixWord ++ tailWord_2414619).sum := by decide
  have hdescent : baseEnd_2414619 < baseStart_2414619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414639 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_2414639 : Nat := 118140960795 + 2414639 * 2 ^ 59
def prefixEnd_2414639 : Nat := 4983230072969 + 3 ^ 40 * 2414639 * 2
def baseEnd_2414639 : Nat := 1239870414091883447507783

theorem tailTrace_2414639 : CollatzResearch.WordTrace tailWord_2414639 prefixEnd_2414639 1239870414091883447507783 := by
  unfold tailWord_2414639
  simp only [CollatzResearch.WordTrace]
  refine ⟨88069119499182765354462971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58712746332788510236308647 88069119499182765354462971)
  ·
    refine ⟨132103679248774148031694457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88069119499182765354462971 132103679248774148031694457)
    ·
      refine ⟨99077759436580611023770843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132103679248774148031694457 99077759436580611023770843)
      ·
        refine ⟨148616639154870916535656265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99077759436580611023770843 148616639154870916535656265)
        ·
          refine ⟨111462479366153187401742199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148616639154870916535656265 111462479366153187401742199)
          ·
            refine ⟨167193719049229781102613299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111462479366153187401742199 167193719049229781102613299)
            ·
              refine ⟨250790578573844671653919949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167193719049229781102613299 250790578573844671653919949)
              ·
                refine ⟨94046466965191751870219981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250790578573844671653919949 94046466965191751870219981)
                ·
                  refine ⟨35267425111946906951332493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94046466965191751870219981 35267425111946906951332493)
                  ·
                    refine ⟨13225284416980090106749685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35267425111946906951332493 13225284416980090106749685)
                    ·
                      refine ⟨1239870414091883447507783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13225284416980090106749685 1239870414091883447507783)
                      ·
                        rfl

theorem cell23_2414639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_2414639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414639 prefixEnd_2414639 := by exact prefixLift 2414639
  have htrace : WordTrace (prefixWord ++ tailWord_2414639) baseStart_2414639 baseEnd_2414639 := by
    simpa [prefixWord, tailWord_2414639, baseEnd_2414639] using wordTrace_append hprefix tailTrace_2414639
  have hstable : (prefixWord ++ tailWord_2414639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414639).length < 2 ^ (prefixWord ++ tailWord_2414639).sum := by decide
  have hdescent : baseEnd_2414639 < baseStart_2414639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414657 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_2414657 : Nat := 118140960795 + 2414657 * 2 ^ 59
def prefixEnd_2414657 : Nat := 4983230072969 + 3 ^ 40 * 2414657 * 2
def baseEnd_2414657 : Nat := 1239879656743664377082701

theorem tailTrace_2414657 : CollatzResearch.WordTrace tailWord_2414657 prefixEnd_2414657 1239879656743664377082701 := by
  unfold tailWord_2414657
  simp only [CollatzResearch.WordTrace]
  refine ⟨88069776013117554428618225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58713184008745036285745483 88069776013117554428618225)
  ·
    refine ⟨66052332009838165821463669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88069776013117554428618225 66052332009838165821463669)
    ·
      refine ⟨6192406125922328045762219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66052332009838165821463669 6192406125922328045762219)
      ·
        refine ⟨9288609188883492068643329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6192406125922328045762219 9288609188883492068643329)
        ·
          refine ⟨6966456891662619051482497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9288609188883492068643329 6966456891662619051482497)
          ·
            refine ⟨5224842668746964288611873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6966456891662619051482497 5224842668746964288611873)
            ·
              refine ⟨3918632001560223216458905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5224842668746964288611873 3918632001560223216458905)
              ·
                refine ⟨2938974001170167412344179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3918632001560223216458905 2938974001170167412344179)
                ·
                  refine ⟨4408461001755251118516269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938974001170167412344179 4408461001755251118516269)
                  ·
                    refine ⟨1653172875658219169443601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4408461001755251118516269 1653172875658219169443601)
                    ·
                      refine ⟨1239879656743664377082701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653172875658219169443601 1239879656743664377082701)
                      ·
                        rfl

theorem cell23_2414657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_2414657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414657 prefixEnd_2414657 := by exact prefixLift 2414657
  have htrace : WordTrace (prefixWord ++ tailWord_2414657) baseStart_2414657 baseEnd_2414657 := by
    simpa [prefixWord, tailWord_2414657, baseEnd_2414657] using wordTrace_append hprefix tailTrace_2414657
  have hstable : (prefixWord ++ tailWord_2414657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414657).length < 2 ^ (prefixWord ++ tailWord_2414657).sum := by decide
  have hdescent : baseEnd_2414657 < baseStart_2414657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414659 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 9]
def baseStart_2414659 : Nat := 118140960795 + 2414659 * 2 ^ 59
def prefixEnd_2414659 : Nat := 4983230072969 + 3 ^ 40 * 2414659 * 2
def baseEnd_2414659 : Nat := 137764520411663707695299

theorem tailTrace_2414659 : CollatzResearch.WordTrace tailWord_2414659 prefixEnd_2414659 137764520411663707695299 := by
  unfold tailWord_2414659
  simp only [CollatzResearch.WordTrace]
  refine ⟨88069848959110308770191031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58713232639406872513460687 88069848959110308770191031)
  ·
    refine ⟨132104773438665463155286547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88069848959110308770191031 132104773438665463155286547)
    ·
      refine ⟨198157160157998194732929821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132104773438665463155286547 198157160157998194732929821)
      ·
        refine ⟨74308935059249323024848683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198157160157998194732929821 74308935059249323024848683)
        ·
          refine ⟨111463402588873984537273025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74308935059249323024848683 111463402588873984537273025)
          ·
            refine ⟨83597551941655488402954769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111463402588873984537273025 83597551941655488402954769)
            ·
              refine ⟨62698163956241616302216077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83597551941655488402954769 62698163956241616302216077)
              ·
                refine ⟨23511811483590606113331029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62698163956241616302216077 23511811483590606113331029)
                ·
                  refine ⟨137764520411663707695299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23511811483590606113331029 137764520411663707695299)
                  ·
                    rfl

theorem cell23_2414659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 9].length) (baseStart_2414659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414659 prefixEnd_2414659 := by exact prefixLift 2414659
  have htrace : WordTrace (prefixWord ++ tailWord_2414659) baseStart_2414659 baseEnd_2414659 := by
    simpa [prefixWord, tailWord_2414659, baseEnd_2414659] using wordTrace_append hprefix tailTrace_2414659
  have hstable : (prefixWord ++ tailWord_2414659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414659).length < 2 ^ (prefixWord ++ tailWord_2414659).sum := by decide
  have hdescent : baseEnd_2414659 < baseStart_2414659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414670 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_2414670 : Nat := 118140960795 + 2414670 * 2 ^ 59
def prefixEnd_2414670 : Nat := 4983230072969 + 3 ^ 40 * 2414670 * 2
def baseEnd_2414670 : Nat := 1239886331992172826220141

theorem tailTrace_2414670 : CollatzResearch.WordTrace tailWord_2414670 prefixEnd_2414670 1239886331992172826220141 := by
  unfold tailWord_2414670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11008781270258807206105183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58713500108046971765894309 11008781270258807206105183)
  ·
    refine ⟨16513171905388210809157775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11008781270258807206105183 16513171905388210809157775)
    ·
      refine ⟨24769757858082316213736663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16513171905388210809157775 24769757858082316213736663)
      ·
        refine ⟨37154636787123474320604995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24769757858082316213736663 37154636787123474320604995)
        ·
          refine ⟨55731955180685211480907493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37154636787123474320604995 55731955180685211480907493)
          ·
            refine ⟨10449741596378477152670155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55731955180685211480907493 10449741596378477152670155)
            ·
              refine ⟨15674612394567715729005233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10449741596378477152670155 15674612394567715729005233)
              ·
                refine ⟨11755959295925786796753925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15674612394567715729005233 11755959295925786796753925)
                ·
                  refine ⟨2204242367986085024391361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11755959295925786796753925 2204242367986085024391361)
                  ·
                    refine ⟨1653181775989563768293521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2204242367986085024391361 1653181775989563768293521)
                    ·
                      refine ⟨1239886331992172826220141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653181775989563768293521 1239886331992172826220141)
                      ·
                        rfl

theorem cell23_2414670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_2414670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414670 prefixEnd_2414670 := by exact prefixLift 2414670
  have htrace : WordTrace (prefixWord ++ tailWord_2414670) baseStart_2414670 baseEnd_2414670 := by
    simpa [prefixWord, tailWord_2414670, baseEnd_2414670] using wordTrace_append hprefix tailTrace_2414670
  have hstable : (prefixWord ++ tailWord_2414670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414670).length < 2 ^ (prefixWord ++ tailWord_2414670).sum := by decide
  have hdescent : baseEnd_2414670 < baseStart_2414670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414693 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 7]
def baseStart_2414693 : Nat := 118140960795 + 2414693 * 2 ^ 59
def prefixEnd_2414693 : Nat := 4983230072969 + 3 ^ 40 * 2414693 * 2
def baseEnd_2414693 : Nat := 137766460227469581803615

theorem tailTrace_2414693 : CollatzResearch.WordTrace tailWord_2414693 prefixEnd_2414693 137766460227469581803615 := by
  unfold tailWord_2414693
  simp only [CollatzResearch.WordTrace]
  refine ⟨88071089040987132576928733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58714059360658088384619155 88071089040987132576928733)
  ·
    refine ⟨33026658390370174716348275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88071089040987132576928733 33026658390370174716348275)
    ·
      refine ⟨49539987585555262074522413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33026658390370174716348275 49539987585555262074522413)
      ·
        refine ⟨18577495344583223277945905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49539987585555262074522413 18577495344583223277945905)
        ·
          refine ⟨13933121508437417458459429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18577495344583223277945905 13933121508437417458459429)
          ·
            refine ⟨2612460282832015773461143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13933121508437417458459429 2612460282832015773461143)
            ·
              refine ⟨3918690424248023660191715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612460282832015773461143 3918690424248023660191715)
              ·
                refine ⟨5878035636372035490287573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3918690424248023660191715 5878035636372035490287573)
                ·
                  refine ⟨137766460227469581803615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5878035636372035490287573 137766460227469581803615)
                  ·
                    rfl

theorem cell23_2414693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_2414693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414693 prefixEnd_2414693 := by exact prefixLift 2414693
  have htrace : WordTrace (prefixWord ++ tailWord_2414693) baseStart_2414693 baseEnd_2414693 := by
    simpa [prefixWord, tailWord_2414693, baseEnd_2414693] using wordTrace_append hprefix tailTrace_2414693
  have hstable : (prefixWord ++ tailWord_2414693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414693).length < 2 ^ (prefixWord ++ tailWord_2414693).sum := by decide
  have hdescent : baseEnd_2414693 < baseStart_2414693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414704 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 2, 2, 2]
def baseStart_2414704 : Nat := 118140960795 + 2414704 * 2 ^ 59
def prefixEnd_2414704 : Nat := 4983230072969 + 3 ^ 40 * 2414704 * 2
def baseEnd_2414704 : Nat := 1239903790334425693194985

theorem tailTrace_2414704 : CollatzResearch.WordTrace tailWord_2414704 prefixEnd_2414704 1239903790334425693194985 := by
  unfold tailWord_2414704
  simp only [CollatzResearch.WordTrace]
  refine ⟨44035745121973640727789583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58714326829298187637052777 44035745121973640727789583)
  ·
    refine ⟨66053617682960461091684375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44035745121973640727789583 66053617682960461091684375)
    ·
      refine ⟨99080426524440691637526563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66053617682960461091684375 99080426524440691637526563)
      ·
        refine ⟨148620639786661037456289845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99080426524440691637526563 148620639786661037456289845)
        ·
          refine ⟨13933184979999472261527173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148620639786661037456289845 13933184979999472261527173)
          ·
            refine ⟨2612472183749901049036345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13933184979999472261527173 2612472183749901049036345)
            ·
              refine ⟨1959354137812425786777259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2612472183749901049036345 1959354137812425786777259)
              ·
                refine ⟨2939031206718638680165889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959354137812425786777259 2939031206718638680165889)
                ·
                  refine ⟨2204273405038979010124417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2939031206718638680165889 2204273405038979010124417)
                  ·
                    refine ⟨1653205053779234257593313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2204273405038979010124417 1653205053779234257593313)
                    ·
                      refine ⟨1239903790334425693194985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653205053779234257593313 1239903790334425693194985)
                      ·
                        rfl

theorem cell23_2414704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 2, 2, 2].length) (baseStart_2414704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414704 prefixEnd_2414704 := by exact prefixLift 2414704
  have htrace : WordTrace (prefixWord ++ tailWord_2414704) baseStart_2414704 baseEnd_2414704 := by
    simpa [prefixWord, tailWord_2414704, baseEnd_2414704] using wordTrace_append hprefix tailTrace_2414704
  have hstable : (prefixWord ++ tailWord_2414704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414704).length < 2 ^ (prefixWord ++ tailWord_2414704).sum := by decide
  have hdescent : baseEnd_2414704 < baseStart_2414704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414723 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 2, 5]
def baseStart_2414723 : Nat := 118140960795 + 2414723 * 2 ^ 59
def prefixEnd_2414723 : Nat := 4983230072969 + 3 ^ 40 * 2414723 * 2
def baseEnd_2414723 : Nat := 413304515488953706285799

theorem tailTrace_2414723 : CollatzResearch.WordTrace tailWord_2414723 prefixEnd_2414723 413304515488953706285799 := by
  unfold tailWord_2414723
  simp only [CollatzResearch.WordTrace]
  refine ⟨88072183230878447700520823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58714788820585631800347215 88072183230878447700520823)
  ·
    refine ⟨132108274846317671550781235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88072183230878447700520823 132108274846317671550781235)
    ·
      refine ⟨198162412269476507326171853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132108274846317671550781235 198162412269476507326171853)
      ·
        refine ⟨74310904601053690247314445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198162412269476507326171853 74310904601053690247314445)
        ·
          refine ⟨27866589225395133842742917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74310904601053690247314445 27866589225395133842742917)
          ·
            refine ⟨5224985479761587595514297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27866589225395133842742917 5224985479761587595514297)
            ·
              refine ⟨3918739109821190696635723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5224985479761587595514297 3918739109821190696635723)
              ·
                refine ⟨5878108664731786044953585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3918739109821190696635723 5878108664731786044953585)
                ·
                  refine ⟨4408581498548839533715189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5878108664731786044953585 4408581498548839533715189)
                  ·
                    refine ⟨413304515488953706285799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4408581498548839533715189 413304515488953706285799)
                    ·
                      rfl

theorem cell23_2414723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 5].length) (baseStart_2414723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414723 prefixEnd_2414723 := by exact prefixLift 2414723
  have htrace : WordTrace (prefixWord ++ tailWord_2414723) baseStart_2414723 baseEnd_2414723 := by
    simpa [prefixWord, tailWord_2414723, baseEnd_2414723] using wordTrace_append hprefix tailTrace_2414723
  have hstable : (prefixWord ++ tailWord_2414723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414723).length < 2 ^ (prefixWord ++ tailWord_2414723).sum := by decide
  have hdescent : baseEnd_2414723 < baseStart_2414723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414744 : List Nat := [2, 1, 2, 4, 4, 1, 2, 2, 5]
def baseStart_2414744 : Nat := 118140960795 + 2414744 * 2 ^ 59
def prefixEnd_2414744 : Nat := 4983230072969 + 3 ^ 40 * 2414744 * 2
def baseEnd_2414744 : Nat := 137769369951178392966089

theorem tailTrace_2414744 : CollatzResearch.WordTrace tailWord_2414744 prefixEnd_2414744 137769369951178392966089 := by
  unfold tailWord_2414744
  simp only [CollatzResearch.WordTrace]
  refine ⟨44036474581901184143517643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58715299442534912191356857 44036474581901184143517643)
  ·
    refine ⟨66054711872851776215276465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44036474581901184143517643 66054711872851776215276465)
    ·
      refine ⟨49541033904638832161457349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66054711872851776215276465 49541033904638832161457349)
      ·
        refine ⟨9288943857119781030273253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49541033904638832161457349 9288943857119781030273253)
        ·
          refine ⟨1741676973209958943176235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9288943857119781030273253 1741676973209958943176235)
          ·
            refine ⟨2612515459814938414764353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741676973209958943176235 2612515459814938414764353)
            ·
              refine ⟨1959386594861203811073265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2612515459814938414764353 1959386594861203811073265)
              ·
                refine ⟨1469539946145902858304949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1959386594861203811073265 1469539946145902858304949)
                ·
                  refine ⟨137769369951178392966089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1469539946145902858304949 137769369951178392966089)
                  ·
                    rfl

theorem cell23_2414744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 5].length) (baseStart_2414744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414744 prefixEnd_2414744 := by exact prefixLift 2414744
  have htrace : WordTrace (prefixWord ++ tailWord_2414744) baseStart_2414744 baseEnd_2414744 := by
    simpa [prefixWord, tailWord_2414744, baseEnd_2414744] using wordTrace_append hprefix tailTrace_2414744
  have hstable : (prefixWord ++ tailWord_2414744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414744).length < 2 ^ (prefixWord ++ tailWord_2414744).sum := by decide
  have hdescent : baseEnd_2414744 < baseStart_2414744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414780 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_2414780 : Nat := 118140960795 + 2414780 * 2 ^ 59
def prefixEnd_2414780 : Nat := 4983230072969 + 3 ^ 40 * 2414780 * 2
def baseEnd_2414780 : Nat := 1239942814864167395844635

theorem tailTrace_2414780 : CollatzResearch.WordTrace tailWord_2414780 prefixEnd_2414780 1239942814864167395844635 := by
  unfold tailWord_2414780
  simp only [CollatzResearch.WordTrace]
  refine ⟨44037131095835973217672897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58716174794447964290230529 44037131095835973217672897)
  ·
    refine ⟨33027848321876979913254673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44037131095835973217672897 33027848321876979913254673)
    ·
      refine ⟨24770886241407734934941005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33027848321876979913254673 24770886241407734934941005)
      ·
        refine ⟨9289082340527900600602877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24770886241407734934941005 9289082340527900600602877)
        ·
          refine ⟨3483405877697962725226079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9289082340527900600602877 3483405877697962725226079)
          ·
            refine ⟨5225108816546944087839119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483405877697962725226079 5225108816546944087839119)
            ·
              refine ⟨7837663224820416131758679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5225108816546944087839119 7837663224820416131758679)
              ·
                refine ⟨11756494837230624197638019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7837663224820416131758679 11756494837230624197638019)
                ·
                  refine ⟨17634742255845936296457029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11756494837230624197638019 17634742255845936296457029)
                  ·
                    refine ⟨3306514172971113055585693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17634742255845936296457029 3306514172971113055585693)
                    ·
                      refine ⟨1239942814864167395844635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3306514172971113055585693 1239942814864167395844635)
                      ·
                        rfl

theorem cell23_2414780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_2414780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414780 prefixEnd_2414780 := by exact prefixLift 2414780
  have htrace : WordTrace (prefixWord ++ tailWord_2414780) baseStart_2414780 baseEnd_2414780 := by
    simpa [prefixWord, tailWord_2414780, baseEnd_2414780] using wordTrace_append hprefix tailTrace_2414780
  have hstable : (prefixWord ++ tailWord_2414780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414780).length < 2 ^ (prefixWord ++ tailWord_2414780).sum := by decide
  have hdescent : baseEnd_2414780 < baseStart_2414780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414803 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 5, 5, 2]
def baseStart_2414803 : Nat := 118140960795 + 2414803 * 2 ^ 59
def prefixEnd_2414803 : Nat := 4983230072969 + 3 ^ 40 * 2414803 * 2
def baseEnd_2414803 : Nat := 1239954624919220805857029

theorem tailTrace_2414803 : CollatzResearch.WordTrace tailWord_2414803 prefixEnd_2414803 1239954624919220805857029 := by
  unfold tailWord_2414803
  simp only [CollatzResearch.WordTrace]
  refine ⟨88075101070588621363433063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58716734047059080908955375 88075101070588621363433063)
  ·
    refine ⟨132112651605882932045149595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88075101070588621363433063 132112651605882932045149595)
    ·
      refine ⟨198168977408824398067724393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132112651605882932045149595 198168977408824398067724393)
      ·
        refine ⟨148626733056618298550793295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198168977408824398067724393 148626733056618298550793295)
        ·
          refine ⟨222940099584927447826189943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148626733056618298550793295 222940099584927447826189943)
          ·
            refine ⟨334410149377391171739284915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222940099584927447826189943 334410149377391171739284915)
            ·
              refine ⟨501615224066086757608927373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334410149377391171739284915 501615224066086757608927373)
              ·
                refine ⟨188105709024782534103347765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501615224066086757608927373 188105709024782534103347765)
                ·
                  refine ⟨17634910221073362572188853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188105709024782534103347765 17634910221073362572188853)
                  ·
                    refine ⟨1653272833225627741142705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17634910221073362572188853 1653272833225627741142705)
                    ·
                      refine ⟨1239954624919220805857029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653272833225627741142705 1239954624919220805857029)
                      ·
                        rfl

theorem cell23_2414803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 5, 2].length) (baseStart_2414803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414803 prefixEnd_2414803 := by exact prefixLift 2414803
  have htrace : WordTrace (prefixWord ++ tailWord_2414803) baseStart_2414803 baseEnd_2414803 := by
    simpa [prefixWord, tailWord_2414803, baseEnd_2414803] using wordTrace_append hprefix tailTrace_2414803
  have hstable : (prefixWord ++ tailWord_2414803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414803).length < 2 ^ (prefixWord ++ tailWord_2414803).sum := by decide
  have hdescent : baseEnd_2414803 < baseStart_2414803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414810 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_2414810 : Nat := 118140960795 + 2414810 * 2 ^ 59
def prefixEnd_2414810 : Nat := 4983230072969 + 3 ^ 40 * 2414810 * 2
def baseEnd_2414810 : Nat := 1239958219283802278469497

theorem tailTrace_2414810 : CollatzResearch.WordTrace tailWord_2414810 prefixEnd_2414810 1239958219283802278469497 := by
  unfold tailWord_2414810
  simp only [CollatzResearch.WordTrace]
  refine ⟨22018839095390815389734471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58716904254375507705958589 22018839095390815389734471)
  ·
    refine ⟨33028258643086223084601707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22018839095390815389734471 33028258643086223084601707)
    ·
      refine ⟨49542387964629334626902561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33028258643086223084601707 49542387964629334626902561)
      ·
        refine ⟨37156790973472000970176921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49542387964629334626902561 37156790973472000970176921)
        ·
          refine ⟨27867593230104000727632691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37156790973472000970176921 27867593230104000727632691)
          ·
            refine ⟨41801389845156001091449037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27867593230104000727632691 41801389845156001091449037)
            ·
              refine ⟨15675521191933500409293389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41801389845156001091449037 15675521191933500409293389)
              ·
                refine ⟨5878320446975062653485021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15675521191933500409293389 5878320446975062653485021)
                ·
                  refine ⟨2204370167615648495056883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5878320446975062653485021 2204370167615648495056883)
                  ·
                    refine ⟨3306555251423472742585325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2204370167615648495056883 3306555251423472742585325)
                    ·
                      refine ⟨1239958219283802278469497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3306555251423472742585325 1239958219283802278469497)
                      ·
                        rfl

theorem cell23_2414810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_2414810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414810 prefixEnd_2414810 := by exact prefixLift 2414810
  have htrace : WordTrace (prefixWord ++ tailWord_2414810) baseStart_2414810 baseEnd_2414810 := by
    simpa [prefixWord, tailWord_2414810, baseEnd_2414810] using wordTrace_append hprefix tailTrace_2414810
  have hstable : (prefixWord ++ tailWord_2414810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414810).length < 2 ^ (prefixWord ++ tailWord_2414810).sum := by decide
  have hdescent : baseEnd_2414810 < baseStart_2414810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414833 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_2414833 : Nat := 118140960795 + 2414833 * 2 ^ 59
def prefixEnd_2414833 : Nat := 4983230072969 + 3 ^ 40 * 2414833 * 2
def baseEnd_2414833 : Nat := 1239970029338855688481891

theorem tailTrace_2414833 : CollatzResearch.WordTrace tailWord_2414833 prefixEnd_2414833 1239970029338855688481891 := by
  unfold tailWord_2414833
  simp only [CollatzResearch.WordTrace]
  refine ⟨88076195260479936487025153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58717463506986624324683435 88076195260479936487025153)
  ·
    refine ⟨66057146445359952365268865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88076195260479936487025153 66057146445359952365268865)
    ·
      refine ⟨49542859834019964273951649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66057146445359952365268865 49542859834019964273951649)
      ·
        refine ⟨37157144875514973205463737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49542859834019964273951649 37157144875514973205463737)
        ·
          refine ⟨27867858656636229904097803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37157144875514973205463737 27867858656636229904097803)
          ·
            refine ⟨41801787984954344856146705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27867858656636229904097803 41801787984954344856146705)
            ·
              refine ⟨31351340988715758642110029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41801787984954344856146705 31351340988715758642110029)
              ·
                refine ⟨11756752870768409490791261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31351340988715758642110029 11756752870768409490791261)
                ·
                  refine ⟨4408782326538153559046723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11756752870768409490791261 4408782326538153559046723)
                  ·
                    refine ⟨6613173489807230338570085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4408782326538153559046723 6613173489807230338570085)
                    ·
                      refine ⟨1239970029338855688481891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6613173489807230338570085 1239970029338855688481891)
                      ·
                        rfl

theorem cell23_2414833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_2414833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414833 prefixEnd_2414833 := by exact prefixLift 2414833
  have htrace : WordTrace (prefixWord ++ tailWord_2414833) baseStart_2414833 baseEnd_2414833 := by
    simpa [prefixWord, tailWord_2414833, baseEnd_2414833] using wordTrace_append hprefix tailTrace_2414833
  have hstable : (prefixWord ++ tailWord_2414833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414833).length < 2 ^ (prefixWord ++ tailWord_2414833).sum := by decide
  have hdescent : baseEnd_2414833 < baseStart_2414833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414844 : List Nat := [2, 2, 2, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_2414844 : Nat := 118140960795 + 2414844 * 2 ^ 59
def prefixEnd_2414844 : Nat := 4983230072969 + 3 ^ 40 * 2414844 * 2
def baseEnd_2414844 : Nat := 1239975677626055145444341

theorem tailTrace_2414844 : CollatzResearch.WordTrace tailWord_2414844 prefixEnd_2414844 1239975677626055145444341 := by
  unfold tailWord_2414844
  simp only [CollatzResearch.WordTrace]
  refine ⟨44038298231720042682837793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58717730975626723577117057 44038298231720042682837793)
  ·
    refine ⟨33028723673790032012128345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44038298231720042682837793 33028723673790032012128345)
    ·
      refine ⟨24771542755342524009096259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33028723673790032012128345 24771542755342524009096259)
      ·
        refine ⟨37157314133013786013644389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24771542755342524009096259 37157314133013786013644389)
        ·
          refine ⟨6966996399940084877558323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37157314133013786013644389 6966996399940084877558323)
          ·
            refine ⟨10450494599910127316337485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6966996399940084877558323 10450494599910127316337485)
            ·
              refine ⟨3918935474966297743626557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10450494599910127316337485 3918935474966297743626557)
              ·
                refine ⟨1469600803112361653859959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3918935474966297743626557 1469600803112361653859959)
                ·
                  refine ⟨2204401204668542480789939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469600803112361653859959 2204401204668542480789939)
                  ·
                    refine ⟨3306601807002813721184909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2204401204668542480789939 3306601807002813721184909)
                    ·
                      refine ⟨1239975677626055145444341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3306601807002813721184909 1239975677626055145444341)
                      ·
                        rfl

theorem cell23_2414844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_2414844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414844 prefixEnd_2414844 := by exact prefixLift 2414844
  have htrace : WordTrace (prefixWord ++ tailWord_2414844) baseStart_2414844 baseEnd_2414844 := by
    simpa [prefixWord, tailWord_2414844, baseEnd_2414844] using wordTrace_append hprefix tailTrace_2414844
  have hstable : (prefixWord ++ tailWord_2414844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414844).length < 2 ^ (prefixWord ++ tailWord_2414844).sum := by decide
  have hdescent : baseEnd_2414844 < baseStart_2414844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414860 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_2414860 : Nat := 118140960795 + 2414860 * 2 ^ 59
def prefixEnd_2414860 : Nat := 4983230072969 + 3 ^ 40 * 2414860 * 2
def baseEnd_2414860 : Nat := 413327964438842360948089

theorem tailTrace_2414860 : CollatzResearch.WordTrace tailWord_2414860 prefixEnd_2414860 413327964438842360948089 := by
  unfold tailWord_2414860
  simp only [CollatzResearch.WordTrace]
  refine ⟨44038590015691060049129017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58718120020921413398838689 44038590015691060049129017)
  ·
    refine ⟨33028942511768295036846763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44038590015691060049129017 33028942511768295036846763)
    ·
      refine ⟨49543413767652442555270145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33028942511768295036846763 49543413767652442555270145)
      ·
        refine ⟨37157560325739331916452609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49543413767652442555270145 37157560325739331916452609)
        ·
          refine ⟨27868170244304498937339457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37157560325739331916452609 27868170244304498937339457)
          ·
            refine ⟨20901127683228374203004593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27868170244304498937339457 20901127683228374203004593)
            ·
              refine ⟨15675845762421280652253445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20901127683228374203004593 15675845762421280652253445)
              ·
                refine ⟨2939221080453990122297521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15675845762421280652253445 2939221080453990122297521)
                ·
                  refine ⟨2204415810340492591723141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2939221080453990122297521 2204415810340492591723141)
                  ·
                    refine ⟨413327964438842360948089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2204415810340492591723141 413327964438842360948089)
                    ·
                      rfl

theorem cell23_2414860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_2414860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414860 prefixEnd_2414860 := by exact prefixLift 2414860
  have htrace : WordTrace (prefixWord ++ tailWord_2414860) baseStart_2414860 baseEnd_2414860 := by
    simpa [prefixWord, tailWord_2414860, baseEnd_2414860] using wordTrace_append hprefix tailTrace_2414860
  have hstable : (prefixWord ++ tailWord_2414860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414860).length < 2 ^ (prefixWord ++ tailWord_2414860).sum := by decide
  have hdescent : baseEnd_2414860 < baseStart_2414860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414943 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_2414943 : Nat := 118140960795 + 2414943 * 2 ^ 59
def prefixEnd_2414943 : Nat := 4983230072969 + 3 ^ 40 * 2414943 * 2
def baseEnd_2414943 : Nat := 1240026512210850258106385

theorem tailTrace_2414943 : CollatzResearch.WordTrace tailWord_2414943 prefixEnd_2414943 1240026512210850258106385 := by
  unfold tailWord_2414943
  simp only [CollatzResearch.WordTrace]
  refine ⟨88080207290081425273529483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58720138193387616849019655 88080207290081425273529483)
  ·
    refine ⟨132120310935122137910294225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88080207290081425273529483 132120310935122137910294225)
    ·
      refine ⟨99090233201341603432720669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132120310935122137910294225 99090233201341603432720669)
      ·
        refine ⟨37158837450503101287270251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99090233201341603432720669 37158837450503101287270251)
        ·
          refine ⟨55738256175754651930905377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37158837450503101287270251 55738256175754651930905377)
          ·
            refine ⟨41803692131815988948179033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55738256175754651930905377 41803692131815988948179033)
            ·
              refine ⟨31352769098861991711134275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41803692131815988948179033 31352769098861991711134275)
              ·
                refine ⟨47029153648292987566701413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31352769098861991711134275 47029153648292987566701413)
                ·
                  refine ⟨8817966309054935168756515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47029153648292987566701413 8817966309054935168756515)
                  ·
                    refine ⟨13226949463582402753134773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8817966309054935168756515 13226949463582402753134773)
                    ·
                      refine ⟨1240026512210850258106385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13226949463582402753134773 1240026512210850258106385)
                      ·
                        rfl

theorem cell23_2414943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_2414943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414943 prefixEnd_2414943 := by exact prefixLift 2414943
  have htrace : WordTrace (prefixWord ++ tailWord_2414943) baseStart_2414943 baseEnd_2414943 := by
    simpa [prefixWord, tailWord_2414943, baseEnd_2414943] using wordTrace_append hprefix tailTrace_2414943
  have hstable : (prefixWord ++ tailWord_2414943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414943).length < 2 ^ (prefixWord ++ tailWord_2414943).sum := by decide
  have hdescent : baseEnd_2414943 < baseStart_2414943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414953 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_2414953 : Nat := 118140960795 + 2414953 * 2 ^ 59
def prefixEnd_2414953 : Nat := 4983230072969 + 3 ^ 40 * 2414953 * 2
def baseEnd_2414953 : Nat := 1240031647017395218981339

theorem tailTrace_2414953 : CollatzResearch.WordTrace tailWord_2414953 prefixEnd_2414953 1240031647017395218981339 := by
  unfold tailWord_2414953
  simp only [CollatzResearch.WordTrace]
  refine ⟨88080572020045196981393513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58720381346696797987595675 88080572020045196981393513)
  ·
    refine ⟨66060429015033897736045135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88080572020045196981393513 66060429015033897736045135)
    ·
      refine ⟨99090643522550846604067703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66060429015033897736045135 99090643522550846604067703)
      ·
        refine ⟨148635965283826269906101555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99090643522550846604067703 148635965283826269906101555)
        ·
          refine ⟨222953947925739404859152333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148635965283826269906101555 222953947925739404859152333)
          ·
            refine ⟨83607730472152276822182125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222953947925739404859152333 83607730472152276822182125)
            ·
              refine ⟨31352898927057103808318297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83607730472152276822182125 31352898927057103808318297)
              ·
                refine ⟨23514674195292827856238723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31352898927057103808318297 23514674195292827856238723)
                ·
                  refine ⟨35272011292939241784358085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23514674195292827856238723 35272011292939241784358085)
                  ·
                    refine ⟨6613502117426107834567141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35272011292939241784358085 6613502117426107834567141)
                    ·
                      refine ⟨1240031647017395218981339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6613502117426107834567141 1240031647017395218981339)
                      ·
                        rfl

theorem cell23_2414953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_2414953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414953 prefixEnd_2414953 := by exact prefixLift 2414953
  have htrace : WordTrace (prefixWord ++ tailWord_2414953) baseStart_2414953 baseEnd_2414953 := by
    simpa [prefixWord, tailWord_2414953, baseEnd_2414953] using wordTrace_append hprefix tailTrace_2414953
  have hstable : (prefixWord ++ tailWord_2414953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414953).length < 2 ^ (prefixWord ++ tailWord_2414953).sum := by decide
  have hdescent : baseEnd_2414953 < baseStart_2414953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414957 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_2414957 : Nat := 118140960795 + 2414957 * 2 ^ 59
def prefixEnd_2414957 : Nat := 4983230072969 + 3 ^ 40 * 2414957 * 2
def baseEnd_2414957 : Nat := 1240033700940013203331321

theorem tailTrace_2414957 : CollatzResearch.WordTrace tailWord_2414957 prefixEnd_2414957 1240033700940013203331321 := by
  unfold tailWord_2414957
  simp only [CollatzResearch.WordTrace]
  refine ⟨88080717912030705664539125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58720478608020470443026083 88080717912030705664539125)
  ·
    refine ⟨8257567304252878656050543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88080717912030705664539125 8257567304252878656050543)
    ·
      refine ⟨12386350956379317984075815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8257567304252878656050543 12386350956379317984075815)
      ·
        refine ⟨18579526434568976976113723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12386350956379317984075815 18579526434568976976113723)
        ·
          refine ⟨27869289651853465464170585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18579526434568976976113723 27869289651853465464170585)
          ·
            refine ⟨20901967238890099098127939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27869289651853465464170585 20901967238890099098127939)
            ·
              refine ⟨31352950858335148647191909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20901967238890099098127939 31352950858335148647191909)
              ·
                refine ⟨5878678285937840371348483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31352950858335148647191909 5878678285937840371348483)
                ·
                  refine ⟨8818017428906760557022725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5878678285937840371348483 8818017428906760557022725)
                  ·
                    refine ⟨1653378267920017604441761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8818017428906760557022725 1653378267920017604441761)
                    ·
                      refine ⟨1240033700940013203331321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653378267920017604441761 1240033700940013203331321)
                      ·
                        rfl

theorem cell23_2414957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_2414957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414957 prefixEnd_2414957 := by exact prefixLift 2414957
  have htrace : WordTrace (prefixWord ++ tailWord_2414957) baseStart_2414957 baseEnd_2414957 := by
    simpa [prefixWord, tailWord_2414957, baseEnd_2414957] using wordTrace_append hprefix tailTrace_2414957
  have hstable : (prefixWord ++ tailWord_2414957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414957).length < 2 ^ (prefixWord ++ tailWord_2414957).sum := by decide
  have hdescent : baseEnd_2414957 < baseStart_2414957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2414980 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 7]
def baseStart_2414980 : Nat := 118140960795 + 2414980 * 2 ^ 59
def prefixEnd_2414980 : Nat := 4983230072969 + 3 ^ 40 * 2414980 * 2
def baseEnd_2414980 : Nat := 137782834555007401482635

theorem tailTrace_2414980 : CollatzResearch.WordTrace tailWord_2414980 prefixEnd_2414980 137782834555007401482635 := by
  unfold tailWord_2414980
  simp only [CollatzResearch.WordTrace]
  refine ⟨44040778395473690296313197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58721037860631587061750929 44040778395473690296313197)
  ·
    refine ⟨16515291898302633861117449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44040778395473690296313197 16515291898302633861117449)
    ·
      refine ⟨12386468923726975395838087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16515291898302633861117449 12386468923726975395838087)
      ·
        refine ⟨18579703385590463093757131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12386468923726975395838087 18579703385590463093757131)
        ·
          refine ⟨27869555078385694640635697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18579703385590463093757131 27869555078385694640635697)
          ·
            refine ⟨20902166308789270980476773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27869555078385694640635697 20902166308789270980476773)
            ·
              refine ⟨3919156182897988308839395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20902166308789270980476773 3919156182897988308839395)
              ·
                refine ⟨5878734274346982463259093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919156182897988308839395 5878734274346982463259093)
                ·
                  refine ⟨137782834555007401482635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5878734274346982463259093 137782834555007401482635)
                  ·
                    rfl

theorem cell23_2414980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_2414980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2414980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2414980 prefixEnd_2414980 := by exact prefixLift 2414980
  have htrace : WordTrace (prefixWord ++ tailWord_2414980) baseStart_2414980 baseEnd_2414980 := by
    simpa [prefixWord, tailWord_2414980, baseEnd_2414980] using wordTrace_append hprefix tailTrace_2414980
  have hstable : (prefixWord ++ tailWord_2414980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2414980).length < 2 ^ (prefixWord ++ tailWord_2414980).sum := by decide
  have hdescent : baseEnd_2414980 < baseStart_2414980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2414980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415010 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2415010 : Nat := 118140960795 + 2415010 * 2 ^ 59
def prefixEnd_2415010 : Nat := 4983230072969 + 3 ^ 40 * 2415010 * 2
def baseEnd_2415010 : Nat := 413353638471567165322859

theorem tailTrace_2415010 : CollatzResearch.WordTrace tailWord_2415010 prefixEnd_2415010 413353638471567165322859 := by
  unfold tailWord_2415010
  simp only [CollatzResearch.WordTrace]
  refine ⟨22020662745209673929054621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58721767320559130477478989 22020662745209673929054621)
  ·
    refine ⟨8257748529453627723395483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22020662745209673929054621 8257748529453627723395483)
    ·
      refine ⟨12386622794180441585093225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8257748529453627723395483 12386622794180441585093225)
      ·
        refine ⟨9289967095635331188819919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12386622794180441585093225 9289967095635331188819919)
        ·
          refine ⟨13934950643452996783229879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9289967095635331188819919 13934950643452996783229879)
          ·
            refine ⟨20902425965179495174844819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13934950643452996783229879 20902425965179495174844819)
            ·
              refine ⟨31353638947769242762267229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20902425965179495174844819 31353638947769242762267229)
              ·
                refine ⟨11757614605413466035850211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31353638947769242762267229 11757614605413466035850211)
                ·
                  refine ⟨17636421908120199053775317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11757614605413466035850211 17636421908120199053775317)
                  ·
                    refine ⟨413353638471567165322859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17636421908120199053775317 413353638471567165322859)
                    ·
                      rfl

theorem cell23_2415010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2415010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415010 prefixEnd_2415010 := by exact prefixLift 2415010
  have htrace : WordTrace (prefixWord ++ tailWord_2415010) baseStart_2415010 baseEnd_2415010 := by
    simpa [prefixWord, tailWord_2415010, baseEnd_2415010] using wordTrace_append hprefix tailTrace_2415010
  have hstable : (prefixWord ++ tailWord_2415010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415010).length < 2 ^ (prefixWord ++ tailWord_2415010).sum := by decide
  have hdescent : baseEnd_2415010 < baseStart_2415010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415107 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 1, 5, 2]
def baseStart_2415107 : Nat := 118140960795 + 2415107 * 2 ^ 59
def prefixEnd_2415107 : Nat := 4983230072969 + 3 ^ 40 * 2415107 * 2
def baseEnd_2415107 : Nat := 1240110723038187616455631

theorem tailTrace_2415107 : CollatzResearch.WordTrace tailWord_2415107 prefixEnd_2415107 1240110723038187616455631 := by
  unfold tailWord_2415107
  simp only [CollatzResearch.WordTrace]
  refine ⟨88086188861487281282499575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58724125907658187521666383 88086188861487281282499575)
  ·
    refine ⟨132129283292230921923749363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88086188861487281282499575 132129283292230921923749363)
    ·
      refine ⟨198193924938346382885624045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132129283292230921923749363 198193924938346382885624045)
      ·
        refine ⟨74322721851879893582109017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198193924938346382885624045 74322721851879893582109017)
        ·
          refine ⟨55742041388909920186581763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74322721851879893582109017 55742041388909920186581763)
          ·
            refine ⟨83613062083364880279872645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55742041388909920186581763 83613062083364880279872645)
            ·
              refine ⟨15677449140630915052476121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83613062083364880279872645 15677449140630915052476121)
              ·
                refine ⟨11758086855473186289357091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15677449140630915052476121 11758086855473186289357091)
                ·
                  refine ⟨17637130283209779434035637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11758086855473186289357091 17637130283209779434035637)
                  ·
                    refine ⟨1653480964050916821940841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17637130283209779434035637 1653480964050916821940841)
                    ·
                      refine ⟨1240110723038187616455631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653480964050916821940841 1240110723038187616455631)
                      ·
                        rfl

theorem cell23_2415107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_2415107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415107 prefixEnd_2415107 := by exact prefixLift 2415107
  have htrace : WordTrace (prefixWord ++ tailWord_2415107) baseStart_2415107 baseEnd_2415107 := by
    simpa [prefixWord, tailWord_2415107, baseEnd_2415107] using wordTrace_append hprefix tailTrace_2415107
  have hstable : (prefixWord ++ tailWord_2415107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415107).length < 2 ^ (prefixWord ++ tailWord_2415107).sum := by decide
  have hdescent : baseEnd_2415107 < baseStart_2415107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415114 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2415114 : Nat := 118140960795 + 2415114 * 2 ^ 59
def prefixEnd_2415114 : Nat := 4983230072969 + 3 ^ 40 * 2415114 * 2
def baseEnd_2415114 : Nat := 1240114317402769089068099

theorem tailTrace_2415114 : CollatzResearch.WordTrace tailWord_2415114 prefixEnd_2415114 1240114317402769089068099 := by
  unfold tailWord_2415114
  simp only [CollatzResearch.WordTrace]
  refine ⟨22021611043115480369501099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58724296114974614318669597 22021611043115480369501099)
  ·
    refine ⟨33032416564673220554251649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22021611043115480369501099 33032416564673220554251649)
    ·
      refine ⟨24774312423504915415688737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33032416564673220554251649 24774312423504915415688737)
      ·
        refine ⟨18580734317628686561766553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24774312423504915415688737 18580734317628686561766553)
        ·
          refine ⟨13935550738221514921324915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18580734317628686561766553 13935550738221514921324915)
          ·
            refine ⟨20903326107332272381987373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13935550738221514921324915 20903326107332272381987373)
            ·
              refine ⟨7838747290249602143245265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20903326107332272381987373 7838747290249602143245265)
              ·
                refine ⟨5879060467687201607433949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7838747290249602143245265 5879060467687201607433949)
                ·
                  refine ⟨2204647675382700602787731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5879060467687201607433949 2204647675382700602787731)
                  ·
                    refine ⟨3306971513074050904181597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2204647675382700602787731 3306971513074050904181597)
                    ·
                      refine ⟨1240114317402769089068099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3306971513074050904181597 1240114317402769089068099)
                      ·
                        rfl

theorem cell23_2415114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2415114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415114 prefixEnd_2415114 := by exact prefixLift 2415114
  have htrace : WordTrace (prefixWord ++ tailWord_2415114) baseStart_2415114 baseEnd_2415114 := by
    simpa [prefixWord, tailWord_2415114, baseEnd_2415114] using wordTrace_append hprefix tailTrace_2415114
  have hstable : (prefixWord ++ tailWord_2415114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415114).length < 2 ^ (prefixWord ++ tailWord_2415114).sum := by decide
  have hdescent : baseEnd_2415114 < baseStart_2415114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415157 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2415157 : Nat := 118140960795 + 2415157 * 2 ^ 59
def prefixEnd_2415157 : Nat := 4983230072969 + 3 ^ 40 * 2415157 * 2
def baseEnd_2415157 : Nat := 1240136397070912420830401

theorem tailTrace_2415157 : CollatzResearch.WordTrace tailWord_2415157 prefixEnd_2415157 1240136397070912420830401 := by
  unfold tailWord_2415157
  simp only [CollatzResearch.WordTrace]
  refine ⟨88088012511306139821819725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58725341674204093214546483 88088012511306139821819725)
  ·
    refine ⟨33033004691739802433182397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88088012511306139821819725 33033004691739802433182397)
    ·
      refine ⟨12387376759402425912443399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33033004691739802433182397 12387376759402425912443399)
      ·
        refine ⟨18581065139103638868665099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12387376759402425912443399 18581065139103638868665099)
        ·
          refine ⟨27871597708655458302997649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18581065139103638868665099 27871597708655458302997649)
          ·
            refine ⟨20903698281491593727248237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27871597708655458302997649 20903698281491593727248237)
            ·
              refine ⟨7838886855559347647718089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20903698281491593727248237 7838886855559347647718089)
              ·
                refine ⟨5879165141669510735788567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7838886855559347647718089 5879165141669510735788567)
                ·
                  refine ⟨8818747712504266103682851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879165141669510735788567 8818747712504266103682851)
                  ·
                    refine ⟨13228121568756399155524277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8818747712504266103682851 13228121568756399155524277)
                    ·
                      refine ⟨1240136397070912420830401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13228121568756399155524277 1240136397070912420830401)
                      ·
                        rfl

theorem cell23_2415157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2415157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415157 prefixEnd_2415157 := by exact prefixLift 2415157
  have htrace : WordTrace (prefixWord ++ tailWord_2415157) baseStart_2415157 baseEnd_2415157 := by
    simpa [prefixWord, tailWord_2415157, baseEnd_2415157] using wordTrace_append hprefix tailTrace_2415157
  have hstable : (prefixWord ++ tailWord_2415157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415157).length < 2 ^ (prefixWord ++ tailWord_2415157).sum := by decide
  have hdescent : baseEnd_2415157 < baseStart_2415157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415160 : List Nat := [2, 1, 2, 1, 4, 1, 2, 10]
def baseStart_2415160 : Nat := 118140960795 + 2415160 * 2 ^ 59
def prefixEnd_2415160 : Nat := 4983230072969 + 3 ^ 40 * 2415160 * 2
def baseEnd_2415160 : Nat := 45931034722699107744181

theorem tailTrace_2415160 : CollatzResearch.WordTrace tailWord_2415160 prefixEnd_2415160 45931034722699107744181 := by
  unfold tailWord_2415160
  simp only [CollatzResearch.WordTrace]
  refine ⟨44044060965147635667089467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58725414620196847556119289 44044060965147635667089467)
  ·
    refine ⟨66066091447721453500634201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44044060965147635667089467 66066091447721453500634201)
    ·
      refine ⟨49549568585791090125475651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66066091447721453500634201 49549568585791090125475651)
      ·
        refine ⟨74324352878686635188213477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49549568585791090125475651 74324352878686635188213477)
        ·
          refine ⟨13935816164753744097790027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74324352878686635188213477 13935816164753744097790027)
          ·
            refine ⟨20903724247130616146685041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13935816164753744097790027 20903724247130616146685041)
            ·
              refine ⟨15677793185347962110013781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20903724247130616146685041 15677793185347962110013781)
              ·
                refine ⟨45931034722699107744181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15677793185347962110013781 45931034722699107744181)
                ·
                  rfl

theorem cell23_2415160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 10].length) (baseStart_2415160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415160 prefixEnd_2415160 := by exact prefixLift 2415160
  have htrace : WordTrace (prefixWord ++ tailWord_2415160) baseStart_2415160 baseEnd_2415160 := by
    simpa [prefixWord, tailWord_2415160, baseEnd_2415160] using wordTrace_append hprefix tailTrace_2415160
  have hstable : (prefixWord ++ tailWord_2415160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415160).length < 2 ^ (prefixWord ++ tailWord_2415160).sum := by decide
  have hdescent : baseEnd_2415160 < baseStart_2415160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415164 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_2415164 : Nat := 118140960795 + 2415164 * 2 ^ 59
def prefixEnd_2415164 : Nat := 4983230072969 + 3 ^ 40 * 2415164 * 2
def baseEnd_2415164 : Nat := 413379997145164631147623

theorem tailTrace_2415164 : CollatzResearch.WordTrace tailWord_2415164 prefixEnd_2415164 413379997145164631147623 := by
  unfold tailWord_2415164
  simp only [CollatzResearch.WordTrace]
  refine ⟨44044133911140390008662273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58725511881520520011549697 44044133911140390008662273)
  ·
    refine ⟨33033100433355292506496705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44044133911140390008662273 33033100433355292506496705)
    ·
      refine ⟨24774825325016469379872529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33033100433355292506496705 24774825325016469379872529)
      ·
        refine ⟨18581118993762352034904397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24774825325016469379872529 18581118993762352034904397)
        ·
          refine ⟨6967919622660882013089149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18581118993762352034904397 6967919622660882013089149)
          ·
            refine ⟨2612969858497830754908431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6967919622660882013089149 2612969858497830754908431)
            ·
              refine ⟨3919454787746746132362647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612969858497830754908431 3919454787746746132362647)
              ·
                refine ⟨5879182181620119198543971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919454787746746132362647 5879182181620119198543971)
                ·
                  refine ⟨8818773272430178797815957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879182181620119198543971 8818773272430178797815957)
                  ·
                    refine ⟨413379997145164631147623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8818773272430178797815957 413379997145164631147623)
                    ·
                      rfl

theorem cell23_2415164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_2415164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415164 prefixEnd_2415164 := by exact prefixLift 2415164
  have htrace : WordTrace (prefixWord ++ tailWord_2415164) baseStart_2415164 baseEnd_2415164 := by
    simpa [prefixWord, tailWord_2415164, baseEnd_2415164] using wordTrace_append hprefix tailTrace_2415164
  have hstable : (prefixWord ++ tailWord_2415164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415164).length < 2 ^ (prefixWord ++ tailWord_2415164).sum := by decide
  have hdescent : baseEnd_2415164 < baseStart_2415164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415204 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_2415204 : Nat := 118140960795 + 2415204 * 2 ^ 59
def prefixEnd_2415204 : Nat := 4983230072969 + 3 ^ 40 * 2415204 * 2
def baseEnd_2415204 : Nat := 1240160530661673736942685

theorem tailTrace_2415204 : CollatzResearch.WordTrace tailWord_2415204 prefixEnd_2415204 1240160530661673736942685 := by
  unfold tailWord_2415204
  simp only [CollatzResearch.WordTrace]
  refine ⟨44044863371067933424390333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58726484494757244565853777 44044863371067933424390333)
  ·
    refine ⟨16516823764150475034146375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44044863371067933424390333 16516823764150475034146375)
    ·
      refine ⟨24775235646225712551219563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16516823764150475034146375 24775235646225712551219563)
      ·
        refine ⟨37162853469338568826829345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24775235646225712551219563 37162853469338568826829345)
        ·
          refine ⟨27872140102003926620122009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37162853469338568826829345 27872140102003926620122009)
          ·
            refine ⟨20904105076502944965091507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27872140102003926620122009 20904105076502944965091507)
            ·
              refine ⟨31356157614754417447637261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20904105076502944965091507 31356157614754417447637261)
              ·
                refine ⟨11758559105532906542863973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31356157614754417447637261 11758559105532906542863973)
                ·
                  refine ⟨2204729832287419976786995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11758559105532906542863973 2204729832287419976786995)
                  ·
                    refine ⟨3307094748431129965180493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2204729832287419976786995 3307094748431129965180493)
                    ·
                      refine ⟨1240160530661673736942685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3307094748431129965180493 1240160530661673736942685)
                      ·
                        rfl

theorem cell23_2415204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_2415204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415204 prefixEnd_2415204 := by exact prefixLift 2415204
  have htrace : WordTrace (prefixWord ++ tailWord_2415204) baseStart_2415204 baseEnd_2415204 := by
    simpa [prefixWord, tailWord_2415204, baseEnd_2415204] using wordTrace_append hprefix tailTrace_2415204
  have hstable : (prefixWord ++ tailWord_2415204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415204).length < 2 ^ (prefixWord ++ tailWord_2415204).sum := by decide
  have hdescent : baseEnd_2415204 < baseStart_2415204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415205 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 3, 2, 2]
def baseStart_2415205 : Nat := 118140960795 + 2415205 * 2 ^ 59
def prefixEnd_2415205 : Nat := 4983230072969 + 3 ^ 40 * 2415205 * 2
def baseEnd_2415205 : Nat := 1240161044142328233030181

theorem tailTrace_2415205 : CollatzResearch.WordTrace tailWord_2415205 prefixEnd_2415205 1240161044142328233030181 := by
  unfold tailWord_2415205
  simp only [CollatzResearch.WordTrace]
  refine ⟨88089763215132244019567069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58726508810088162679711379 88089763215132244019567069)
  ·
    refine ⟨33033661205674591507337651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88089763215132244019567069 33033661205674591507337651)
    ·
      refine ⟨49550491808511887261006477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33033661205674591507337651 49550491808511887261006477)
      ·
        refine ⟨18581434428191957722877429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49550491808511887261006477 18581434428191957722877429)
        ·
          refine ⟨1742009477642996036519759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18581434428191957722877429 1742009477642996036519759)
          ·
            refine ⟨2613014216464494054779639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742009477642996036519759 2613014216464494054779639)
            ·
              refine ⟨3919521324696741082169459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613014216464494054779639 3919521324696741082169459)
              ·
                refine ⟨5879281987045111623254189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3919521324696741082169459 5879281987045111623254189)
                ·
                  refine ⟨2204730745141916858720321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5879281987045111623254189 2204730745141916858720321)
                  ·
                    refine ⟨1653548058856437644040241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2204730745141916858720321 1653548058856437644040241)
                    ·
                      refine ⟨1240161044142328233030181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653548058856437644040241 1240161044142328233030181)
                      ·
                        rfl

theorem cell23_2415205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_2415205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415205 prefixEnd_2415205 := by exact prefixLift 2415205
  have htrace : WordTrace (prefixWord ++ tailWord_2415205) baseStart_2415205 baseEnd_2415205 := by
    simpa [prefixWord, tailWord_2415205, baseEnd_2415205] using wordTrace_append hprefix tailTrace_2415205
  have hstable : (prefixWord ++ tailWord_2415205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415205).length < 2 ^ (prefixWord ++ tailWord_2415205).sum := by decide
  have hdescent : baseEnd_2415205 < baseStart_2415205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415257 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_2415257 : Nat := 118140960795 + 2415257 * 2 ^ 59
def prefixEnd_2415257 : Nat := 4983230072969 + 3 ^ 40 * 2415257 * 2
def baseEnd_2415257 : Nat := 1240187745136362029579941

theorem tailTrace_2415257 : CollatzResearch.WordTrace tailWord_2415257 prefixEnd_2415257 1240187745136362029579941 := by
  unfold tailWord_2415257
  simp only [CollatzResearch.WordTrace]
  refine ⟨88091659810943856900460025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58727773207295904600306683 88091659810943856900460025)
  ·
    refine ⟨66068744858207892675345019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88091659810943856900460025 66068744858207892675345019)
    ·
      refine ⟨99103117287311839013017529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66068744858207892675345019 99103117287311839013017529)
      ·
        refine ⟨74327337965483879259763147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99103117287311839013017529 74327337965483879259763147)
        ·
          refine ⟨111491006948225818889644721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74327337965483879259763147 111491006948225818889644721)
          ·
            refine ⟨83618255211169364167233541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111491006948225818889644721 83618255211169364167233541)
            ·
              refine ⟨15678422852094255781356289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83618255211169364167233541 15678422852094255781356289)
              ·
                refine ⟨11758817139070691836017217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15678422852094255781356289 11758817139070691836017217)
                ·
                  refine ⟨8819112854303018877012913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11758817139070691836017217 8819112854303018877012913)
                  ·
                    refine ⟨6614334640727264157759685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8819112854303018877012913 6614334640727264157759685)
                    ·
                      refine ⟨1240187745136362029579941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6614334640727264157759685 1240187745136362029579941)
                      ·
                        rfl

theorem cell23_2415257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_2415257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415257 prefixEnd_2415257 := by exact prefixLift 2415257
  have htrace : WordTrace (prefixWord ++ tailWord_2415257) baseStart_2415257 baseEnd_2415257 := by
    simpa [prefixWord, tailWord_2415257, baseEnd_2415257] using wordTrace_append hprefix tailTrace_2415257
  have hstable : (prefixWord ++ tailWord_2415257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415257).length < 2 ^ (prefixWord ++ tailWord_2415257).sum := by decide
  have hdescent : baseEnd_2415257 < baseStart_2415257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415261 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_2415261 : Nat := 118140960795 + 2415261 * 2 ^ 59
def prefixEnd_2415261 : Nat := 4983230072969 + 3 ^ 40 * 2415261 * 2
def baseEnd_2415261 : Nat := 1240189799058980013929923

theorem tailTrace_2415261 : CollatzResearch.WordTrace tailWord_2415261 prefixEnd_2415261 1240189799058980013929923 := by
  unfold tailWord_2415261
  simp only [CollatzResearch.WordTrace]
  refine ⟨88091805702929365583605637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58727870468619577055737091 88091805702929365583605637)
  ·
    refine ⟨16517213569299256046926057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88091805702929365583605637 16517213569299256046926057)
    ·
      refine ⟨12387910176974442035194543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16517213569299256046926057 12387910176974442035194543)
      ·
        refine ⟨18581865265461663052791815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12387910176974442035194543 18581865265461663052791815)
        ·
          refine ⟨27872797898192494579187723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18581865265461663052791815 27872797898192494579187723)
          ·
            refine ⟨41809196847288741868781585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27872797898192494579187723 41809196847288741868781585)
            ·
              refine ⟨31356897635466556401586189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41809196847288741868781585 31356897635466556401586189)
              ·
                refine ⟨11758836613299958650594821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31356897635466556401586189 11758836613299958650594821)
                ·
                  refine ⟨2204781864993742246986529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11758836613299958650594821 2204781864993742246986529)
                  ·
                    refine ⟨1653586398745306685239897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2204781864993742246986529 1653586398745306685239897)
                    ·
                      refine ⟨1240189799058980013929923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653586398745306685239897 1240189799058980013929923)
                      ·
                        rfl

theorem cell23_2415261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_2415261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415261 prefixEnd_2415261 := by exact prefixLift 2415261
  have htrace : WordTrace (prefixWord ++ tailWord_2415261) baseStart_2415261 baseEnd_2415261 := by
    simpa [prefixWord, tailWord_2415261, baseEnd_2415261] using wordTrace_append hprefix tailTrace_2415261
  have hstable : (prefixWord ++ tailWord_2415261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415261).length < 2 ^ (prefixWord ++ tailWord_2415261).sum := by decide
  have hdescent : baseEnd_2415261 < baseStart_2415261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415271 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2415271 : Nat := 118140960795 + 2415271 * 2 ^ 59
def prefixEnd_2415271 : Nat := 4983230072969 + 3 ^ 40 * 2415271 * 2
def baseEnd_2415271 : Nat := 413398311288508324934959

theorem tailTrace_2415271 : CollatzResearch.WordTrace tailWord_2415271 prefixEnd_2415271 413398311288508324934959 := by
  unfold tailWord_2415271
  simp only [CollatzResearch.WordTrace]
  refine ⟨88092170432893137291469667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58728113621928758194313111 88092170432893137291469667)
  ·
    refine ⟨132138255649339705937204501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88092170432893137291469667 132138255649339705937204501)
    ·
      refine ⟨6193980733562798715806461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132138255649339705937204501 6193980733562798715806461)
      ·
        refine ⟨2322742775086049518427423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6193980733562798715806461 2322742775086049518427423)
        ·
          refine ⟨3484114162629074277641135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2322742775086049518427423 3484114162629074277641135)
          ·
            refine ⟨5226171243943611416461703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484114162629074277641135 5226171243943611416461703)
            ·
              refine ⟨7839256865915417124692555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5226171243943611416461703 7839256865915417124692555)
              ·
                refine ⟨11758885298873125687038833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7839256865915417124692555 11758885298873125687038833)
                ·
                  refine ⟨8819163974154844265279125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11758885298873125687038833 8819163974154844265279125)
                  ·
                    refine ⟨413398311288508324934959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8819163974154844265279125 413398311288508324934959)
                    ·
                      rfl

theorem cell23_2415271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2415271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415271 prefixEnd_2415271 := by exact prefixLift 2415271
  have htrace : WordTrace (prefixWord ++ tailWord_2415271) baseStart_2415271 baseEnd_2415271 := by
    simpa [prefixWord, tailWord_2415271, baseEnd_2415271] using wordTrace_append hprefix tailTrace_2415271
  have hstable : (prefixWord ++ tailWord_2415271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415271).length < 2 ^ (prefixWord ++ tailWord_2415271).sum := by decide
  have hdescent : baseEnd_2415271 < baseStart_2415271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415278 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2415278 : Nat := 118140960795 + 2415278 * 2 ^ 59
def prefixEnd_2415278 : Nat := 4983230072969 + 3 ^ 40 * 2415278 * 2
def baseEnd_2415278 : Nat := 1240198528230106447417345

theorem tailTrace_2415278 : CollatzResearch.WordTrace tailWord_2415278 prefixEnd_2415278 1240198528230106447417345 := by
  unfold tailWord_2415278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011553217983472185871811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58728283829245184991316325 11011553217983472185871811)
  ·
    refine ⟨16517329826975208278807717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11011553217983472185871811 16517329826975208278807717)
    ·
      refine ⟨3096999342557851552276447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16517329826975208278807717 3096999342557851552276447)
      ·
        refine ⟨4645499013836777328414671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3096999342557851552276447 4645499013836777328414671)
        ·
          refine ⟨6968248520755165992622007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645499013836777328414671 6968248520755165992622007)
          ·
            refine ⟨10452372781132748988933011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968248520755165992622007 10452372781132748988933011)
            ·
              refine ⟨15678559171699123483399517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10452372781132748988933011 15678559171699123483399517)
              ·
                refine ⟨5879459689387171306274819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15678559171699123483399517 5879459689387171306274819)
                ·
                  refine ⟨8819189534080756959412229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5879459689387171306274819 8819189534080756959412229)
                  ·
                    refine ⟨1653598037640141929889793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8819189534080756959412229 1653598037640141929889793)
                    ·
                      refine ⟨1240198528230106447417345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653598037640141929889793 1240198528230106447417345)
                      ·
                        rfl

theorem cell23_2415278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2415278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415278 prefixEnd_2415278 := by exact prefixLift 2415278
  have htrace : WordTrace (prefixWord ++ tailWord_2415278) baseStart_2415278 baseEnd_2415278 := by
    simpa [prefixWord, tailWord_2415278, baseEnd_2415278] using wordTrace_append hprefix tailTrace_2415278
  have hstable : (prefixWord ++ tailWord_2415278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415278).length < 2 ^ (prefixWord ++ tailWord_2415278).sum := by decide
  have hdescent : baseEnd_2415278 < baseStart_2415278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415294 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_2415294 : Nat := 118140960795 + 2415294 * 2 ^ 59
def prefixEnd_2415294 : Nat := 4983230072969 + 3 ^ 40 * 2415294 * 2
def baseEnd_2415294 : Nat := 1240206743920578384817271

theorem tailTrace_2415294 : CollatzResearch.WordTrace tailWord_2415294 prefixEnd_2415294 1240206743920578384817271 := by
  unfold tailWord_2415294
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011626163976226527444617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58728672874539874813037957 11011626163976226527444617)
  ·
    refine ⟨8258719622982169895583463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11011626163976226527444617 8258719622982169895583463)
    ·
      refine ⟨12388079434473254843375195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8258719622982169895583463 12388079434473254843375195)
      ·
        refine ⟨18582119151709882265062793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12388079434473254843375195 18582119151709882265062793)
        ·
          refine ⟨13936589363782411698797095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18582119151709882265062793 13936589363782411698797095)
          ·
            refine ⟨20904884045673617548195643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13936589363782411698797095 20904884045673617548195643)
            ·
              refine ⟨31357326068510426322293465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20904884045673617548195643 31357326068510426322293465)
              ·
                refine ⟨23517994551382819741720099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31357326068510426322293465 23517994551382819741720099)
                ·
                  refine ⟨35276991827074229612580149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23517994551382819741720099 35276991827074229612580149)
                  ·
                    refine ⟨3307217983788209026179389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35276991827074229612580149 3307217983788209026179389)
                    ·
                      refine ⟨1240206743920578384817271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3307217983788209026179389 1240206743920578384817271)
                      ·
                        rfl

theorem cell23_2415294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_2415294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415294 prefixEnd_2415294 := by exact prefixLift 2415294
  have htrace : WordTrace (prefixWord ++ tailWord_2415294) baseStart_2415294 baseEnd_2415294 := by
    simpa [prefixWord, tailWord_2415294, baseEnd_2415294] using wordTrace_append hprefix tailTrace_2415294
  have hstable : (prefixWord ++ tailWord_2415294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415294).length < 2 ^ (prefixWord ++ tailWord_2415294).sum := by decide
  have hdescent : baseEnd_2415294 < baseStart_2415294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415344 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 3, 4]
def baseStart_2415344 : Nat := 118140960795 + 2415344 * 2 ^ 59
def prefixEnd_2415344 : Nat := 4983230072969 + 3 ^ 40 * 2415344 * 2
def baseEnd_2415344 : Nat := 413410805984434396397347

theorem tailTrace_2415344 : CollatzResearch.WordTrace tailWord_2415344 prefixEnd_2415344 413410805984434396397347 := by
  unfold tailWord_2415344
  simp only [CollatzResearch.WordTrace]
  refine ⟨44047416480814335379438543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58729888641085780505918057 44047416480814335379438543)
  ·
    refine ⟨66071124721221503069157815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44047416480814335379438543 66071124721221503069157815)
    ·
      refine ⟨99106687081832254603736723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66071124721221503069157815 99106687081832254603736723)
      ·
        refine ⟨148660030622748381905605085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99106687081832254603736723 148660030622748381905605085)
        ·
          refine ⟨55747511483530643214601907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148660030622748381905605085 55747511483530643214601907)
          ·
            refine ⟨83621267225295964821902861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55747511483530643214601907 83621267225295964821902861)
            ·
              refine ⟨31357975209485986808213573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83621267225295964821902861 31357975209485986808213573)
              ·
                refine ⟨5879620351778622526540045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31357975209485986808213573 5879620351778622526540045)
                ·
                  refine ⟨2204857631916983447452517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5879620351778622526540045 2204857631916983447452517)
                  ·
                    refine ⟨413410805984434396397347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2204857631916983447452517 413410805984434396397347)
                    ·
                      rfl

theorem cell23_2415344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 3, 4].length) (baseStart_2415344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415344 prefixEnd_2415344 := by exact prefixLift 2415344
  have htrace : WordTrace (prefixWord ++ tailWord_2415344) baseStart_2415344 baseEnd_2415344 := by
    simpa [prefixWord, tailWord_2415344, baseEnd_2415344] using wordTrace_append hprefix tailTrace_2415344
  have hstable : (prefixWord ++ tailWord_2415344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415344).length < 2 ^ (prefixWord ++ tailWord_2415344).sum := by decide
  have hdescent : baseEnd_2415344 < baseStart_2415344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415347 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 4]
def baseStart_2415347 : Nat := 118140960795 + 2415347 * 2 ^ 59
def prefixEnd_2415347 : Nat := 4983230072969 + 3 ^ 40 * 2415347 * 2
def baseEnd_2415347 : Nat := 1240233958395266677454527

theorem tailTrace_2415347 : CollatzResearch.WordTrace tailWord_2415347 prefixEnd_2415347 1240233958395266677454527 := by
  unfold tailWord_2415347
  simp only [CollatzResearch.WordTrace]
  refine ⟨88094942380617802271236295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58729961587078534847490863 88094942380617802271236295)
  ·
    refine ⟨132142413570926703406854443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88094942380617802271236295 132142413570926703406854443)
    ·
      refine ⟨198213620356390055110281665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132142413570926703406854443 198213620356390055110281665)
      ·
        refine ⟨148660215267292541332711249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198213620356390055110281665 148660215267292541332711249)
        ·
          refine ⟨111495161450469405999533437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148660215267292541332711249 111495161450469405999533437)
          ·
            refine ⟨41810685543926027249825039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111495161450469405999533437 41810685543926027249825039)
            ·
              refine ⟨62716028315889040874737559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41810685543926027249825039 62716028315889040874737559)
              ·
                refine ⟨94074042473833561312106339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62716028315889040874737559 94074042473833561312106339)
                ·
                  refine ⟨141111063710750341968159509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94074042473833561312106339 141111063710750341968159509)
                  ·
                    refine ⟨6614581111441422279757477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141111063710750341968159509 6614581111441422279757477)
                    ·
                      refine ⟨1240233958395266677454527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6614581111441422279757477 1240233958395266677454527)
                      ·
                        rfl

theorem cell23_2415347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_2415347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415347 prefixEnd_2415347 := by exact prefixLift 2415347
  have htrace : WordTrace (prefixWord ++ tailWord_2415347) baseStart_2415347 baseEnd_2415347 := by
    simpa [prefixWord, tailWord_2415347, baseEnd_2415347] using wordTrace_append hprefix tailTrace_2415347
  have hstable : (prefixWord ++ tailWord_2415347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415347).length < 2 ^ (prefixWord ++ tailWord_2415347).sum := by decide
  have hdescent : baseEnd_2415347 < baseStart_2415347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415354 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_2415354 : Nat := 118140960795 + 2415354 * 2 ^ 59
def prefixEnd_2415354 : Nat := 4983230072969 + 3 ^ 40 * 2415354 * 2
def baseEnd_2415354 : Nat := 1240237552759848150066995

theorem tailTrace_2415354 : CollatzResearch.WordTrace tailWord_2415354 prefixEnd_2415354 1240237552759848150066995 := by
  unfold tailWord_2415354
  simp only [CollatzResearch.WordTrace]
  refine ⟨22023799422898110616685279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58730131794394961644494077 22023799422898110616685279)
  ·
    refine ⟨33035699134347165925027919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22023799422898110616685279 33035699134347165925027919)
    ·
      refine ⟨49553548701520748887541879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33035699134347165925027919 49553548701520748887541879)
      ·
        refine ⟨74330323052281123331312819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49553548701520748887541879 74330323052281123331312819)
        ·
          refine ⟨111495484578421684996969229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74330323052281123331312819 111495484578421684996969229)
          ·
            refine ⟨41810806716908131873863461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111495484578421684996969229 41810806716908131873863461)
            ·
              refine ⟨7839526259420274726349399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41810806716908131873863461 7839526259420274726349399)
              ·
                refine ⟨11759289389130412089524099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7839526259420274726349399 11759289389130412089524099)
                ·
                  refine ⟨17638934083695618134286149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11759289389130412089524099 17638934083695618134286149)
                  ·
                    refine ⟨3307300140692928400178653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17638934083695618134286149 3307300140692928400178653)
                    ·
                      refine ⟨1240237552759848150066995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3307300140692928400178653 1240237552759848150066995)
                      ·
                        rfl

theorem cell23_2415354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_2415354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415354 prefixEnd_2415354 := by exact prefixLift 2415354
  have htrace : WordTrace (prefixWord ++ tailWord_2415354) baseStart_2415354 baseEnd_2415354 := by
    simpa [prefixWord, tailWord_2415354, baseEnd_2415354] using wordTrace_append hprefix tailTrace_2415354
  have hstable : (prefixWord ++ tailWord_2415354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415354).length < 2 ^ (prefixWord ++ tailWord_2415354).sum := by decide
  have hdescent : baseEnd_2415354 < baseStart_2415354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415357 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 10]
def baseStart_2415357 : Nat := 118140960795 + 2415357 * 2 ^ 59
def prefixEnd_2415357 : Nat := 4983230072969 + 3 ^ 40 * 2415357 * 2
def baseEnd_2415357 : Nat := 137804343689090182036609

theorem tailTrace_2415357 : CollatzResearch.WordTrace tailWord_2415357 prefixEnd_2415357 137804343689090182036609 := by
  unfold tailWord_2415357
  simp only [CollatzResearch.WordTrace]
  refine ⟨88095307110581573979100325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58730204740387715986066883 88095307110581573979100325)
  ·
    refine ⟨16517870083234045121081311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88095307110581573979100325 16517870083234045121081311)
    ·
      refine ⟨24776805124851067681621967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16517870083234045121081311 24776805124851067681621967)
      ·
        refine ⟨37165207687276601522432951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24776805124851067681621967 37165207687276601522432951)
        ·
          refine ⟨55747811530914902283649427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37165207687276601522432951 55747811530914902283649427)
          ·
            refine ⟨83621717296372353425474141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55747811530914902283649427 83621717296372353425474141)
            ·
              refine ⟨31358143986139632534552803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83621717296372353425474141 31358143986139632534552803)
              ·
                refine ⟨47037215979209448801829205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31358143986139632534552803 47037215979209448801829205)
                ·
                  refine ⟨137804343689090182036609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 47037215979209448801829205 137804343689090182036609)
                  ·
                    rfl

theorem cell23_2415357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_2415357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415357 prefixEnd_2415357 := by exact prefixLift 2415357
  have htrace : WordTrace (prefixWord ++ tailWord_2415357) baseStart_2415357 baseEnd_2415357 := by
    simpa [prefixWord, tailWord_2415357, baseEnd_2415357] using wordTrace_append hprefix tailTrace_2415357
  have hstable : (prefixWord ++ tailWord_2415357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415357).length < 2 ^ (prefixWord ++ tailWord_2415357).sum := by decide
  have hdescent : baseEnd_2415357 < baseStart_2415357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415374 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_2415374 : Nat := 118140960795 + 2415374 * 2 ^ 59
def prefixEnd_2415374 : Nat := 4983230072969 + 3 ^ 40 * 2415374 * 2
def baseEnd_2415374 : Nat := 137805313596993119090767

theorem tailTrace_2415374 : CollatzResearch.WordTrace tailWord_2415374 prefixEnd_2415374 137805313596993119090767 := by
  unfold tailWord_2415374
  simp only [CollatzResearch.WordTrace]
  refine ⟨11011990893939998235308647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58730618101013323921646117 11011990893939998235308647)
  ·
    refine ⟨16517986340909997352962971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11011990893939998235308647 16517986340909997352962971)
    ·
      refine ⟨24776979511364996029444457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16517986340909997352962971 24776979511364996029444457)
      ·
        refine ⟨18582734633523747022083343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24776979511364996029444457 18582734633523747022083343)
        ·
          refine ⟨27874101950285620533125015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18582734633523747022083343 27874101950285620533125015)
          ·
            refine ⟨41811152925428430799687523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27874101950285620533125015 41811152925428430799687523)
            ·
              refine ⟨62716729388142646199531285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41811152925428430799687523 62716729388142646199531285)
              ·
                refine ⟨2939846690069186540603029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62716729388142646199531285 2939846690069186540603029)
                ·
                  refine ⟨137805313596993119090767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2939846690069186540603029 137805313596993119090767)
                  ·
                    rfl

theorem cell23_2415374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_2415374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415374 prefixEnd_2415374 := by exact prefixLift 2415374
  have htrace : WordTrace (prefixWord ++ tailWord_2415374) baseStart_2415374 baseEnd_2415374 := by
    simpa [prefixWord, tailWord_2415374, baseEnd_2415374] using wordTrace_append hprefix tailTrace_2415374
  have hstable : (prefixWord ++ tailWord_2415374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415374).length < 2 ^ (prefixWord ++ tailWord_2415374).sum := by decide
  have hdescent : baseEnd_2415374 < baseStart_2415374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415377 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_2415377 : Nat := 118140960795 + 2415377 * 2 ^ 59
def prefixEnd_2415377 : Nat := 4983230072969 + 3 ^ 40 * 2415377 * 2
def baseEnd_2415377 : Nat := 1240249362814901560079389

theorem tailTrace_2415377 : CollatzResearch.WordTrace tailWord_2415377 prefixEnd_2415377 1240249362814901560079389 := by
  unfold tailWord_2415377
  simp only [CollatzResearch.WordTrace]
  refine ⟨88096036570509117394828385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58730691047006078263218923 88096036570509117394828385)
  ·
    refine ⟨66072027427881838046121289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88096036570509117394828385 66072027427881838046121289)
    ·
      refine ⟨49554020570911378534590967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66072027427881838046121289 49554020570911378534590967)
      ·
        refine ⟨74331030856367067801886451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49554020570911378534590967 74331030856367067801886451)
        ·
          refine ⟨111496546284550601702829677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74331030856367067801886451 111496546284550601702829677)
          ·
            refine ⟨41811204856706475638561129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111496546284550601702829677 41811204856706475638561129)
            ·
              refine ⟨31358403642529856728920847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41811204856706475638561129 31358403642529856728920847)
              ·
                refine ⟨47037605463794785093381271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31358403642529856728920847 47037605463794785093381271)
                ·
                  refine ⟨70556408195692177640071907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47037605463794785093381271 70556408195692177640071907)
                  ·
                    refine ⟨105834612293538266460107861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70556408195692177640071907 105834612293538266460107861)
                    ·
                      refine ⟨1240249362814901560079389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 105834612293538266460107861 1240249362814901560079389)
                      ·
                        rfl

theorem cell23_2415377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_2415377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415377 prefixEnd_2415377 := by exact prefixLift 2415377
  have htrace : WordTrace (prefixWord ++ tailWord_2415377) baseStart_2415377 baseEnd_2415377 := by
    simpa [prefixWord, tailWord_2415377, baseEnd_2415377] using wordTrace_append hprefix tailTrace_2415377
  have hstable : (prefixWord ++ tailWord_2415377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415377).length < 2 ^ (prefixWord ++ tailWord_2415377).sum := by decide
  have hdescent : baseEnd_2415377 < baseStart_2415377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415391 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 6]
def baseStart_2415391 : Nat := 118140960795 + 2415391 * 2 ^ 59
def prefixEnd_2415391 : Nat := 4983230072969 + 3 ^ 40 * 2415391 * 2
def baseEnd_2415391 : Nat := 137806283504896056144925

theorem tailTrace_2415391 : CollatzResearch.WordTrace tailWord_2415391 prefixEnd_2415391 137806283504896056144925 := by
  unfold tailWord_2415391
  simp only [CollatzResearch.WordTrace]
  refine ⟨88096547192458397785838027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58731031461638931857225351 88096547192458397785838027)
  ·
    refine ⟨132144820788687596678757041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88096547192458397785838027 132144820788687596678757041)
    ·
      refine ⟨99108615591515697509067781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132144820788687596678757041 99108615591515697509067781)
      ·
        refine ⟨18582865423409193282950209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99108615591515697509067781 18582865423409193282950209)
        ·
          refine ⟨13937149067556894962212657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18582865423409193282950209 13937149067556894962212657)
          ·
            refine ⟨10452861800667671221659493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13937149067556894962212657 10452861800667671221659493)
            ·
              refine ⟨1959911587625188354061155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10452861800667671221659493 1959911587625188354061155)
              ·
                refine ⟨2939867381437782531091733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959911587625188354061155 2939867381437782531091733)
                ·
                  refine ⟨137806283504896056144925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2939867381437782531091733 137806283504896056144925)
                  ·
                    rfl

theorem cell23_2415391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 6].length) (baseStart_2415391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415391 prefixEnd_2415391 := by exact prefixLift 2415391
  have htrace : WordTrace (prefixWord ++ tailWord_2415391) baseStart_2415391 baseEnd_2415391 := by
    simpa [prefixWord, tailWord_2415391, baseEnd_2415391] using wordTrace_append hprefix tailTrace_2415391
  have hstable : (prefixWord ++ tailWord_2415391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415391).length < 2 ^ (prefixWord ++ tailWord_2415391).sum := by decide
  have hdescent : baseEnd_2415391 < baseStart_2415391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415404 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_2415404 : Nat := 118140960795 + 2415404 * 2 ^ 59
def prefixEnd_2415404 : Nat := 4983230072969 + 3 ^ 40 * 2415404 * 2
def baseEnd_2415404 : Nat := 413421075597524318147255

theorem tailTrace_2415404 : CollatzResearch.WordTrace tailWord_2415404 prefixEnd_2415404 413421075597524318147255 := by
  unfold tailWord_2415404
  simp only [CollatzResearch.WordTrace]
  refine ⟨44048510670705650503030633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58731347560940867337374177 44048510670705650503030633)
  ·
    refine ⟨33036383003029237877272975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44048510670705650503030633 33036383003029237877272975)
    ·
      refine ⟨49554574504543856815909463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33036383003029237877272975 49554574504543856815909463)
      ·
        refine ⟨74331861756815785223864195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49554574504543856815909463 74331861756815785223864195)
        ·
          refine ⟨111497792635223677835796293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74331861756815785223864195 111497792635223677835796293)
          ·
            refine ⟨20905836119104439594211805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111497792635223677835796293 20905836119104439594211805)
            ·
              refine ⟨7839688544664164847829427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20905836119104439594211805 7839688544664164847829427)
              ·
                refine ⟨11759532816996247271744141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7839688544664164847829427 11759532816996247271744141)
                ·
                  refine ⟨4409824806373592726904053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11759532816996247271744141 4409824806373592726904053)
                  ·
                    refine ⟨413421075597524318147255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4409824806373592726904053 413421075597524318147255)
                    ·
                      rfl

theorem cell23_2415404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_2415404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415404 prefixEnd_2415404 := by exact prefixLift 2415404
  have htrace : WordTrace (prefixWord ++ tailWord_2415404) baseStart_2415404 baseEnd_2415404 := by
    simpa [prefixWord, tailWord_2415404, baseEnd_2415404] using wordTrace_append hprefix tailTrace_2415404
  have hstable : (prefixWord ++ tailWord_2415404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415404).length < 2 ^ (prefixWord ++ tailWord_2415404).sum := by decide
  have hdescent : baseEnd_2415404 < baseStart_2415404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415461 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_2415461 : Nat := 118140960795 + 2415461 * 2 ^ 59
def prefixEnd_2415461 : Nat := 4983230072969 + 3 ^ 40 * 2415461 * 2
def baseEnd_2415461 : Nat := 1240292495189879231429003

theorem tailTrace_2415461 : CollatzResearch.WordTrace tailWord_2415461 prefixEnd_2415461 1240292495189879231429003 := by
  unfold tailWord_2415461
  simp only [CollatzResearch.WordTrace]
  refine ⟨88099100302204799740886237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58732733534803199827257491 88099100302204799740886237)
  ·
    refine ⟨33037162613326799902832339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88099100302204799740886237 33037162613326799902832339)
    ·
      refine ⟨49555743919990199854248509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33037162613326799902832339 49555743919990199854248509)
      ·
        refine ⟨18583403969996324945343191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49555743919990199854248509 18583403969996324945343191)
        ·
          refine ⟨27875105954994487418014787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18583403969996324945343191 27875105954994487418014787)
          ·
            refine ⟨41812658932491731127022181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27875105954994487418014787 41812658932491731127022181)
            ·
              refine ⟨7839873549842199586316659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41812658932491731127022181 7839873549842199586316659)
              ·
                refine ⟨11759810324763299379474989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7839873549842199586316659 11759810324763299379474989)
                ·
                  refine ⟨4409928871786237267303121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11759810324763299379474989 4409928871786237267303121)
                  ·
                    refine ⟨3307446653839677950477341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4409928871786237267303121 3307446653839677950477341)
                    ·
                      refine ⟨1240292495189879231429003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3307446653839677950477341 1240292495189879231429003)
                      ·
                        rfl

theorem cell23_2415461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_2415461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415461 prefixEnd_2415461 := by exact prefixLift 2415461
  have htrace : WordTrace (prefixWord ++ tailWord_2415461) baseStart_2415461 baseEnd_2415461 := by
    simpa [prefixWord, tailWord_2415461, baseEnd_2415461] using wordTrace_append hprefix tailTrace_2415461
  have hstable : (prefixWord ++ tailWord_2415461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415461).length < 2 ^ (prefixWord ++ tailWord_2415461).sum := by decide
  have hdescent : baseEnd_2415461 < baseStart_2415461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415475 : List Nat := [1, 1, 1, 2, 2, 1, 5, 5, 1, 2, 2]
def baseStart_2415475 : Nat := 118140960795 + 2415475 * 2 ^ 59
def prefixEnd_2415475 : Nat := 4983230072969 + 3 ^ 40 * 2415475 * 2
def baseEnd_2415475 : Nat := 1240299683919042176653939

theorem tailTrace_2415475 : CollatzResearch.WordTrace tailWord_2415475 prefixEnd_2415475 1240299683919042176653939 := by
  unfold tailWord_2415475
  simp only [CollatzResearch.WordTrace]
  refine ⟨88099610924154080131895879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58733073949436053421263919 88099610924154080131895879)
  ·
    refine ⟨132149416386231120197843819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88099610924154080131895879 132149416386231120197843819)
    ·
      refine ⟨198224124579346680296765729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132149416386231120197843819 198224124579346680296765729)
      ·
        refine ⟨148668093434510010222574297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198224124579346680296765729 148668093434510010222574297)
        ·
          refine ⟨111501070075882507666930723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148668093434510010222574297 111501070075882507666930723)
          ·
            refine ⟨167251605113823761500396085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111501070075882507666930723 167251605113823761500396085)
            ·
              refine ⟨15679837979420977640662133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167251605113823761500396085 15679837979420977640662133)
              ·
                refine ⟨1469984810570716653812075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15679837979420977640662133 1469984810570716653812075)
                ·
                  refine ⟨2204977215856074980718113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469984810570716653812075 2204977215856074980718113)
                  ·
                    refine ⟨1653732911892056235538585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2204977215856074980718113 1653732911892056235538585)
                    ·
                      refine ⟨1240299683919042176653939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653732911892056235538585 1240299683919042176653939)
                      ·
                        rfl

theorem cell23_2415475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 1, 2, 2].length) (baseStart_2415475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415475 prefixEnd_2415475 := by exact prefixLift 2415475
  have htrace : WordTrace (prefixWord ++ tailWord_2415475) baseStart_2415475 baseEnd_2415475 := by
    simpa [prefixWord, tailWord_2415475, baseEnd_2415475] using wordTrace_append hprefix tailTrace_2415475
  have hstable : (prefixWord ++ tailWord_2415475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415475).length < 2 ^ (prefixWord ++ tailWord_2415475).sum := by decide
  have hdescent : baseEnd_2415475 < baseStart_2415475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415521 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2415521 : Nat := 118140960795 + 2415521 * 2 ^ 59
def prefixEnd_2415521 : Nat := 4983230072969 + 3 ^ 40 * 2415521 * 2
def baseEnd_2415521 : Nat := 1240323304029148996678727

theorem tailTrace_2415521 : CollatzResearch.WordTrace tailWord_2415521 prefixEnd_2415521 1240323304029148996678727 := by
  unfold tailWord_2415521
  simp only [CollatzResearch.WordTrace]
  refine ⟨88101288681987429988070417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58734192454658286658713611 88101288681987429988070417)
  ·
    refine ⟨66075966511490572491052813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88101288681987429988070417 66075966511490572491052813)
    ·
      refine ⟨24778487441808964684144805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66075966511490572491052813 24778487441808964684144805)
      ·
        refine ⟨4645966395339180878277151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24778487441808964684144805 4645966395339180878277151)
        ·
          refine ⟨6968949593008771317415727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645966395339180878277151 6968949593008771317415727)
          ·
            refine ⟨10453424389513156976123591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968949593008771317415727 10453424389513156976123591)
            ·
              refine ⟨15680136584269735464185387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10453424389513156976123591 15680136584269735464185387)
              ·
                refine ⟨23520204876404603196278081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15680136584269735464185387 23520204876404603196278081)
                ·
                  refine ⟨17640153657303452397208561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23520204876404603196278081 17640153657303452397208561)
                  ·
                    refine ⟨13230115242977589297906421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17640153657303452397208561 13230115242977589297906421)
                    ·
                      refine ⟨1240323304029148996678727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13230115242977589297906421 1240323304029148996678727)
                      ·
                        rfl

theorem cell23_2415521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2415521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415521 prefixEnd_2415521 := by exact prefixLift 2415521
  have htrace : WordTrace (prefixWord ++ tailWord_2415521) baseStart_2415521 baseEnd_2415521 := by
    simpa [prefixWord, tailWord_2415521, baseEnd_2415521] using wordTrace_append hprefix tailTrace_2415521
  have hstable : (prefixWord ++ tailWord_2415521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415521).length < 2 ^ (prefixWord ++ tailWord_2415521).sum := by decide
  have hdescent : baseEnd_2415521 < baseStart_2415521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415621 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_2415621 : Nat := 118140960795 + 2415621 * 2 ^ 59
def prefixEnd_2415621 : Nat := 4983230072969 + 3 ^ 40 * 2415621 * 2
def baseEnd_2415621 : Nat := 1240374652094598605428267

theorem tailTrace_2415621 : CollatzResearch.WordTrace tailWord_2415621 prefixEnd_2415621 1240374652094598605428267 := by
  unfold tailWord_2415621
  simp only [CollatzResearch.WordTrace]
  refine ⟨88104935981625147066710717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58736623987750098044473811 88104935981625147066710717)
  ·
    refine ⟨33039350993109430150016519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88104935981625147066710717 33039350993109430150016519)
    ·
      refine ⟨49559026489664145225024779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33039350993109430150016519 49559026489664145225024779)
      ·
        refine ⟨74338539734496217837537169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49559026489664145225024779 74338539734496217837537169)
        ·
          refine ⟨55753904800872163378152877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74338539734496217837537169 55753904800872163378152877)
          ·
            refine ⟨20907714300327061266807329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55753904800872163378152877 20907714300327061266807329)
            ·
              refine ⟨15680785725245295950105497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20907714300327061266807329 15680785725245295950105497)
              ·
                refine ⟨11760589293933971962579123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15680785725245295950105497 11760589293933971962579123)
                ·
                  refine ⟨17640883940900957943868685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11760589293933971962579123 17640883940900957943868685)
                  ·
                    refine ⟨6615331477837859228950757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17640883940900957943868685 6615331477837859228950757)
                    ·
                      refine ⟨1240374652094598605428267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6615331477837859228950757 1240374652094598605428267)
                      ·
                        rfl

theorem cell23_2415621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_2415621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415621 prefixEnd_2415621 := by exact prefixLift 2415621
  have htrace : WordTrace (prefixWord ++ tailWord_2415621) baseStart_2415621 baseEnd_2415621 := by
    simpa [prefixWord, tailWord_2415621, baseEnd_2415621] using wordTrace_append hprefix tailTrace_2415621
  have hstable : (prefixWord ++ tailWord_2415621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415621).length < 2 ^ (prefixWord ++ tailWord_2415621).sum := by decide
  have hdescent : baseEnd_2415621 < baseStart_2415621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415651 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 6]
def baseStart_2415651 : Nat := 118140960795 + 2415651 * 2 ^ 59
def prefixEnd_2415651 : Nat := 4983230072969 + 3 ^ 40 * 2415651 * 2
def baseEnd_2415651 : Nat := 1240390056514233488053129

theorem tailTrace_2415651 : CollatzResearch.WordTrace tailWord_2415651 prefixEnd_2415651 1240390056514233488053129 := by
  unfold tailWord_2415651
  simp only [CollatzResearch.WordTrace]
  refine ⟨88106030171516462190302807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58737353447677641460201871 88106030171516462190302807)
  ·
    refine ⟨132159045257274693285454211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88106030171516462190302807 132159045257274693285454211)
    ·
      refine ⟨198238567885912039928181317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132159045257274693285454211 198238567885912039928181317)
      ·
        refine ⟨37169731478608507486533997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198238567885912039928181317 37169731478608507486533997)
        ·
          refine ⟨13938649304478190307450249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37169731478608507486533997 13938649304478190307450249)
          ·
            refine ⟨10453986978358642730587687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13938649304478190307450249 10453986978358642730587687)
            ·
              refine ⟨15680980467537964095881531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10453986978358642730587687 15680980467537964095881531)
              ·
                refine ⟨23521470701306946143822297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15680980467537964095881531 23521470701306946143822297)
                ·
                  refine ⟨17641103025980209607866723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23521470701306946143822297 17641103025980209607866723)
                  ·
                    refine ⟨26461654538970314411800085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17641103025980209607866723 26461654538970314411800085)
                    ·
                      refine ⟨1240390056514233488053129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26461654538970314411800085 1240390056514233488053129)
                      ·
                        rfl

theorem cell23_2415651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_2415651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415651 prefixEnd_2415651 := by exact prefixLift 2415651
  have htrace : WordTrace (prefixWord ++ tailWord_2415651) baseStart_2415651 baseEnd_2415651 := by
    simpa [prefixWord, tailWord_2415651, baseEnd_2415651] using wordTrace_append hprefix tailTrace_2415651
  have hstable : (prefixWord ++ tailWord_2415651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415651).length < 2 ^ (prefixWord ++ tailWord_2415651).sum := by decide
  have hdescent : baseEnd_2415651 < baseStart_2415651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415665 : List Nat := [1, 2, 2, 3, 1, 2, 1, 6, 1, 4]
def baseStart_2415665 : Nat := 118140960795 + 2415665 * 2 ^ 59
def prefixEnd_2415665 : Nat := 4983230072969 + 3 ^ 40 * 2415665 * 2
def baseEnd_2415665 : Nat := 413465748414465477759355

theorem tailTrace_2415665 : CollatzResearch.WordTrace tailWord_2415665 prefixEnd_2415665 413465748414465477759355 := by
  unfold tailWord_2415665
  simp only [CollatzResearch.WordTrace]
  refine ⟨88106540793465742581312449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58737693862310495054208299 88106540793465742581312449)
  ·
    refine ⟨66079905595099306935984337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88106540793465742581312449 66079905595099306935984337)
    ·
      refine ⟨49559929196324480201988253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66079905595099306935984337 49559929196324480201988253)
      ·
        refine ⟨18584973448621680075745595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49559929196324480201988253 18584973448621680075745595)
        ·
          refine ⟨27877460172932520113618393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18584973448621680075745595 27877460172932520113618393)
          ·
            refine ⟨20908095129699390085213795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27877460172932520113618393 20908095129699390085213795)
            ·
              refine ⟨31362142694549085127820693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20908095129699390085213795 31362142694549085127820693)
              ·
                refine ⟨1470100438806988365366595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31362142694549085127820693 1470100438806988365366595)
                ·
                  refine ⟨2205150658210482548049893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470100438806988365366595 2205150658210482548049893)
                  ·
                    refine ⟨413465748414465477759355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2205150658210482548049893 413465748414465477759355)
                    ·
                      rfl

theorem cell23_2415665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_2415665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415665 prefixEnd_2415665 := by exact prefixLift 2415665
  have htrace : WordTrace (prefixWord ++ tailWord_2415665) baseStart_2415665 baseEnd_2415665 := by
    simpa [prefixWord, tailWord_2415665, baseEnd_2415665] using wordTrace_append hprefix tailTrace_2415665
  have hstable : (prefixWord ++ tailWord_2415665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415665).length < 2 ^ (prefixWord ++ tailWord_2415665).sum := by decide
  have hdescent : baseEnd_2415665 < baseStart_2415665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415722 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2415722 : Nat := 118140960795 + 2415722 * 2 ^ 59
def prefixEnd_2415722 : Nat := 4983230072969 + 3 ^ 40 * 2415722 * 2
def baseEnd_2415722 : Nat := 1240426513640702710265303

theorem tailTrace_2415722 : CollatzResearch.WordTrace tailWord_2415722 prefixEnd_2415722 1240426513640702710265303 := by
  unfold tailWord_2415722
  simp only [CollatzResearch.WordTrace]
  refine ⟨22027154938564810329034355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58739079836172827544091613 22027154938564810329034355)
  ·
    refine ⟨33040732407847215493551533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22027154938564810329034355 33040732407847215493551533)
    ·
      refine ⟨12390274652942705810081825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33040732407847215493551533 12390274652942705810081825)
      ·
        refine ⟨9292705989707029357561369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12390274652942705810081825 9292705989707029357561369)
        ·
          refine ⟨6969529492280272018171027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9292705989707029357561369 6969529492280272018171027)
          ·
            refine ⟨10454294238420408027256541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6969529492280272018171027 10454294238420408027256541)
            ·
              refine ⟨3920360339407653010221203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10454294238420408027256541 3920360339407653010221203)
              ·
                refine ⟨5880540509111479515331805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920360339407653010221203 5880540509111479515331805)
                ·
                  refine ⟨2205202690916804818249427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5880540509111479515331805 2205202690916804818249427)
                  ·
                    refine ⟨3307804036375207227374141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2205202690916804818249427 3307804036375207227374141)
                    ·
                      refine ⟨1240426513640702710265303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3307804036375207227374141 1240426513640702710265303)
                      ·
                        rfl

theorem cell23_2415722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2415722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415722 prefixEnd_2415722 := by exact prefixLift 2415722
  have htrace : WordTrace (prefixWord ++ tailWord_2415722) baseStart_2415722 baseEnd_2415722 := by
    simpa [prefixWord, tailWord_2415722, baseEnd_2415722] using wordTrace_append hprefix tailTrace_2415722
  have hstable : (prefixWord ++ tailWord_2415722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415722).length < 2 ^ (prefixWord ++ tailWord_2415722).sum := by decide
  have hdescent : baseEnd_2415722 < baseStart_2415722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415728 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_2415728 : Nat := 118140960795 + 2415728 * 2 ^ 59
def prefixEnd_2415728 : Nat := 4983230072969 + 3 ^ 40 * 2415728 * 2
def baseEnd_2415728 : Nat := 1240429594524629686790275

theorem tailTrace_2415728 : CollatzResearch.WordTrace tailWord_2415728 prefixEnd_2415728 1240429594524629686790275 := by
  unfold tailWord_2415728
  simp only [CollatzResearch.WordTrace]
  refine ⟨44054419296118752170427919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58739225728158336227237225 44054419296118752170427919)
  ·
    refine ⟨66081628944178128255641879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44054419296118752170427919 66081628944178128255641879)
    ·
      refine ⟨99122443416267192383462819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66081628944178128255641879 99122443416267192383462819)
      ·
        refine ⟨148683665124400788575194229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99122443416267192383462819 148683665124400788575194229)
        ·
          refine ⟨13939093605412573928924459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148683665124400788575194229 13939093605412573928924459)
          ·
            refine ⟨20908640408118860893386689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13939093605412573928924459 20908640408118860893386689)
            ·
              refine ⟨15681480306089145670040017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20908640408118860893386689 15681480306089145670040017)
              ·
                refine ⟨11761110229566859252530013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15681480306089145670040017 11761110229566859252530013)
                ·
                  refine ⟨4410416336087572219698755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11761110229566859252530013 4410416336087572219698755)
                  ·
                    refine ⟨6615624504131358329548133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4410416336087572219698755 6615624504131358329548133)
                    ·
                      refine ⟨1240429594524629686790275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6615624504131358329548133 1240429594524629686790275)
                      ·
                        rfl

theorem cell23_2415728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_2415728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415728 prefixEnd_2415728 := by exact prefixLift 2415728
  have htrace : WordTrace (prefixWord ++ tailWord_2415728) baseStart_2415728 baseEnd_2415728 := by
    simpa [prefixWord, tailWord_2415728, baseEnd_2415728] using wordTrace_append hprefix tailTrace_2415728
  have hstable : (prefixWord ++ tailWord_2415728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415728).length < 2 ^ (prefixWord ++ tailWord_2415728).sum := by decide
  have hdescent : baseEnd_2415728 < baseStart_2415728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415745 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2415745 : Nat := 118140960795 + 2415745 * 2 ^ 59
def prefixEnd_2415745 : Nat := 4983230072969 + 3 ^ 40 * 2415745 * 2
def baseEnd_2415745 : Nat := 1240438323695756120277697

theorem tailTrace_2415745 : CollatzResearch.WordTrace tailWord_2415745 prefixEnd_2415745 1240438323695756120277697 := by
  unfold tailWord_2415745
  simp only [CollatzResearch.WordTrace]
  refine ⟨88109458633175916244224689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58739639088783944162816459 88109458633175916244224689)
  ·
    refine ⟨66082093974881937183168517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88109458633175916244224689 66082093974881937183168517)
    ·
      refine ⟨12390392620290363221844097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66082093974881937183168517 12390392620290363221844097)
      ·
        refine ⟨9292794465217772416383073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12390392620290363221844097 9292794465217772416383073)
        ·
          refine ⟨6969595848913329312287305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9292794465217772416383073 6969595848913329312287305)
          ·
            refine ⟨5227196886684996984215479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6969595848913329312287305 5227196886684996984215479)
            ·
              refine ⟨7840795330027495476323219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227196886684996984215479 7840795330027495476323219)
              ·
                refine ⟨11761192995041243214484829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7840795330027495476323219 11761192995041243214484829)
                ·
                  refine ⟨4410447373140466205431811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11761192995041243214484829 4410447373140466205431811)
                  ·
                    refine ⟨6615671059710699308147717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4410447373140466205431811 6615671059710699308147717)
                    ·
                      refine ⟨1240438323695756120277697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6615671059710699308147717 1240438323695756120277697)
                      ·
                        rfl

theorem cell23_2415745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2415745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415745 prefixEnd_2415745 := by exact prefixLift 2415745
  have htrace : WordTrace (prefixWord ++ tailWord_2415745) baseStart_2415745 baseEnd_2415745 := by
    simpa [prefixWord, tailWord_2415745, baseEnd_2415745] using wordTrace_append hprefix tailTrace_2415745
  have hstable : (prefixWord ++ tailWord_2415745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415745).length < 2 ^ (prefixWord ++ tailWord_2415745).sum := by decide
  have hdescent : baseEnd_2415745 < baseStart_2415745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415771 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 6]
def baseStart_2415771 : Nat := 118140960795 + 2415771 * 2 ^ 59
def prefixEnd_2415771 : Nat := 4983230072969 + 3 ^ 40 * 2415771 * 2
def baseEnd_2415771 : Nat := 1240451674192773018552577

theorem tailTrace_2415771 : CollatzResearch.WordTrace tailWord_2415771 prefixEnd_2415771 1240451674192773018552577 := by
  unfold tailWord_2415771
  simp only [CollatzResearch.WordTrace]
  refine ⟨88110406931081722684671167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58740271287387815123114111 88110406931081722684671167)
  ·
    refine ⟨132165610396622584027006751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88110406931081722684671167 132165610396622584027006751)
    ·
      refine ⟨198248415594933876040510127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132165610396622584027006751 198248415594933876040510127)
      ·
        refine ⟨297372623392400814060765191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198248415594933876040510127 297372623392400814060765191)
        ·
          refine ⟨446058935088601221091147787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297372623392400814060765191 446058935088601221091147787)
          ·
            refine ⟨669088402632901831636721681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446058935088601221091147787 669088402632901831636721681)
            ·
              refine ⟨501816301974676373727541261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669088402632901831636721681 501816301974676373727541261)
              ·
                refine ⟨188181113240503640147827973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501816301974676373727541261 188181113240503640147827973)
                ·
                  refine ⟨35283958732594432527717745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188181113240503640147827973 35283958732594432527717745)
                  ·
                    refine ⟨26462969049445824395788309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35283958732594432527717745 26462969049445824395788309)
                    ·
                      refine ⟨1240451674192773018552577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26462969049445824395788309 1240451674192773018552577)
                      ·
                        rfl

theorem cell23_2415771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_2415771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415771 prefixEnd_2415771 := by exact prefixLift 2415771
  have htrace : WordTrace (prefixWord ++ tailWord_2415771) baseStart_2415771 baseEnd_2415771 := by
    simpa [prefixWord, tailWord_2415771, baseEnd_2415771] using wordTrace_append hprefix tailTrace_2415771
  have hstable : (prefixWord ++ tailWord_2415771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415771).length < 2 ^ (prefixWord ++ tailWord_2415771).sum := by decide
  have hdescent : baseEnd_2415771 < baseStart_2415771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415772 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_2415772 : Nat := 118140960795 + 2415772 * 2 ^ 59
def prefixEnd_2415772 : Nat := 4983230072969 + 3 ^ 40 * 2415772 * 2
def baseEnd_2415772 : Nat := 413484062557809171546691

theorem tailTrace_2415772 : CollatzResearch.WordTrace tailWord_2415772 prefixEnd_2415772 413484062557809171546691 := by
  unfold tailWord_2415772
  simp only [CollatzResearch.WordTrace]
  refine ⟨44055221702039049927728785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58740295602718733236971713 44055221702039049927728785)
  ·
    refine ⟨33041416276529287445796589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44055221702039049927728785 33041416276529287445796589)
    ·
      refine ⟨12390531103698482792173721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33041416276529287445796589 12390531103698482792173721)
      ·
        refine ⟨9292898327773862094130291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12390531103698482792173721 9292898327773862094130291)
        ·
          refine ⟨13939347491660793141195437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9292898327773862094130291 13939347491660793141195437)
          ·
            refine ⟨5227255309372797427948289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13939347491660793141195437 5227255309372797427948289)
            ·
              refine ⟨3920441482029598070961217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5227255309372797427948289 3920441482029598070961217)
              ·
                refine ⟨2940331111522198553220913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920441482029598070961217 2940331111522198553220913)
                ·
                  refine ⟨2205248333641648914915685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940331111522198553220913 2205248333641648914915685)
                  ·
                    refine ⟨413484062557809171546691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2205248333641648914915685 413484062557809171546691)
                    ·
                      rfl

theorem cell23_2415772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_2415772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415772 prefixEnd_2415772 := by exact prefixLift 2415772
  have htrace : WordTrace (prefixWord ++ tailWord_2415772) baseStart_2415772 baseEnd_2415772 := by
    simpa [prefixWord, tailWord_2415772, baseEnd_2415772] using wordTrace_append hprefix tailTrace_2415772
  have hstable : (prefixWord ++ tailWord_2415772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415772).length < 2 ^ (prefixWord ++ tailWord_2415772).sum := by decide
  have hdescent : baseEnd_2415772 < baseStart_2415772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415829 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2415829 : Nat := 118140960795 + 2415829 * 2 ^ 59
def prefixEnd_2415829 : Nat := 4983230072969 + 3 ^ 40 * 2415829 * 2
def baseEnd_2415829 : Nat := 1240481456070733791627311

theorem tailTrace_2415829 : CollatzResearch.WordTrace tailWord_2415829 prefixEnd_2415829 1240481456070733791627311 := by
  unfold tailWord_2415829
  simp only [CollatzResearch.WordTrace]
  refine ⟨88112522364871598590282541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58741681576581065726855027 88112522364871598590282541)
  ·
    refine ⟨33042195886826849471355953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88112522364871598590282541 33042195886826849471355953)
    ·
      refine ⟨24781646915120137103516965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33042195886826849471355953 24781646915120137103516965)
      ·
        refine ⟨4646558796585025706909431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24781646915120137103516965 4646558796585025706909431)
        ·
          refine ⟨6969838194877538560364147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4646558796585025706909431 6969838194877538560364147)
          ·
            refine ⟨10454757292316307840546221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6969838194877538560364147 10454757292316307840546221)
            ·
              refine ⟨3920533984618615440204833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10454757292316307840546221 3920533984618615440204833)
              ·
                refine ⟨2940400488463961580153625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920533984618615440204833 2940400488463961580153625)
                ·
                  refine ⟨2205300366347971185115219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940400488463961580153625 2205300366347971185115219)
                  ·
                    refine ⟨3307950549521956777672829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2205300366347971185115219 3307950549521956777672829)
                    ·
                      refine ⟨1240481456070733791627311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3307950549521956777672829 1240481456070733791627311)
                      ·
                        rfl

theorem cell23_2415829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2415829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415829 prefixEnd_2415829 := by exact prefixLift 2415829
  have htrace : WordTrace (prefixWord ++ tailWord_2415829) baseStart_2415829 baseEnd_2415829 := by
    simpa [prefixWord, tailWord_2415829, baseEnd_2415829] using wordTrace_append hprefix tailTrace_2415829
  have hstable : (prefixWord ++ tailWord_2415829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415829).length < 2 ^ (prefixWord ++ tailWord_2415829).sum := by decide
  have hdescent : baseEnd_2415829 < baseStart_2415829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415852 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 1, 4, 2]
def baseStart_2415852 : Nat := 118140960795 + 2415852 * 2 ^ 59
def prefixEnd_2415852 : Nat := 4983230072969 + 3 ^ 40 * 2415852 * 2
def baseEnd_2415852 : Nat := 1240493266125787201639705

theorem tailTrace_2415852 : CollatzResearch.WordTrace tailWord_2415852 prefixEnd_2415852 1240493266125787201639705 := by
  unfold tailWord_2415852
  simp only [CollatzResearch.WordTrace]
  refine ⟨44056680621894136759184905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58742240829192182345579873 44056680621894136759184905)
  ·
    refine ⟨33042510466420602569388679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44056680621894136759184905 33042510466420602569388679)
    ·
      refine ⟨49563765699630903854083019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33042510466420602569388679 49563765699630903854083019)
      ·
        refine ⟨74345648549446355781124529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49563765699630903854083019 74345648549446355781124529)
        ·
          refine ⟨55759236412084766835843397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74345648549446355781124529 55759236412084766835843397)
          ·
            refine ⟨10454856827265893781720637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55759236412084766835843397 10454856827265893781720637)
            ·
              refine ⟨3920571310224710168145239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10454856827265893781720637 3920571310224710168145239)
              ·
                refine ⟨5880856965337065252217859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920571310224710168145239 5880856965337065252217859)
                ·
                  refine ⟨8821285448005597878326789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5880856965337065252217859 8821285448005597878326789)
                  ·
                    refine ⟨1653991021501049602186273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8821285448005597878326789 1653991021501049602186273)
                    ·
                      refine ⟨1240493266125787201639705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1653991021501049602186273 1240493266125787201639705)
                      ·
                        rfl

theorem cell23_2415852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_2415852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415852 prefixEnd_2415852 := by exact prefixLift 2415852
  have htrace : WordTrace (prefixWord ++ tailWord_2415852) baseStart_2415852 baseEnd_2415852 := by
    simpa [prefixWord, tailWord_2415852, baseEnd_2415852] using wordTrace_append hprefix tailTrace_2415852
  have hstable : (prefixWord ++ tailWord_2415852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415852).length < 2 ^ (prefixWord ++ tailWord_2415852).sum := by decide
  have hdescent : baseEnd_2415852 < baseStart_2415852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415903 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 2, 2, 2]
def baseStart_2415903 : Nat := 118140960795 + 2415903 * 2 ^ 59
def prefixEnd_2415903 : Nat := 4983230072969 + 3 ^ 40 * 2415903 * 2
def baseEnd_2415903 : Nat := 1240519453639166502101971

theorem tailTrace_2415903 : CollatzResearch.WordTrace tailWord_2415903 prefixEnd_2415903 1240519453639166502101971 := by
  unfold tailWord_2415903
  simp only [CollatzResearch.WordTrace]
  refine ⟨88115221366603509228476363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58743480911069006152317575 88115221366603509228476363)
  ·
    refine ⟨132172832049905263842714545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88115221366603509228476363 132172832049905263842714545)
    ·
      refine ⟨99129624037428947882035909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132172832049905263842714545 99129624037428947882035909)
      ·
        refine ⟨18586804507017927727881733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99129624037428947882035909 18586804507017927727881733)
        ·
          refine ⟨3485025845065861448977825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18586804507017927727881733 3485025845065861448977825)
          ·
            refine ⟨2613769383799396086733369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3485025845065861448977825 2613769383799396086733369)
            ·
              refine ⟨1960327037849547065050027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2613769383799396086733369 1960327037849547065050027)
              ·
                refine ⟨2940490556774320597575041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960327037849547065050027 2940490556774320597575041)
                ·
                  refine ⟨2205367917580740448181281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940490556774320597575041 2205367917580740448181281)
                  ·
                    refine ⟨1654025938185555336135961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2205367917580740448181281 1654025938185555336135961)
                    ·
                      refine ⟨1240519453639166502101971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654025938185555336135961 1240519453639166502101971)
                      ·
                        rfl

theorem cell23_2415903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_2415903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415903 prefixEnd_2415903 := by exact prefixLift 2415903
  have htrace : WordTrace (prefixWord ++ tailWord_2415903) baseStart_2415903 baseEnd_2415903 := by
    simpa [prefixWord, tailWord_2415903, baseEnd_2415903] using wordTrace_append hprefix tailTrace_2415903
  have hstable : (prefixWord ++ tailWord_2415903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415903).length < 2 ^ (prefixWord ++ tailWord_2415903).sum := by decide
  have hdescent : baseEnd_2415903 < baseStart_2415903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415922 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_2415922 : Nat := 118140960795 + 2415922 * 2 ^ 59
def prefixEnd_2415922 : Nat := 4983230072969 + 3 ^ 40 * 2415922 * 2
def baseEnd_2415922 : Nat := 413509736590533975921461

theorem tailTrace_2415922 : CollatzResearch.WordTrace tailWord_2415922 prefixEnd_2415922 413509736590533975921461 := by
  unfold tailWord_2415922
  simp only [CollatzResearch.WordTrace]
  refine ⟨22028978588383668868354505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58743942902356450315612013 22028978588383668868354505)
  ·
    refine ⟨16521733941287751651265879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22028978588383668868354505 16521733941287751651265879)
    ·
      refine ⟨24782600911931627476898819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16521733941287751651265879 24782600911931627476898819)
      ·
        refine ⟨37173901367897441215348229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24782600911931627476898819 37173901367897441215348229)
        ·
          refine ⟨6970106506480770227877793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37173901367897441215348229 6970106506480770227877793)
          ·
            refine ⟨5227579879860577670908345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6970106506480770227877793 5227579879860577670908345)
            ·
              refine ⟨3920684909895433253181259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5227579879860577670908345 3920684909895433253181259)
              ·
                refine ⟨5881027364843149879771889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920684909895433253181259 5881027364843149879771889)
                ·
                  refine ⟨4410770523632362409828917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5881027364843149879771889 4410770523632362409828917)
                  ·
                    refine ⟨413509736590533975921461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4410770523632362409828917 413509736590533975921461)
                    ·
                      rfl

theorem cell23_2415922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_2415922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415922 prefixEnd_2415922 := by exact prefixLift 2415922
  have htrace : WordTrace (prefixWord ++ tailWord_2415922) baseStart_2415922 baseEnd_2415922 := by
    simpa [prefixWord, tailWord_2415922, baseEnd_2415922] using wordTrace_append hprefix tailTrace_2415922
  have hstable : (prefixWord ++ tailWord_2415922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415922).length < 2 ^ (prefixWord ++ tailWord_2415922).sum := by decide
  have hdescent : baseEnd_2415922 < baseStart_2415922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2415976 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_2415976 : Nat := 118140960795 + 2415976 * 2 ^ 59
def prefixEnd_2415976 : Nat := 4983230072969 + 3 ^ 40 * 2415976 * 2
def baseEnd_2415976 : Nat := 1240556937726944716489135

theorem tailTrace_2415976 : CollatzResearch.WordTrace tailWord_2415976 prefixEnd_2415976 1240556937726944716489135 := by
  unfold tailWord_2415976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44058941947669521347941891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58745255930226028463922521 44058941947669521347941891)
  ·
    refine ⟨66088412921504282021912837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44058941947669521347941891 66088412921504282021912837)
    ·
      refine ⟨12391577422782052879108657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66088412921504282021912837 12391577422782052879108657)
      ·
        refine ⟨9293683067086539659331493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12391577422782052879108657 9293683067086539659331493)
        ·
          refine ⟨1742565575078726186124655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9293683067086539659331493 1742565575078726186124655)
          ·
            refine ⟨2613848362618089279186983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1742565575078726186124655 2613848362618089279186983)
            ·
              refine ⟨3920772543927133918780475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613848362618089279186983 3920772543927133918780475)
              ·
                refine ⟨5881158815890700878170713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3920772543927133918780475 5881158815890700878170713)
                ·
                  refine ⟨4410869111918025658628035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5881158815890700878170713 4410869111918025658628035)
                  ·
                    refine ⟨6616303667877038487942053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4410869111918025658628035 6616303667877038487942053)
                    ·
                      refine ⟨1240556937726944716489135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6616303667877038487942053 1240556937726944716489135)
                      ·
                        rfl

theorem cell23_2415976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_2415976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2415976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2415976 prefixEnd_2415976 := by exact prefixLift 2415976
  have htrace : WordTrace (prefixWord ++ tailWord_2415976) baseStart_2415976 baseEnd_2415976 := by
    simpa [prefixWord, tailWord_2415976, baseEnd_2415976] using wordTrace_append hprefix tailTrace_2415976
  have hstable : (prefixWord ++ tailWord_2415976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2415976).length < 2 ^ (prefixWord ++ tailWord_2415976).sum := by decide
  have hdescent : baseEnd_2415976 < baseStart_2415976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2415976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416029 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_2416029 : Nat := 118140960795 + 2416029 * 2 ^ 59
def prefixEnd_2416029 : Nat := 4983230072969 + 3 ^ 40 * 2416029 * 2
def baseEnd_2416029 : Nat := 413528050733877669708797

theorem tailTrace_2416029 : CollatzResearch.WordTrace tailWord_2416029 prefixEnd_2416029 413528050733877669708797 := by
  unfold tailWord_2416029
  simp only [CollatzResearch.WordTrace]
  refine ⟨88119816964147032747563141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58746544642764688498375427 88119816964147032747563141)
  ·
    refine ⟨16522465680777568640168089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88119816964147032747563141 16522465680777568640168089)
    ·
      refine ⟨12391849260583176480126067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16522465680777568640168089 12391849260583176480126067)
      ·
        refine ⟨18587773890874764720189101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12391849260583176480126067 18587773890874764720189101)
        ·
          refine ⟨6970415209078036770070913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18587773890874764720189101 6970415209078036770070913)
          ·
            refine ⟨5227811406808527577553185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6970415209078036770070913 5227811406808527577553185)
            ·
              refine ⟨3920858555106395683164889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5227811406808527577553185 3920858555106395683164889)
              ·
                refine ⟨2940643916329796762373667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3920858555106395683164889 2940643916329796762373667)
                ·
                  refine ⟨4410965874494695143560501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940643916329796762373667 4410965874494695143560501)
                  ·
                    refine ⟨413528050733877669708797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4410965874494695143560501 413528050733877669708797)
                    ·
                      rfl

theorem cell23_2416029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_2416029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416029 prefixEnd_2416029 := by exact prefixLift 2416029
  have htrace : WordTrace (prefixWord ++ tailWord_2416029) baseStart_2416029 baseEnd_2416029 := by
    simpa [prefixWord, tailWord_2416029, baseEnd_2416029] using wordTrace_append hprefix tailTrace_2416029
  have hstable : (prefixWord ++ tailWord_2416029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416029).length < 2 ^ (prefixWord ++ tailWord_2416029).sum := by decide
  have hdescent : baseEnd_2416029 < baseStart_2416029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416032 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 2, 6, 2]
def baseStart_2416032 : Nat := 118140960795 + 2416032 * 2 ^ 59
def prefixEnd_2416032 : Nat := 4983230072969 + 3 ^ 40 * 2416032 * 2
def baseEnd_2416032 : Nat := 1240585692643596497388877

theorem tailTrace_2416032 : CollatzResearch.WordTrace tailWord_2416032 prefixEnd_2416032 1240585692643596497388877 := by
  unfold tailWord_2416032
  simp only [CollatzResearch.WordTrace]
  refine ⟨44059963191568082129961175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58746617588757442839948233 44059963191568082129961175)
  ·
    refine ⟨66089944787352123194941763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44059963191568082129961175 66089944787352123194941763)
    ·
      refine ⟨99134917181028184792412645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66089944787352123194941763 99134917181028184792412645)
      ·
        refine ⟨18587796971442784648577371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99134917181028184792412645 18587796971442784648577371)
        ·
          refine ⟨27881695457164176972866057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18587796971442784648577371 27881695457164176972866057)
          ·
            refine ⟨20911271592873132729649543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27881695457164176972866057 20911271592873132729649543)
            ·
              refine ⟨31366907389309699094474315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20911271592873132729649543 31366907389309699094474315)
              ·
                refine ⟨47050361083964548641711473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31366907389309699094474315 47050361083964548641711473)
                ·
                  refine ⟨35287770812973411481283605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47050361083964548641711473 35287770812973411481283605)
                  ·
                    refine ⟨1654114256858128663185169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35287770812973411481283605 1654114256858128663185169)
                    ·
                      refine ⟨1240585692643596497388877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654114256858128663185169 1240585692643596497388877)
                      ·
                        rfl

theorem cell23_2416032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_2416032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416032 prefixEnd_2416032 := by exact prefixLift 2416032
  have htrace : WordTrace (prefixWord ++ tailWord_2416032) baseStart_2416032 baseEnd_2416032 := by
    simpa [prefixWord, tailWord_2416032, baseEnd_2416032] using wordTrace_append hprefix tailTrace_2416032
  have hstable : (prefixWord ++ tailWord_2416032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416032).length < 2 ^ (prefixWord ++ tailWord_2416032).sum := by decide
  have hdescent : baseEnd_2416032 < baseStart_2416032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416035 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 5]
def baseStart_2416035 : Nat := 118140960795 + 2416035 * 2 ^ 59
def prefixEnd_2416035 : Nat := 4983230072969 + 3 ^ 40 * 2416035 * 2
def baseEnd_2416035 : Nat := 1240587233085559985651363

theorem tailTrace_2416035 : CollatzResearch.WordTrace tailWord_2416035 prefixEnd_2416035 1240587233085559985651363 := by
  unfold tailWord_2416035
  simp only [CollatzResearch.WordTrace]
  refine ⟨88120035802125295772281559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58746690534750197181521039 88120035802125295772281559)
  ·
    refine ⟨132180053703187943658422339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88120035802125295772281559 132180053703187943658422339)
    ·
      refine ⟨198270080554781915487633509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132180053703187943658422339 198270080554781915487633509)
      ·
        refine ⟨37175640104021609153931283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198270080554781915487633509 37175640104021609153931283)
        ·
          refine ⟨55763460156032413730896925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37175640104021609153931283 55763460156032413730896925)
          ·
            refine ⟨20911297558512155149086347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55763460156032413730896925 20911297558512155149086347)
            ·
              refine ⟨31366946337768232723629521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20911297558512155149086347 31366946337768232723629521)
              ·
                refine ⟨23525209753326174542722141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31366946337768232723629521 23525209753326174542722141)
                ·
                  refine ⟨8821953657497315453520803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23525209753326174542722141 8821953657497315453520803)
                  ·
                    refine ⟨13232930486245973180281205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8821953657497315453520803 13232930486245973180281205)
                    ·
                      refine ⟨1240587233085559985651363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13232930486245973180281205 1240587233085559985651363)
                      ·
                        rfl

theorem cell23_2416035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_2416035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416035 prefixEnd_2416035 := by exact prefixLift 2416035
  have htrace : WordTrace (prefixWord ++ tailWord_2416035) baseStart_2416035 baseEnd_2416035 := by
    simpa [prefixWord, tailWord_2416035, baseEnd_2416035] using wordTrace_append hprefix tailTrace_2416035
  have hstable : (prefixWord ++ tailWord_2416035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416035).length < 2 ^ (prefixWord ++ tailWord_2416035).sum := by decide
  have hdescent : baseEnd_2416035 < baseStart_2416035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416060 : List Nat := [2, 2, 2, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_2416060 : Nat := 118140960795 + 2416060 * 2 ^ 59
def prefixEnd_2416060 : Nat := 4983230072969 + 3 ^ 40 * 2416060 * 2
def baseEnd_2416060 : Nat := 1240600070101922387838749

theorem tailTrace_2416060 : CollatzResearch.WordTrace tailWord_2416060 prefixEnd_2416060 1240600070101922387838749 := by
  unfold tailWord_2416060
  simp only [CollatzResearch.WordTrace]
  refine ⟨44060473813517362520970817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58747298418023150027961089 44060473813517362520970817)
  ·
    refine ⟨33045355360138021890728113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44060473813517362520970817 33045355360138021890728113)
    ·
      refine ⟨24784016520103516418046085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33045355360138021890728113 24784016520103516418046085)
      ·
        refine ⟨4647003097519409328383641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24784016520103516418046085 4647003097519409328383641)
        ·
          refine ⟨3485252323139556996287731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4647003097519409328383641 3485252323139556996287731)
          ·
            refine ⟨5227878484709335494431597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485252323139556996287731 5227878484709335494431597)
            ·
              refine ⟨1960454431766000810411849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5227878484709335494431597 1960454431766000810411849)
              ·
                refine ⟨1470340823824500607808887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960454431766000810411849 1470340823824500607808887)
                ·
                  refine ⟨2205511235736750911713331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470340823824500607808887 2205511235736750911713331)
                  ·
                    refine ⟨3308266853605126367569997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2205511235736750911713331 3308266853605126367569997)
                    ·
                      refine ⟨1240600070101922387838749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3308266853605126367569997 1240600070101922387838749)
                      ·
                        rfl

theorem cell23_2416060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_2416060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416060 prefixEnd_2416060 := by exact prefixLift 2416060
  have htrace : WordTrace (prefixWord ++ tailWord_2416060) baseStart_2416060 baseEnd_2416060 := by
    simpa [prefixWord, tailWord_2416060, baseEnd_2416060] using wordTrace_append hprefix tailTrace_2416060
  have hstable : (prefixWord ++ tailWord_2416060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416060).length < 2 ^ (prefixWord ++ tailWord_2416060).sum := by decide
  have hdescent : baseEnd_2416060 < baseStart_2416060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416076 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_2416076 : Nat := 118140960795 + 2416076 * 2 ^ 59
def prefixEnd_2416076 : Nat := 4983230072969 + 3 ^ 40 * 2416076 * 2
def baseEnd_2416076 : Nat := 413536095264131441746225

theorem tailTrace_2416076 : CollatzResearch.WordTrace tailWord_2416076 prefixEnd_2416076 413536095264131441746225 := by
  unfold tailWord_2416076
  simp only [CollatzResearch.WordTrace]
  refine ⟨44060765597488379887262041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58747687463317839849682721 44060765597488379887262041)
  ·
    refine ⟨33045574198116284915446531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44060765597488379887262041 33045574198116284915446531)
    ·
      refine ⟨49568361297174427373169797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33045574198116284915446531 49568361297174427373169797)
      ·
        refine ⟨9294067743220205132469337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49568361297174427373169797 9294067743220205132469337)
        ·
          refine ⟨6970550807415153849352003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9294067743220205132469337 6970550807415153849352003)
          ·
            refine ⟨10455826211122730774028005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6970550807415153849352003 10455826211122730774028005)
            ·
              refine ⟨1960467414585512020130251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10455826211122730774028005 1960467414585512020130251)
              ·
                refine ⟨2940701121878268030195377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960467414585512020130251 2940701121878268030195377)
                ·
                  refine ⟨2205525841408701022646533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2940701121878268030195377 2205525841408701022646533)
                  ·
                    refine ⟨413536095264131441746225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2205525841408701022646533 413536095264131441746225)
                    ·
                      rfl

theorem cell23_2416076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_2416076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416076 prefixEnd_2416076 := by exact prefixLift 2416076
  have htrace : WordTrace (prefixWord ++ tailWord_2416076) baseStart_2416076 baseEnd_2416076 := by
    simpa [prefixWord, tailWord_2416076, baseEnd_2416076] using wordTrace_append hprefix tailTrace_2416076
  have hstable : (prefixWord ++ tailWord_2416076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416076).length < 2 ^ (prefixWord ++ tailWord_2416076).sum := by decide
  have hdescent : baseEnd_2416076 < baseStart_2416076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416086 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2416086 : Nat := 118140960795 + 2416086 * 2 ^ 59
def prefixEnd_2416086 : Nat := 4983230072969 + 3 ^ 40 * 2416086 * 2
def baseEnd_2416086 : Nat := 1240613420598939286113629

theorem tailTrace_2416086 : CollatzResearch.WordTrace tailWord_2416086 prefixEnd_2416086 1240613420598939286113629 := by
  unfold tailWord_2416086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5507618495308783217649257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58747930616627020988258741 5507618495308783217649257)
  ·
    refine ⟨4130713871481587413236943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5507618495308783217649257 4130713871481587413236943)
    ·
      refine ⟨6196070807222381119855415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4130713871481587413236943 6196070807222381119855415)
      ·
        refine ⟨9294106210833571679783123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196070807222381119855415 9294106210833571679783123)
        ·
          refine ⟨13941159316250357519674685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9294106210833571679783123 13941159316250357519674685)
          ·
            refine ⟨5227934743593884069878007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13941159316250357519674685 5227934743593884069878007)
            ·
              refine ⟨7841902115390826104817011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227934743593884069878007 7841902115390826104817011)
              ·
                refine ⟨11762853173086239157225517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7841902115390826104817011 11762853173086239157225517)
                ·
                  refine ⟨4411069939907339683959569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11762853173086239157225517 4411069939907339683959569)
                  ·
                    refine ⟨3308302454930504762969677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4411069939907339683959569 3308302454930504762969677)
                    ·
                      refine ⟨1240613420598939286113629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3308302454930504762969677 1240613420598939286113629)
                      ·
                        rfl

theorem cell23_2416086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2416086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416086 prefixEnd_2416086 := by exact prefixLift 2416086
  have htrace : WordTrace (prefixWord ++ tailWord_2416086) baseStart_2416086 baseEnd_2416086 := by
    simpa [prefixWord, tailWord_2416086, baseEnd_2416086] using wordTrace_append hprefix tailTrace_2416086
  have hstable : (prefixWord ++ tailWord_2416086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416086).length < 2 ^ (prefixWord ++ tailWord_2416086).sum := by decide
  have hdescent : baseEnd_2416086 < baseStart_2416086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416099 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2416099 : Nat := 118140960795 + 2416099 * 2 ^ 59
def prefixEnd_2416099 : Nat := 4983230072969 + 3 ^ 40 * 2416099 * 2
def baseEnd_2416099 : Nat := 1240620095847447735251069

theorem tailTrace_2416099 : CollatzResearch.WordTrace tailWord_2416099 prefixEnd_2416099 1240620095847447735251069 := by
  unfold tailWord_2416099
  simp only [CollatzResearch.WordTrace]
  refine ⟨88122370073893434702611351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58748246715928956468407567 88122370073893434702611351)
  ·
    refine ⟨132183555110840152053917027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88122370073893434702611351 132183555110840152053917027)
    ·
      refine ⟨198275332666260228080875541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132183555110840152053917027 198275332666260228080875541)
      ·
        refine ⟨9294156218730948191291041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 198275332666260228080875541 9294156218730948191291041)
        ·
          refine ⟨6970617164048211143468281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9294156218730948191291041 6970617164048211143468281)
          ·
            refine ⟨5227962873036158357601211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6970617164048211143468281 5227962873036158357601211)
            ·
              refine ⟨7841944309554237536401817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227962873036158357601211 7841944309554237536401817)
              ·
                refine ⟨5881458232165678152301363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7841944309554237536401817 5881458232165678152301363)
                ·
                  refine ⟨8822187348248517228452045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5881458232165678152301363 8822187348248517228452045)
                  ·
                    refine ⟨3308320255593193960669517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8822187348248517228452045 3308320255593193960669517)
                    ·
                      refine ⟨1240620095847447735251069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3308320255593193960669517 1240620095847447735251069)
                      ·
                        rfl

theorem cell23_2416099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2416099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416099 prefixEnd_2416099 := by exact prefixLift 2416099
  have htrace : WordTrace (prefixWord ++ tailWord_2416099) baseStart_2416099 baseEnd_2416099 := by
    simpa [prefixWord, tailWord_2416099, baseEnd_2416099] using wordTrace_append hprefix tailTrace_2416099
  have hstable : (prefixWord ++ tailWord_2416099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416099).length < 2 ^ (prefixWord ++ tailWord_2416099).sum := by decide
  have hdescent : baseEnd_2416099 < baseStart_2416099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416117 : List Nat := [1, 3, 5, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2416117 : Nat := 118140960795 + 2416117 * 2 ^ 59
def prefixEnd_2416117 : Nat := 4983230072969 + 3 ^ 40 * 2416117 * 2
def baseEnd_2416117 : Nat := 1240629338499228664825987

theorem tailTrace_2416117 : CollatzResearch.WordTrace tailWord_2416117 prefixEnd_2416117 1240629338499228664825987 := by
  unfold tailWord_2416117
  simp only [CollatzResearch.WordTrace]
  refine ⟨88123026587828223776766605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58748684391885482517844403 88123026587828223776766605)
  ·
    refine ⟨33046134970435583916287477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88123026587828223776766605 33046134970435583916287477)
    ·
      refine ⟨3098075153478335992151951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33046134970435583916287477 3098075153478335992151951)
      ·
        refine ⟨4647112730217503988227927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098075153478335992151951 4647112730217503988227927)
        ·
          refine ⟨6970669095326255982341891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647112730217503988227927 6970669095326255982341891)
          ·
            refine ⟨10456003642989383973512837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6970669095326255982341891 10456003642989383973512837)
            ·
              refine ⟨1960500683060509495033657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10456003642989383973512837 1960500683060509495033657)
              ·
                refine ⟨1470375512295382121275243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960500683060509495033657 1470375512295382121275243)
                ·
                  refine ⟨2205563268443073181912865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470375512295382121275243 2205563268443073181912865)
                  ·
                    refine ⟨1654172451332304886434649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2205563268443073181912865 1654172451332304886434649)
                    ·
                      refine ⟨1240629338499228664825987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654172451332304886434649 1240629338499228664825987)
                      ·
                        rfl

theorem cell23_2416117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2416117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416117 prefixEnd_2416117 := by exact prefixLift 2416117
  have htrace : WordTrace (prefixWord ++ tailWord_2416117) baseStart_2416117 baseEnd_2416117 := by
    simpa [prefixWord, tailWord_2416117, baseEnd_2416117] using wordTrace_append hprefix tailTrace_2416117
  have hstable : (prefixWord ++ tailWord_2416117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416117).length < 2 ^ (prefixWord ++ tailWord_2416117).sum := by decide
  have hdescent : baseEnd_2416117 < baseStart_2416117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416156 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_2416156 : Nat := 118140960795 + 2416156 * 2 ^ 59
def prefixEnd_2416156 : Nat := 4983230072969 + 3 ^ 40 * 2416156 * 2
def baseEnd_2416156 : Nat := 1240649364244754012238307

theorem tailTrace_2416156 : CollatzResearch.WordTrace tailWord_2416156 prefixEnd_2416156 1240649364244754012238307 := by
  unfold tailWord_2416156
  simp only [CollatzResearch.WordTrace]
  refine ⟨44062224517343466718718161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58749632689791288958290881 44062224517343466718718161)
  ·
    refine ⟨33046668388007600039038621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44062224517343466718718161 33046668388007600039038621)
    ·
      refine ⟨12392500645502850014639483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33046668388007600039038621 12392500645502850014639483)
      ·
        refine ⟨18588750968254275021959225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12392500645502850014639483 18588750968254275021959225)
        ·
          refine ⟨13941563226190706266469419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18588750968254275021959225 13941563226190706266469419)
          ·
            refine ⟨20912344839286059399704129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13941563226190706266469419 20912344839286059399704129)
            ·
              refine ⟨15684258629464544549778097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20912344839286059399704129 15684258629464544549778097)
              ·
                refine ⟨11763193972098408412333573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15684258629464544549778097 11763193972098408412333573)
                ·
                  refine ⟨2205598869768451577312545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11763193972098408412333573 2205598869768451577312545)
                  ·
                    refine ⟨1654199152326338682984409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2205598869768451577312545 1654199152326338682984409)
                    ·
                      refine ⟨1240649364244754012238307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654199152326338682984409 1240649364244754012238307)
                      ·
                        rfl

theorem cell23_2416156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_2416156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416156 prefixEnd_2416156 := by exact prefixLift 2416156
  have htrace : WordTrace (prefixWord ++ tailWord_2416156) baseStart_2416156 baseEnd_2416156 := by
    simpa [prefixWord, tailWord_2416156, baseEnd_2416156] using wordTrace_append hprefix tailTrace_2416156
  have hstable : (prefixWord ++ tailWord_2416156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416156).length < 2 ^ (prefixWord ++ tailWord_2416156).sum := by decide
  have hdescent : baseEnd_2416156 < baseStart_2416156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416160 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2416160 : Nat := 118140960795 + 2416160 * 2 ^ 59
def prefixEnd_2416160 : Nat := 4983230072969 + 3 ^ 40 * 2416160 * 2
def baseEnd_2416160 : Nat := 1240651418167371996588289

theorem tailTrace_2416160 : CollatzResearch.WordTrace tailWord_2416160 prefixEnd_2416160 1240651418167371996588289 := by
  unfold tailWord_2416160
  simp only [CollatzResearch.WordTrace]
  refine ⟨44062297463336221060290967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58749729951114961413721289 44062297463336221060290967)
  ·
    refine ⟨66093446195004331590436451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44062297463336221060290967 66093446195004331590436451)
    ·
      refine ⟨99140169292506497385654677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66093446195004331590436451 99140169292506497385654677)
      ·
        refine ⟨4647195435586242064952563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99140169292506497385654677 4647195435586242064952563)
        ·
          refine ⟨6970793153379363097428845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647195435586242064952563 6970793153379363097428845)
          ·
            refine ⟨2614047432517261161535817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6970793153379363097428845 2614047432517261161535817)
            ·
              refine ⟨1960535574387945871151863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2614047432517261161535817 1960535574387945871151863)
              ·
                refine ⟨2940803361581918806727795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960535574387945871151863 2940803361581918806727795)
                ·
                  refine ⟨4411205042372878210091693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2940803361581918806727795 4411205042372878210091693)
                  ·
                    refine ⟨1654201890889829328784385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4411205042372878210091693 1654201890889829328784385)
                    ·
                      refine ⟨1240651418167371996588289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654201890889829328784385 1240651418167371996588289)
                      ·
                        rfl

theorem cell23_2416160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2416160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416160 prefixEnd_2416160 := by exact prefixLift 2416160
  have htrace : WordTrace (prefixWord ++ tailWord_2416160) baseStart_2416160 baseEnd_2416160 := by
    simpa [prefixWord, tailWord_2416160, baseEnd_2416160] using wordTrace_append hprefix tailTrace_2416160
  have hstable : (prefixWord ++ tailWord_2416160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416160).length < 2 ^ (prefixWord ++ tailWord_2416160).sum := by decide
  have hdescent : baseEnd_2416160 < baseStart_2416160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416179 : List Nat := [1, 1, 1, 2, 4, 3, 2, 4, 5]
def baseStart_2416179 : Nat := 118140960795 + 2416179 * 2 ^ 59
def prefixEnd_2416179 : Nat := 4983230072969 + 3 ^ 40 * 2416179 * 2
def baseEnd_2416179 : Nat := 137851241588867491361189

theorem tailTrace_2416179 : CollatzResearch.WordTrace tailWord_2416179 prefixEnd_2416179 137851241588867491361189 := by
  unfold tailWord_2416179
  simp only [CollatzResearch.WordTrace]
  refine ⟨88125287913603608365523591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58750191942402405577015727 88125287913603608365523591)
  ·
    refine ⟨132187931870405412548285387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88125287913603608365523591 132187931870405412548285387)
    ·
      refine ⟨198281897805608118822428081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132187931870405412548285387 198281897805608118822428081)
      ·
        refine ⟨148711423354206089116821061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198281897805608118822428081 148711423354206089116821061)
        ·
          refine ⟨27883391878913641709403949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148711423354206089116821061 27883391878913641709403949)
          ·
            refine ⟨10456271954592615641026481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27883391878913641709403949 10456271954592615641026481)
            ·
              refine ⟨7842203965944461730769861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10456271954592615641026481 7842203965944461730769861)
              ·
                refine ⟨1470413243614586574519349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7842203965944461730769861 1470413243614586574519349)
                ·
                  refine ⟨137851241588867491361189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1470413243614586574519349 137851241588867491361189)
                  ·
                    rfl

theorem cell23_2416179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 5].length) (baseStart_2416179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416179 prefixEnd_2416179 := by exact prefixLift 2416179
  have htrace : WordTrace (prefixWord ++ tailWord_2416179) baseStart_2416179 baseEnd_2416179 := by
    simpa [prefixWord, tailWord_2416179, baseEnd_2416179] using wordTrace_append hprefix tailTrace_2416179
  have hstable : (prefixWord ++ tailWord_2416179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416179).length < 2 ^ (prefixWord ++ tailWord_2416179).sum := by decide
  have hdescent : baseEnd_2416179 < baseStart_2416179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416229 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2416229 : Nat := 118140960795 + 2416229 * 2 ^ 59
def prefixEnd_2416229 : Nat := 4983230072969 + 3 ^ 40 * 2416229 * 2
def baseEnd_2416229 : Nat := 1240686848332532226625471

theorem tailTrace_2416229 : CollatzResearch.WordTrace tailWord_2416229 prefixEnd_2416229 1240686848332532226625471 := by
  unfold tailWord_2416229
  simp only [CollatzResearch.WordTrace]
  refine ⟨88127111563422466904843741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58751407708948311269895827 88127111563422466904843741)
  ·
    refine ⟨33047666836283425089316403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88127111563422466904843741 33047666836283425089316403)
    ·
      refine ⟨49571500254425137633974605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33047666836283425089316403 49571500254425137633974605)
      ·
        refine ⟨18589312595409426612740477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49571500254425137633974605 18589312595409426612740477)
        ·
          refine ⟨6970992223278534979777679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18589312595409426612740477 6970992223278534979777679)
          ·
            refine ⟨10456488334917802469666519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6970992223278534979777679 10456488334917802469666519)
            ·
              refine ⟨15684732502376703704499779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10456488334917802469666519 15684732502376703704499779)
              ·
                refine ⟨23527098753565055556749669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15684732502376703704499779 23527098753565055556749669)
                ·
                  refine ⟨4411331016293447916890563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23527098753565055556749669 4411331016293447916890563)
                  ·
                    refine ⟨6616996524440171875335845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4411331016293447916890563 6616996524440171875335845)
                    ·
                      refine ⟨1240686848332532226625471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6616996524440171875335845 1240686848332532226625471)
                      ·
                        rfl

theorem cell23_2416229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2416229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416229 prefixEnd_2416229 := by exact prefixLift 2416229
  have htrace : WordTrace (prefixWord ++ tailWord_2416229) baseStart_2416229 baseEnd_2416229 := by
    simpa [prefixWord, tailWord_2416229, baseEnd_2416229] using wordTrace_append hprefix tailTrace_2416229
  have hstable : (prefixWord ++ tailWord_2416229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416229).length < 2 ^ (prefixWord ++ tailWord_2416229).sum := by decide
  have hdescent : baseEnd_2416229 < baseStart_2416229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416249 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 3]
def baseStart_2416249 : Nat := 118140960795 + 2416249 * 2 ^ 59
def prefixEnd_2416249 : Nat := 4983230072969 + 3 ^ 40 * 2416249 * 2
def baseEnd_2416249 : Nat := 1240697117945622148375379

theorem tailTrace_2416249 : CollatzResearch.WordTrace tailWord_2416249 prefixEnd_2416249 1240697117945622148375379 := by
  unfold tailWord_2416249
  simp only [CollatzResearch.WordTrace]
  refine ⟨88127841023350010320571801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58751894015566673547047867 88127841023350010320571801)
  ·
    refine ⟨66095880767512507740428851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88127841023350010320571801 66095880767512507740428851)
    ·
      refine ⟨99143821151268761610643277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66095880767512507740428851 99143821151268761610643277)
      ·
        refine ⟨37178932931725785603991229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99143821151268761610643277 37178932931725785603991229)
        ·
          refine ⟨13942099849397169601496711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37178932931725785603991229 13942099849397169601496711)
          ·
            refine ⟨20913149774095754402245067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13942099849397169601496711 20913149774095754402245067)
            ·
              refine ⟨31369724661143631603367601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20913149774095754402245067 31369724661143631603367601)
              ·
                refine ⟨23527293495857723702525701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31369724661143631603367601 23527293495857723702525701)
                ·
                  refine ⟨4411367530473323194223569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23527293495857723702525701 4411367530473323194223569)
                  ·
                    refine ⟨3308525647854992395667677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4411367530473323194223569 3308525647854992395667677)
                    ·
                      refine ⟨1240697117945622148375379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3308525647854992395667677 1240697117945622148375379)
                      ·
                        rfl

theorem cell23_2416249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_2416249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416249 prefixEnd_2416249 := by exact prefixLift 2416249
  have htrace : WordTrace (prefixWord ++ tailWord_2416249) baseStart_2416249 baseEnd_2416249 := by
    simpa [prefixWord, tailWord_2416249, baseEnd_2416249] using wordTrace_append hprefix tailTrace_2416249
  have hstable : (prefixWord ++ tailWord_2416249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416249).length < 2 ^ (prefixWord ++ tailWord_2416249).sum := by decide
  have hdescent : baseEnd_2416249 < baseStart_2416249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416266 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2416266 : Nat := 118140960795 + 2416266 * 2 ^ 59
def prefixEnd_2416266 : Nat := 4983230072969 + 3 ^ 40 * 2416266 * 2
def baseEnd_2416266 : Nat := 1240705847116748581862801

theorem tailTrace_2416266 : CollatzResearch.WordTrace tailWord_2416266 prefixEnd_2416266 1240705847116748581862801 := by
  unfold tailWord_2416266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22032115266072105555985163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58752307376192281482627101 22032115266072105555985163)
  ·
    refine ⟨33048172899108158333977745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22032115266072105555985163 33048172899108158333977745)
    ·
      refine ⟨24786129674331118750483309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33048172899108158333977745 24786129674331118750483309)
      ·
        refine ⟨9294798627874169531431241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24786129674331118750483309 9294798627874169531431241)
        ·
          refine ⟨6971098970905627148573431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9294798627874169531431241 6971098970905627148573431)
          ·
            refine ⟨10456648456358440722860147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6971098970905627148573431 10456648456358440722860147)
            ·
              refine ⟨15684972684537661084290221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10456648456358440722860147 15684972684537661084290221)
              ·
                refine ⟨5881864756701622906608833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15684972684537661084290221 5881864756701622906608833)
                ·
                  refine ⟨4411398567526217179956625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5881864756701622906608833 4411398567526217179956625)
                  ·
                    refine ⟨3308548925644662884967469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4411398567526217179956625 3308548925644662884967469)
                    ·
                      refine ⟨1240705847116748581862801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3308548925644662884967469 1240705847116748581862801)
                      ·
                        rfl

theorem cell23_2416266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2416266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416266 prefixEnd_2416266 := by exact prefixLift 2416266
  have htrace : WordTrace (prefixWord ++ tailWord_2416266) baseStart_2416266 baseEnd_2416266 := by
    simpa [prefixWord, tailWord_2416266, baseEnd_2416266] using wordTrace_append hprefix tailTrace_2416266
  have hstable : (prefixWord ++ tailWord_2416266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416266).length < 2 ^ (prefixWord ++ tailWord_2416266).sum := by decide
  have hdescent : baseEnd_2416266 < baseStart_2416266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416286 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_2416286 : Nat := 118140960795 + 2416286 * 2 ^ 59
def prefixEnd_2416286 : Nat := 4983230072969 + 3 ^ 40 * 2416286 * 2
def baseEnd_2416286 : Nat := 137857346303315389290301

theorem tailTrace_2416286 : CollatzResearch.WordTrace tailWord_2416286 prefixEnd_2416286 137857346303315389290301 := by
  unfold tailWord_2416286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11016148815526995704958589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58752793682810643759779141 11016148815526995704958589)
  ·
    refine ⟨4131055805822623389359471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11016148815526995704958589 4131055805822623389359471)
    ·
      refine ⟨6196583708733935084039207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4131055805822623389359471 6196583708733935084039207)
      ·
        refine ⟨9294875563100902626058811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6196583708733935084039207 9294875563100902626058811)
        ·
          refine ⟨13942313344651353939088217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9294875563100902626058811 13942313344651353939088217)
          ·
            refine ⟨10456735008488515454316163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13942313344651353939088217 10456735008488515454316163)
            ·
              refine ⟨15685102512732773181474245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10456735008488515454316163 15685102512732773181474245)
              ·
                refine ⟨2940956721137394971526421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15685102512732773181474245 2940956721137394971526421)
                ·
                  refine ⟨137857346303315389290301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2940956721137394971526421 137857346303315389290301)
                  ·
                    rfl

theorem cell23_2416286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_2416286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416286 prefixEnd_2416286 := by exact prefixLift 2416286
  have htrace : WordTrace (prefixWord ++ tailWord_2416286) baseStart_2416286 baseEnd_2416286 := by
    simpa [prefixWord, tailWord_2416286, baseEnd_2416286] using wordTrace_append hprefix tailTrace_2416286
  have hstable : (prefixWord ++ tailWord_2416286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416286).length < 2 ^ (prefixWord ++ tailWord_2416286).sum := by decide
  have hdescent : baseEnd_2416286 < baseStart_2416286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416306 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_2416306 : Nat := 118140960795 + 2416306 * 2 ^ 59
def prefixEnd_2416306 : Nat := 4983230072969 + 3 ^ 40 * 2416306 * 2
def baseEnd_2416306 : Nat := 1240726386342928425362617

theorem tailTrace_2416306 : CollatzResearch.WordTrace tailWord_2416306 prefixEnd_2416306 1240726386342928425362617 := by
  unfold tailWord_2416306
  simp only [CollatzResearch.WordTrace]
  refine ⟨22032479996035877263849193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58753279989429006036931181 22032479996035877263849193)
  ·
    refine ⟨16524359997026907947886895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22032479996035877263849193 16524359997026907947886895)
    ·
      refine ⟨24786539995540361921830343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16524359997026907947886895 24786539995540361921830343)
      ·
        refine ⟨37179809993310542882745515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24786539995540361921830343 37179809993310542882745515)
        ·
          refine ⟨55769714989965814324118273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37179809993310542882745515 55769714989965814324118273)
          ·
            refine ⟨41827286242474360743088705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55769714989965814324118273 41827286242474360743088705)
            ·
              refine ⟨31370464681855770557316529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41827286242474360743088705 31370464681855770557316529)
              ·
                refine ⟨23527848511391827917987397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31370464681855770557316529 23527848511391827917987397)
                ·
                  refine ⟨4411471595885967734622637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23527848511391827917987397 4411471595885967734622637)
                  ·
                    refine ⟨1654301848457237900483489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4411471595885967734622637 1654301848457237900483489)
                    ·
                      refine ⟨1240726386342928425362617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654301848457237900483489 1240726386342928425362617)
                      ·
                        rfl

theorem cell23_2416306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_2416306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416306 prefixEnd_2416306 := by exact prefixLift 2416306
  have htrace : WordTrace (prefixWord ++ tailWord_2416306) baseStart_2416306 baseEnd_2416306 := by
    simpa [prefixWord, tailWord_2416306, baseEnd_2416306] using wordTrace_append hprefix tailTrace_2416306
  have hstable : (prefixWord ++ tailWord_2416306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416306).length < 2 ^ (prefixWord ++ tailWord_2416306).sum := by decide
  have hdescent : baseEnd_2416306 < baseStart_2416306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416319 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_2416319 : Nat := 118140960795 + 2416319 * 2 ^ 59
def prefixEnd_2416319 : Nat := 4983230072969 + 3 ^ 40 * 2416319 * 2
def baseEnd_2416319 : Nat := 1240733061591436874500057

theorem tailTrace_2416319 : CollatzResearch.WordTrace tailWord_2416319 prefixEnd_2416319 1240733061591436874500057 := by
  unfold tailWord_2416319
  simp only [CollatzResearch.WordTrace]
  refine ⟨88130394133096412275620011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58753596088730941517080007 88130394133096412275620011)
  ·
    refine ⟨132195591199644618413430017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88130394133096412275620011 132195591199644618413430017)
    ·
      refine ⟨99146693399733463810072513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132195591199644618413430017 99146693399733463810072513)
      ·
        refine ⟨74360020049800097857554385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99146693399733463810072513 74360020049800097857554385)
        ·
          refine ⟨55770015037350073393165789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74360020049800097857554385 55770015037350073393165789)
          ·
            refine ⟨20913755639006277522437171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55770015037350073393165789 20913755639006277522437171)
            ·
              refine ⟨31370633458509416283655757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20913755639006277522437171 31370633458509416283655757)
              ·
                refine ⟨11763987546941031106370909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31370633458509416283655757 11763987546941031106370909)
                ·
                  refine ⟨4411495330102886664889091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11763987546941031106370909 4411495330102886664889091)
                  ·
                    refine ⟨6617242995154329997333637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4411495330102886664889091 6617242995154329997333637)
                    ·
                      refine ⟨1240733061591436874500057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6617242995154329997333637 1240733061591436874500057)
                      ·
                        rfl

theorem cell23_2416319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_2416319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416319 prefixEnd_2416319 := by exact prefixLift 2416319
  have htrace : WordTrace (prefixWord ++ tailWord_2416319) baseStart_2416319 baseEnd_2416319 := by
    simpa [prefixWord, tailWord_2416319, baseEnd_2416319] using wordTrace_append hprefix tailTrace_2416319
  have hstable : (prefixWord ++ tailWord_2416319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416319).length < 2 ^ (prefixWord ++ tailWord_2416319).sum := by decide
  have hdescent : baseEnd_2416319 < baseStart_2416319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416346 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_2416346 : Nat := 118140960795 + 2416346 * 2 ^ 59
def prefixEnd_2416346 : Nat := 4983230072969 + 3 ^ 40 * 2416346 * 2
def baseEnd_2416346 : Nat := 413582308523036089620811

theorem tailTrace_2416346 : CollatzResearch.WordTrace tailWord_2416346 prefixEnd_2416346 413582308523036089620811 := by
  unfold tailWord_2416346
  simp only [CollatzResearch.WordTrace]
  refine ⟨22032844725999648971713223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58754252602665730591235261 22032844725999648971713223)
  ·
    refine ⟨33049267088999473457569835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22032844725999648971713223 33049267088999473457569835)
    ·
      refine ⟨49573900633499210186354753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33049267088999473457569835 49573900633499210186354753)
      ·
        refine ⟨37180425475124407639766065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49573900633499210186354753 37180425475124407639766065)
        ·
          refine ⟨27885319106343305729824549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37180425475124407639766065 27885319106343305729824549)
          ·
            refine ⟨5228497332439369824342103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27885319106343305729824549 5228497332439369824342103)
            ·
              refine ⟨7842745998659054736513155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228497332439369824342103 7842745998659054736513155)
              ·
                refine ⟨11764118997988582104769733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7842745998659054736513155 11764118997988582104769733)
                ·
                  refine ⟨2205772312122859144644325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11764118997988582104769733 2205772312122859144644325)
                  ·
                    refine ⟨413582308523036089620811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2205772312122859144644325 413582308523036089620811)
                    ·
                      rfl

theorem cell23_2416346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_2416346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416346 prefixEnd_2416346 := by exact prefixLift 2416346
  have htrace : WordTrace (prefixWord ++ tailWord_2416346) baseStart_2416346 baseEnd_2416346 := by
    simpa [prefixWord, tailWord_2416346, baseEnd_2416346] using wordTrace_append hprefix tailTrace_2416346
  have hstable : (prefixWord ++ tailWord_2416346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416346).length < 2 ^ (prefixWord ++ tailWord_2416346).sum := by decide
  have hdescent : baseEnd_2416346 < baseStart_2416346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416419 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 2, 6]
def baseStart_2416419 : Nat := 118140960795 + 2416419 * 2 ^ 59
def prefixEnd_2416419 : Nat := 4983230072969 + 3 ^ 40 * 2416419 * 2
def baseEnd_2416419 : Nat := 413594803218962161083199

theorem tailTrace_2416419 : CollatzResearch.WordTrace tailWord_2416419 prefixEnd_2416419 413594803218962161083199 := by
  unfold tailWord_2416419
  simp only [CollatzResearch.WordTrace]
  refine ⟨88134041432734129354260311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58756027621822752902840207 88134041432734129354260311)
  ·
    refine ⟨132201062149101194031390467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88134041432734129354260311 132201062149101194031390467)
    ·
      refine ⟨198301593223651791047085701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132201062149101194031390467 198301593223651791047085701)
      ·
        refine ⟨37181548729434710821328569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198301593223651791047085701 37181548729434710821328569)
        ·
          refine ⟨27886161547076033115996427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37181548729434710821328569 27886161547076033115996427)
          ·
            refine ⟨41829242320614049673994641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27886161547076033115996427 41829242320614049673994641)
            ·
              refine ⟨31371931740460537255495981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41829242320614049673994641 31371931740460537255495981)
              ·
                refine ⟨11764474402672701470810993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31371931740460537255495981 11764474402672701470810993)
                ·
                  refine ⟨8823355802004526103108245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11764474402672701470810993 8823355802004526103108245)
                  ·
                    refine ⟨413594803218962161083199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8823355802004526103108245 413594803218962161083199)
                    ·
                      rfl

theorem cell23_2416419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 6].length) (baseStart_2416419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416419 prefixEnd_2416419 := by exact prefixLift 2416419
  have htrace : WordTrace (prefixWord ++ tailWord_2416419) baseStart_2416419 baseEnd_2416419 := by
    simpa [prefixWord, tailWord_2416419, baseEnd_2416419] using wordTrace_append hprefix tailTrace_2416419
  have hstable : (prefixWord ++ tailWord_2416419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416419).length < 2 ^ (prefixWord ++ tailWord_2416419).sum := by decide
  have hdescent : baseEnd_2416419 < baseStart_2416419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416420 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_2416420 : Nat := 118140960795 + 2416420 * 2 ^ 59
def prefixEnd_2416420 : Nat := 4983230072969 + 3 ^ 40 * 2416420 * 2
def baseEnd_2416420 : Nat := 1240784923137540979337093

theorem tailTrace_2416420 : CollatzResearch.WordTrace tailWord_2416420 prefixEnd_2416420 1240784923137540979337093 := by
  unfold tailWord_2416420
  simp only [CollatzResearch.WordTrace]
  refine ⟨44067038952865253262523357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58756051937153671016697809 44067038952865253262523357)
  ·
    refine ⟨16525139607324469973446259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44067038952865253262523357 16525139607324469973446259)
    ·
      refine ⟨24787709410986704960169389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16525139607324469973446259 24787709410986704960169389)
      ·
        refine ⟨9295391029120014360063521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24787709410986704960169389 9295391029120014360063521)
        ·
          refine ⟨6971543271840010770047641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9295391029120014360063521 6971543271840010770047641)
          ·
            refine ⟨5228657453880008077535731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6971543271840010770047641 5228657453880008077535731)
            ·
              refine ⟨7842986180820012116303597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5228657453880008077535731 7842986180820012116303597)
              ·
                refine ⟨2941119817807504543613849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7842986180820012116303597 2941119817807504543613849)
                ·
                  refine ⟨2205839863355628407710387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2941119817807504543613849 2205839863355628407710387)
                  ·
                    refine ⟨3308759795033442611565581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2205839863355628407710387 3308759795033442611565581)
                    ·
                      refine ⟨1240784923137540979337093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3308759795033442611565581 1240784923137540979337093)
                      ·
                        rfl

theorem cell23_2416420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_2416420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416420 prefixEnd_2416420 := by exact prefixLift 2416420
  have htrace : WordTrace (prefixWord ++ tailWord_2416420) baseStart_2416420 baseEnd_2416420 := by
    simpa [prefixWord, tailWord_2416420, baseEnd_2416420] using wordTrace_append hprefix tailTrace_2416420
  have hstable : (prefixWord ++ tailWord_2416420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416420).length < 2 ^ (prefixWord ++ tailWord_2416420).sum := by decide
  have hdescent : baseEnd_2416420 < baseStart_2416420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416439 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_2416439 : Nat := 118140960795 + 2416439 * 2 ^ 59
def prefixEnd_2416439 : Nat := 4983230072969 + 3 ^ 40 * 2416439 * 2
def baseEnd_2416439 : Nat := 1240794679269976404999505

theorem tailTrace_2416439 : CollatzResearch.WordTrace tailWord_2416439 prefixEnd_2416439 1240794679269976404999505 := by
  unfold tailWord_2416439
  simp only [CollatzResearch.WordTrace]
  refine ⟨88134770892661672769988371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58756513928441115179992247 88134770892661672769988371)
  ·
    refine ⟨132202156338992509154982557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88134770892661672769988371 132202156338992509154982557)
    ·
      refine ⟨49575808627122190933118459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132202156338992509154982557 49575808627122190933118459)
      ·
        refine ⟨74363712940683286399677689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49575808627122190933118459 74363712940683286399677689)
        ·
          refine ⟨55772784705512464799758267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74363712940683286399677689 55772784705512464799758267)
          ·
            refine ⟨83659177058268697199637401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55772784705512464799758267 83659177058268697199637401)
            ·
              refine ⟨62744382793701522899728051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83659177058268697199637401 62744382793701522899728051)
              ·
                refine ⟨94116574190552284349592077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62744382793701522899728051 94116574190552284349592077)
                ·
                  refine ⟨35293715321457106631097029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94116574190552284349592077 35293715321457106631097029)
                  ·
                    refine ⟨6617571622773207493330693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35293715321457106631097029 6617571622773207493330693)
                    ·
                      refine ⟨1240794679269976404999505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6617571622773207493330693 1240794679269976404999505)
                      ·
                        rfl

theorem cell23_2416439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_2416439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416439 prefixEnd_2416439 := by exact prefixLift 2416439
  have htrace : WordTrace (prefixWord ++ tailWord_2416439) baseStart_2416439 baseEnd_2416439 := by
    simpa [prefixWord, tailWord_2416439, baseEnd_2416439] using wordTrace_append hprefix tailTrace_2416439
  have hstable : (prefixWord ++ tailWord_2416439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416439).length < 2 ^ (prefixWord ++ tailWord_2416439).sum := by decide
  have hdescent : baseEnd_2416439 < baseStart_2416439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416447 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 1, 3, 2]
def baseStart_2416447 : Nat := 118140960795 + 2416447 * 2 ^ 59
def prefixEnd_2416447 : Nat := 4983230072969 + 3 ^ 40 * 2416447 * 2
def baseEnd_2416447 : Nat := 1240798787115212373699469

theorem tailTrace_2416447 : CollatzResearch.WordTrace tailWord_2416447 prefixEnd_2416447 1240798787115212373699469 := by
  unfold tailWord_2416447
  simp only [CollatzResearch.WordTrace]
  refine ⟨88135062676632690136279595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58756708451088460090853063 88135062676632690136279595)
  ·
    refine ⟨132202594014949035204419393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88135062676632690136279595 132202594014949035204419393)
    ·
      refine ⟨99151945511211776403314545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132202594014949035204419393 99151945511211776403314545)
      ·
        refine ⟨74363959133408832302485909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99151945511211776403314545 74363959133408832302485909)
        ·
          refine ⟨3485810584378539014179027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74363959133408832302485909 3485810584378539014179027)
          ·
            refine ⟨5228715876567808521268541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3485810584378539014179027 5228715876567808521268541)
            ·
              refine ⟨1960768453712928195475703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5228715876567808521268541 1960768453712928195475703)
              ·
                refine ⟨2941152680569392293213555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960768453712928195475703 2941152680569392293213555)
                ·
                  refine ⟨4411729020854088439820333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941152680569392293213555 4411729020854088439820333)
                  ·
                    refine ⟨1654398382820283164932625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4411729020854088439820333 1654398382820283164932625)
                    ·
                      refine ⟨1240798787115212373699469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654398382820283164932625 1240798787115212373699469)
                      ·
                        rfl

theorem cell23_2416447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_2416447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416447 prefixEnd_2416447 := by exact prefixLift 2416447
  have htrace : WordTrace (prefixWord ++ tailWord_2416447) baseStart_2416447 baseEnd_2416447 := by
    simpa [prefixWord, tailWord_2416447, baseEnd_2416447] using wordTrace_append hprefix tailTrace_2416447
  have hstable : (prefixWord ++ tailWord_2416447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416447).length < 2 ^ (prefixWord ++ tailWord_2416447).sum := by decide
  have hdescent : baseEnd_2416447 < baseStart_2416447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416454 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2416454 : Nat := 118140960795 + 2416454 * 2 ^ 59
def prefixEnd_2416454 : Nat := 4983230072969 + 3 ^ 40 * 2416454 * 2
def baseEnd_2416454 : Nat := 1240802381479793846311937

theorem tailTrace_2416454 : CollatzResearch.WordTrace tailWord_2416454 prefixEnd_2416454 1240802381479793846311937 := by
  unfold tailWord_2416454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754228687112729072868263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58756878658404886887856277 2754228687112729072868263)
  ·
    refine ⟨4131343030669093609302395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2754228687112729072868263 4131343030669093609302395)
    ·
      refine ⟨6197014546003640413953593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4131343030669093609302395 6197014546003640413953593)
      ·
        refine ⟨4647760909502730310465195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6197014546003640413953593 4647760909502730310465195)
        ·
          refine ⟨6971641364254095465697793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647760909502730310465195 6971641364254095465697793)
          ·
            refine ⟨5228731023190571599273345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6971641364254095465697793 5228731023190571599273345)
            ·
              refine ⟨3921548267392928699455009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5228731023190571599273345 3921548267392928699455009)
              ·
                refine ⟨2941161200544696524591257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3921548267392928699455009 2941161200544696524591257)
                ·
                  refine ⟨2205870900408522393443443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2941161200544696524591257 2205870900408522393443443)
                  ·
                    refine ⟨3308806350612783590165165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2205870900408522393443443 3308806350612783590165165)
                    ·
                      refine ⟨1240802381479793846311937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3308806350612783590165165 1240802381479793846311937)
                      ·
                        rfl

theorem cell23_2416454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2416454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416454 prefixEnd_2416454 := by exact prefixLift 2416454
  have htrace : WordTrace (prefixWord ++ tailWord_2416454) baseStart_2416454 baseEnd_2416454 := by
    simpa [prefixWord, tailWord_2416454, baseEnd_2416454] using wordTrace_append hprefix tailTrace_2416454
  have hstable : (prefixWord ++ tailWord_2416454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416454).length < 2 ^ (prefixWord ++ tailWord_2416454).sum := by decide
  have hdescent : baseEnd_2416454 < baseStart_2416454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416489 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_2416489 : Nat := 118140960795 + 2416489 * 2 ^ 59
def prefixEnd_2416489 : Nat := 4983230072969 + 3 ^ 40 * 2416489 * 2
def baseEnd_2416489 : Nat := 1240820353302701209374275

theorem tailTrace_2416489 : CollatzResearch.WordTrace tailWord_2416489 prefixEnd_2416489 1240820353302701209374275 := by
  unfold tailWord_2416489
  simp only [CollatzResearch.WordTrace]
  refine ⟨88136594542480531309308521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58757729694987020872872347 88136594542480531309308521)
  ·
    refine ⟨66102445906860398481981391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88136594542480531309308521 66102445906860398481981391)
    ·
      refine ⟨99153668860290597722972087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66102445906860398481981391 99153668860290597722972087)
      ·
        refine ⟨148730503290435896584458131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99153668860290597722972087 148730503290435896584458131)
        ·
          refine ⟨223095754935653844876687197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148730503290435896584458131 223095754935653844876687197)
          ·
            refine ⟨83660908100870191828757699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223095754935653844876687197 83660908100870191828757699)
            ·
              refine ⟨125491362151305287743136549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83660908100870191828757699 125491362151305287743136549)
              ·
                refine ⟨23529630403369741451838103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125491362151305287743136549 23529630403369741451838103)
                ·
                  refine ⟨35294445605054612177757155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23529630403369741451838103 35294445605054612177757155)
                  ·
                    refine ⟨52941668407581918266635733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35294445605054612177757155 52941668407581918266635733)
                    ·
                      refine ⟨1240820353302701209374275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52941668407581918266635733 1240820353302701209374275)
                      ·
                        rfl

theorem cell23_2416489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_2416489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416489 prefixEnd_2416489 := by exact prefixLift 2416489
  have htrace : WordTrace (prefixWord ++ tailWord_2416489) baseStart_2416489 baseEnd_2416489 := by
    simpa [prefixWord, tailWord_2416489, baseEnd_2416489] using wordTrace_append hprefix tailTrace_2416489
  have hstable : (prefixWord ++ tailWord_2416489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416489).length < 2 ^ (prefixWord ++ tailWord_2416489).sum := by decide
  have hdescent : baseEnd_2416489 < baseStart_2416489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416510 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2416510 : Nat := 118140960795 + 2416510 * 2 ^ 59
def prefixEnd_2416510 : Nat := 4983230072969 + 3 ^ 40 * 2416510 * 2
def baseEnd_2416510 : Nat := 1240831136396445627211679

theorem tailTrace_2416510 : CollatzResearch.WordTrace tailWord_2416510 prefixEnd_2416510 1240831136396445627211679 := by
  unfold tailWord_2416510
  simp only [CollatzResearch.WordTrace]
  refine ⟨11017170059425556486977873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58758240316936301263881989 11017170059425556486977873)
  ·
    refine ⟨8262877544569167365233405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11017170059425556486977873 8262877544569167365233405)
    ·
      refine ⟨3098579079213437761962527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8262877544569167365233405 3098579079213437761962527)
      ·
        refine ⟨4647868618820156642943791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098579079213437761962527 4647868618820156642943791)
        ·
          refine ⟨6971802928230234964415687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647868618820156642943791 6971802928230234964415687)
          ·
            refine ⟨10457704392345352446623531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6971802928230234964415687 10457704392345352446623531)
            ·
              refine ⟨15686556588518028669935297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10457704392345352446623531 15686556588518028669935297)
              ·
                refine ⟨11764917441388521502451473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15686556588518028669935297 11764917441388521502451473)
                ·
                  refine ⟨8823688081041391126838605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11764917441388521502451473 8823688081041391126838605)
                  ·
                    refine ⟨3308883030390521672564477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8823688081041391126838605 3308883030390521672564477)
                    ·
                      refine ⟨1240831136396445627211679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3308883030390521672564477 1240831136396445627211679)
                      ·
                        rfl

theorem cell23_2416510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2416510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416510 prefixEnd_2416510 := by exact prefixLift 2416510
  have htrace : WordTrace (prefixWord ++ tailWord_2416510) baseStart_2416510 baseEnd_2416510 := by
    simpa [prefixWord, tailWord_2416510, baseEnd_2416510] using wordTrace_append hprefix tailTrace_2416510
  have hstable : (prefixWord ++ tailWord_2416510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416510).length < 2 ^ (prefixWord ++ tailWord_2416510).sum := by decide
  have hdescent : baseEnd_2416510 < baseStart_2416510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416533 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_2416533 : Nat := 118140960795 + 2416533 * 2 ^ 59
def prefixEnd_2416533 : Nat := 4983230072969 + 3 ^ 40 * 2416533 * 2
def baseEnd_2416533 : Nat := 1240842946451499037224073

theorem tailTrace_2416533 : CollatzResearch.WordTrace tailWord_2416533 prefixEnd_2416533 1240842946451499037224073 := by
  unfold tailWord_2416533
  simp only [CollatzResearch.WordTrace]
  refine ⟨88138199354321126823910253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58758799569547417882606835 88138199354321126823910253)
  ·
    refine ⟨33051824757870422558966345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88138199354321126823910253 33051824757870422558966345)
    ·
      refine ⟨24788868568402816919224759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33051824757870422558966345 24788868568402816919224759)
      ·
        refine ⟨37183302852604225378837139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24788868568402816919224759 37183302852604225378837139)
        ·
          refine ⟨55774954278906338068255709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37183302852604225378837139 55774954278906338068255709)
          ·
            refine ⟨20915607854589876775595891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55774954278906338068255709 20915607854589876775595891)
            ·
              refine ⟨31373411781884815163393837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20915607854589876775595891 31373411781884815163393837)
              ·
                refine ⟨11765029418206805686272689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31373411781884815163393837 11765029418206805686272689)
                ·
                  refine ⟨8823772063655104264704517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11765029418206805686272689 8823772063655104264704517)
                  ·
                    refine ⟨1654457261935332049632097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8823772063655104264704517 1654457261935332049632097)
                    ·
                      refine ⟨1240842946451499037224073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654457261935332049632097 1240842946451499037224073)
                      ·
                        rfl

theorem cell23_2416533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_2416533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416533 prefixEnd_2416533 := by exact prefixLift 2416533
  have htrace : WordTrace (prefixWord ++ tailWord_2416533) baseStart_2416533 baseEnd_2416533 := by
    simpa [prefixWord, tailWord_2416533, baseEnd_2416533] using wordTrace_append hprefix tailTrace_2416533
  have hstable : (prefixWord ++ tailWord_2416533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416533).length < 2 ^ (prefixWord ++ tailWord_2416533).sum := by decide
  have hdescent : baseEnd_2416533 < baseStart_2416533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416593 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 1, 5, 2]
def baseStart_2416593 : Nat := 118140960795 + 2416593 * 2 ^ 59
def prefixEnd_2416593 : Nat := 4983230072969 + 3 ^ 40 * 2416593 * 2
def baseEnd_2416593 : Nat := 1240873755290768802473797

theorem tailTrace_2416593 : CollatzResearch.WordTrace tailWord_2416593 prefixEnd_2416593 1240873755290768802473797 := by
  unfold tailWord_2416593
  simp only [CollatzResearch.WordTrace]
  refine ⟨88140387734103757071094433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58760258489402504714062955 88140387734103757071094433)
  ·
    refine ⟨66105290800577817803320825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88140387734103757071094433 66105290800577817803320825)
    ·
      refine ⟨49578968100433363352490619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66105290800577817803320825 49578968100433363352490619)
      ·
        refine ⟨74368452150650045028735929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49578968100433363352490619 74368452150650045028735929)
        ·
          refine ⟨55776339112987533771551947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74368452150650045028735929 55776339112987533771551947)
          ·
            refine ⟨83664508669481300657327921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55776339112987533771551947 83664508669481300657327921)
            ·
              refine ⟨62748381502110975492995941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83664508669481300657327921 62748381502110975492995941)
              ·
                refine ⟨11765321531645807904936739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62748381502110975492995941 11765321531645807904936739)
                ·
                  refine ⟨17647982297468711857405109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11765321531645807904936739 17647982297468711857405109)
                  ·
                    refine ⟨1654498340387691736631729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17647982297468711857405109 1654498340387691736631729)
                    ·
                      refine ⟨1240873755290768802473797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654498340387691736631729 1240873755290768802473797)
                      ·
                        rfl

theorem cell23_2416593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_2416593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416593 prefixEnd_2416593 := by exact prefixLift 2416593
  have htrace : WordTrace (prefixWord ++ tailWord_2416593) baseStart_2416593 baseEnd_2416593 := by
    simpa [prefixWord, tailWord_2416593, baseEnd_2416593] using wordTrace_append hprefix tailTrace_2416593
  have hstable : (prefixWord ++ tailWord_2416593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416593).length < 2 ^ (prefixWord ++ tailWord_2416593).sum := by decide
  have hdescent : baseEnd_2416593 < baseStart_2416593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416650 : List Nat := [3, 1, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_2416650 : Nat := 118140960795 + 2416650 * 2 ^ 59
def prefixEnd_2416650 : Nat := 4983230072969 + 3 ^ 40 * 2416650 * 2
def baseEnd_2416650 : Nat := 413634341229358359820345

theorem tailTrace_2416650 : CollatzResearch.WordTrace tailWord_2416650 prefixEnd_2416650 413634341229358359820345 := by
  unfold tailWord_2416650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22035616673724313951479851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58761644463264837203946269 22035616673724313951479851)
  ·
    refine ⟨33053425010586470927219777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22035616673724313951479851 33053425010586470927219777)
    ·
      refine ⟨24790068757939853195414833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33053425010586470927219777 24790068757939853195414833)
      ·
        refine ⟨18592551568454889896561125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24790068757939853195414833 18592551568454889896561125)
        ·
          refine ⟨3486103419085291855605211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18592551568454889896561125 3486103419085291855605211)
          ·
            refine ⟨5229155128627937783407817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486103419085291855605211 5229155128627937783407817)
            ·
              refine ⟨3921866346470953337555863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5229155128627937783407817 3921866346470953337555863)
              ·
                refine ⟨5882799519706430006333795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3921866346470953337555863 5882799519706430006333795)
                ·
                  refine ⟨8824199279559645009500693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5882799519706430006333795 8824199279559645009500693)
                  ·
                    refine ⟨413634341229358359820345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8824199279559645009500693 413634341229358359820345)
                    ·
                      rfl

theorem cell23_2416650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_2416650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416650 prefixEnd_2416650 := by exact prefixLift 2416650
  have htrace : WordTrace (prefixWord ++ tailWord_2416650) baseStart_2416650 baseEnd_2416650 := by
    simpa [prefixWord, tailWord_2416650, baseEnd_2416650] using wordTrace_append hprefix tailTrace_2416650
  have hstable : (prefixWord ++ tailWord_2416650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416650).length < 2 ^ (prefixWord ++ tailWord_2416650).sum := by decide
  have hdescent : baseEnd_2416650 < baseStart_2416650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416677 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 1, 2, 3]
def baseStart_2416677 : Nat := 118140960795 + 2416677 * 2 ^ 59
def prefixEnd_2416677 : Nat := 4983230072969 + 3 ^ 40 * 2416677 * 2
def baseEnd_2416677 : Nat := 1240916887665746473823411

theorem tailTrace_2416677 : CollatzResearch.WordTrace tailWord_2416677 prefixEnd_2416677 1240916887665746473823411 := by
  unfold tailWord_2416677
  simp only [CollatzResearch.WordTrace]
  refine ⟨88143451465799439417152285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58762300977199626278101523 88143451465799439417152285)
  ·
    refine ⟨33053794299674789781432107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88143451465799439417152285 33053794299674789781432107)
    ·
      refine ⟨49580691449512184672148161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33053794299674789781432107 49580691449512184672148161)
      ·
        refine ⟨37185518587134138504111121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49580691449512184672148161 37185518587134138504111121)
        ·
          refine ⟨27889138940350603878083341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37185518587134138504111121 27889138940350603878083341)
          ·
            refine ⟨10458427102631476454281253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27889138940350603878083341 10458427102631476454281253)
            ·
              refine ⟨1960955081743401835177735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10458427102631476454281253 1960955081743401835177735)
              ·
                refine ⟨2941432622615102752766603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960955081743401835177735 2941432622615102752766603)
                ·
                  refine ⟨4412148933922654129149905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941432622615102752766603 4412148933922654129149905)
                  ·
                    refine ⟨3309111700441990596862429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412148933922654129149905 3309111700441990596862429)
                    ·
                      refine ⟨1240916887665746473823411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3309111700441990596862429 1240916887665746473823411)
                      ·
                        rfl

theorem cell23_2416677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_2416677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416677 prefixEnd_2416677 := by exact prefixLift 2416677
  have htrace : WordTrace (prefixWord ++ tailWord_2416677) baseStart_2416677 baseEnd_2416677 := by
    simpa [prefixWord, tailWord_2416677, baseEnd_2416677] using wordTrace_append hprefix tailTrace_2416677
  have hstable : (prefixWord ++ tailWord_2416677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416677).length < 2 ^ (prefixWord ++ tailWord_2416677).sum := by decide
  have hdescent : baseEnd_2416677 < baseStart_2416677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416680 : List Nat := [2, 1, 5, 3, 1, 1, 10]
def baseStart_2416680 : Nat := 118140960795 + 2416680 * 2 ^ 59
def prefixEnd_2416680 : Nat := 4983230072969 + 3 ^ 40 * 2416680 * 2
def baseEnd_2416680 : Nat := 15319980593922345210937

theorem tailTrace_2416680 : CollatzResearch.WordTrace tailWord_2416680 prefixEnd_2416680 15319980593922345210937 := by
  unfold tailWord_2416680
  simp only [CollatzResearch.WordTrace]
  refine ⟨44071780442394285464755747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58762373923192380619674329 44071780442394285464755747)
  ·
    refine ⟨66107670663591428197133621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44071780442394285464755747 66107670663591428197133621)
    ·
      refine ⟨6197594124711696393481277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66107670663591428197133621 6197594124711696393481277)
      ·
        refine ⟨2324097796766886147555479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6197594124711696393481277 2324097796766886147555479)
        ·
          refine ⟨3486146695150329221333219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324097796766886147555479 3486146695150329221333219)
          ·
            refine ⟨5229220042725493831999829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486146695150329221333219 5229220042725493831999829)
            ·
              refine ⟨15319980593922345210937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5229220042725493831999829 15319980593922345210937)
              ·
                rfl

theorem cell23_2416680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 10].length) (baseStart_2416680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416680 prefixEnd_2416680 := by exact prefixLift 2416680
  have htrace : WordTrace (prefixWord ++ tailWord_2416680) baseStart_2416680 baseEnd_2416680 := by
    simpa [prefixWord, tailWord_2416680, baseEnd_2416680] using wordTrace_append hprefix tailTrace_2416680
  have hstable : (prefixWord ++ tailWord_2416680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416680).length < 2 ^ (prefixWord ++ tailWord_2416680).sum := by decide
  have hdescent : baseEnd_2416680 < baseStart_2416680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416730 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2]
def baseStart_2416730 : Nat := 118140960795 + 2416730 * 2 ^ 59
def prefixEnd_2416730 : Nat := 4983230072969 + 3 ^ 40 * 2416730 * 2
def baseEnd_2416730 : Nat := 1240944102140434766460667

theorem tailTrace_2416730 : CollatzResearch.WordTrace tailWord_2416730 prefixEnd_2416730 1240944102140434766460667 := by
  unfold tailWord_2416730
  simp only [CollatzResearch.WordTrace]
  refine ⟨22036346133651857367207911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58763589689738286312554429 22036346133651857367207911)
  ·
    refine ⟨33054519200477786050811867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22036346133651857367207911 33054519200477786050811867)
    ·
      refine ⟨49581778800716679076217801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33054519200477786050811867 49581778800716679076217801)
      ·
        refine ⟨37186334100537509307163351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49581778800716679076217801 37186334100537509307163351)
        ·
          refine ⟨55779501150806263960745027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37186334100537509307163351 55779501150806263960745027)
          ·
            refine ⟨83669251726209395941117541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55779501150806263960745027 83669251726209395941117541)
            ·
              refine ⟨15687984698664261738959539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83669251726209395941117541 15687984698664261738959539)
              ·
                refine ⟨23531977047996392608439309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15687984698664261738959539 23531977047996392608439309)
                ·
                  refine ⟨8824491392998647228164741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23531977047996392608439309 8824491392998647228164741)
                  ·
                    refine ⟨1654592136187246355280889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8824491392998647228164741 1654592136187246355280889)
                    ·
                      refine ⟨1240944102140434766460667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654592136187246355280889 1240944102140434766460667)
                      ·
                        rfl

theorem cell23_2416730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_2416730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416730 prefixEnd_2416730 := by exact prefixLift 2416730
  have htrace : WordTrace (prefixWord ++ tailWord_2416730) baseStart_2416730 baseEnd_2416730 := by
    simpa [prefixWord, tailWord_2416730, baseEnd_2416730] using wordTrace_append hprefix tailTrace_2416730
  have hstable : (prefixWord ++ tailWord_2416730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416730).length < 2 ^ (prefixWord ++ tailWord_2416730).sum := by decide
  have hdescent : baseEnd_2416730 < baseStart_2416730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416750 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2416750 : Nat := 118140960795 + 2416750 * 2 ^ 59
def prefixEnd_2416750 : Nat := 4983230072969 + 3 ^ 40 * 2416750 * 2
def baseEnd_2416750 : Nat := 1240954371753524688210575

theorem tailTrace_2416750 : CollatzResearch.WordTrace tailWord_2416750 prefixEnd_2416750 1240954371753524688210575 := by
  unfold tailWord_2416750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11018264249316871610569963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58764075996356648589706469 11018264249316871610569963)
  ·
    refine ⟨16527396373975307415854945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11018264249316871610569963 16527396373975307415854945)
    ·
      refine ⟨12395547280481480561891209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16527396373975307415854945 12395547280481480561891209)
      ·
        refine ⟨9296660460361110421418407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12395547280481480561891209 9296660460361110421418407)
        ·
          refine ⟨13944990690541665632127611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9296660460361110421418407 13944990690541665632127611)
          ·
            refine ⟨20917486035812498448191417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13944990690541665632127611 20917486035812498448191417)
            ·
              refine ⟨15688114526859373836143563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20917486035812498448191417 15688114526859373836143563)
              ·
                refine ⟨23532171790289060754215345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15688114526859373836143563 23532171790289060754215345)
                ·
                  refine ⟨17649128842716795565661509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23532171790289060754215345 17649128842716795565661509)
                  ·
                    refine ⟨3309211658009399168561533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17649128842716795565661509 3309211658009399168561533)
                    ·
                      refine ⟨1240954371753524688210575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3309211658009399168561533 1240954371753524688210575)
                      ·
                        rfl

theorem cell23_2416750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2416750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416750 prefixEnd_2416750 := by exact prefixLift 2416750
  have htrace : WordTrace (prefixWord ++ tailWord_2416750) baseStart_2416750 baseEnd_2416750 := by
    simpa [prefixWord, tailWord_2416750, baseEnd_2416750] using wordTrace_append hprefix tailTrace_2416750
  have hstable : (prefixWord ++ tailWord_2416750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416750).length < 2 ^ (prefixWord ++ tailWord_2416750).sum := by decide
  have hdescent : baseEnd_2416750 < baseStart_2416750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416764 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_2416764 : Nat := 118140960795 + 2416764 * 2 ^ 59
def prefixEnd_2416764 : Nat := 4983230072969 + 3 ^ 40 * 2416764 * 2
def baseEnd_2416764 : Nat := 1240961560482687633435511

theorem tailTrace_2416764 : CollatzResearch.WordTrace tailWord_2416764 prefixEnd_2416764 1240961560482687633435511 := by
  unfold tailWord_2416764
  simp only [CollatzResearch.WordTrace]
  refine ⟨44073312308242126637784673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58764416410989502183712897 44073312308242126637784673)
  ·
    refine ⟨33054984231181594978338505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44073312308242126637784673 33054984231181594978338505)
    ·
      refine ⟨24791238173386196233753879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33054984231181594978338505 24791238173386196233753879)
      ·
        refine ⟨37186857260079294350630819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24791238173386196233753879 37186857260079294350630819)
        ·
          refine ⟨55780285890118941525946229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37186857260079294350630819 55780285890118941525946229)
          ·
            refine ⟨5229401802198650768057459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55780285890118941525946229 5229401802198650768057459)
            ·
              refine ⟨7844102703297976152086189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229401802198650768057459 7844102703297976152086189)
              ·
                refine ⟨2941538513736741057032321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7844102703297976152086189 2941538513736741057032321)
                ·
                  refine ⟨2206153885302555792774241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2941538513736741057032321 2206153885302555792774241)
                  ·
                    refine ⟨1654615413976916844580681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2206153885302555792774241 1654615413976916844580681)
                    ·
                      refine ⟨1240961560482687633435511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654615413976916844580681 1240961560482687633435511)
                      ·
                        rfl

theorem cell23_2416764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_2416764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416764 prefixEnd_2416764 := by exact prefixLift 2416764
  have htrace : WordTrace (prefixWord ++ tailWord_2416764) baseStart_2416764 baseEnd_2416764 := by
    simpa [prefixWord, tailWord_2416764, baseEnd_2416764] using wordTrace_append hprefix tailTrace_2416764
  have hstable : (prefixWord ++ tailWord_2416764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416764).length < 2 ^ (prefixWord ++ tailWord_2416764).sum := by decide
  have hdescent : baseEnd_2416764 < baseStart_2416764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416798 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_2416798 : Nat := 118140960795 + 2416798 * 2 ^ 59
def prefixEnd_2416798 : Nat := 4983230072969 + 3 ^ 40 * 2416798 * 2
def baseEnd_2416798 : Nat := 1240979018824940500410355

theorem tailTrace_2416798 : CollatzResearch.WordTrace tailWord_2416798 prefixEnd_2416798 1240979018824940500410355 := by
  unfold tailWord_2416798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11018483087295134635288381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58765243132240718054871365 11018483087295134635288381)
  ·
    refine ⟨4131931157735675488233143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11018483087295134635288381 4131931157735675488233143)
    ·
      refine ⟨6197896736603513232349715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4131931157735675488233143 6197896736603513232349715)
      ·
        refine ⟨9296845104905269848524573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6197896736603513232349715 9296845104905269848524573)
        ·
          refine ⟨3486316914339476193196715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9296845104905269848524573 3486316914339476193196715)
          ·
            refine ⟨5229475371509214289795073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3486316914339476193196715 5229475371509214289795073)
            ·
              refine ⟨3922106528631910717346305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5229475371509214289795073 3922106528631910717346305)
              ·
                refine ⟨2941579896473933038009729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3922106528631910717346305 2941579896473933038009729)
                ·
                  refine ⟨2206184922355449778507297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2941579896473933038009729 2206184922355449778507297)
                  ·
                    refine ⟨1654638691766587333880473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2206184922355449778507297 1654638691766587333880473)
                    ·
                      refine ⟨1240979018824940500410355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654638691766587333880473 1240979018824940500410355)
                      ·
                        rfl

theorem cell23_2416798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_2416798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416798 prefixEnd_2416798 := by exact prefixLift 2416798
  have htrace : WordTrace (prefixWord ++ tailWord_2416798) baseStart_2416798 baseEnd_2416798 := by
    simpa [prefixWord, tailWord_2416798, baseEnd_2416798] using wordTrace_append hprefix tailTrace_2416798
  have hstable : (prefixWord ++ tailWord_2416798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416798).length < 2 ^ (prefixWord ++ tailWord_2416798).sum := by decide
  have hdescent : baseEnd_2416798 < baseStart_2416798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416800 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 2, 5]
def baseStart_2416800 : Nat := 118140960795 + 2416800 * 2 ^ 59
def prefixEnd_2416800 : Nat := 4983230072969 + 3 ^ 40 * 2416800 * 2
def baseEnd_2416800 : Nat := 413660015262083164195115

theorem tailTrace_2416800 : CollatzResearch.WordTrace tailWord_2416800 prefixEnd_2416800 413660015262083164195115 := by
  unfold tailWord_2416800
  simp only [CollatzResearch.WordTrace]
  refine ⟨44073968822176915711939927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58765291762902554282586569 44073968822176915711939927)
  ·
    refine ⟨66110953233265373567909891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44073968822176915711939927 66110953233265373567909891)
    ·
      refine ⟨99166429849898060351864837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66110953233265373567909891 99166429849898060351864837)
      ·
        refine ⟨18593705596855886315974657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99166429849898060351864837 18593705596855886315974657)
        ·
          refine ⟨13945279197641914736980993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18593705596855886315974657 13945279197641914736980993)
          ·
            refine ⟨10458959398231436052735745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13945279197641914736980993 10458959398231436052735745)
            ·
              refine ⟨7844219548673577039551809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10458959398231436052735745 7844219548673577039551809)
              ·
                refine ⟨5883164661505182779663857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7844219548673577039551809 5883164661505182779663857)
                ·
                  refine ⟨4412373496128887084747893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5883164661505182779663857 4412373496128887084747893)
                  ·
                    refine ⟨413660015262083164195115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4412373496128887084747893 413660015262083164195115)
                    ·
                      rfl

theorem cell23_2416800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_2416800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416800 prefixEnd_2416800 := by exact prefixLift 2416800
  have htrace : WordTrace (prefixWord ++ tailWord_2416800) baseStart_2416800 baseEnd_2416800 := by
    simpa [prefixWord, tailWord_2416800, baseEnd_2416800] using wordTrace_append hprefix tailTrace_2416800
  have hstable : (prefixWord ++ tailWord_2416800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416800).length < 2 ^ (prefixWord ++ tailWord_2416800).sum := by decide
  have hdescent : baseEnd_2416800 < baseStart_2416800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416803 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 4]
def baseStart_2416803 : Nat := 118140960795 + 2416803 * 2 ^ 59
def prefixEnd_2416803 : Nat := 4983230072969 + 3 ^ 40 * 2416803 * 2
def baseEnd_2416803 : Nat := 1240981586228212980847831

theorem tailTrace_2416803 : CollatzResearch.WordTrace tailWord_2416803 prefixEnd_2416803 1240981586228212980847831 := by
  unfold tailWord_2416803
  simp only [CollatzResearch.WordTrace]
  refine ⟨88148047063342962936239063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58765364708895308624159375 88148047063342962936239063)
  ·
    refine ⟨132222070595014444404358595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88148047063342962936239063 132222070595014444404358595)
    ·
      refine ⟨198333105892521666606537893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132222070595014444404358595 198333105892521666606537893)
      ·
        refine ⟨37187457354847812488725855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198333105892521666606537893 37187457354847812488725855)
        ·
          refine ⟨55781186032271718733088783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37187457354847812488725855 55781186032271718733088783)
          ·
            refine ⟨83671779048407578099633175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55781186032271718733088783 83671779048407578099633175)
            ·
              refine ⟨125507668572611367149449763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83671779048407578099633175 125507668572611367149449763)
              ·
                refine ⟨188261502858917050724174645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125507668572611367149449763 188261502858917050724174645)
                ·
                  refine ⟨17649515893023473505391373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188261502858917050724174645 17649515893023473505391373)
                  ·
                    refine ⟨6618568459883802564521765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17649515893023473505391373 6618568459883802564521765)
                    ·
                      refine ⟨1240981586228212980847831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6618568459883802564521765 1240981586228212980847831)
                      ·
                        rfl

theorem cell23_2416803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_2416803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416803 prefixEnd_2416803 := by exact prefixLift 2416803
  have htrace : WordTrace (prefixWord ++ tailWord_2416803) baseStart_2416803 baseEnd_2416803 := by
    simpa [prefixWord, tailWord_2416803, baseEnd_2416803] using wordTrace_append hprefix tailTrace_2416803
  have hstable : (prefixWord ++ tailWord_2416803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416803).length < 2 ^ (prefixWord ++ tailWord_2416803).sum := by decide
  have hdescent : baseEnd_2416803 < baseStart_2416803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416834 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2416834 : Nat := 118140960795 + 2416834 * 2 ^ 59
def prefixEnd_2416834 : Nat := 4983230072969 + 3 ^ 40 * 2416834 * 2
def baseEnd_2416834 : Nat := 413665834709500786520063

theorem tailTrace_2416834 : CollatzResearch.WordTrace tailWord_2416834 prefixEnd_2416834 413665834709500786520063 := by
  unfold tailWord_2416834
  simp only [CollatzResearch.WordTrace]
  refine ⟨22037294431557663807654389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58766118484153770153745037 22037294431557663807654389)
  ·
    refine ⟨2065996352958530981967599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22037294431557663807654389 2065996352958530981967599)
    ·
      refine ⟨3098994529437796472951399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2065996352958530981967599 3098994529437796472951399)
      ·
        refine ⟨4648491794156694709427099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098994529437796472951399 4648491794156694709427099)
        ·
          refine ⟨6972737691235042064140649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4648491794156694709427099 6972737691235042064140649)
          ·
            refine ⟨5229553268426281548105487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6972737691235042064140649 5229553268426281548105487)
            ·
              refine ⟨7844329902639422322158231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229553268426281548105487 7844329902639422322158231)
              ·
                refine ⟨11766494853959133483237347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7844329902639422322158231 11766494853959133483237347)
                ·
                  refine ⟨17649742280938700224856021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11766494853959133483237347 17649742280938700224856021)
                  ·
                    refine ⟨413665834709500786520063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17649742280938700224856021 413665834709500786520063)
                    ·
                      rfl

theorem cell23_2416834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2416834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416834 prefixEnd_2416834 := by exact prefixLift 2416834
  have htrace : WordTrace (prefixWord ++ tailWord_2416834) baseStart_2416834 baseEnd_2416834 := by
    simpa [prefixWord, tailWord_2416834, baseEnd_2416834] using wordTrace_append hprefix tailTrace_2416834
  have hstable : (prefixWord ++ tailWord_2416834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416834).length < 2 ^ (prefixWord ++ tailWord_2416834).sum := by decide
  have hdescent : baseEnd_2416834 < baseStart_2416834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416843 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 8]
def baseStart_2416843 : Nat := 118140960795 + 2416843 * 2 ^ 59
def prefixEnd_2416843 : Nat := 4983230072969 + 3 ^ 40 * 2416843 * 2
def baseEnd_2416843 : Nat := 137889125050488091594183

theorem tailTrace_2416843 : CollatzResearch.WordTrace tailWord_2416843 prefixEnd_2416843 137889125050488091594183 := by
  unfold tailWord_2416843
  simp only [CollatzResearch.WordTrace]
  refine ⟨88149505983198049767695183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58766337322132033178463455 88149505983198049767695183)
  ·
    refine ⟨132224258974797074651542775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88149505983198049767695183 132224258974797074651542775)
    ·
      refine ⟨198336388462195611977314163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132224258974797074651542775 198336388462195611977314163)
      ·
        refine ⟨297504582693293417965971245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198336388462195611977314163 297504582693293417965971245)
        ·
          refine ⟨111564218509985031737239217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297504582693293417965971245 111564218509985031737239217)
          ·
            refine ⟨83673163882488773802929413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111564218509985031737239217 83673163882488773802929413)
            ·
              refine ⟨15688718227966645088049265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83673163882488773802929413 15688718227966645088049265)
              ·
                refine ⟨11766538670974983816036949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15688718227966645088049265 11766538670974983816036949)
                ·
                  refine ⟨137889125050488091594183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11766538670974983816036949 137889125050488091594183)
                  ·
                    rfl

theorem cell23_2416843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 8].length) (baseStart_2416843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416843 prefixEnd_2416843 := by exact prefixLift 2416843
  have htrace : WordTrace (prefixWord ++ tailWord_2416843) baseStart_2416843 baseEnd_2416843 := by
    simpa [prefixWord, tailWord_2416843, baseEnd_2416843] using wordTrace_append hprefix tailTrace_2416843
  have hstable : (prefixWord ++ tailWord_2416843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416843).length < 2 ^ (prefixWord ++ tailWord_2416843).sum := by decide
  have hdescent : baseEnd_2416843 < baseStart_2416843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416850 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2416850 : Nat := 118140960795 + 2416850 * 2 ^ 59
def prefixEnd_2416850 : Nat := 4983230072969 + 3 ^ 40 * 2416850 * 2
def baseEnd_2416850 : Nat := 1241005719818974296960115

theorem tailTrace_2416850 : CollatzResearch.WordTrace tailWord_2416850 prefixEnd_2416850 1241005719818974296960115 := by
  unfold tailWord_2416850
  simp only [CollatzResearch.WordTrace]
  refine ⟨22037440323543172490800001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58766507529448459975466669 22037440323543172490800001)
  ·
    refine ⟨16528080242657379368100001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22037440323543172490800001 16528080242657379368100001)
    ·
      refine ⟨12396060181993034526075001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16528080242657379368100001 12396060181993034526075001)
      ·
        refine ⟨9297045136494775894556251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12396060181993034526075001 9297045136494775894556251)
        ·
          refine ⟨13945567704742163841834377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9297045136494775894556251 13945567704742163841834377)
          ·
            refine ⟨10459175778556622881375783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13945567704742163841834377 10459175778556622881375783)
            ·
              refine ⟨15688763667834934322063675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10459175778556622881375783 15688763667834934322063675)
              ·
                refine ⟨23533145501752401483095513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15688763667834934322063675 23533145501752401483095513)
                ·
                  refine ⟨17649859126314301112321635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23533145501752401483095513 17649859126314301112321635)
                  ·
                    refine ⟨26474788689471451668482453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17649859126314301112321635 26474788689471451668482453)
                    ·
                      refine ⟨1241005719818974296960115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26474788689471451668482453 1241005719818974296960115)
                      ·
                        rfl

theorem cell23_2416850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2416850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416850 prefixEnd_2416850 := by exact prefixLift 2416850
  have htrace : WordTrace (prefixWord ++ tailWord_2416850) baseStart_2416850 baseEnd_2416850 := by
    simpa [prefixWord, tailWord_2416850, baseEnd_2416850] using wordTrace_append hprefix tailTrace_2416850
  have hstable : (prefixWord ++ tailWord_2416850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416850).length < 2 ^ (prefixWord ++ tailWord_2416850).sum := by decide
  have hdescent : baseEnd_2416850 < baseStart_2416850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416897 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_2416897 : Nat := 118140960795 + 2416897 * 2 ^ 59
def prefixEnd_2416897 : Nat := 4983230072969 + 3 ^ 40 * 2416897 * 2
def baseEnd_2416897 : Nat := 1241029853409735613072399

theorem tailTrace_2416897 : CollatzResearch.WordTrace tailWord_2416897 prefixEnd_2416897 1241029853409735613072399 := by
  unfold tailWord_2416897
  simp only [CollatzResearch.WordTrace]
  refine ⟨88151475525002416990160945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58767650350001611326773963 88151475525002416990160945)
  ·
    refine ⟨66113606643751812742620709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88151475525002416990160945 66113606643751812742620709)
    ·
      refine ⟨12396301245703464889241383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66113606643751812742620709 12396301245703464889241383)
      ·
        refine ⟨18594451868555197333862075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12396301245703464889241383 18594451868555197333862075)
        ·
          refine ⟨27891677802832796000793113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18594451868555197333862075 27891677802832796000793113)
          ·
            refine ⟨20918758352124597000594835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27891677802832796000793113 20918758352124597000594835)
            ·
              refine ⟨31378137528186895500892253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20918758352124597000594835 31378137528186895500892253)
              ·
                refine ⟨11766801573070085812834595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31378137528186895500892253 11766801573070085812834595)
                ·
                  refine ⟨17650202359605128719251893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11766801573070085812834595 17650202359605128719251893)
                  ·
                    refine ⟨1654706471212980817429865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17650202359605128719251893 1654706471212980817429865)
                    ·
                      refine ⟨1241029853409735613072399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654706471212980817429865 1241029853409735613072399)
                      ·
                        rfl

theorem cell23_2416897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_2416897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416897 prefixEnd_2416897 := by exact prefixLift 2416897
  have htrace : WordTrace (prefixWord ++ tailWord_2416897) baseStart_2416897 baseEnd_2416897 := by
    simpa [prefixWord, tailWord_2416897, baseEnd_2416897] using wordTrace_append hprefix tailTrace_2416897
  have hstable : (prefixWord ++ tailWord_2416897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416897).length < 2 ^ (prefixWord ++ tailWord_2416897).sum := by decide
  have hdescent : baseEnd_2416897 < baseStart_2416897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416898 : List Nat := [3, 4, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_2416898 : Nat := 118140960795 + 2416898 * 2 ^ 59
def prefixEnd_2416898 : Nat := 4983230072969 + 3 ^ 40 * 2416898 * 2
def baseEnd_2416898 : Nat := 413676788963463369719965

theorem tailTrace_2416898 : CollatzResearch.WordTrace tailWord_2416898 prefixEnd_2416898 413676788963463369719965 := by
  unfold tailWord_2416898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22037877999499698540236837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58767674665332529440631565 22037877999499698540236837)
  ·
    refine ⟨4132102124906193476294407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22037877999499698540236837 4132102124906193476294407)
    ·
      refine ⟨6198153187359290214441611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4132102124906193476294407 6198153187359290214441611)
      ·
        refine ⟨9297229781038935321662417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198153187359290214441611 9297229781038935321662417)
        ·
          refine ⟨6972922335779201491246813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9297229781038935321662417 6972922335779201491246813)
          ·
            refine ⟨2614845875917200559217555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6972922335779201491246813 2614845875917200559217555)
            ·
              refine ⟨3922268813875800838826333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2614845875917200559217555 3922268813875800838826333)
              ·
                refine ⟨1470850805203425314559875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3922268813875800838826333 1470850805203425314559875)
                ·
                  refine ⟨2206276207805137971839813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1470850805203425314559875 2206276207805137971839813)
                  ·
                    refine ⟨413676788963463369719965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2206276207805137971839813 413676788963463369719965)
                    ·
                      rfl

theorem cell23_2416898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_2416898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416898 prefixEnd_2416898 := by exact prefixLift 2416898
  have htrace : WordTrace (prefixWord ++ tailWord_2416898) baseStart_2416898 baseEnd_2416898 := by
    simpa [prefixWord, tailWord_2416898, baseEnd_2416898] using wordTrace_append hprefix tailTrace_2416898
  have hstable : (prefixWord ++ tailWord_2416898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416898).length < 2 ^ (prefixWord ++ tailWord_2416898).sum := by decide
  have hdescent : baseEnd_2416898 < baseStart_2416898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416940 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_2416940 : Nat := 118140960795 + 2416940 * 2 ^ 59
def prefixEnd_2416940 : Nat := 4983230072969 + 3 ^ 40 * 2416940 * 2
def baseEnd_2416940 : Nat := 1241051933077878944834701

theorem tailTrace_2416940 : CollatzResearch.WordTrace tailWord_2416940 prefixEnd_2416940 1241051933077878944834701 := by
  unfold tailWord_2416940
  simp only [CollatzResearch.WordTrace]
  refine ⟨44076521931923317666988137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58768695909231090222650849 44076521931923317666988137)
  ·
    refine ⟨33057391448942488250241103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44076521931923317666988137 33057391448942488250241103)
    ·
      refine ⟨49586087173413732375361655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33057391448942488250241103 49586087173413732375361655)
      ·
        refine ⟨74379130760120598563042483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49586087173413732375361655 74379130760120598563042483)
        ·
          refine ⟨111568696140180897844563725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74379130760120598563042483 111568696140180897844563725)
          ·
            refine ⟨41838261052567836691711397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111568696140180897844563725 41838261052567836691711397)
            ·
              refine ⟨7844673947356469379695887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41838261052567836691711397 7844673947356469379695887)
              ·
                refine ⟨11767010921034704069543831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7844673947356469379695887 11767010921034704069543831)
                ·
                  refine ⟨17650516381552056104315747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11767010921034704069543831 17650516381552056104315747)
                  ·
                    refine ⟨26475774572328084156473621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17650516381552056104315747 26475774572328084156473621)
                    ·
                      refine ⟨1241051933077878944834701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26475774572328084156473621 1241051933077878944834701)
                      ·
                        rfl

theorem cell23_2416940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_2416940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416940 prefixEnd_2416940 := by exact prefixLift 2416940
  have htrace : WordTrace (prefixWord ++ tailWord_2416940) baseStart_2416940 baseEnd_2416940 := by
    simpa [prefixWord, tailWord_2416940, baseEnd_2416940] using wordTrace_append hprefix tailTrace_2416940
  have hstable : (prefixWord ++ tailWord_2416940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416940).length < 2 ^ (prefixWord ++ tailWord_2416940).sum := by decide
  have hdescent : baseEnd_2416940 < baseStart_2416940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416947 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 3]
def baseStart_2416947 : Nat := 118140960795 + 2416947 * 2 ^ 59
def prefixEnd_2416947 : Nat := 4983230072969 + 3 ^ 40 * 2416947 * 2
def baseEnd_2416947 : Nat := 1241055527442460417447169

theorem tailTrace_2416947 : CollatzResearch.WordTrace tailWord_2416947 prefixEnd_2416947 1241055527442460417447169 := by
  unfold tailWord_2416947
  simp only [CollatzResearch.WordTrace]
  refine ⟨88153299174821275529481095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58768866116547517019654063 88153299174821275529481095)
  ·
    refine ⟨132229948762231913294221643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88153299174821275529481095 132229948762231913294221643)
    ·
      refine ⟨198344923143347869941332465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132229948762231913294221643 198344923143347869941332465)
      ·
        refine ⟨148758692357510902455999349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198344923143347869941332465 148758692357510902455999349)
        ·
          refine ⟨13946127408516647105249939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148758692357510902455999349 13946127408516647105249939)
          ·
            refine ⟨20919191112774970657874909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13946127408516647105249939 20919191112774970657874909)
            ·
              refine ⟨7844696667290613996703091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20919191112774970657874909 7844696667290613996703091)
              ·
                refine ⟨11767045000935920995054637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7844696667290613996703091 11767045000935920995054637)
                ·
                  refine ⟨4412641875350970373145489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11767045000935920995054637 4412641875350970373145489)
                  ·
                    refine ⟨3309481406513227779859117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4412641875350970373145489 3309481406513227779859117)
                    ·
                      refine ⟨1241055527442460417447169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3309481406513227779859117 1241055527442460417447169)
                      ·
                        rfl

theorem cell23_2416947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_2416947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416947 prefixEnd_2416947 := by exact prefixLift 2416947
  have htrace : WordTrace (prefixWord ++ tailWord_2416947) baseStart_2416947 baseEnd_2416947 := by
    simpa [prefixWord, tailWord_2416947, baseEnd_2416947] using wordTrace_append hprefix tailTrace_2416947
  have hstable : (prefixWord ++ tailWord_2416947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416947).length < 2 ^ (prefixWord ++ tailWord_2416947).sum := by decide
  have hdescent : baseEnd_2416947 < baseStart_2416947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2416994 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2416994 : Nat := 118140960795 + 2416994 * 2 ^ 59
def prefixEnd_2416994 : Nat := 4983230072969 + 3 ^ 40 * 2416994 * 2
def baseEnd_2416994 : Nat := 1241079661033221733559453

theorem tailTrace_2416994 : CollatzResearch.WordTrace tailWord_2416994 prefixEnd_2416994 1241079661033221733559453 := by
  unfold tailWord_2416994
  simp only [CollatzResearch.WordTrace]
  refine ⟨22038753351412750639110509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58770008937100668370961357 22038753351412750639110509)
  ·
    refine ⟨8264532506779781489666441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22038753351412750639110509 8264532506779781489666441)
    ·
      refine ⟨6198399380084836117249831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8264532506779781489666441 6198399380084836117249831)
      ·
        refine ⟨9297599070127254175874747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198399380084836117249831 9297599070127254175874747)
        ·
          refine ⟨13946398605190881263812121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9297599070127254175874747 13946398605190881263812121)
          ·
            refine ⟨10459798953893160947859091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13946398605190881263812121 10459798953893160947859091)
            ·
              refine ⟨15689698430839741421788637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10459798953893160947859091 15689698430839741421788637)
              ·
                refine ⟨5883636911564903033170739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15689698430839741421788637 5883636911564903033170739)
                ·
                  refine ⟨8825455367347354549756109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5883636911564903033170739 8825455367347354549756109)
                  ·
                    refine ⟨3309545762755257956158541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8825455367347354549756109 3309545762755257956158541)
                    ·
                      refine ⟨1241079661033221733559453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3309545762755257956158541 1241079661033221733559453)
                      ·
                        rfl

theorem cell23_2416994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2416994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2416994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2416994 prefixEnd_2416994 := by exact prefixLift 2416994
  have htrace : WordTrace (prefixWord ++ tailWord_2416994) baseStart_2416994 baseEnd_2416994 := by
    simpa [prefixWord, tailWord_2416994, baseEnd_2416994] using wordTrace_append hprefix tailTrace_2416994
  have hstable : (prefixWord ++ tailWord_2416994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2416994).length < 2 ^ (prefixWord ++ tailWord_2416994).sum := by decide
  have hdescent : baseEnd_2416994 < baseStart_2416994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2416994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417021 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_2417021 : Nat := 118140960795 + 2417021 * 2 ^ 59
def prefixEnd_2417021 : Nat := 4983230072969 + 3 ^ 40 * 2417021 * 2
def baseEnd_2417021 : Nat := 1241093525010893127921829

theorem tailTrace_2417021 : CollatzResearch.WordTrace tailWord_2417021 prefixEnd_2417021 1241093525010893127921829 := by
  unfold tailWord_2417021
  simp only [CollatzResearch.WordTrace]
  refine ⟨88155998176553186167674917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58770665451035457445116611 88155998176553186167674917)
  ·
    refine ⟨16529249658103722406439047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88155998176553186167674917 16529249658103722406439047)
    ·
      refine ⟨24793874487155583609658571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16529249658103722406439047 24793874487155583609658571)
      ·
        refine ⟨37190811730733375414487857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24793874487155583609658571 37190811730733375414487857)
        ·
          refine ⟨27893108798050031560865893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37190811730733375414487857 27893108798050031560865893)
          ·
            refine ⟨5229957899634380917662355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27893108798050031560865893 5229957899634380917662355)
            ·
              refine ⟨7844936849451571376493533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5229957899634380917662355 7844936849451571376493533)
              ·
                refine ⟨2941851318544339266185075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7844936849451571376493533 2941851318544339266185075)
                ·
                  refine ⟨4412776977816508899277613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2941851318544339266185075 4412776977816508899277613)
                  ·
                    refine ⟨1654791366681190837229105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4412776977816508899277613 1654791366681190837229105)
                    ·
                      refine ⟨1241093525010893127921829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654791366681190837229105 1241093525010893127921829)
                      ·
                        rfl

theorem cell23_2417021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_2417021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417021 prefixEnd_2417021 := by exact prefixLift 2417021
  have htrace : WordTrace (prefixWord ++ tailWord_2417021) baseStart_2417021 baseEnd_2417021 := by
    simpa [prefixWord, tailWord_2417021, baseEnd_2417021] using wordTrace_append hprefix tailTrace_2417021
  have hstable : (prefixWord ++ tailWord_2417021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417021).length < 2 ^ (prefixWord ++ tailWord_2417021).sum := by decide
  have hdescent : baseEnd_2417021 < baseStart_2417021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417047 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2417047 : Nat := 118140960795 + 2417047 * 2 ^ 59
def prefixEnd_2417047 : Nat := 4983230072969 + 3 ^ 40 * 2417047 * 2
def baseEnd_2417047 : Nat := 1241106875507910026196709

theorem tailTrace_2417047 : CollatzResearch.WordTrace tailWord_2417047 prefixEnd_2417047 1241106875507910026196709 := by
  unfold tailWord_2417047
  simp only [CollatzResearch.WordTrace]
  refine ⟨88156946474458992608121395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58771297649639328405414263 88156946474458992608121395)
  ·
    refine ⟨132235419711688488912182093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88156946474458992608121395 132235419711688488912182093)
    ·
      refine ⟨49588282391883183342068285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132235419711688488912182093 49588282391883183342068285)
      ·
        refine ⟨18595605896956193753275607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49588282391883183342068285 18595605896956193753275607)
        ·
          refine ⟨27893408845434290629913411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18595605896956193753275607 27893408845434290629913411)
          ·
            refine ⟨41840113268151435944870117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27893408845434290629913411 41840113268151435944870117)
            ·
              refine ⟨7845021237778394239663147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41840113268151435944870117 7845021237778394239663147)
              ·
                refine ⟨11767531856667591359494721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7845021237778394239663147 11767531856667591359494721)
                ·
                  refine ⟨8825648892500693519621041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11767531856667591359494721 8825648892500693519621041)
                  ·
                    refine ⟨6619236669375520139715781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8825648892500693519621041 6619236669375520139715781)
                    ·
                      refine ⟨1241106875507910026196709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6619236669375520139715781 1241106875507910026196709)
                      ·
                        rfl

theorem cell23_2417047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2417047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417047 prefixEnd_2417047 := by exact prefixLift 2417047
  have htrace : WordTrace (prefixWord ++ tailWord_2417047) baseStart_2417047 baseEnd_2417047 := by
    simpa [prefixWord, tailWord_2417047, baseEnd_2417047] using wordTrace_append hprefix tailTrace_2417047
  have hstable : (prefixWord ++ tailWord_2417047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417047).length < 2 ^ (prefixWord ++ tailWord_2417047).sum := by decide
  have hdescent : baseEnd_2417047 < baseStart_2417047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417124 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_2417124 : Nat := 118140960795 + 2417124 * 2 ^ 59
def prefixEnd_2417124 : Nat := 4983230072969 + 3 ^ 40 * 2417124 * 2
def baseEnd_2417124 : Nat := 1241146413518306224933855

theorem tailTrace_2417124 : CollatzResearch.WordTrace tailWord_2417124 prefixEnd_2417124 1241146413518306224933855 := by
  unfold tailWord_2417124
  simp only [CollatzResearch.WordTrace]
  refine ⟨44079877447590017379337213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58773169930120023172449617 44079877447590017379337213)
  ·
    refine ⟨16529954042846256517251455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44079877447590017379337213 16529954042846256517251455)
    ·
      refine ⟨24794931064269384775877183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16529954042846256517251455 24794931064269384775877183)
      ·
        refine ⟨37192396596404077163815775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24794931064269384775877183 37192396596404077163815775)
        ·
          refine ⟨55788594894606115745723663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37192396596404077163815775 55788594894606115745723663)
          ·
            refine ⟨83682892341909173618585495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55788594894606115745723663 83682892341909173618585495)
            ·
              refine ⟨125524338512863760427878243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83682892341909173618585495 125524338512863760427878243)
              ·
                refine ⟨188286507769295640641817365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125524338512863760427878243 188286507769295640641817365)
                ·
                  refine ⟨8825930051685733155085189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188286507769295640641817365 8825930051685733155085189)
                  ·
                    refine ⟨1654861884691074966578473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8825930051685733155085189 1654861884691074966578473)
                    ·
                      refine ⟨1241146413518306224933855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654861884691074966578473 1241146413518306224933855)
                      ·
                        rfl

theorem cell23_2417124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_2417124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417124 prefixEnd_2417124 := by exact prefixLift 2417124
  have htrace : WordTrace (prefixWord ++ tailWord_2417124) baseStart_2417124 baseEnd_2417124 := by
    simpa [prefixWord, tailWord_2417124, baseEnd_2417124] using wordTrace_append hprefix tailTrace_2417124
  have hstable : (prefixWord ++ tailWord_2417124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417124).length < 2 ^ (prefixWord ++ tailWord_2417124).sum := by decide
  have hdescent : baseEnd_2417124 < baseStart_2417124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417137 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_2417137 : Nat := 118140960795 + 2417137 * 2 ^ 59
def prefixEnd_2417137 : Nat := 4983230072969 + 3 ^ 40 * 2417137 * 2
def baseEnd_2417137 : Nat := 1241153088766814674071295

theorem tailTrace_2417137 : CollatzResearch.WordTrace tailWord_2417137 prefixEnd_2417137 1241153088766814674071295 := by
  unfold tailWord_2417137
  simp only [CollatzResearch.WordTrace]
  refine ⟨88160229044132937978897665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58773486029421958652598443 88160229044132937978897665)
  ·
    refine ⟨66120171783099703484173249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88160229044132937978897665 66120171783099703484173249)
    ·
      refine ⟨49590128837324777613129937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66120171783099703484173249 49590128837324777613129937)
      ·
        refine ⟨37192596627993583209847453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49590128837324777613129937 37192596627993583209847453)
        ·
          refine ⟨13947223735497593703692795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37192596627993583209847453 13947223735497593703692795)
          ·
            refine ⟨20920835603246390555539193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13947223735497593703692795 20920835603246390555539193)
            ·
              refine ⟨15690626702434792916654395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20920835603246390555539193 15690626702434792916654395)
              ·
                refine ⟨23535940053652189374981593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15690626702434792916654395 23535940053652189374981593)
                ·
                  refine ⟨17651955040239142031236195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23535940053652189374981593 17651955040239142031236195)
                  ·
                    refine ⟨26477932560358713046854293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17651955040239142031236195 26477932560358713046854293)
                    ·
                      refine ⟨1241153088766814674071295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26477932560358713046854293 1241153088766814674071295)
                      ·
                        rfl

theorem cell23_2417137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_2417137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417137 prefixEnd_2417137 := by exact prefixLift 2417137
  have htrace : WordTrace (prefixWord ++ tailWord_2417137) baseStart_2417137 baseEnd_2417137 := by
    simpa [prefixWord, tailWord_2417137, baseEnd_2417137] using wordTrace_append hprefix tailTrace_2417137
  have hstable : (prefixWord ++ tailWord_2417137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417137).length < 2 ^ (prefixWord ++ tailWord_2417137).sum := by decide
  have hdescent : baseEnd_2417137 < baseStart_2417137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417144 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_2417144 : Nat := 118140960795 + 2417144 * 2 ^ 59
def prefixEnd_2417144 : Nat := 4983230072969 + 3 ^ 40 * 2417144 * 2
def baseEnd_2417144 : Nat := 1241156683131396146683763

theorem tailTrace_2417144 : CollatzResearch.WordTrace tailWord_2417144 prefixEnd_2417144 1241156683131396146683763 := by
  unfold tailWord_2417144
  simp only [CollatzResearch.WordTrace]
  refine ⟨44080242177553789087201243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58773656236738385449601657 44080242177553789087201243)
  ·
    refine ⟨66120363266330683630801865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44080242177553789087201243 66120363266330683630801865)
    ·
      refine ⟨49590272449748012723101399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66120363266330683630801865 49590272449748012723101399)
      ·
        refine ⟨74385408674622019084652099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49590272449748012723101399 74385408674622019084652099)
        ·
          refine ⟨111578113011933028626978149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74385408674622019084652099 111578113011933028626978149)
          ·
            refine ⟨20920896189737442867558403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111578113011933028626978149 20920896189737442867558403)
            ·
              refine ⟨31381344284606164301337605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20920896189737442867558403 31381344284606164301337605)
              ·
                refine ⟨5884002053363655806500801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31381344284606164301337605 5884002053363655806500801)
                ·
                  refine ⟨4413001540022741854875601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5884002053363655806500801 4413001540022741854875601)
                  ·
                    refine ⟨3309751155017056391156701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4413001540022741854875601 3309751155017056391156701)
                    ·
                      refine ⟨1241156683131396146683763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3309751155017056391156701 1241156683131396146683763)
                      ·
                        rfl

theorem cell23_2417144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_2417144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417144 prefixEnd_2417144 := by exact prefixLift 2417144
  have htrace : WordTrace (prefixWord ++ tailWord_2417144) baseStart_2417144 baseEnd_2417144 := by
    simpa [prefixWord, tailWord_2417144, baseEnd_2417144] using wordTrace_append hprefix tailTrace_2417144
  have hstable : (prefixWord ++ tailWord_2417144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417144).length < 2 ^ (prefixWord ++ tailWord_2417144).sum := by decide
  have hdescent : baseEnd_2417144 < baseStart_2417144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417151 : List Nat := [1, 1, 2, 2, 1, 2, 5, 4, 1, 4]
def baseStart_2417151 : Nat := 118140960795 + 2417151 * 2 ^ 59
def prefixEnd_2417151 : Nat := 4983230072969 + 3 ^ 40 * 2417151 * 2
def baseEnd_2417151 : Nat := 413720092498659206432077

theorem tailTrace_2417151 : CollatzResearch.WordTrace tailWord_2417151 prefixEnd_2417151 413720092498659206432077 := by
  unfold tailWord_2417151
  simp only [CollatzResearch.WordTrace]
  refine ⟨88160739666082218369907307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58773826444054812246604871 88160739666082218369907307)
  ·
    refine ⟨132241109499123327554860961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88160739666082218369907307 132241109499123327554860961)
    ·
      refine ⟨99180832124342495666145721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132241109499123327554860961 99180832124342495666145721)
      ·
        refine ⟨74385624093256871749609291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99180832124342495666145721 74385624093256871749609291)
        ·
          refine ⟨111578436139885307624413937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74385624093256871749609291 111578436139885307624413937)
          ·
            refine ⟨83683827104913980718310453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111578436139885307624413937 83683827104913980718310453)
            ·
              refine ⟨7845358791085685692341605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83683827104913980718310453 7845358791085685692341605)
              ·
                refine ⟨1471004773328566067314051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7845358791085685692341605 1471004773328566067314051)
                ·
                  refine ⟨2206507159992849100971077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471004773328566067314051 2206507159992849100971077)
                  ·
                    refine ⟨413720092498659206432077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2206507159992849100971077 413720092498659206432077)
                    ·
                      rfl

theorem cell23_2417151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 1, 4].length) (baseStart_2417151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417151 prefixEnd_2417151 := by exact prefixLift 2417151
  have htrace : WordTrace (prefixWord ++ tailWord_2417151) baseStart_2417151 baseEnd_2417151 := by
    simpa [prefixWord, tailWord_2417151, baseEnd_2417151] using wordTrace_append hprefix tailTrace_2417151
  have hstable : (prefixWord ++ tailWord_2417151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417151).length < 2 ^ (prefixWord ++ tailWord_2417151).sum := by decide
  have hdescent : baseEnd_2417151 < baseStart_2417151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417164 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 6]
def baseStart_2417164 : Nat := 118140960795 + 2417164 * 2 ^ 59
def prefixEnd_2417164 : Nat := 4983230072969 + 3 ^ 40 * 2417164 * 2
def baseEnd_2417164 : Nat := 137907439193831785381519

theorem tailTrace_2417164 : CollatzResearch.WordTrace tailWord_2417164 prefixEnd_2417164 137907439193831785381519 := by
  unfold tailWord_2417164
  simp only [CollatzResearch.WordTrace]
  refine ⟨44080606907517560795065273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58774142543356747726753697 44080606907517560795065273)
  ·
    refine ⟨33060455180638170596298955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44080606907517560795065273 33060455180638170596298955)
    ·
      refine ⟨49590682770957255894448433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33060455180638170596298955 49590682770957255894448433)
      ·
        refine ⟨37193012078217941920836325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49590682770957255894448433 37193012078217941920836325)
        ·
          refine ⟨6973689764665864110156811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37193012078217941920836325 6973689764665864110156811)
          ·
            refine ⟨10460534646998796165235217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6973689764665864110156811 10460534646998796165235217)
            ·
              refine ⟨7845400985249097123926413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10460534646998796165235217 7845400985249097123926413)
              ·
                refine ⟨2942025369468411421472405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7845400985249097123926413 2942025369468411421472405)
                ·
                  refine ⟨137907439193831785381519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2942025369468411421472405 137907439193831785381519)
                  ·
                    rfl

theorem cell23_2417164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_2417164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417164 prefixEnd_2417164 := by exact prefixLift 2417164
  have htrace : WordTrace (prefixWord ++ tailWord_2417164) baseStart_2417164 baseEnd_2417164 := by
    simpa [prefixWord, tailWord_2417164, baseEnd_2417164] using wordTrace_append hprefix tailTrace_2417164
  have hstable : (prefixWord ++ tailWord_2417164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417164).length < 2 ^ (prefixWord ++ tailWord_2417164).sum := by decide
  have hdescent : baseEnd_2417164 < baseStart_2417164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417175 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2417175 : Nat := 118140960795 + 2417175 * 2 ^ 59
def prefixEnd_2417175 : Nat := 4983230072969 + 3 ^ 40 * 2417175 * 2
def baseEnd_2417175 : Nat := 1241172601031685525396121

theorem tailTrace_2417175 : CollatzResearch.WordTrace tailWord_2417175 prefixEnd_2417175 1241172601031685525396121 := by
  unfold tailWord_2417175
  simp only [CollatzResearch.WordTrace]
  refine ⟨88161615017995270468780979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58774410011996846979187319 88161615017995270468780979)
  ·
    refine ⟨132242422526992905703171469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88161615017995270468780979 132242422526992905703171469)
    ·
      refine ⟨49590908447622339638689301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132242422526992905703171469 49590908447622339638689301)
      ·
        refine ⟨2324573833482297170563561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49590908447622339638689301 2324573833482297170563561)
        ·
          refine ⟨1743430375111722877922671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2324573833482297170563561 1743430375111722877922671)
          ·
            refine ⟨2615145562667584316884007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743430375111722877922671 2615145562667584316884007)
            ·
              refine ⟨3922718344001376475326011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615145562667584316884007 3922718344001376475326011)
              ·
                refine ⟨5884077516002064712989017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3922718344001376475326011 5884077516002064712989017)
                ·
                  refine ⟨4413058137001548534741763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5884077516002064712989017 4413058137001548534741763)
                  ·
                    refine ⟨6619587205502322802112645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4413058137001548534741763 6619587205502322802112645)
                    ·
                      refine ⟨1241172601031685525396121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6619587205502322802112645 1241172601031685525396121)
                      ·
                        rfl

theorem cell23_2417175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2417175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417175 prefixEnd_2417175 := by exact prefixLift 2417175
  have htrace : WordTrace (prefixWord ++ tailWord_2417175) baseStart_2417175 baseEnd_2417175 := by
    simpa [prefixWord, tailWord_2417175, baseEnd_2417175] using wordTrace_append hprefix tailTrace_2417175
  have hstable : (prefixWord ++ tailWord_2417175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417175).length < 2 ^ (prefixWord ++ tailWord_2417175).sum := by decide
  have hdescent : baseEnd_2417175 < baseStart_2417175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417198 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_2417198 : Nat := 118140960795 + 2417198 * 2 ^ 59
def prefixEnd_2417198 : Nat := 4983230072969 + 3 ^ 40 * 2417198 * 2
def baseEnd_2417198 : Nat := 137909379009637659489835

theorem tailTrace_2417198 : CollatzResearch.WordTrace tailWord_2417198 prefixEnd_2417198 137909379009637659489835 := by
  unfold tailWord_2417198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020306737113993174608531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58774969264607963597912165 11020306737113993174608531)
  ·
    refine ⟨16530460105670989761912797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11020306737113993174608531 16530460105670989761912797)
    ·
      refine ⟨6198922539626621160717299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16530460105670989761912797 6198922539626621160717299)
      ·
        refine ⟨9298383809439931741075949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198922539626621160717299 9298383809439931741075949)
        ·
          refine ⟨3486893928539974402903481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9298383809439931741075949 3486893928539974402903481)
          ·
            refine ⟨2615170446404980802177611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3486893928539974402903481 2615170446404980802177611)
            ·
              refine ⟨3922755669607471203266417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615170446404980802177611 3922755669607471203266417)
              ·
                refine ⟨2942066752205603402449813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3922755669607471203266417 2942066752205603402449813)
                ·
                  refine ⟨137909379009637659489835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2942066752205603402449813 137909379009637659489835)
                  ·
                    rfl

theorem cell23_2417198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_2417198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417198 prefixEnd_2417198 := by exact prefixLift 2417198
  have htrace : WordTrace (prefixWord ++ tailWord_2417198) baseStart_2417198 baseEnd_2417198 := by
    simpa [prefixWord, tailWord_2417198, baseEnd_2417198] using wordTrace_append hprefix tailTrace_2417198
  have hstable : (prefixWord ++ tailWord_2417198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417198).length < 2 ^ (prefixWord ++ tailWord_2417198).sum := by decide
  have hdescent : baseEnd_2417198 < baseStart_2417198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417201 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 2, 3, 2]
def baseStart_2417201 : Nat := 118140960795 + 2417201 * 2 ^ 59
def prefixEnd_2417201 : Nat := 4983230072969 + 3 ^ 40 * 2417201 * 2
def baseEnd_2417201 : Nat := 1241185951528702423671001

theorem tailTrace_2417201 : CollatzResearch.WordTrace tailWord_2417201 prefixEnd_2417201 1241185951528702423671001 := by
  unfold tailWord_2417201
  simp only [CollatzResearch.WordTrace]
  refine ⟨88162563315901076909227457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58775042210600717939484971 88162563315901076909227457)
  ·
    refine ⟨66121922486925807681920593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88162563315901076909227457 66121922486925807681920593)
    ·
      refine ⟨49591441865194355761440445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66121922486925807681920593 49591441865194355761440445)
      ·
        refine ⟨18596790699447883410540167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49591441865194355761440445 18596790699447883410540167)
        ·
          refine ⟨27895186049171825115810251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18596790699447883410540167 27895186049171825115810251)
          ·
            refine ⟨41842779073757737673715377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27895186049171825115810251 41842779073757737673715377)
            ·
              refine ⟨31382084305318303255286533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41842779073757737673715377 31382084305318303255286533)
              ·
                refine ⟨5884140807247181860366225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31382084305318303255286533 5884140807247181860366225)
                ·
                  refine ⟨4413105605435386395274669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5884140807247181860366225 4413105605435386395274669)
                  ·
                    refine ⟨1654914602038269898228001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4413105605435386395274669 1654914602038269898228001)
                    ·
                      refine ⟨1241185951528702423671001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1654914602038269898228001 1241185951528702423671001)
                      ·
                        rfl

theorem cell23_2417201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_2417201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417201 prefixEnd_2417201 := by exact prefixLift 2417201
  have htrace : WordTrace (prefixWord ++ tailWord_2417201) baseStart_2417201 baseEnd_2417201 := by
    simpa [prefixWord, tailWord_2417201, baseEnd_2417201] using wordTrace_append hprefix tailTrace_2417201
  have hstable : (prefixWord ++ tailWord_2417201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417201).length < 2 ^ (prefixWord ++ tailWord_2417201).sum := by decide
  have hdescent : baseEnd_2417201 < baseStart_2417201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417208 : List Nat := [2, 1, 2, 1, 4, 1, 1, 6, 1, 1, 3]
def baseStart_2417208 : Nat := 118140960795 + 2417208 * 2 ^ 59
def prefixEnd_2417208 : Nat := 4983230072969 + 3 ^ 40 * 2417208 * 2
def baseEnd_2417208 : Nat := 1241189545893283896283469

theorem tailTrace_2417208 : CollatzResearch.WordTrace tailWord_2417208 prefixEnd_2417208 1241189545893283896283469 := by
  unfold tailWord_2417208
  simp only [CollatzResearch.WordTrace]
  refine ⟨44081409313437858552366139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58775212417917144736488185 44081409313437858552366139)
  ·
    refine ⟨66122113970156787828549209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44081409313437858552366139 66122113970156787828549209)
    ·
      refine ⟨49591585477617590871411907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66122113970156787828549209 49591585477617590871411907)
      ·
        refine ⟨74387378216426386307117861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49591585477617590871411907 74387378216426386307117861)
        ·
          refine ⟨13947633415579947432584599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74387378216426386307117861 13947633415579947432584599)
          ·
            refine ⟨20921450123369921148876899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13947633415579947432584599 20921450123369921148876899)
            ·
              refine ⟨31382175185054881723315349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20921450123369921148876899 31382175185054881723315349)
              ·
                refine ⟨1471039461799447580780407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31382175185054881723315349 1471039461799447580780407)
                ·
                  refine ⟨2206559192699171371170611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471039461799447580780407 2206559192699171371170611)
                  ·
                    refine ⟨3309838789048757056755917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2206559192699171371170611 3309838789048757056755917)
                    ·
                      refine ⟨1241189545893283896283469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3309838789048757056755917 1241189545893283896283469)
                      ·
                        rfl

theorem cell23_2417208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_2417208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417208 prefixEnd_2417208 := by exact prefixLift 2417208
  have htrace : WordTrace (prefixWord ++ tailWord_2417208) baseStart_2417208 baseEnd_2417208 := by
    simpa [prefixWord, tailWord_2417208, baseEnd_2417208] using wordTrace_append hprefix tailTrace_2417208
  have hstable : (prefixWord ++ tailWord_2417208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417208).length < 2 ^ (prefixWord ++ tailWord_2417208).sum := by decide
  have hdescent : baseEnd_2417208 < baseStart_2417208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417234 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2417234 : Nat := 118140960795 + 2417234 * 2 ^ 59
def prefixEnd_2417234 : Nat := 4983230072969 + 3 ^ 40 * 2417234 * 2
def baseEnd_2417234 : Nat := 1241202896390300794558349

theorem tailTrace_2417234 : CollatzResearch.WordTrace tailWord_2417234 prefixEnd_2417234 1241202896390300794558349 := by
  unfold tailWord_2417234
  simp only [CollatzResearch.WordTrace]
  refine ⟨22040941731195380886294689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58775844616521015696785837 22040941731195380886294689)
  ·
    refine ⟨16530706298396535664721017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22040941731195380886294689 16530706298396535664721017)
    ·
      refine ⟨12398029723797401748540763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16530706298396535664721017 12398029723797401748540763)
      ·
        refine ⟨18597044585696102622811145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12398029723797401748540763 18597044585696102622811145)
        ·
          refine ⟨13947783439272076967108359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18597044585696102622811145 13947783439272076967108359)
          ·
            refine ⟨20921675158908115450662539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13947783439272076967108359 20921675158908115450662539)
            ·
              refine ⟨31382512738362173175993809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20921675158908115450662539 31382512738362173175993809)
              ·
                refine ⟨23536884553771629881995357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31382512738362173175993809 23536884553771629881995357)
                ·
                  refine ⟨8826331707664361205748259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23536884553771629881995357 8826331707664361205748259)
                  ·
                    refine ⟨13239497561496541808622389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8826331707664361205748259 13239497561496541808622389)
                    ·
                      refine ⟨1241202896390300794558349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13239497561496541808622389 1241202896390300794558349)
                      ·
                        rfl

theorem cell23_2417234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2417234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417234 prefixEnd_2417234 := by exact prefixLift 2417234
  have htrace : WordTrace (prefixWord ++ tailWord_2417234) baseStart_2417234 baseEnd_2417234 := by
    simpa [prefixWord, tailWord_2417234, baseEnd_2417234] using wordTrace_append hprefix tailTrace_2417234
  have hstable : (prefixWord ++ tailWord_2417234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417234).length < 2 ^ (prefixWord ++ tailWord_2417234).sum := by decide
  have hdescent : baseEnd_2417234 < baseStart_2417234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417251 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 3]
def baseStart_2417251 : Nat := 118140960795 + 2417251 * 2 ^ 59
def prefixEnd_2417251 : Nat := 4983230072969 + 3 ^ 40 * 2417251 * 2
def baseEnd_2417251 : Nat := 1241211625561427228045771

theorem tailTrace_2417251 : CollatzResearch.WordTrace tailWord_2417251 prefixEnd_2417251 1241211625561427228045771 := by
  unfold tailWord_2417251
  simp only [CollatzResearch.WordTrace]
  refine ⟨88164386965719935448547607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58776257977146623632365071 88164386965719935448547607)
  ·
    refine ⟨132246580448579903172821411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88164386965719935448547607 132246580448579903172821411)
    ·
      refine ⟨198369870672869854759232117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132246580448579903172821411 198369870672869854759232117)
      ·
        refine ⟨18597175375581548883678011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198369870672869854759232117 18597175375581548883678011)
        ·
          refine ⟨27895763063372323325517017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18597175375581548883678011 27895763063372323325517017)
          ·
            refine ⟨20921822297529242494137763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27895763063372323325517017 20921822297529242494137763)
            ·
              refine ⟨31382733446293863741206645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20921822297529242494137763 31382733446293863741206645)
              ·
                refine ⟨2942131260590049725738123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31382733446293863741206645 2942131260590049725738123)
                ·
                  refine ⟨4413196890885074588607185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942131260590049725738123 4413196890885074588607185)
                  ·
                    refine ⟨3309897668163805941455389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4413196890885074588607185 3309897668163805941455389)
                    ·
                      refine ⟨1241211625561427228045771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3309897668163805941455389 1241211625561427228045771)
                      ·
                        rfl

theorem cell23_2417251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_2417251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417251 prefixEnd_2417251 := by exact prefixLift 2417251
  have htrace : WordTrace (prefixWord ++ tailWord_2417251) baseStart_2417251 baseEnd_2417251 := by
    simpa [prefixWord, tailWord_2417251, baseEnd_2417251] using wordTrace_append hprefix tailTrace_2417251
  have hstable : (prefixWord ++ tailWord_2417251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417251).length < 2 ^ (prefixWord ++ tailWord_2417251).sum := by decide
  have hdescent : baseEnd_2417251 < baseStart_2417251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417281 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2417281 : Nat := 118140960795 + 2417281 * 2 ^ 59
def prefixEnd_2417281 : Nat := 4983230072969 + 3 ^ 40 * 2417281 * 2
def baseEnd_2417281 : Nat := 1241227029981062110670633

theorem tailTrace_2417281 : CollatzResearch.WordTrace tailWord_2417281 prefixEnd_2417281 1241227029981062110670633 := by
  unfold tailWord_2417281
  simp only [CollatzResearch.WordTrace]
  refine ⟨88165481155611250572139697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58776987437074167048093131 88165481155611250572139697)
  ·
    refine ⟨66124110866708437929104773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88165481155611250572139697 66124110866708437929104773)
    ·
      refine ⟨12398270787507832111707145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66124110866708437929104773 12398270787507832111707145)
      ·
        refine ⟨9298703090630874083780359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12398270787507832111707145 9298703090630874083780359)
        ·
          refine ⟨13948054635946311125670539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9298703090630874083780359 13948054635946311125670539)
          ·
            refine ⟨20922081953919466688505809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13948054635946311125670539 20922081953919466688505809)
            ·
              refine ⟨15691561465439600016379357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20922081953919466688505809 15691561465439600016379357)
              ·
                refine ⟨5884335549539850006142259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15691561465439600016379357 5884335549539850006142259)
                ·
                  refine ⟨8826503324309775009213389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5884335549539850006142259 8826503324309775009213389)
                  ·
                    refine ⟨3309938746616165628455021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8826503324309775009213389 3309938746616165628455021)
                    ·
                      refine ⟨1241227029981062110670633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3309938746616165628455021 1241227029981062110670633)
                      ·
                        rfl

theorem cell23_2417281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2417281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417281 prefixEnd_2417281 := by exact prefixLift 2417281
  have htrace : WordTrace (prefixWord ++ tailWord_2417281) baseStart_2417281 baseEnd_2417281 := by
    simpa [prefixWord, tailWord_2417281, baseEnd_2417281] using wordTrace_append hprefix tailTrace_2417281
  have hstable : (prefixWord ++ tailWord_2417281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417281).length < 2 ^ (prefixWord ++ tailWord_2417281).sum := by decide
  have hdescent : baseEnd_2417281 < baseStart_2417281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417282 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2417282 : Nat := 118140960795 + 2417282 * 2 ^ 59
def prefixEnd_2417282 : Nat := 4983230072969 + 3 ^ 40 * 2417282 * 2
def baseEnd_2417282 : Nat := 1241227543461716606758129

theorem tailTrace_2417282 : CollatzResearch.WordTrace tailWord_2417282 prefixEnd_2417282 1241227543461716606758129 := by
  unfold tailWord_2417282
  simp only [CollatzResearch.WordTrace]
  refine ⟨22041379407151906935731525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58777011752405085161950733 22041379407151906935731525)
  ·
    refine ⟨4132758638840982550449661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22041379407151906935731525 4132758638840982550449661)
    ·
      refine ⟨1549784489565368456418623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4132758638840982550449661 1549784489565368456418623)
      ·
        refine ⟨2324676734348052684627935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1549784489565368456418623 2324676734348052684627935)
        ·
          refine ⟨3487015101522079026941903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324676734348052684627935 3487015101522079026941903)
          ·
            refine ⟨5230522652283118540412855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487015101522079026941903 5230522652283118540412855)
            ·
              refine ⟨7845783978424677810619283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230522652283118540412855 7845783978424677810619283)
              ·
                refine ⟨11768675967637016715928925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7845783978424677810619283 11768675967637016715928925)
                ·
                  refine ⟨4413253487863881268473347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11768675967637016715928925 4413253487863881268473347)
                  ·
                    refine ⟨6619880231795821902710021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4413253487863881268473347 6619880231795821902710021)
                    ·
                      refine ⟨1241227543461716606758129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6619880231795821902710021 1241227543461716606758129)
                      ·
                        rfl

theorem cell23_2417282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2417282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417282 prefixEnd_2417282 := by exact prefixLift 2417282
  have htrace : WordTrace (prefixWord ++ tailWord_2417282) baseStart_2417282 baseEnd_2417282 := by
    simpa [prefixWord, tailWord_2417282, baseEnd_2417282] using wordTrace_append hprefix tailTrace_2417282
  have hstable : (prefixWord ++ tailWord_2417282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417282).length < 2 ^ (prefixWord ++ tailWord_2417282).sum := by decide
  have hdescent : baseEnd_2417282 < baseStart_2417282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417298 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2417298 : Nat := 118140960795 + 2417298 * 2 ^ 59
def prefixEnd_2417298 : Nat := 4983230072969 + 3 ^ 40 * 2417298 * 2
def baseEnd_2417298 : Nat := 1241235759152188544158055

theorem tailTrace_2417298 : CollatzResearch.WordTrace tailWord_2417298 prefixEnd_2417298 1241235759152188544158055 := by
  unfold tailWord_2417298
  simp only [CollatzResearch.WordTrace]
  refine ⟨22041525299137415618877137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58777400797699774983672365 22041525299137415618877137)
  ·
    refine ⟨16531143974353061714157853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22041525299137415618877137 16531143974353061714157853)
    ·
      refine ⟨6199178990382398142809195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16531143974353061714157853 6199178990382398142809195)
      ·
        refine ⟨9298768485573597214213793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6199178990382398142809195 9298768485573597214213793)
        ·
          refine ⟨6974076364180197910660345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9298768485573597214213793 6974076364180197910660345)
          ·
            refine ⟨5230557273135148432995259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6974076364180197910660345 5230557273135148432995259)
            ·
              refine ⟨7845835909702722649492889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230557273135148432995259 7845835909702722649492889)
              ·
                refine ⟨5884376932277041987119667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7845835909702722649492889 5884376932277041987119667)
                ·
                  refine ⟨8826565398415562980679501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5884376932277041987119667 8826565398415562980679501)
                  ·
                    refine ⟨3309962024405836117754813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8826565398415562980679501 3309962024405836117754813)
                    ·
                      refine ⟨1241235759152188544158055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3309962024405836117754813 1241235759152188544158055)
                      ·
                        rfl

theorem cell23_2417298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2417298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417298 prefixEnd_2417298 := by exact prefixLift 2417298
  have htrace : WordTrace (prefixWord ++ tailWord_2417298) baseStart_2417298 baseEnd_2417298 := by
    simpa [prefixWord, tailWord_2417298, baseEnd_2417298] using wordTrace_append hprefix tailTrace_2417298
  have hstable : (prefixWord ++ tailWord_2417298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417298).length < 2 ^ (prefixWord ++ tailWord_2417298).sum := by decide
  have hdescent : baseEnd_2417298 < baseStart_2417298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417338 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2]
def baseStart_2417338 : Nat := 118140960795 + 2417338 * 2 ^ 59
def prefixEnd_2417338 : Nat := 4983230072969 + 3 ^ 40 * 2417338 * 2
def baseEnd_2417338 : Nat := 1241256298378368387657871

theorem tailTrace_2417338 : CollatzResearch.WordTrace tailWord_2417338 prefixEnd_2417338 1241256298378368387657871 := by
  unfold tailWord_2417338
  simp only [CollatzResearch.WordTrace]
  refine ⟨22041890029101187326741167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58778373410936499537976445 22041890029101187326741167)
  ·
    refine ⟨33062835043651780990111751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22041890029101187326741167 33062835043651780990111751)
    ·
      refine ⟨49594252565477671485167627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33062835043651780990111751 49594252565477671485167627)
      ·
        refine ⟨74391378848216507227751441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49594252565477671485167627 74391378848216507227751441)
        ·
          refine ⟨55793534136162380420813581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74391378848216507227751441 55793534136162380420813581)
          ·
            refine ⟨20922575301060892657805093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55793534136162380420813581 20922575301060892657805093)
            ·
              refine ⟨3922982868948917373338455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20922575301060892657805093 3922982868948917373338455)
              ·
                refine ⟨5884474303423376060007683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3922982868948917373338455 5884474303423376060007683)
                ·
                  refine ⟨8826711455135064090011525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5884474303423376060007683 8826711455135064090011525)
                  ·
                    refine ⟨1655008397837824516877161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8826711455135064090011525 1655008397837824516877161)
                    ·
                      refine ⟨1241256298378368387657871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655008397837824516877161 1241256298378368387657871)
                      ·
                        rfl

theorem cell23_2417338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_2417338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417338 prefixEnd_2417338 := by exact prefixLift 2417338
  have htrace : WordTrace (prefixWord ++ tailWord_2417338) baseStart_2417338 baseEnd_2417338 := by
    simpa [prefixWord, tailWord_2417338, baseEnd_2417338] using wordTrace_append hprefix tailTrace_2417338
  have hstable : (prefixWord ++ tailWord_2417338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417338).length < 2 ^ (prefixWord ++ tailWord_2417338).sum := by decide
  have hdescent : baseEnd_2417338 < baseStart_2417338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417344 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 9]
def baseStart_2417344 : Nat := 118140960795 + 2417344 * 2 ^ 59
def prefixEnd_2417344 : Nat := 4983230072969 + 3 ^ 40 * 2417344 * 2
def baseEnd_2417344 : Nat := 137917708806921707131427

theorem tailTrace_2417344 : CollatzResearch.WordTrace tailWord_2417344 prefixEnd_2417344 137917708806921707131427 := by
  unfold tailWord_2417344
  simp only [CollatzResearch.WordTrace]
  refine ⟨44083889477191506165841543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58778519302922008221122057 44083889477191506165841543)
  ·
    refine ⟨66125834215787259248762315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44083889477191506165841543 66125834215787259248762315)
    ·
      refine ⟨99188751323680888873143473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66125834215787259248762315 99188751323680888873143473)
      ·
        refine ⟨74391563492760666654857605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99188751323680888873143473 74391563492760666654857605)
        ·
          refine ⟨13948418154892624997785801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74391563492760666654857605 13948418154892624997785801)
          ·
            refine ⟨10461313616169468748339351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13948418154892624997785801 10461313616169468748339351)
            ·
              refine ⟨15691970424254203122509027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10461313616169468748339351 15691970424254203122509027)
              ·
                refine ⟨23537955636381304683763541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15691970424254203122509027 23537955636381304683763541)
                ·
                  refine ⟨137917708806921707131427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23537955636381304683763541 137917708806921707131427)
                  ·
                    rfl

theorem cell23_2417344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 9].length) (baseStart_2417344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417344 prefixEnd_2417344 := by exact prefixLift 2417344
  have htrace : WordTrace (prefixWord ++ tailWord_2417344) baseStart_2417344 baseEnd_2417344 := by
    simpa [prefixWord, tailWord_2417344, baseEnd_2417344] using wordTrace_append hprefix tailTrace_2417344
  have hstable : (prefixWord ++ tailWord_2417344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417344).length < 2 ^ (prefixWord ++ tailWord_2417344).sum := by decide
  have hdescent : baseEnd_2417344 < baseStart_2417344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417372 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2417372 : Nat := 118140960795 + 2417372 * 2 ^ 59
def prefixEnd_2417372 : Nat := 4983230072969 + 3 ^ 40 * 2417372 * 2
def baseEnd_2417372 : Nat := 1241273756720621254632715

theorem tailTrace_2417372 : CollatzResearch.WordTrace tailWord_2417372 prefixEnd_2417372 1241273756720621254632715 := by
  unfold tailWord_2417372
  simp only [CollatzResearch.WordTrace]
  refine ⟨44084400099140786556851185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58779200132187715409134913 44084400099140786556851185)
  ·
    refine ⟨33063300074355589917638389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44084400099140786556851185 33063300074355589917638389)
    ·
      refine ⟨3099684381970836554778599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33063300074355589917638389 3099684381970836554778599)
      ·
        refine ⟨4649526572956254832167899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3099684381970836554778599 4649526572956254832167899)
        ·
          refine ⟨6974289859434382248251849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4649526572956254832167899 6974289859434382248251849)
          ·
            refine ⟨5230717394575786686188887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6974289859434382248251849 5230717394575786686188887)
            ·
              refine ⟨7846076091863680029283331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5230717394575786686188887 7846076091863680029283331)
              ·
                refine ⟨11769114137795520043924997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7846076091863680029283331 11769114137795520043924997)
                ·
                  refine ⟨2206708900836660008235937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11769114137795520043924997 2206708900836660008235937)
                  ·
                    refine ⟨1655031675627495006176953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2206708900836660008235937 1655031675627495006176953)
                    ·
                      refine ⟨1241273756720621254632715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655031675627495006176953 1241273756720621254632715)
                      ·
                        rfl

theorem cell23_2417372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2417372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417372 prefixEnd_2417372 := by exact prefixLift 2417372
  have htrace : WordTrace (prefixWord ++ tailWord_2417372) baseStart_2417372 baseEnd_2417372 := by
    simpa [prefixWord, tailWord_2417372, baseEnd_2417372] using wordTrace_append hprefix tailTrace_2417372
  have hstable : (prefixWord ++ tailWord_2417372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417372).length < 2 ^ (prefixWord ++ tailWord_2417372).sum := by decide
  have hdescent : baseEnd_2417372 < baseStart_2417372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417411 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 4]
def baseStart_2417411 : Nat := 118140960795 + 2417411 * 2 ^ 59
def prefixEnd_2417411 : Nat := 4983230072969 + 3 ^ 40 * 2417411 * 2
def baseEnd_2417411 : Nat := 1241293782466146602045035

theorem tailTrace_2417411 : CollatzResearch.WordTrace tailWord_2417411 prefixEnd_2417411 1241293782466146602045035 := by
  unfold tailWord_2417411
  simp only [CollatzResearch.WordTrace]
  refine ⟨88170222645140282774372087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58780148430093521849581391 88170222645140282774372087)
  ·
    refine ⟨132255333967710424161558131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88170222645140282774372087 132255333967710424161558131)
    ·
      refine ⟨198383000951565636242337197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132255333967710424161558131 198383000951565636242337197)
      ·
        refine ⟨74393625356837113590876449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198383000951565636242337197 74393625356837113590876449)
        ·
          refine ⟨55795219017627835193157337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74393625356837113590876449 55795219017627835193157337)
          ·
            refine ⟨41846414263220876394868003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55795219017627835193157337 41846414263220876394868003)
            ·
              refine ⟨62769621394831314592302005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41846414263220876394868003 62769621394831314592302005)
              ·
                refine ⟨5884652005765435743028313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62769621394831314592302005 5884652005765435743028313)
                ·
                  refine ⟨4413489004324076807271235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5884652005765435743028313 4413489004324076807271235)
                  ·
                    refine ⟨6620233506486115210906853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4413489004324076807271235 6620233506486115210906853)
                    ·
                      refine ⟨1241293782466146602045035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6620233506486115210906853 1241293782466146602045035)
                      ·
                        rfl

theorem cell23_2417411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_2417411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417411 prefixEnd_2417411 := by exact prefixLift 2417411
  have htrace : WordTrace (prefixWord ++ tailWord_2417411) baseStart_2417411 baseEnd_2417411 := by
    simpa [prefixWord, tailWord_2417411, baseEnd_2417411] using wordTrace_append hprefix tailTrace_2417411
  have hstable : (prefixWord ++ tailWord_2417411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417411).length < 2 ^ (prefixWord ++ tailWord_2417411).sum := by decide
  have hdescent : baseEnd_2417411 < baseStart_2417411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417448 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2417448 : Nat := 118140960795 + 2417448 * 2 ^ 59
def prefixEnd_2417448 : Nat := 4983230072969 + 3 ^ 40 * 2417448 * 2
def baseEnd_2417448 : Nat := 1241312781250362957282365

theorem tailTrace_2417448 : CollatzResearch.WordTrace tailWord_2417448 prefixEnd_2417448 1241312781250362957282365 := by
  unfold tailWord_2417448
  simp only [CollatzResearch.WordTrace]
  refine ⟨44085786073003119046734499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58781048097337492062312665 44085786073003119046734499)
  ·
    refine ⟨66128679109504678570101749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44085786073003119046734499 66128679109504678570101749)
    ·
      refine ⟨6199563666516063615947039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66128679109504678570101749 6199563666516063615947039)
      ·
        refine ⟨9299345499774095423920559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6199563666516063615947039 9299345499774095423920559)
        ·
          refine ⟨13949018249661143135880839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9299345499774095423920559 13949018249661143135880839)
          ·
            refine ⟨20923527374491714703821259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13949018249661143135880839 20923527374491714703821259)
            ·
              refine ⟨31385291061737572055731889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20923527374491714703821259 31385291061737572055731889)
              ·
                refine ⟨23538968296303179041798917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31385291061737572055731889 23538968296303179041798917)
                ·
                  refine ⟨4413556555556846070337297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23538968296303179041798917 4413556555556846070337297)
                  ·
                    refine ⟨3310167416667634552752973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4413556555556846070337297 3310167416667634552752973)
                    ·
                      refine ⟨1241312781250362957282365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3310167416667634552752973 1241312781250362957282365)
                      ·
                        rfl

theorem cell23_2417448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2417448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417448 prefixEnd_2417448 := by exact prefixLift 2417448
  have htrace : WordTrace (prefixWord ++ tailWord_2417448) baseStart_2417448 baseEnd_2417448 := by
    simpa [prefixWord, tailWord_2417448, baseEnd_2417448] using wordTrace_append hprefix tailTrace_2417448
  have hstable : (prefixWord ++ tailWord_2417448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417448).length < 2 ^ (prefixWord ++ tailWord_2417448).sum := by decide
  have hdescent : baseEnd_2417448 < baseStart_2417448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417462 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2417462 : Nat := 118140960795 + 2417462 * 2 ^ 59
def prefixEnd_2417462 : Nat := 4983230072969 + 3 ^ 40 * 2417462 * 2
def baseEnd_2417462 : Nat := 1241319969979525902507301

theorem tailTrace_2417462 : CollatzResearch.WordTrace tailWord_2417462 prefixEnd_2417462 1241319969979525902507301 := by
  unfold tailWord_2417462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510755172997219905279915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58781388511970345656319093 5510755172997219905279915)
  ·
    refine ⟨8266132759495829857919873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5510755172997219905279915 8266132759495829857919873)
    ·
      refine ⟨6199599569621872393439905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8266132759495829857919873 6199599569621872393439905)
      ·
        refine ⟨4649699677216404295079929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6199599569621872393439905 4649699677216404295079929)
        ·
          refine ⟨3487274757912303221309947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4649699677216404295079929 3487274757912303221309947)
          ·
            refine ⟨5230912136868454831964921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487274757912303221309947 5230912136868454831964921)
            ·
              refine ⟨3923184102651341123973691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5230912136868454831964921 3923184102651341123973691)
              ·
                refine ⟨5884776153977011685960537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923184102651341123973691 5884776153977011685960537)
                ·
                  refine ⟨4413582115482758764470403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5884776153977011685960537 4413582115482758764470403)
                  ·
                    refine ⟨6620373173224138146705605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4413582115482758764470403 6620373173224138146705605)
                    ·
                      refine ⟨1241319969979525902507301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6620373173224138146705605 1241319969979525902507301)
                      ·
                        rfl

theorem cell23_2417462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2417462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417462 prefixEnd_2417462 := by exact prefixLift 2417462
  have htrace : WordTrace (prefixWord ++ tailWord_2417462) baseStart_2417462 baseEnd_2417462 := by
    simpa [prefixWord, tailWord_2417462, baseEnd_2417462] using wordTrace_append hprefix tailTrace_2417462
  have hstable : (prefixWord ++ tailWord_2417462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417462).length < 2 ^ (prefixWord ++ tailWord_2417462).sum := by decide
  have hdescent : baseEnd_2417462 < baseStart_2417462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417489 : List Nat := [1, 2, 2, 1, 6, 2, 2, 2, 1, 4]
def baseStart_2417489 : Nat := 118140960795 + 2417489 * 2 ^ 59
def prefixEnd_2417489 : Nat := 4983230072969 + 3 ^ 40 * 2417489 * 2
def baseEnd_2417489 : Nat := 413777944652399098956559

theorem tailTrace_2417489 : CollatzResearch.WordTrace tailWord_2417489 prefixEnd_2417489 413777944652399098956559 := by
  unfold tailWord_2417489
  simp only [CollatzResearch.WordTrace]
  refine ⟨88173067538857702095711521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58782045025905134730474347 88173067538857702095711521)
  ·
    refine ⟨66129800654143276571783641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88173067538857702095711521 66129800654143276571783641)
    ·
      refine ⟨49597350490607457428837731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66129800654143276571783641 49597350490607457428837731)
      ·
        refine ⟨74396025735911186143256597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49597350490607457428837731 74396025735911186143256597)
        ·
          refine ⟨3487313706370836850465153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74396025735911186143256597 3487313706370836850465153)
          ·
            refine ⟨2615485279778127637848865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3487313706370836850465153 2615485279778127637848865)
            ·
              refine ⟨1961613959833595728386649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2615485279778127637848865 1961613959833595728386649)
              ·
                refine ⟨1471210469875196796289987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1961613959833595728386649 1471210469875196796289987)
                ·
                  refine ⟨2206815704812795194434981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471210469875196796289987 2206815704812795194434981)
                  ·
                    refine ⟨413777944652399098956559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2206815704812795194434981 413777944652399098956559)
                    ·
                      rfl

theorem cell23_2417489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_2417489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417489 prefixEnd_2417489 := by exact prefixLift 2417489
  have htrace : WordTrace (prefixWord ++ tailWord_2417489) baseStart_2417489 baseEnd_2417489 := by
    simpa [prefixWord, tailWord_2417489, baseEnd_2417489] using wordTrace_append hprefix tailTrace_2417489
  have hstable : (prefixWord ++ tailWord_2417489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417489).length < 2 ^ (prefixWord ++ tailWord_2417489).sum := by decide
  have hdescent : baseEnd_2417489 < baseStart_2417489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417535 : List Nat := [1, 1, 2, 2, 1, 1, 8, 1, 1, 1, 4]
def baseStart_2417535 : Nat := 118140960795 + 2417535 * 2 ^ 59
def prefixEnd_2417535 : Nat := 4983230072969 + 3 ^ 40 * 2417535 * 2
def baseEnd_2417535 : Nat := 1241357454067304116894465

theorem tailTrace_2417535 : CollatzResearch.WordTrace tailWord_2417535 prefixEnd_2417535 1241357454067304116894465 := by
  unfold tailWord_2417535
  simp only [CollatzResearch.WordTrace]
  refine ⟨88174745296691051951886059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58783163531127367967924039 88174745296691051951886059)
  ·
    refine ⟨132262117945036577927829089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88174745296691051951886059 132262117945036577927829089)
    ·
      refine ⟨99196588458777433445871817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132262117945036577927829089 99196588458777433445871817)
      ·
        refine ⟨74397441344083075084403863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99196588458777433445871817 74397441344083075084403863)
        ·
          refine ⟨111596162016124612626605795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74397441344083075084403863 111596162016124612626605795)
          ·
            refine ⟨167394243024186918939908693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111596162016124612626605795 167394243024186918939908693)
            ·
              refine ⟨1961651285439690456327055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 167394243024186918939908693 1961651285439690456327055)
              ·
                refine ⟨2942476928159535684490583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961651285439690456327055 2942476928159535684490583)
                ·
                  refine ⟨4413715392239303526735875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942476928159535684490583 4413715392239303526735875)
                  ·
                    refine ⟨6620573088358955290103813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4413715392239303526735875 6620573088358955290103813)
                    ·
                      refine ⟨1241357454067304116894465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6620573088358955290103813 1241357454067304116894465)
                      ·
                        rfl

theorem cell23_2417535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_2417535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417535 prefixEnd_2417535 := by exact prefixLift 2417535
  have htrace : WordTrace (prefixWord ++ tailWord_2417535) baseStart_2417535 baseEnd_2417535 := by
    simpa [prefixWord, tailWord_2417535, baseEnd_2417535] using wordTrace_append hprefix tailTrace_2417535
  have hstable : (prefixWord ++ tailWord_2417535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417535).length < 2 ^ (prefixWord ++ tailWord_2417535).sum := by decide
  have hdescent : baseEnd_2417535 < baseStart_2417535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417541 : List Nat := [1, 3, 1, 1, 3, 4, 10]
def baseStart_2417541 : Nat := 118140960795 + 2417541 * 2 ^ 59
def prefixEnd_2417541 : Nat := 4983230072969 + 3 ^ 40 * 2417541 * 2
def baseEnd_2417541 : Nat := 15325438703101618437277

theorem tailTrace_2417541 : CollatzResearch.WordTrace tailWord_2417541 prefixEnd_2417541 15325438703101618437277 := by
  unfold tailWord_2417541
  simp only [CollatzResearch.WordTrace]
  refine ⟨88174964134669314976604477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58783309423112876651069651 88174964134669314976604477)
  ·
    refine ⟨33065611550500993116226679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88174964134669314976604477 33065611550500993116226679)
    ·
      refine ⟨49598417325751489674340019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33065611550500993116226679 49598417325751489674340019)
      ·
        refine ⟨74397625988627234511510029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49598417325751489674340019 74397625988627234511510029)
        ·
          refine ⟨27899109745735212941816261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74397625988627234511510029 27899109745735212941816261)
          ·
            refine ⟨5231083077325352426590549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27899109745735212941816261 5231083077325352426590549)
            ·
              refine ⟨15325438703101618437277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5231083077325352426590549 15325438703101618437277)
              ·
                rfl

theorem cell23_2417541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 10].length) (baseStart_2417541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417541 prefixEnd_2417541 := by exact prefixLift 2417541
  have htrace : WordTrace (prefixWord ++ tailWord_2417541) baseStart_2417541 baseEnd_2417541 := by
    simpa [prefixWord, tailWord_2417541, baseEnd_2417541] using wordTrace_append hprefix tailTrace_2417541
  have hstable : (prefixWord ++ tailWord_2417541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417541).length < 2 ^ (prefixWord ++ tailWord_2417541).sum := by decide
  have hdescent : baseEnd_2417541 < baseStart_2417541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417545 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 2, 4]
def baseStart_2417545 : Nat := 118140960795 + 2417545 * 2 ^ 59
def prefixEnd_2417545 : Nat := 4983230072969 + 3 ^ 40 * 2417545 * 2
def baseEnd_2417545 : Nat := 413787529624616359256473

theorem tailTrace_2417545 : CollatzResearch.WordTrace tailWord_2417545 prefixEnd_2417545 413787529624616359256473 := by
  unfold tailWord_2417545
  simp only [CollatzResearch.WordTrace]
  refine ⟨88175110026654823659750089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58783406684436549106500059 88175110026654823659750089)
  ·
    refine ⟨66131332519991117744812567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88175110026654823659750089 66131332519991117744812567)
    ·
      refine ⟨99196998779986676617218851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66131332519991117744812567 99196998779986676617218851)
      ·
        refine ⟨148795498169980014925828277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99196998779986676617218851 148795498169980014925828277)
        ·
          refine ⟨13949577953435626399296401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148795498169980014925828277 13949577953435626399296401)
          ·
            refine ⟨10462183465076719799472301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13949577953435626399296401 10462183465076719799472301)
            ·
              refine ⟨3923318799403769924802113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10462183465076719799472301 3923318799403769924802113)
              ·
                refine ⟨2942489099552827443601585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3923318799403769924802113 2942489099552827443601585)
                ·
                  refine ⟨2206866824664620582701189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2942489099552827443601585 2206866824664620582701189)
                  ·
                    refine ⟨413787529624616359256473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2206866824664620582701189 413787529624616359256473)
                    ·
                      rfl

theorem cell23_2417545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 4].length) (baseStart_2417545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417545 prefixEnd_2417545 := by exact prefixLift 2417545
  have htrace : WordTrace (prefixWord ++ tailWord_2417545) baseStart_2417545 baseEnd_2417545 := by
    simpa [prefixWord, tailWord_2417545, baseEnd_2417545] using wordTrace_append hprefix tailTrace_2417545
  have hstable : (prefixWord ++ tailWord_2417545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417545).length < 2 ^ (prefixWord ++ tailWord_2417545).sum := by decide
  have hdescent : baseEnd_2417545 < baseStart_2417545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417562 : List Nat := [3, 1, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_2417562 : Nat := 118140960795 + 2417562 * 2 ^ 59
def prefixEnd_2417562 : Nat := 4983230072969 + 3 ^ 40 * 2417562 * 2
def baseEnd_2417562 : Nat := 413790439348325170418947

theorem tailTrace_2417562 : CollatzResearch.WordTrace tailWord_2417562 prefixEnd_2417562 413790439348325170418947 := by
  unfold tailWord_2417562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22043932516898308890779735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58783820045062157042079293 22043932516898308890779735)
  ·
    refine ⟨33065898775347463336169603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22043932516898308890779735 33065898775347463336169603)
    ·
      refine ⟨49598848163021195004254405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33065898775347463336169603 49598848163021195004254405)
      ·
        refine ⟨9299784030566474063297701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49598848163021195004254405 9299784030566474063297701)
        ·
          refine ⟨1743709505731213886868319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9299784030566474063297701 1743709505731213886868319)
          ·
            refine ⟨2615564258596820830302479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743709505731213886868319 2615564258596820830302479)
            ·
              refine ⟨3923346387895231245453719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615564258596820830302479 3923346387895231245453719)
              ·
                refine ⟨5885019581842846868180579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923346387895231245453719 5885019581842846868180579)
                ·
                  refine ⟨8827529372764270302270869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5885019581842846868180579 8827529372764270302270869)
                  ·
                    refine ⟨413790439348325170418947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8827529372764270302270869 413790439348325170418947)
                    ·
                      rfl

theorem cell23_2417562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_2417562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417562 prefixEnd_2417562 := by exact prefixLift 2417562
  have htrace : WordTrace (prefixWord ++ tailWord_2417562) baseStart_2417562 baseEnd_2417562 := by
    simpa [prefixWord, tailWord_2417562, baseEnd_2417562] using wordTrace_append hprefix tailTrace_2417562
  have hstable : (prefixWord ++ tailWord_2417562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417562).length < 2 ^ (prefixWord ++ tailWord_2417562).sum := by decide
  have hdescent : baseEnd_2417562 < baseStart_2417562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417571 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 2, 7]
def baseStart_2417571 : Nat := 118140960795 + 2417571 * 2 ^ 59
def prefixEnd_2417571 : Nat := 4983230072969 + 3 ^ 40 * 2417571 * 2
def baseEnd_2417571 : Nat := 413791979790288658681433

theorem tailTrace_2417571 : CollatzResearch.WordTrace tailWord_2417571 prefixEnd_2417571 413791979790288658681433 := by
  unfold tailWord_2417571
  simp only [CollatzResearch.WordTrace]
  refine ⟨88176058324560630100196567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58784038883040420066797711 88176058324560630100196567)
  ·
    refine ⟨132264087486840945150294851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88176058324560630100196567 132264087486840945150294851)
    ·
      refine ⟨198396131230261417725442277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132264087486840945150294851 198396131230261417725442277)
      ·
        refine ⟨37199274605674015823520427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198396131230261417725442277 37199274605674015823520427)
        ·
          refine ⟨55798911908511023735280641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37199274605674015823520427 55798911908511023735280641)
          ·
            refine ⟨41849183931383267801460481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55798911908511023735280641 41849183931383267801460481)
            ·
              refine ⟨31386887948537450851095361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41849183931383267801460481 31386887948537450851095361)
              ·
                refine ⟨23540165961403088138321521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31386887948537450851095361 23540165961403088138321521)
                ·
                  refine ⟨17655124471052316103741141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23540165961403088138321521 17655124471052316103741141)
                  ·
                    refine ⟨413791979790288658681433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17655124471052316103741141 413791979790288658681433)
                    ·
                      rfl

theorem cell23_2417571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 7].length) (baseStart_2417571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417571 prefixEnd_2417571 := by exact prefixLift 2417571
  have htrace : WordTrace (prefixWord ++ tailWord_2417571) baseStart_2417571 baseEnd_2417571 := by
    simpa [prefixWord, tailWord_2417571, baseEnd_2417571] using wordTrace_append hprefix tailTrace_2417571
  have hstable : (prefixWord ++ tailWord_2417571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417571).length < 2 ^ (prefixWord ++ tailWord_2417571).sum := by decide
  have hdescent : baseEnd_2417571 < baseStart_2417571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417598 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2417598 : Nat := 118140960795 + 2417598 * 2 ^ 59
def prefixEnd_2417598 : Nat := 4983230072969 + 3 ^ 40 * 2417598 * 2
def baseEnd_2417598 : Nat := 1241389803348537370406675

theorem tailTrace_2417598 : CollatzResearch.WordTrace tailWord_2417598 prefixEnd_2417598 1241389803348537370406675 := by
  unfold tailWord_2417598
  simp only [CollatzResearch.WordTrace]
  refine ⟨11022130386932851713928681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58784695396975209140952965 11022130386932851713928681)
  ·
    refine ⟨8266597790199638785446511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11022130386932851713928681 8266597790199638785446511)
    ·
      refine ⟨12399896685299458178169767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8266597790199638785446511 12399896685299458178169767)
      ·
        refine ⟨18599845027949187267254651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12399896685299458178169767 18599845027949187267254651)
        ·
          refine ⟨27899767541923780900881977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18599845027949187267254651 27899767541923780900881977)
          ·
            refine ⟨20924825656442835675661483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27899767541923780900881977 20924825656442835675661483)
            ·
              refine ⟨31387238484664253513492225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20924825656442835675661483 31387238484664253513492225)
              ·
                refine ⟨23540428863498190135119169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31387238484664253513492225 23540428863498190135119169)
                ·
                  refine ⟨17655321647623642601339377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23540428863498190135119169 17655321647623642601339377)
                  ·
                    refine ⟨13241491235717731951004533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17655321647623642601339377 13241491235717731951004533)
                    ·
                      refine ⟨1241389803348537370406675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13241491235717731951004533 1241389803348537370406675)
                      ·
                        rfl

theorem cell23_2417598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2417598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417598 prefixEnd_2417598 := by exact prefixLift 2417598
  have htrace : WordTrace (prefixWord ++ tailWord_2417598) baseStart_2417598 baseEnd_2417598 := by
    simpa [prefixWord, tailWord_2417598, baseEnd_2417598] using wordTrace_append hprefix tailTrace_2417598
  have hstable : (prefixWord ++ tailWord_2417598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417598).length < 2 ^ (prefixWord ++ tailWord_2417598).sum := by decide
  have hdescent : baseEnd_2417598 < baseStart_2417598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417629 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_2417629 : Nat := 118140960795 + 2417629 * 2 ^ 59
def prefixEnd_2417629 : Nat := 4983230072969 + 3 ^ 40 * 2417629 * 2
def baseEnd_2417629 : Nat := 1241405721248826749119033

theorem tailTrace_2417629 : CollatzResearch.WordTrace tailWord_2417629 prefixEnd_2417629 1241405721248826749119033 := by
  unfold tailWord_2417629
  simp only [CollatzResearch.WordTrace]
  refine ⟨88178173758350506005807941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58785449172233670670538627 88178173758350506005807941)
  ·
    refine ⟨16533407579690719876088989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88178173758350506005807941 16533407579690719876088989)
    ·
      refine ⟨6200027842384019953533371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16533407579690719876088989 6200027842384019953533371)
      ·
        refine ⟨9300041763576029930300057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6200027842384019953533371 9300041763576029930300057)
        ·
          refine ⟨6975031322682022447725043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9300041763576029930300057 6975031322682022447725043)
          ·
            refine ⟨10462546984023033671587565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975031322682022447725043 10462546984023033671587565)
            ·
              refine ⟨3923455119008637626845337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10462546984023033671587565 3923455119008637626845337)
              ·
                refine ⟨2942591339256478220134003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3923455119008637626845337 2942591339256478220134003)
                ·
                  refine ⟨4413887008884717330201005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942591339256478220134003 4413887008884717330201005)
                  ·
                    refine ⟨1655207628331768998825377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4413887008884717330201005 1655207628331768998825377)
                    ·
                      refine ⟨1241405721248826749119033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655207628331768998825377 1241405721248826749119033)
                      ·
                        rfl

theorem cell23_2417629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_2417629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417629 prefixEnd_2417629 := by exact prefixLift 2417629
  have htrace : WordTrace (prefixWord ++ tailWord_2417629) baseStart_2417629 baseEnd_2417629 := by
    simpa [prefixWord, tailWord_2417629, baseEnd_2417629] using wordTrace_append hprefix tailTrace_2417629
  have hstable : (prefixWord ++ tailWord_2417629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417629).length < 2 ^ (prefixWord ++ tailWord_2417629).sum := by decide
  have hdescent : baseEnd_2417629 < baseStart_2417629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417642 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_2417642 : Nat := 118140960795 + 2417642 * 2 ^ 59
def prefixEnd_2417642 : Nat := 4983230072969 + 3 ^ 40 * 2417642 * 2
def baseEnd_2417642 : Nat := 1241412396497335198256473

theorem tailTrace_2417642 : CollatzResearch.WordTrace tailWord_2417642 prefixEnd_2417642 1241412396497335198256473 := by
  unfold tailWord_2417642
  simp only [CollatzResearch.WordTrace]
  refine ⟨22044661976825852306507795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58785765271535606150687453 22044661976825852306507795)
  ·
    refine ⟨33066992965238778459761693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22044661976825852306507795 33066992965238778459761693)
    ·
      refine ⟨12400122361964541922410635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33066992965238778459761693 12400122361964541922410635)
      ·
        refine ⟨18600183542946812883615953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12400122361964541922410635 18600183542946812883615953)
        ·
          refine ⟨13950137657210109662711965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18600183542946812883615953 13950137657210109662711965)
          ·
            refine ⟨5231301621453791123516987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13950137657210109662711965 5231301621453791123516987)
            ·
              refine ⟨7846952432180686685275481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231301621453791123516987 7846952432180686685275481)
              ·
                refine ⟨5885214324135515013956611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7846952432180686685275481 5885214324135515013956611)
                ·
                  refine ⟨8827821486203272520934917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5885214324135515013956611 8827821486203272520934917)
                  ·
                    refine ⟨1655216528663113597675297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8827821486203272520934917 1655216528663113597675297)
                    ·
                      refine ⟨1241412396497335198256473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655216528663113597675297 1241412396497335198256473)
                      ·
                        rfl

theorem cell23_2417642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_2417642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417642 prefixEnd_2417642 := by exact prefixLift 2417642
  have htrace : WordTrace (prefixWord ++ tailWord_2417642) baseStart_2417642 baseEnd_2417642 := by
    simpa [prefixWord, tailWord_2417642, baseEnd_2417642] using wordTrace_append hprefix tailTrace_2417642
  have hstable : (prefixWord ++ tailWord_2417642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417642).length < 2 ^ (prefixWord ++ tailWord_2417642).sum := by decide
  have hdescent : baseEnd_2417642 < baseStart_2417642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417646 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_2417646 : Nat := 118140960795 + 2417646 * 2 ^ 59
def prefixEnd_2417646 : Nat := 4983230072969 + 3 ^ 40 * 2417646 * 2
def baseEnd_2417646 : Nat := 1241414450419953182606455

theorem tailTrace_2417646 : CollatzResearch.WordTrace tailWord_2417646 prefixEnd_2417646 1241414450419953182606455 := by
  unfold tailWord_2417646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11022349224911114738647099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58785862532859278606117861 11022349224911114738647099)
  ·
    refine ⟨16533523837366672107970649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11022349224911114738647099 16533523837366672107970649)
    ·
      refine ⟨12400142878025004080977987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16533523837366672107970649 12400142878025004080977987)
      ·
        refine ⟨18600214317037506121466981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12400142878025004080977987 18600214317037506121466981)
        ·
          refine ⟨3487540184444532397775059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18600214317037506121466981 3487540184444532397775059)
          ·
            refine ⟨5231310276666798596662589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487540184444532397775059 5231310276666798596662589)
            ·
              refine ⟨1961741353750049473748471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5231310276666798596662589 1961741353750049473748471)
              ·
                refine ⟨2942612030625074210622707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961741353750049473748471 2942612030625074210622707)
                ·
                  refine ⟨4413918045937611315934061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2942612030625074210622707 4413918045937611315934061)
                  ·
                    refine ⟨1655219267226604243475273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4413918045937611315934061 1655219267226604243475273)
                    ·
                      refine ⟨1241414450419953182606455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655219267226604243475273 1241414450419953182606455)
                      ·
                        rfl

theorem cell23_2417646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_2417646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417646 prefixEnd_2417646 := by exact prefixLift 2417646
  have htrace : WordTrace (prefixWord ++ tailWord_2417646) baseStart_2417646 baseEnd_2417646 := by
    simpa [prefixWord, tailWord_2417646, baseEnd_2417646] using wordTrace_append hprefix tailTrace_2417646
  have hstable : (prefixWord ++ tailWord_2417646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417646).length < 2 ^ (prefixWord ++ tailWord_2417646).sum := by decide
  have hdescent : baseEnd_2417646 < baseStart_2417646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417658 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_2417658 : Nat := 118140960795 + 2417658 * 2 ^ 59
def prefixEnd_2417658 : Nat := 4983230072969 + 3 ^ 40 * 2417658 * 2
def baseEnd_2417658 : Nat := 1241420612187807135656399

theorem tailTrace_2417658 : CollatzResearch.WordTrace tailWord_2417658 prefixEnd_2417658 1241420612187807135656399 := by
  unfold tailWord_2417658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22044807868811360989653407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58786154316830295972409085 22044807868811360989653407)
  ·
    refine ⟨33067211803217041484480111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22044807868811360989653407 33067211803217041484480111)
    ·
      refine ⟨49600817704825562226720167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33067211803217041484480111 49600817704825562226720167)
      ·
        refine ⟨74401226557238343340080251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49600817704825562226720167 74401226557238343340080251)
        ·
          refine ⟨111601839835857515010120377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74401226557238343340080251 111601839835857515010120377)
          ·
            refine ⟨83701379876893136257590283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111601839835857515010120377 83701379876893136257590283)
            ·
              refine ⟨125552069815339704386385425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83701379876893136257590283 125552069815339704386385425)
              ·
                refine ⟨94164052361504778289789069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125552069815339704386385425 94164052361504778289789069)
                ·
                  refine ⟨35311519635564291858670901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94164052361504778289789069 35311519635564291858670901)
                  ·
                    refine ⟨3310454965834152361750397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35311519635564291858670901 3310454965834152361750397)
                    ·
                      refine ⟨1241420612187807135656399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3310454965834152361750397 1241420612187807135656399)
                      ·
                        rfl

theorem cell23_2417658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_2417658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417658 prefixEnd_2417658 := by exact prefixLift 2417658
  have htrace : WordTrace (prefixWord ++ tailWord_2417658) baseStart_2417658 baseEnd_2417658 := by
    simpa [prefixWord, tailWord_2417658, baseEnd_2417658] using wordTrace_append hprefix tailTrace_2417658
  have hstable : (prefixWord ++ tailWord_2417658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417658).length < 2 ^ (prefixWord ++ tailWord_2417658).sum := by decide
  have hdescent : baseEnd_2417658 < baseStart_2417658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417675 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 3]
def baseStart_2417675 : Nat := 118140960795 + 2417675 * 2 ^ 59
def prefixEnd_2417675 : Nat := 4983230072969 + 3 ^ 40 * 2417675 * 2
def baseEnd_2417675 : Nat := 1241429341358933569143821

theorem tailTrace_2417675 : CollatzResearch.WordTrace tailWord_2417675 prefixEnd_2417675 1241429341358933569143821 := by
  unfold tailWord_2417675
  simp only [CollatzResearch.WordTrace]
  refine ⟨88179851516183855861982479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58786567677455903907988319 88179851516183855861982479)
  ·
    refine ⟨132269777274275783792973719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88179851516183855861982479 132269777274275783792973719)
    ·
      refine ⟨198404665911413675689460579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132269777274275783792973719 198404665911413675689460579)
      ·
        refine ⟨297606998867120513534190869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198404665911413675689460579 297606998867120513534190869)
        ·
          refine ⟨13950328071896274071915197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 297606998867120513534190869 13950328071896274071915197)
          ·
            refine ⟨5231373026961102776968199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13950328071896274071915197 5231373026961102776968199)
            ·
              refine ⟨7847059540441654165452299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231373026961102776968199 7847059540441654165452299)
              ·
                refine ⟨11770589310662481248178449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7847059540441654165452299 11770589310662481248178449)
                ·
                  refine ⟨8827941982996860936133837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11770589310662481248178449 8827941982996860936133837)
                  ·
                    refine ⟨3310478243623822851050189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8827941982996860936133837 3310478243623822851050189)
                    ·
                      refine ⟨1241429341358933569143821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3310478243623822851050189 1241429341358933569143821)
                      ·
                        rfl

theorem cell23_2417675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 3].length) (baseStart_2417675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417675 prefixEnd_2417675 := by exact prefixLift 2417675
  have htrace : WordTrace (prefixWord ++ tailWord_2417675) baseStart_2417675 baseEnd_2417675 := by
    simpa [prefixWord, tailWord_2417675, baseEnd_2417675] using wordTrace_append hprefix tailTrace_2417675
  have hstable : (prefixWord ++ tailWord_2417675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417675).length < 2 ^ (prefixWord ++ tailWord_2417675).sum := by decide
  have hdescent : baseEnd_2417675 < baseStart_2417675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417695 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 2, 5]
def baseStart_2417695 : Nat := 118140960795 + 2417695 * 2 ^ 59
def prefixEnd_2417695 : Nat := 4983230072969 + 3 ^ 40 * 2417695 * 2
def baseEnd_2417695 : Nat := 413813203657341163631243

theorem tailTrace_2417695 : CollatzResearch.WordTrace tailWord_2417695 prefixEnd_2417695 413813203657341163631243 := by
  unfold tailWord_2417695
  simp only [CollatzResearch.WordTrace]
  refine ⟨88180580976111399277710539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58787053984074266185140359 88180580976111399277710539)
  ·
    refine ⟨132270871464167098916565809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88180580976111399277710539 132270871464167098916565809)
    ·
      refine ⟨99203153598125324187424357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132270871464167098916565809 99203153598125324187424357)
      ·
        refine ⟨18600591299648498285142067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99203153598125324187424357 18600591299648498285142067)
        ·
          refine ⟨27900886949472747427713101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18600591299648498285142067 27900886949472747427713101)
          ·
            refine ⟨10462832606052280285392413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27900886949472747427713101 10462832606052280285392413)
            ·
              refine ⟨3923562227269605107022155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10462832606052280285392413 3923562227269605107022155)
              ·
                refine ⟨5885343340904407660533233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923562227269605107022155 5885343340904407660533233)
                ·
                  refine ⟨4414007505678305745399925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5885343340904407660533233 4414007505678305745399925)
                  ·
                    refine ⟨413813203657341163631243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4414007505678305745399925 413813203657341163631243)
                    ·
                      rfl

theorem cell23_2417695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_2417695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417695 prefixEnd_2417695 := by exact prefixLift 2417695
  have htrace : WordTrace (prefixWord ++ tailWord_2417695) baseStart_2417695 baseEnd_2417695 := by
    simpa [prefixWord, tailWord_2417695, baseEnd_2417695] using wordTrace_append hprefix tailTrace_2417695
  have hstable : (prefixWord ++ tailWord_2417695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417695).length < 2 ^ (prefixWord ++ tailWord_2417695).sum := by decide
  have hdescent : baseEnd_2417695 < baseStart_2417695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417728 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_2417728 : Nat := 118140960795 + 2417728 * 2 ^ 59
def prefixEnd_2417728 : Nat := 4983230072969 + 3 ^ 40 * 2417728 * 2
def baseEnd_2417728 : Nat := 1241456555833621861781077

theorem tailTrace_2417728 : CollatzResearch.WordTrace tailWord_2417728 prefixEnd_2417728 1241456555833621861781077 := by
  unfold tailWord_2417728
  simp only [CollatzResearch.WordTrace]
  refine ⟨44090892292495922956830919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58787856389994563942441225 44090892292495922956830919)
  ·
    refine ⟨66136338438743884435246379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44090892292495922956830919 66136338438743884435246379)
    ·
      refine ⟨99204507658115826652869569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66136338438743884435246379 99204507658115826652869569)
      ·
        refine ⟨74403380743586869989652177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99204507658115826652869569 74403380743586869989652177)
        ·
          refine ⟨55802535557690152492239133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74403380743586869989652177 55802535557690152492239133)
          ·
            refine ⟨20925950834133807184589675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55802535557690152492239133 20925950834133807184589675)
            ·
              refine ⟨31388926251200710776884513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20925950834133807184589675 31388926251200710776884513)
              ·
                refine ⟨23541694688400533082663385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31388926251200710776884513 23541694688400533082663385)
                ·
                  refine ⟨17656271016300399811997539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23541694688400533082663385 17656271016300399811997539)
                  ·
                    refine ⟨26484406524450599717996309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17656271016300399811997539 26484406524450599717996309)
                    ·
                      refine ⟨1241456555833621861781077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26484406524450599717996309 1241456555833621861781077)
                      ·
                        rfl

theorem cell23_2417728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_2417728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417728 prefixEnd_2417728 := by exact prefixLift 2417728
  have htrace : WordTrace (prefixWord ++ tailWord_2417728) baseStart_2417728 baseEnd_2417728 := by
    simpa [prefixWord, tailWord_2417728, baseEnd_2417728] using wordTrace_append hprefix tailTrace_2417728
  have hstable : (prefixWord ++ tailWord_2417728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417728).length < 2 ^ (prefixWord ++ tailWord_2417728).sum := by decide
  have hdescent : baseEnd_2417728 < baseStart_2417728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417735 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 3]
def baseStart_2417735 : Nat := 118140960795 + 2417735 * 2 ^ 59
def prefixEnd_2417735 : Nat := 4983230072969 + 3 ^ 40 * 2417735 * 2
def baseEnd_2417735 : Nat := 1241460150198203334393545

theorem tailTrace_2417735 : CollatzResearch.WordTrace tailWord_2417735 prefixEnd_2417735 1241460150198203334393545 := by
  unfold tailWord_2417735
  simp only [CollatzResearch.WordTrace]
  refine ⟨88182039895966486109166659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58788026597310990739444439 88182039895966486109166659)
  ·
    refine ⟨132273059843949729163749989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88182039895966486109166659 132273059843949729163749989)
    ·
      refine ⟨24801198720740574218203123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132273059843949729163749989 24801198720740574218203123)
      ·
        refine ⟨37201798081110861327304685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24801198720740574218203123 37201798081110861327304685)
        ·
          refine ⟨13950674280416572997739257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37201798081110861327304685 13950674280416572997739257)
          ·
            refine ⟨10463005710312429748304443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13950674280416572997739257 10463005710312429748304443)
            ·
              refine ⟨15694508565468644622456665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10463005710312429748304443 15694508565468644622456665)
              ·
                refine ⟨11770881424101483466842499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15694508565468644622456665 11770881424101483466842499)
                ·
                  refine ⟨17656322136152225200263749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11770881424101483466842499 17656322136152225200263749)
                  ·
                    refine ⟨3310560400528542225049453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17656322136152225200263749 3310560400528542225049453)
                    ·
                      refine ⟨1241460150198203334393545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3310560400528542225049453 1241460150198203334393545)
                      ·
                        rfl

theorem cell23_2417735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_2417735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417735 prefixEnd_2417735 := by exact prefixLift 2417735
  have htrace : WordTrace (prefixWord ++ tailWord_2417735) baseStart_2417735 baseEnd_2417735 := by
    simpa [prefixWord, tailWord_2417735, baseEnd_2417735] using wordTrace_append hprefix tailTrace_2417735
  have hstable : (prefixWord ++ tailWord_2417735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417735).length < 2 ^ (prefixWord ++ tailWord_2417735).sum := by decide
  have hdescent : baseEnd_2417735 < baseStart_2417735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417815 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 3, 6]
def baseStart_2417815 : Nat := 118140960795 + 2417815 * 2 ^ 59
def prefixEnd_2417815 : Nat := 4983230072969 + 3 ^ 40 * 2417815 * 2
def baseEnd_2417815 : Nat := 413833742883521007131059

theorem tailTrace_2417815 : CollatzResearch.WordTrace tailWord_2417815 prefixEnd_2417815 413833742883521007131059 := by
  unfold tailWord_2417815
  simp only [CollatzResearch.WordTrace]
  refine ⟨88184957735676659772078899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58789971823784439848052599 88184957735676659772078899)
  ·
    refine ⟨132277436603514989658118349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88184957735676659772078899 132277436603514989658118349)
    ·
      refine ⟨49604038726318121121794381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132277436603514989658118349 49604038726318121121794381)
      ·
        refine ⟨18601514522369295420672893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49604038726318121121794381 18601514522369295420672893)
        ·
          refine ⟨6975567945888485782752335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18601514522369295420672893 6975567945888485782752335)
          ·
            refine ⟨10463351918832728674128503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975567945888485782752335 10463351918832728674128503)
            ·
              refine ⟨15695027878249093011192755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10463351918832728674128503 15695027878249093011192755)
              ·
                refine ⟨23542541817373639516789133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15695027878249093011192755 23542541817373639516789133)
                ·
                  refine ⟨8828453181515114818795925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23542541817373639516789133 8828453181515114818795925)
                  ·
                    refine ⟨413833742883521007131059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8828453181515114818795925 413833742883521007131059)
                    ·
                      rfl

theorem cell23_2417815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_2417815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417815 prefixEnd_2417815 := by exact prefixLift 2417815
  have htrace : WordTrace (prefixWord ++ tailWord_2417815) baseStart_2417815 baseEnd_2417815 := by
    simpa [prefixWord, tailWord_2417815, baseEnd_2417815] using wordTrace_append hprefix tailTrace_2417815
  have hstable : (prefixWord ++ tailWord_2417815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417815).length < 2 ^ (prefixWord ++ tailWord_2417815).sum := by decide
  have hdescent : baseEnd_2417815 < baseStart_2417815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417842 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_2417842 : Nat := 118140960795 + 2417842 * 2 ^ 59
def prefixEnd_2417842 : Nat := 4983230072969 + 3 ^ 40 * 2417842 * 2
def baseEnd_2417842 : Nat := 1241515092628234415755553

theorem tailTrace_2417842 : CollatzResearch.WordTrace tailWord_2417842 prefixEnd_2417842 1241515092628234415755553 := by
  unfold tailWord_2417842
  simp only [CollatzResearch.WordTrace]
  refine ⟨22046485626644710845827945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58790628337719228922207853 22046485626644710845827945)
  ·
    refine ⟨16534864219983533134370959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22046485626644710845827945 16534864219983533134370959)
    ·
      refine ⟨24802296329975299701556439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16534864219983533134370959 24802296329975299701556439)
      ·
        refine ⟨37203444494962949552334659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24802296329975299701556439 37203444494962949552334659)
        ·
          refine ⟨55805166742444424328501989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37203444494962949552334659 55805166742444424328501989)
          ·
            refine ⟨10463468764208329561594123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55805166742444424328501989 10463468764208329561594123)
            ·
              refine ⟨15695203146312494342391185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10463468764208329561594123 15695203146312494342391185)
              ·
                refine ⟨11771402359734370756793389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15695203146312494342391185 11771402359734370756793389)
                ·
                  refine ⟨4414275884900389033797521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11771402359734370756793389 4414275884900389033797521)
                  ·
                    refine ⟨3310706913675291775348141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4414275884900389033797521 3310706913675291775348141)
                    ·
                      refine ⟨1241515092628234415755553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3310706913675291775348141 1241515092628234415755553)
                      ·
                        rfl

theorem cell23_2417842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_2417842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417842 prefixEnd_2417842 := by exact prefixLift 2417842
  have htrace : WordTrace (prefixWord ++ tailWord_2417842) baseStart_2417842 baseEnd_2417842 := by
    simpa [prefixWord, tailWord_2417842, baseEnd_2417842] using wordTrace_append hprefix tailTrace_2417842
  have hstable : (prefixWord ++ tailWord_2417842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417842).length < 2 ^ (prefixWord ++ tailWord_2417842).sum := by decide
  have hdescent : baseEnd_2417842 < baseStart_2417842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417852 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2417852 : Nat := 118140960795 + 2417852 * 2 ^ 59
def prefixEnd_2417852 : Nat := 4983230072969 + 3 ^ 40 * 2417852 * 2
def baseEnd_2417852 : Nat := 1241520227434779376630507

theorem tailTrace_2417852 : CollatzResearch.WordTrace tailWord_2417852 prefixEnd_2417852 1241520227434779376630507 := by
  unfold tailWord_2417852
  simp only [CollatzResearch.WordTrace]
  refine ⟨44093153618271307545587905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58790871491028410060783873 44093153618271307545587905)
  ·
    refine ⟨33069865213703480659190929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44093153618271307545587905 33069865213703480659190929)
    ·
      refine ⟨24802398910277610494393197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33069865213703480659190929 24802398910277610494393197)
      ·
        refine ⟨9300899591354103935397449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24802398910277610494393197 9300899591354103935397449)
        ·
          refine ⟨6975674693515577951548087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9300899591354103935397449 6975674693515577951548087)
          ·
            refine ⟨10463512040273366927322131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975674693515577951548087 10463512040273366927322131)
            ·
              refine ⟨15695268060410050390983197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10463512040273366927322131 15695268060410050390983197)
              ·
                refine ⟨5885725522653768896618699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15695268060410050390983197 5885725522653768896618699)
                ·
                  refine ⟨8828588283980653344928049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5885725522653768896618699 8828588283980653344928049)
                  ·
                    refine ⟨6621441212985490008696037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8828588283980653344928049 6621441212985490008696037)
                    ·
                      refine ⟨1241520227434779376630507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6621441212985490008696037 1241520227434779376630507)
                      ·
                        rfl

theorem cell23_2417852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2417852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417852 prefixEnd_2417852 := by exact prefixLift 2417852
  have htrace : WordTrace (prefixWord ++ tailWord_2417852) baseStart_2417852 baseEnd_2417852 := by
    simpa [prefixWord, tailWord_2417852, baseEnd_2417852] using wordTrace_append hprefix tailTrace_2417852
  have hstable : (prefixWord ++ tailWord_2417852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417852).length < 2 ^ (prefixWord ++ tailWord_2417852).sum := by decide
  have hdescent : baseEnd_2417852 < baseStart_2417852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417856 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 3, 2, 2]
def baseStart_2417856 : Nat := 118140960795 + 2417856 * 2 ^ 59
def prefixEnd_2417856 : Nat := 4983230072969 + 3 ^ 40 * 2417856 * 2
def baseEnd_2417856 : Nat := 1241522281357397360980489

theorem tailTrace_2417856 : CollatzResearch.WordTrace tailWord_2417856 prefixEnd_2417856 1241522281357397360980489 := by
  unfold tailWord_2417856
  simp only [CollatzResearch.WordTrace]
  refine ⟨44093226564264061887160711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58790968752352082516214281 44093226564264061887160711)
  ·
    refine ⟨66139839846396092830741067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44093226564264061887160711 66139839846396092830741067)
    ·
      refine ⟨99209759769594139246111601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66139839846396092830741067 99209759769594139246111601)
      ·
        refine ⟨74407319827195604434583701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99209759769594139246111601 74407319827195604434583701)
        ·
          refine ⟨3487843116899793957871111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74407319827195604434583701 3487843116899793957871111)
          ·
            refine ⟨5231764675349690936806667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487843116899793957871111 5231764675349690936806667)
            ·
              refine ⟨7847647013024536405210001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231764675349690936806667 7847647013024536405210001)
              ·
                refine ⟨5885735259768402303907501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7847647013024536405210001 5885735259768402303907501)
                ·
                  refine ⟨2207150722413150863965313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5885735259768402303907501 2207150722413150863965313)
                  ·
                    refine ⟨1655363041809863147973985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2207150722413150863965313 1655363041809863147973985)
                    ·
                      refine ⟨1241522281357397360980489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655363041809863147973985 1241522281357397360980489)
                      ·
                        rfl

theorem cell23_2417856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_2417856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417856 prefixEnd_2417856 := by exact prefixLift 2417856
  have htrace : WordTrace (prefixWord ++ tailWord_2417856) baseStart_2417856 baseEnd_2417856 := by
    simpa [prefixWord, tailWord_2417856, baseEnd_2417856] using wordTrace_append hprefix tailTrace_2417856
  have hstable : (prefixWord ++ tailWord_2417856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417856).length < 2 ^ (prefixWord ++ tailWord_2417856).sum := by decide
  have hdescent : baseEnd_2417856 < baseStart_2417856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417889 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_2417889 : Nat := 118140960795 + 2417889 * 2 ^ 59
def prefixEnd_2417889 : Nat := 4983230072969 + 3 ^ 40 * 2417889 * 2
def baseEnd_2417889 : Nat := 1241539226218995731867837

theorem tailTrace_2417889 : CollatzResearch.WordTrace tailWord_2417889 prefixEnd_2417889 1241539226218995731867837 := by
  unfold tailWord_2417889
  simp only [CollatzResearch.WordTrace]
  refine ⟨88187656737408570410272721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58791771158272380273515147 88187656737408570410272721)
  ·
    refine ⟨66140742553056427807704541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88187656737408570410272721 66140742553056427807704541)
    ·
      refine ⟨24802778457396160427889203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66140742553056427807704541 24802778457396160427889203)
      ·
        refine ⟨37204167686094240641833805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24802778457396160427889203 37204167686094240641833805)
        ·
          refine ⟨13951562882285340240687677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37204167686094240641833805 13951562882285340240687677)
          ·
            refine ⟨5231836080857002590257879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13951562882285340240687677 5231836080857002590257879)
            ·
              refine ⟨7847754121285503885386819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231836080857002590257879 7847754121285503885386819)
              ·
                refine ⟨11771631181928255828080229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7847754121285503885386819 11771631181928255828080229)
                ·
                  refine ⟨2207180846611547967765043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11771631181928255828080229 2207180846611547967765043)
                  ·
                    refine ⟨3310771269917321951647565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2207180846611547967765043 3310771269917321951647565)
                    ·
                      refine ⟨1241539226218995731867837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3310771269917321951647565 1241539226218995731867837)
                      ·
                        rfl

theorem cell23_2417889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_2417889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417889 prefixEnd_2417889 := by exact prefixLift 2417889
  have htrace : WordTrace (prefixWord ++ tailWord_2417889) baseStart_2417889 baseEnd_2417889 := by
    simpa [prefixWord, tailWord_2417889, baseEnd_2417889] using wordTrace_append hprefix tailTrace_2417889
  have hstable : (prefixWord ++ tailWord_2417889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417889).length < 2 ^ (prefixWord ++ tailWord_2417889).sum := by decide
  have hdescent : baseEnd_2417889 < baseStart_2417889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417906 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2417906 : Nat := 118140960795 + 2417906 * 2 ^ 59
def prefixEnd_2417906 : Nat := 4983230072969 + 3 ^ 40 * 2417906 * 2
def baseEnd_2417906 : Nat := 1241547955390122165355259

theorem tailTrace_2417906 : CollatzResearch.WordTrace tailWord_2417906 prefixEnd_2417906 1241547955390122165355259 := by
  unfold tailWord_2417906
  simp only [CollatzResearch.WordTrace]
  refine ⟨22047069194586745578410393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58792184518897988209094381 22047069194586745578410393)
  ·
    refine ⟨16535301895940059183807795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22047069194586745578410393 16535301895940059183807795)
    ·
      refine ⟨24802952843910088775711693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16535301895940059183807795 24802952843910088775711693)
      ·
        refine ⟨9301107316466283290891885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24802952843910088775711693 9301107316466283290891885)
        ·
          refine ⟨3487915243674856234084457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9301107316466283290891885 3487915243674856234084457)
          ·
            refine ⟨2615936432756142175563343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3487915243674856234084457 2615936432756142175563343)
            ·
              refine ⟨3923904649134213263345015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615936432756142175563343 3923904649134213263345015)
              ·
                refine ⟨5885856973701319895017523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923904649134213263345015 5885856973701319895017523)
                ·
                  refine ⟨8828785460551979842526285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5885856973701319895017523 8828785460551979842526285)
                  ·
                    refine ⟨3310794547706992440947357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8828785460551979842526285 3310794547706992440947357)
                    ·
                      refine ⟨1241547955390122165355259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3310794547706992440947357 1241547955390122165355259)
                      ·
                        rfl

theorem cell23_2417906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2417906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417906 prefixEnd_2417906 := by exact prefixLift 2417906
  have htrace : WordTrace (prefixWord ++ tailWord_2417906) baseStart_2417906 baseEnd_2417906 := by
    simpa [prefixWord, tailWord_2417906, baseEnd_2417906] using wordTrace_append hprefix tailTrace_2417906
  have hstable : (prefixWord ++ tailWord_2417906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417906).length < 2 ^ (prefixWord ++ tailWord_2417906).sum := by decide
  have hdescent : baseEnd_2417906 < baseStart_2417906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417929 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 6, 2, 2]
def baseStart_2417929 : Nat := 118140960795 + 2417929 * 2 ^ 59
def prefixEnd_2417929 : Nat := 4983230072969 + 3 ^ 40 * 2417929 * 2
def baseEnd_2417929 : Nat := 1241559765445175575367653

theorem tailTrace_2417929 : CollatzResearch.WordTrace tailWord_2417929 prefixEnd_2417929 1241559765445175575367653 := by
  unfold tailWord_2417929
  simp only [CollatzResearch.WordTrace]
  refine ⟨88189115657263657241728841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58792743771509104827819227 88189115657263657241728841)
  ·
    refine ⟨66141836742947742931296631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88189115657263657241728841 66141836742947742931296631)
    ·
      refine ⟨99212755114421614396944947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66141836742947742931296631 99212755114421614396944947)
      ·
        refine ⟨148819132671632421595417421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99212755114421614396944947 148819132671632421595417421)
        ·
          refine ⟨55807174751862158098281533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148819132671632421595417421 55807174751862158098281533)
          ·
            refine ⟨20927690531948309286855575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55807174751862158098281533 20927690531948309286855575)
            ·
              refine ⟨31391535797922463930283363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20927690531948309286855575 31391535797922463930283363)
              ·
                refine ⟨47087303696883695895425045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31391535797922463930283363 47087303696883695895425045)
                ·
                  refine ⟨2207217360791423245098049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47087303696883695895425045 2207217360791423245098049)
                  ·
                    refine ⟨1655413020593567433823537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2207217360791423245098049 1655413020593567433823537)
                    ·
                      refine ⟨1241559765445175575367653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655413020593567433823537 1241559765445175575367653)
                      ·
                        rfl

theorem cell23_2417929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 2, 2].length) (baseStart_2417929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417929 prefixEnd_2417929 := by exact prefixLift 2417929
  have htrace : WordTrace (prefixWord ++ tailWord_2417929) baseStart_2417929 baseEnd_2417929 := by
    simpa [prefixWord, tailWord_2417929, baseEnd_2417929] using wordTrace_append hprefix tailTrace_2417929
  have hstable : (prefixWord ++ tailWord_2417929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417929).length < 2 ^ (prefixWord ++ tailWord_2417929).sum := by decide
  have hdescent : baseEnd_2417929 < baseStart_2417929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417932 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2417932 : Nat := 118140960795 + 2417932 * 2 ^ 59
def prefixEnd_2417932 : Nat := 4983230072969 + 3 ^ 40 * 2417932 * 2
def baseEnd_2417932 : Nat := 1241561305887139063630139

theorem tailTrace_2417932 : CollatzResearch.WordTrace tailWord_2417932 prefixEnd_2417932 1241561305887139063630139 := by
  unfold tailWord_2417932
  simp only [CollatzResearch.WordTrace]
  refine ⟨44094612538126394377044025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58792816717501859169392033 44094612538126394377044025)
  ·
    refine ⟨33070959403594795782783019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44094612538126394377044025 33070959403594795782783019)
    ·
      refine ⟨49606439105392193674174529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33070959403594795782783019 49606439105392193674174529)
      ·
        refine ⟨37204829329044145255630897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49606439105392193674174529 37204829329044145255630897)
        ·
          refine ⟨27903621996783108941723173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37204829329044145255630897 27903621996783108941723173)
          ·
            refine ⟨5231929124396832926573095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27903621996783108941723173 5231929124396832926573095)
            ·
              refine ⟨7847893686595249389859643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5231929124396832926573095 7847893686595249389859643)
              ·
                refine ⟨11771840529892874084789465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7847893686595249389859643 11771840529892874084789465)
                ·
                  refine ⟨8828880397419655563592099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11771840529892874084789465 8828880397419655563592099)
                  ·
                    refine ⟨13243320596129483345388149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8828880397419655563592099 13243320596129483345388149)
                    ·
                      refine ⟨1241561305887139063630139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13243320596129483345388149 1241561305887139063630139)
                      ·
                        rfl

theorem cell23_2417932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2417932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417932 prefixEnd_2417932 := by exact prefixLift 2417932
  have htrace : WordTrace (prefixWord ++ tailWord_2417932) baseStart_2417932 baseEnd_2417932 := by
    simpa [prefixWord, tailWord_2417932, baseEnd_2417932] using wordTrace_append hprefix tailTrace_2417932
  have hstable : (prefixWord ++ tailWord_2417932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417932).length < 2 ^ (prefixWord ++ tailWord_2417932).sum := by decide
  have hdescent : baseEnd_2417932 < baseStart_2417932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417946 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2]
def baseStart_2417946 : Nat := 118140960795 + 2417946 * 2 ^ 59
def prefixEnd_2417946 : Nat := 4983230072969 + 3 ^ 40 * 2417946 * 2
def baseEnd_2417946 : Nat := 1241568494616302008855075

theorem tailTrace_2417946 : CollatzResearch.WordTrace tailWord_2417946 prefixEnd_2417946 1241568494616302008855075 := by
  unfold tailWord_2417946
  simp only [CollatzResearch.WordTrace]
  refine ⟨22047433924550517286274423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58793157132134712763398461 22047433924550517286274423)
  ·
    refine ⟨33071150886825775929411635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22047433924550517286274423 33071150886825775929411635)
    ·
      refine ⟨49606726330238663894117453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33071150886825775929411635 49606726330238663894117453)
      ·
        refine ⟨18602522373839498960294045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49606726330238663894117453 18602522373839498960294045)
        ·
          refine ⟨6975945890189812110110267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18602522373839498960294045 6975945890189812110110267)
          ·
            refine ⟨10463918835284718165165401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6975945890189812110110267 10463918835284718165165401)
            ·
              refine ⟨7847939126463538623874051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10463918835284718165165401 7847939126463538623874051)
              ·
                refine ⟨11771908689695307935811077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7847939126463538623874051 11771908689695307935811077)
                ·
                  refine ⟨2207232879317870237964577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11771908689695307935811077 2207232879317870237964577)
                  ·
                    refine ⟨1655424659488402678473433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2207232879317870237964577 1655424659488402678473433)
                    ·
                      refine ⟨1241568494616302008855075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655424659488402678473433 1241568494616302008855075)
                      ·
                        rfl

theorem cell23_2417946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_2417946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417946 prefixEnd_2417946 := by exact prefixLift 2417946
  have htrace : WordTrace (prefixWord ++ tailWord_2417946) baseStart_2417946 baseEnd_2417946 := by
    simpa [prefixWord, tailWord_2417946, baseEnd_2417946] using wordTrace_append hprefix tailTrace_2417946
  have hstable : (prefixWord ++ tailWord_2417946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417946).length < 2 ^ (prefixWord ++ tailWord_2417946).sum := by decide
  have hdescent : baseEnd_2417946 < baseStart_2417946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417995 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 4, 8]
def baseStart_2417995 : Nat := 118140960795 + 2417995 * 2 ^ 59
def prefixEnd_2417995 : Nat := 4983230072969 + 3 ^ 40 * 2417995 * 2
def baseEnd_2417995 : Nat := 413864551722790772380783

theorem tailTrace_2417995 : CollatzResearch.WordTrace tailWord_2417995 prefixEnd_2417995 413864551722790772380783 := by
  unfold tailWord_2417995
  simp only [CollatzResearch.WordTrace]
  refine ⟨88191522875024550513631439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58794348583349700342420959 88191522875024550513631439)
  ·
    refine ⟨132287284312536825770447159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88191522875024550513631439 132287284312536825770447159)
    ·
      refine ⟨198430926468805238655670739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132287284312536825770447159 198430926468805238655670739)
      ·
        refine ⟨297646389703207857983506109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198430926468805238655670739 297646389703207857983506109)
        ·
          refine ⟨111617396138702946743814791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297646389703207857983506109 111617396138702946743814791)
          ·
            refine ⟨167426094208054420115722187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111617396138702946743814791 167426094208054420115722187)
            ·
              refine ⟨251139141312081630173583281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167426094208054420115722187 251139141312081630173583281)
              ·
                refine ⟨188354355984061222630187461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251139141312081630173583281 188354355984061222630187461)
                ·
                  refine ⟨35316441747011479243160149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188354355984061222630187461 35316441747011479243160149)
                  ·
                    refine ⟨413864551722790772380783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35316441747011479243160149 413864551722790772380783)
                    ·
                      rfl

theorem cell23_2417995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 8].length) (baseStart_2417995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417995 prefixEnd_2417995 := by exact prefixLift 2417995
  have htrace : WordTrace (prefixWord ++ tailWord_2417995) baseStart_2417995 baseEnd_2417995 := by
    simpa [prefixWord, tailWord_2417995, baseEnd_2417995] using wordTrace_append hprefix tailTrace_2417995
  have hstable : (prefixWord ++ tailWord_2417995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417995).length < 2 ^ (prefixWord ++ tailWord_2417995).sum := by decide
  have hdescent : baseEnd_2417995 < baseStart_2417995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2417997 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2417997 : Nat := 118140960795 + 2417997 * 2 ^ 59
def prefixEnd_2417997 : Nat := 4983230072969 + 3 ^ 40 * 2417997 * 2
def baseEnd_2417997 : Nat := 1241594682129681309317341

theorem tailTrace_2417997 : CollatzResearch.WordTrace tailWord_2417997 prefixEnd_2417997 1241594682129681309317341 := by
  unfold tailWord_2417997
  simp only [CollatzResearch.WordTrace]
  refine ⟨88191595821017304855204245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58794397214011536570136163 88191595821017304855204245)
  ·
    refine ⟨4133981054110186165087699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88191595821017304855204245 4133981054110186165087699)
    ·
      refine ⟨6200971581165279247631549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4133981054110186165087699 6200971581165279247631549)
      ·
        refine ⟨2325364342936979717861831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6200971581165279247631549 2325364342936979717861831)
        ·
          refine ⟨3488046514405469576792747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325364342936979717861831 3488046514405469576792747)
          ·
            refine ⟨5232069771608204365189121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488046514405469576792747 5232069771608204365189121)
            ·
              refine ⟨3924052328706153273891841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5232069771608204365189121 3924052328706153273891841)
              ·
                refine ⟨2943039246529614955418881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3924052328706153273891841 2943039246529614955418881)
                ·
                  refine ⟨2207279434897211216564161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2943039246529614955418881 2207279434897211216564161)
                  ·
                    refine ⟨1655459576172908412423121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2207279434897211216564161 1655459576172908412423121)
                    ·
                      refine ⟨1241594682129681309317341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655459576172908412423121 1241594682129681309317341)
                      ·
                        rfl

theorem cell23_2417997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2417997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2417997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2417997 prefixEnd_2417997 := by exact prefixLift 2417997
  have htrace : WordTrace (prefixWord ++ tailWord_2417997) baseStart_2417997 baseEnd_2417997 := by
    simpa [prefixWord, tailWord_2417997, baseEnd_2417997] using wordTrace_append hprefix tailTrace_2417997
  have hstable : (prefixWord ++ tailWord_2417997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2417997).length < 2 ^ (prefixWord ++ tailWord_2417997).sum := by decide
  have hdescent : baseEnd_2417997 < baseStart_2417997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2417997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418002 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2418002 : Nat := 118140960795 + 2418002 * 2 ^ 59
def prefixEnd_2418002 : Nat := 4983230072969 + 3 ^ 40 * 2418002 * 2
def baseEnd_2418002 : Nat := 1241597249532953789754817

theorem tailTrace_2418002 : CollatzResearch.WordTrace tailWord_2418002 prefixEnd_2418002 1241597249532953789754817 := by
  unfold tailWord_2418002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22047944546499797677284065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58794518790666127139424173 22047944546499797677284065)
  ·
    refine ⟨16535958409874848257963049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22047944546499797677284065 16535958409874848257963049)
    ·
      refine ⟨12401968807406136193472287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16535958409874848257963049 12401968807406136193472287)
      ·
        refine ⟨18602953211109204290208431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12401968807406136193472287 18602953211109204290208431)
        ·
          refine ⟨27904429816663806435312647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18602953211109204290208431 27904429816663806435312647)
          ·
            refine ⟨41856644724995709652968971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27904429816663806435312647 41856644724995709652968971)
            ·
              refine ⟨62784967087493564479453457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41856644724995709652968971 62784967087493564479453457)
              ·
                refine ⟨47088725315620173359590093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62784967087493564479453457 47088725315620173359590093)
                ·
                  refine ⟨17658271993357565009846285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47088725315620173359590093 17658271993357565009846285)
                  ·
                    refine ⟨6621851997509086878692357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17658271993357565009846285 6621851997509086878692357)
                    ·
                      refine ⟨1241597249532953789754817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6621851997509086878692357 1241597249532953789754817)
                      ·
                        rfl

theorem cell23_2418002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2418002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418002 prefixEnd_2418002 := by exact prefixLift 2418002
  have htrace : WordTrace (prefixWord ++ tailWord_2418002) baseStart_2418002 baseEnd_2418002 := by
    simpa [prefixWord, tailWord_2418002, baseEnd_2418002] using wordTrace_append hprefix tailTrace_2418002
  have hstable : (prefixWord ++ tailWord_2418002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418002).length < 2 ^ (prefixWord ++ tailWord_2418002).sum := by decide
  have hdescent : baseEnd_2418002 < baseStart_2418002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418019 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 1, 6, 2]
def baseStart_2418019 : Nat := 118140960795 + 2418019 * 2 ^ 59
def prefixEnd_2418019 : Nat := 4983230072969 + 3 ^ 40 * 2418019 * 2
def baseEnd_2418019 : Nat := 1241605978704080223242239

theorem tailTrace_2418019 : CollatzResearch.WordTrace tailWord_2418019 prefixEnd_2418019 1241605978704080223242239 := by
  unfold tailWord_2418019
  simp only [CollatzResearch.WordTrace]
  refine ⟨88192398226937602612505111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58794932151291735075003407 88192398226937602612505111)
  ·
    refine ⟨132288597340406403918757667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88192398226937602612505111 132288597340406403918757667)
    ·
      refine ⟨198432896010609605878136501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132288597340406403918757667 198432896010609605878136501)
      ·
        refine ⟨18603084000994650551075297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198432896010609605878136501 18603084000994650551075297)
        ·
          refine ⟨13952313000745987913306473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18603084000994650551075297 13952313000745987913306473)
          ·
            refine ⟨10464234750559490934979855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13952313000745987913306473 10464234750559490934979855)
            ·
              refine ⟨15696352125839236402469783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10464234750559490934979855 15696352125839236402469783)
              ·
                refine ⟨23544528188758854603704675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15696352125839236402469783 23544528188758854603704675)
                ·
                  refine ⟨35316792283138281905557013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23544528188758854603704675 35316792283138281905557013)
                  ·
                    refine ⟨1655474638272106964322985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35316792283138281905557013 1655474638272106964322985)
                    ·
                      refine ⟨1241605978704080223242239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655474638272106964322985 1241605978704080223242239)
                      ·
                        rfl

theorem cell23_2418019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_2418019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418019 prefixEnd_2418019 := by exact prefixLift 2418019
  have htrace : WordTrace (prefixWord ++ tailWord_2418019) baseStart_2418019 baseEnd_2418019 := by
    simpa [prefixWord, tailWord_2418019, baseEnd_2418019] using wordTrace_append hprefix tailTrace_2418019
  have hstable : (prefixWord ++ tailWord_2418019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418019).length < 2 ^ (prefixWord ++ tailWord_2418019).sum := by decide
  have hdescent : baseEnd_2418019 < baseStart_2418019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418029 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_2418029 : Nat := 118140960795 + 2418029 * 2 ^ 59
def prefixEnd_2418029 : Nat := 4983230072969 + 3 ^ 40 * 2418029 * 2
def baseEnd_2418029 : Nat := 413870371170208394705731

theorem tailTrace_2418029 : CollatzResearch.WordTrace tailWord_2418029 prefixEnd_2418029 413870371170208394705731 := by
  unfold tailWord_2418029
  simp only [CollatzResearch.WordTrace]
  refine ⟨88192762956901374320369141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58795175304600916213579427 88192762956901374320369141)
  ·
    refine ⟨8268071527209503842534607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88192762956901374320369141 8268071527209503842534607)
    ·
      refine ⟨12402107290814255763801911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8268071527209503842534607 12402107290814255763801911)
      ·
        refine ⟨18603160936221383645702867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12402107290814255763801911 18603160936221383645702867)
        ·
          refine ⟨27904741404332075468554301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18603160936221383645702867 27904741404332075468554301)
          ·
            refine ⟨10464278026624528300707863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27904741404332075468554301 10464278026624528300707863)
            ·
              refine ⟨15696417039936792451061795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10464278026624528300707863 15696417039936792451061795)
              ·
                refine ⟨23544625559905188676592693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15696417039936792451061795 23544625559905188676592693)
                ·
                  refine ⟨2207308646241111438430565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23544625559905188676592693 2207308646241111438430565)
                  ·
                    refine ⟨413870371170208394705731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2207308646241111438430565 413870371170208394705731)
                    ·
                      rfl

theorem cell23_2418029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_2418029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418029 prefixEnd_2418029 := by exact prefixLift 2418029
  have htrace : WordTrace (prefixWord ++ tailWord_2418029) baseStart_2418029 baseEnd_2418029 := by
    simpa [prefixWord, tailWord_2418029, baseEnd_2418029] using wordTrace_append hprefix tailTrace_2418029
  have hstable : (prefixWord ++ tailWord_2418029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418029).length < 2 ^ (prefixWord ++ tailWord_2418029).sum := by decide
  have hdescent : baseEnd_2418029 < baseStart_2418029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418114 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2418114 : Nat := 118140960795 + 2418114 * 2 ^ 59
def prefixEnd_2418114 : Nat := 4983230072969 + 3 ^ 40 * 2418114 * 2
def baseEnd_2418114 : Nat := 413884919788752450518101

theorem tailTrace_2418114 : CollatzResearch.WordTrace tailWord_2418114 prefixEnd_2418114 413884919788752450518101 := by
  unfold tailWord_2418114
  simp only [CollatzResearch.WordTrace]
  refine ⟨22048965790398358459303349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58797242107728955891475597 22048965790398358459303349)
  ·
    refine ⟨2067090542849846105559689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22048965790398358459303349 2067090542849846105559689)
    ·
      refine ⟨1550317907137384579169767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2067090542849846105559689 1550317907137384579169767)
      ·
        refine ⟨2325476860706076868754651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550317907137384579169767 2325476860706076868754651)
        ·
          refine ⟨3488215291059115303131977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325476860706076868754651 3488215291059115303131977)
          ·
            refine ⟨2616161468294336477348983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3488215291059115303131977 2616161468294336477348983)
            ·
              refine ⟨3924242202441504716023475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616161468294336477348983 3924242202441504716023475)
              ·
                refine ⟨5886363303662257074035213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924242202441504716023475 5886363303662257074035213)
                ·
                  refine ⟨2207386238873346402763205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5886363303662257074035213 2207386238873346402763205)
                  ·
                    refine ⟨413884919788752450518101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2207386238873346402763205 413884919788752450518101)
                    ·
                      rfl

theorem cell23_2418114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2418114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418114 prefixEnd_2418114 := by exact prefixLift 2418114
  have htrace : WordTrace (prefixWord ++ tailWord_2418114) baseStart_2418114 baseEnd_2418114 := by
    simpa [prefixWord, tailWord_2418114, baseEnd_2418114] using wordTrace_append hprefix tailTrace_2418114
  have hstable : (prefixWord ++ tailWord_2418114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418114).length < 2 ^ (prefixWord ++ tailWord_2418114).sum := by decide
  have hdescent : baseEnd_2418114 < baseStart_2418114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418119 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 4, 4]
def baseStart_2418119 : Nat := 118140960795 + 2418119 * 2 ^ 59
def prefixEnd_2418119 : Nat := 4983230072969 + 3 ^ 40 * 2418119 * 2
def baseEnd_2418119 : Nat := 413885775589843277330593

theorem tailTrace_2418119 : CollatzResearch.WordTrace tailWord_2418119 prefixEnd_2418119 413885775589843277330593 := by
  unfold tailWord_2418119
  simp only [CollatzResearch.WordTrace]
  refine ⟨88196045526575319691145411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58797363684383546460763607 88196045526575319691145411)
  ·
    refine ⟨132294068289862979536718117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88196045526575319691145411 132294068289862979536718117)
    ·
      refine ⟨24805137804349308663134647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132294068289862979536718117 24805137804349308663134647)
      ·
        refine ⟨37207706706523962994701971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24805137804349308663134647 37207706706523962994701971)
        ·
          refine ⟨55811560059785944492052957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37207706706523962994701971 55811560059785944492052957)
          ·
            refine ⟨20929335022419729184519859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55811560059785944492052957 20929335022419729184519859)
            ·
              refine ⟨31394002533629593776779789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20929335022419729184519859 31394002533629593776779789)
              ·
                refine ⟨11772750950111097666292421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31394002533629593776779789 11772750950111097666292421)
                ·
                  refine ⟨2207390803145830812429829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11772750950111097666292421 2207390803145830812429829)
                  ·
                    refine ⟨413885775589843277330593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2207390803145830812429829 413885775589843277330593)
                    ·
                      rfl

theorem cell23_2418119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_2418119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418119 prefixEnd_2418119 := by exact prefixLift 2418119
  have htrace : WordTrace (prefixWord ++ tailWord_2418119) baseStart_2418119 baseEnd_2418119 := by
    simpa [prefixWord, tailWord_2418119, baseEnd_2418119] using wordTrace_append hprefix tailTrace_2418119
  have hstable : (prefixWord ++ tailWord_2418119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418119).length < 2 ^ (prefixWord ++ tailWord_2418119).sum := by decide
  have hdescent : baseEnd_2418119 < baseStart_2418119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418120 : List Nat := [2, 1, 3, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_2418120 : Nat := 118140960795 + 2418120 * 2 ^ 59
def prefixEnd_2418120 : Nat := 4983230072969 + 3 ^ 40 * 2418120 * 2
def baseEnd_2418120 : Nat := 1241657840250184328079275

theorem tailTrace_2418120 : CollatzResearch.WordTrace tailWord_2418120 prefixEnd_2418120 1241657840250184328079275 := by
  unfold tailWord_2418120
  simp only [CollatzResearch.WordTrace]
  refine ⟨44098040999785848430965907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58797387999714464574621209 44098040999785848430965907)
  ·
    refine ⟨66147061499678772646448861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44098040999785848430965907 66147061499678772646448861)
    ·
      refine ⟨24805148062379539742418323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66147061499678772646448861 24805148062379539742418323)
      ·
        refine ⟨37207722093569309613627485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24805148062379539742418323 37207722093569309613627485)
        ·
          refine ⟨13952895785088491105110307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37207722093569309613627485 13952895785088491105110307)
          ·
            refine ⟨20929343677632736657665461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13952895785088491105110307 20929343677632736657665461)
            ·
              refine ⟨1962125969778069061656137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20929343677632736657665461 1962125969778069061656137)
              ·
                refine ⟨1471594477333551796242103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1962125969778069061656137 1471594477333551796242103)
                ·
                  refine ⟨2207391716000327694363155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471594477333551796242103 2207391716000327694363155)
                  ·
                    refine ⟨3311087574000491541544733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2207391716000327694363155 3311087574000491541544733)
                    ·
                      refine ⟨1241657840250184328079275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3311087574000491541544733 1241657840250184328079275)
                      ·
                        rfl

theorem cell23_2418120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_2418120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418120 prefixEnd_2418120 := by exact prefixLift 2418120
  have htrace : WordTrace (prefixWord ++ tailWord_2418120) baseStart_2418120 baseEnd_2418120 := by
    simpa [prefixWord, tailWord_2418120, baseEnd_2418120] using wordTrace_append hprefix tailTrace_2418120
  have hstable : (prefixWord ++ tailWord_2418120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418120).length < 2 ^ (prefixWord ++ tailWord_2418120).sum := by decide
  have hdescent : baseEnd_2418120 < baseStart_2418120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418149 : List Nat := [1, 3, 1, 5, 1, 1, 2, 9]
def baseStart_2418149 : Nat := 118140960795 + 2418149 * 2 ^ 59
def prefixEnd_2418149 : Nat := 4983230072969 + 3 ^ 40 * 2418149 * 2
def baseEnd_2418149 : Nat := 45987878932932026467283

theorem tailTrace_2418149 : CollatzResearch.WordTrace tailWord_2418149 prefixEnd_2418149 45987878932932026467283 := by
  unfold tailWord_2418149
  simp only [CollatzResearch.WordTrace]
  refine ⟨88197139716466634814737501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58798093144311089876491667 88197139716466634814737501)
  ·
    refine ⟨33073927393674988055526563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88197139716466634814737501 33073927393674988055526563)
    ·
      refine ⟨49610891090512482083289845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33073927393674988055526563 49610891090512482083289845)
      ·
        refine ⟨4651021039735545195308423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49610891090512482083289845 4651021039735545195308423)
        ·
          refine ⟨6976531559603317792962635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651021039735545195308423 6976531559603317792962635)
          ·
            refine ⟨10464797339404976689443953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6976531559603317792962635 10464797339404976689443953)
            ·
              refine ⟨7848598004553732517082965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10464797339404976689443953 7848598004553732517082965)
              ·
                refine ⟨45987878932932026467283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7848598004553732517082965 45987878932932026467283)
                ·
                  rfl

theorem cell23_2418149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 9].length) (baseStart_2418149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418149 prefixEnd_2418149 := by exact prefixLift 2418149
  have htrace : WordTrace (prefixWord ++ tailWord_2418149) baseStart_2418149 baseEnd_2418149 := by
    simpa [prefixWord, tailWord_2418149, baseEnd_2418149] using wordTrace_append hprefix tailTrace_2418149
  have hstable : (prefixWord ++ tailWord_2418149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418149).length < 2 ^ (prefixWord ++ tailWord_2418149).sum := by decide
  have hdescent : baseEnd_2418149 < baseStart_2418149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418159 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 3]
def baseStart_2418159 : Nat := 118140960795 + 2418159 * 2 ^ 59
def prefixEnd_2418159 : Nat := 4983230072969 + 3 ^ 40 * 2418159 * 2
def baseEnd_2418159 : Nat := 1241677865995709675491595

theorem tailTrace_2418159 : CollatzResearch.WordTrace tailWord_2418159 prefixEnd_2418159 1241677865995709675491595 := by
  unfold tailWord_2418159
  simp only [CollatzResearch.WordTrace]
  refine ⟨88197504446430406522601531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58798336297620271015067687 88197504446430406522601531)
  ·
    refine ⟨132296256669645609783902297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88197504446430406522601531 132296256669645609783902297)
    ·
      refine ⟨99222192502234207337926723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132296256669645609783902297 99222192502234207337926723)
      ·
        refine ⟨148833288753351311006890085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99222192502234207337926723 148833288753351311006890085)
        ·
          refine ⟨27906241641253370813791891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148833288753351311006890085 27906241641253370813791891)
          ·
            refine ⟨41859362461880056220687837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27906241641253370813791891 41859362461880056220687837)
            ·
              refine ⟨15697260923205021082757939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41859362461880056220687837 15697260923205021082757939)
              ·
                refine ⟨23545891384807531624136909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15697260923205021082757939 23545891384807531624136909)
                ·
                  refine ⟨8829709269302824359051341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23545891384807531624136909 8829709269302824359051341)
                  ·
                    refine ⟨3311140975988559134644253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8829709269302824359051341 3311140975988559134644253)
                    ·
                      refine ⟨1241677865995709675491595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3311140975988559134644253 1241677865995709675491595)
                      ·
                        rfl

theorem cell23_2418159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 3].length) (baseStart_2418159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418159 prefixEnd_2418159 := by exact prefixLift 2418159
  have htrace : WordTrace (prefixWord ++ tailWord_2418159) baseStart_2418159 baseEnd_2418159 := by
    simpa [prefixWord, tailWord_2418159, baseEnd_2418159] using wordTrace_append hprefix tailTrace_2418159
  have hstable : (prefixWord ++ tailWord_2418159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418159).length < 2 ^ (prefixWord ++ tailWord_2418159).sum := by decide
  have hdescent : baseEnd_2418159 < baseStart_2418159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418177 : List Nat := [1, 2, 4, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_2418177 : Nat := 118140960795 + 2418177 * 2 ^ 59
def prefixEnd_2418177 : Nat := 4983230072969 + 3 ^ 40 * 2418177 * 2
def baseEnd_2418177 : Nat := 1241687108647490605066513

theorem tailTrace_2418177 : CollatzResearch.WordTrace tailWord_2418177 prefixEnd_2418177 1241687108647490605066513 := by
  unfold tailWord_2418177
  simp only [CollatzResearch.WordTrace]
  refine ⟨88198160960365195596756785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58798773973576797064504523 88198160960365195596756785)
  ·
    refine ⟨66148620720273896697567589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88198160960365195596756785 66148620720273896697567589)
    ·
      refine ⟨12402866385051355630793923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66148620720273896697567589 12402866385051355630793923)
      ·
        refine ⟨18604299577577033446190885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12402866385051355630793923 18604299577577033446190885)
        ·
          refine ⟨3488306170795693771160791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18604299577577033446190885 3488306170795693771160791)
          ·
            refine ⟨5232459256193540656741187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3488306170795693771160791 5232459256193540656741187)
            ·
              refine ⟨7848688884290310985111781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5232459256193540656741187 7848688884290310985111781)
              ·
                refine ⟨1471629165804433309708459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7848688884290310985111781 1471629165804433309708459)
                ·
                  refine ⟨2207443748706649964562689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471629165804433309708459 2207443748706649964562689)
                  ·
                    refine ⟨1655582811529987473422017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2207443748706649964562689 1655582811529987473422017)
                    ·
                      refine ⟨1241687108647490605066513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655582811529987473422017 1241687108647490605066513)
                      ·
                        rfl

theorem cell23_2418177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_2418177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418177 prefixEnd_2418177 := by exact prefixLift 2418177
  have htrace : WordTrace (prefixWord ++ tailWord_2418177) baseStart_2418177 baseEnd_2418177 := by
    simpa [prefixWord, tailWord_2418177, baseEnd_2418177] using wordTrace_append hprefix tailTrace_2418177
  have hstable : (prefixWord ++ tailWord_2418177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418177).length < 2 ^ (prefixWord ++ tailWord_2418177).sum := by decide
  have hdescent : baseEnd_2418177 < baseStart_2418177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418239 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 7]
def baseStart_2418239 : Nat := 118140960795 + 2418239 * 2 ^ 59
def prefixEnd_2418239 : Nat := 4983230072969 + 3 ^ 40 * 2418239 * 2
def baseEnd_2418239 : Nat := 137968771605341040276803

theorem tailTrace_2418239 : CollatzResearch.WordTrace tailWord_2418239 prefixEnd_2418239 137968771605341040276803 := by
  unfold tailWord_2418239
  simp only [CollatzResearch.WordTrace]
  refine ⟨88200422286140580185513771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58800281524093720123675847 88200422286140580185513771)
  ·
    refine ⟨132300633429210870278270657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88200422286140580185513771 132300633429210870278270657)
    ·
      refine ⟨99225475071908152708702993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132300633429210870278270657 99225475071908152708702993)
      ·
        refine ⟨74419106303931114531527245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99225475071908152708702993 74419106303931114531527245)
        ·
          refine ⟨27907164863974167949322717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74419106303931114531527245 27907164863974167949322717)
          ·
            refine ⟨10465186823990312980996019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27907164863974167949322717 10465186823990312980996019)
            ·
              refine ⟨15697780235985469471494029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10465186823990312980996019 15697780235985469471494029)
              ·
                refine ⟨5886667588494551051810261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15697780235985469471494029 5886667588494551051810261)
                ·
                  refine ⟨137968771605341040276803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5886667588494551051810261 137968771605341040276803)
                  ·
                    rfl

theorem cell23_2418239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 7].length) (baseStart_2418239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418239 prefixEnd_2418239 := by exact prefixLift 2418239
  have htrace : WordTrace (prefixWord ++ tailWord_2418239) baseStart_2418239 baseEnd_2418239 := by
    simpa [prefixWord, tailWord_2418239, baseEnd_2418239] using wordTrace_append hprefix tailTrace_2418239
  have hstable : (prefixWord ++ tailWord_2418239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418239).length < 2 ^ (prefixWord ++ tailWord_2418239).sum := by decide
  have hdescent : baseEnd_2418239 < baseStart_2418239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418290 : List Nat := [3, 2, 1, 2, 3, 2, 3, 2, 5]
def baseStart_2418290 : Nat := 118140960795 + 2418290 * 2 ^ 59
def prefixEnd_2418290 : Nat := 4983230072969 + 3 ^ 40 * 2418290 * 2
def baseEnd_2418290 : Nat := 137971681329049851439277

theorem tailTrace_2418290 : CollatzResearch.WordTrace tailWord_2418290 prefixEnd_2418290 137971681329049851439277 := by
  unfold tailWord_2418290
  simp only [CollatzResearch.WordTrace]
  refine ⟨22050570602238953973905081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58801521605970543930413549 22050570602238953973905081)
  ·
    refine ⟨16537927951679215480428811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22050570602238953973905081 16537927951679215480428811)
    ·
      refine ⟨24806891927518823220643217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16537927951679215480428811 24806891927518823220643217)
      ·
        refine ⟨18605168945639117415482413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24806891927518823220643217 18605168945639117415482413)
        ·
          refine ⟨6976938354614669030805905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18605168945639117415482413 6976938354614669030805905)
          ·
            refine ⟨5232703765961001773104429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6976938354614669030805905 5232703765961001773104429)
            ·
              refine ⟨1962263912235375664914161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5232703765961001773104429 1962263912235375664914161)
              ·
                refine ⟨1471697934176531748685621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1962263912235375664914161 1471697934176531748685621)
                ·
                  refine ⟨137971681329049851439277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1471697934176531748685621 137971681329049851439277)
                  ·
                    rfl

theorem cell23_2418290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_2418290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418290 prefixEnd_2418290 := by exact prefixLift 2418290
  have htrace : WordTrace (prefixWord ++ tailWord_2418290) baseStart_2418290 baseEnd_2418290 := by
    simpa [prefixWord, tailWord_2418290, baseEnd_2418290] using wordTrace_append hprefix tailTrace_2418290
  have hstable : (prefixWord ++ tailWord_2418290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418290).length < 2 ^ (prefixWord ++ tailWord_2418290).sum := by decide
  have hdescent : baseEnd_2418290 < baseStart_2418290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
