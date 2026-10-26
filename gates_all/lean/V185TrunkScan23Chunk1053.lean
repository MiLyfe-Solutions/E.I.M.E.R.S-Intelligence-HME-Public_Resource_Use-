import V185TrunkScan23Chunk1052

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6234182 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_6234182 : Nat := 118140960795 + 6234182 * 2 ^ 59
def prefixEnd_6234182 : Nat := 4983230072969 + 3 ^ 40 * 6234182 * 2
def baseEnd_6234182 : Nat := 1067043951202610989318175

theorem tailTrace_6234182 : CollatzResearch.WordTrace tailWord_6234182 prefixEnd_6234182 1067043951202610989318175 := by
  unfold tailWord_6234182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7105603046894712573891775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151586198333753868243024533 7105603046894712573891775)
  ·
    refine ⟨10658404570342068860837663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7105603046894712573891775 10658404570342068860837663)
    ·
      refine ⟨15987606855513103291256495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10658404570342068860837663 15987606855513103291256495)
      ·
        refine ⟨23981410283269654936884743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15987606855513103291256495 23981410283269654936884743)
        ·
          refine ⟨35972115424904482405327115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23981410283269654936884743 35972115424904482405327115)
          ·
            refine ⟨53958173137356723607990673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35972115424904482405327115 53958173137356723607990673)
            ·
              refine ⟨40468629853017542705993005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53958173137356723607990673 40468629853017542705993005)
              ·
                refine ⟨15175736194881578514747377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40468629853017542705993005 15175736194881578514747377)
                ·
                  refine ⟨11381802146161183886060533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15175736194881578514747377 11381802146161183886060533)
                  ·
                    refine ⟨1067043951202610989318175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11381802146161183886060533 1067043951202610989318175)
                    ·
                      rfl

theorem cell23_6234182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_6234182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234182 prefixEnd_6234182 := by exact prefixLift 6234182
  have htrace : WordTrace (prefixWord ++ tailWord_6234182) baseStart_6234182 baseEnd_6234182 := by
    simpa [prefixWord, tailWord_6234182, baseEnd_6234182] using wordTrace_append hprefix tailTrace_6234182
  have hstable : (prefixWord ++ tailWord_6234182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234182).length < 2 ^ (prefixWord ++ tailWord_6234182).sum := by decide
  have hdescent : baseEnd_6234182 < baseStart_6234182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234208 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 8]
def baseStart_6234208 : Nat := 118140960795 + 6234208 * 2 ^ 59
def prefixEnd_6234208 : Nat := 4983230072969 + 3 ^ 40 * 6234208 * 2
def baseEnd_6234208 : Nat := 355682800456094429581045

theorem tailTrace_6234208 : CollatzResearch.WordTrace tailWord_6234208 prefixEnd_6234208 355682800456094429581045 := by
  unfold tailWord_6234208
  simp only [CollatzResearch.WordTrace]
  refine ⟨113690122899268304402491639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151586830532357739203322185 113690122899268304402491639)
  ·
    refine ⟨170535184348902456603737459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113690122899268304402491639 170535184348902456603737459)
    ·
      refine ⟨255802776523353684905606189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170535184348902456603737459 255802776523353684905606189)
      ·
        refine ⟨95926041196257631839602321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255802776523353684905606189 95926041196257631839602321)
        ·
          refine ⟨71944530897193223879701741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95926041196257631839602321 71944530897193223879701741)
          ·
            refine ⟨26979199086447458954888153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71944530897193223879701741 26979199086447458954888153)
            ·
              refine ⟨20234399314835594216166115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26979199086447458954888153 20234399314835594216166115)
              ·
                refine ⟨30351598972253391324249173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20234399314835594216166115 30351598972253391324249173)
                ·
                  refine ⟨355682800456094429581045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30351598972253391324249173 355682800456094429581045)
                  ·
                    rfl

theorem cell23_6234208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 8].length) (baseStart_6234208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234208 prefixEnd_6234208 := by exact prefixLift 6234208
  have htrace : WordTrace (prefixWord ++ tailWord_6234208) baseStart_6234208 baseEnd_6234208 := by
    simpa [prefixWord, tailWord_6234208, baseEnd_6234208] using wordTrace_append hprefix tailTrace_6234208
  have hstable : (prefixWord ++ tailWord_6234208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234208).length < 2 ^ (prefixWord ++ tailWord_6234208).sum := by decide
  have hdescent : baseEnd_6234208 < baseStart_6234208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234212 : List Nat := [2, 3, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_6234212 : Nat := 118140960795 + 6234212 * 2 ^ 59
def prefixEnd_6234212 : Nat := 4983230072969 + 3 ^ 40 * 6234212 * 2
def baseEnd_6234212 : Nat := 1067049086009155950193129

theorem tailTrace_6234212 : CollatzResearch.WordTrace tailWord_6234212 prefixEnd_6234212 1067049086009155950193129 := by
  unfold tailWord_6234212
  simp only [CollatzResearch.WordTrace]
  refine ⟨113690195845261058744064445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151586927793681411658752593 113690195845261058744064445)
  ·
    refine ⟨42633823441972897029024167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113690195845261058744064445 42633823441972897029024167)
    ·
      refine ⟨63950735162959345543536251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42633823441972897029024167 63950735162959345543536251)
      ·
        refine ⟨95926102744439018315304377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63950735162959345543536251 95926102744439018315304377)
        ·
          refine ⟨71944577058329263736478283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95926102744439018315304377 71944577058329263736478283)
          ·
            refine ⟨107916865587493895604717425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71944577058329263736478283 107916865587493895604717425)
            ·
              refine ⟨80937649190620421703538069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107916865587493895604717425 80937649190620421703538069)
              ·
                refine ⟨3793952305810332267353347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80937649190620421703538069 3793952305810332267353347)
                ·
                  refine ⟨5690928458715498401030021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793952305810332267353347 5690928458715498401030021)
                  ·
                    refine ⟨1067049086009155950193129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5690928458715498401030021 1067049086009155950193129)
                    ·
                      rfl

theorem cell23_6234212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_6234212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234212 prefixEnd_6234212 := by exact prefixLift 6234212
  have htrace : WordTrace (prefixWord ++ tailWord_6234212) baseStart_6234212 baseEnd_6234212 := by
    simpa [prefixWord, tailWord_6234212, baseEnd_6234212] using wordTrace_append hprefix tailTrace_6234212
  have hstable : (prefixWord ++ tailWord_6234212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234212).length < 2 ^ (prefixWord ++ tailWord_6234212).sum := by decide
  have hdescent : baseEnd_6234212 < baseStart_6234212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234263 : List Nat := [1, 1, 3, 3, 5, 1, 2, 2, 1, 4]
def baseStart_6234263 : Nat := 118140960795 + 6234263 * 2 ^ 59
def prefixEnd_6234263 : Nat := 4983230072969 + 3 ^ 40 * 6234263 * 2
def baseEnd_6234263 : Nat := 1067057815180282383680551

theorem tailTrace_6234263 : CollatzResearch.WordTrace tailWord_6234263 prefixEnd_6234263 1067057815180282383680551 := by
  unfold tailWord_6234263
  simp only [CollatzResearch.WordTrace]
  refine ⟨227382251813337353198235443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151588167875558235465490295 227382251813337353198235443)
  ·
    refine ⟨341073377720006029797353165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227382251813337353198235443 341073377720006029797353165)
    ·
      refine ⟨127902516645002261174007437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341073377720006029797353165 127902516645002261174007437)
      ·
        refine ⟨47963443741875847940252789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127902516645002261174007437 47963443741875847940252789)
        ·
          refine ⟨4496572850800860744398699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47963443741875847940252789 4496572850800860744398699)
          ·
            refine ⟨6744859276201291116598049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496572850800860744398699 6744859276201291116598049)
            ·
              refine ⟨5058644457150968337448537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6744859276201291116598049 5058644457150968337448537)
              ·
                refine ⟨3793983342863226253086403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5058644457150968337448537 3793983342863226253086403)
                ·
                  refine ⟨5690975014294839379629605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3793983342863226253086403 5690975014294839379629605)
                  ·
                    refine ⟨1067057815180282383680551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5690975014294839379629605 1067057815180282383680551)
                    ·
                      rfl

theorem cell23_6234263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_6234263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234263 prefixEnd_6234263 := by exact prefixLift 6234263
  have htrace : WordTrace (prefixWord ++ tailWord_6234263) baseStart_6234263 baseEnd_6234263 := by
    simpa [prefixWord, tailWord_6234263, baseEnd_6234263] using wordTrace_append hprefix tailTrace_6234263
  have hstable : (prefixWord ++ tailWord_6234263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234263).length < 2 ^ (prefixWord ++ tailWord_6234263).sum := by decide
  have hdescent : baseEnd_6234263 < baseStart_6234263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234275 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 4, 6, 2]
def baseStart_6234275 : Nat := 118140960795 + 6234275 * 2 ^ 59
def prefixEnd_6234275 : Nat := 4983230072969 + 3 ^ 40 * 6234275 * 2
def baseEnd_6234275 : Nat := 3201179607308701104091597

theorem tailTrace_6234275 : CollatzResearch.WordTrace tailWord_6234275 prefixEnd_6234275 3201179607308701104091597 := by
  unfold tailWord_6234275
  simp only [CollatzResearch.WordTrace]
  refine ⟨227382689489293879247672279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151588459659529252831781519 227382689489293879247672279)
  ·
    refine ⟨341074034233940818871508419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227382689489293879247672279 341074034233940818871508419)
    ·
      refine ⟨511611051350911228307262629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341074034233940818871508419 511611051350911228307262629)
      ·
        refine ⟨95927072128295855307611743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 511611051350911228307262629 95927072128295855307611743)
        ·
          refine ⟨143890608192443782961417615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95927072128295855307611743 143890608192443782961417615)
          ·
            refine ⟨215835912288665674442126423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143890608192443782961417615 215835912288665674442126423)
            ·
              refine ⟨323753868432998511663189635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215835912288665674442126423 323753868432998511663189635)
              ·
                refine ⟨485630802649497767494784453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323753868432998511663189635 485630802649497767494784453)
                ·
                  refine ⟨91055775496780831405272085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485630802649497767494784453 91055775496780831405272085)
                  ·
                    refine ⟨4268239476411601472122129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91055775496780831405272085 4268239476411601472122129)
                    ·
                      refine ⟨3201179607308701104091597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268239476411601472122129 3201179607308701104091597)
                      ·
                        rfl

theorem cell23_6234275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_6234275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234275 prefixEnd_6234275 := by exact prefixLift 6234275
  have htrace : WordTrace (prefixWord ++ tailWord_6234275) baseStart_6234275 baseEnd_6234275 := by
    simpa [prefixWord, tailWord_6234275, baseEnd_6234275] using wordTrace_append hprefix tailTrace_6234275
  have hstable : (prefixWord ++ tailWord_6234275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234275).length < 2 ^ (prefixWord ++ tailWord_6234275).sum := by decide
  have hdescent : baseEnd_6234275 < baseStart_6234275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234298 : List Nat := [3, 1, 1, 1, 2, 2, 2, 11]
def baseStart_6234298 : Nat := 118140960795 + 6234298 * 2 ^ 59
def prefixEnd_6234298 : Nat := 4983230072969 + 3 ^ 40 * 6234298 * 2
def baseEnd_6234298 : Nat := 118562645087546463485333

theorem tailTrace_6234298 : CollatzResearch.WordTrace tailWord_6234298 prefixEnd_6234298 118562645087546463485333 := by
  unfold tailWord_6234298
  simp only [CollatzResearch.WordTrace]
  refine ⟨56845882092052638543939887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151589018912140369450506365 56845882092052638543939887)
  ·
    refine ⟨85268823138078957815909831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56845882092052638543939887 85268823138078957815909831)
    ·
      refine ⟨127903234707118436723864747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85268823138078957815909831 127903234707118436723864747)
      ·
        refine ⟨191854852060677655085797121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127903234707118436723864747 191854852060677655085797121)
        ·
          refine ⟨143891139045508241314347841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191854852060677655085797121 143891139045508241314347841)
          ·
            refine ⟨107918354284131180985760881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143891139045508241314347841 107918354284131180985760881)
            ·
              refine ⟨80938765713098385739320661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107918354284131180985760881 80938765713098385739320661)
              ·
                refine ⟨118562645087546463485333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80938765713098385739320661 118562645087546463485333)
                ·
                  rfl

theorem cell23_6234298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 11].length) (baseStart_6234298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234298 prefixEnd_6234298 := by exact prefixLift 6234298
  have htrace : WordTrace (prefixWord ++ tailWord_6234298) baseStart_6234298 baseEnd_6234298 := by
    simpa [prefixWord, tailWord_6234298, baseEnd_6234298] using wordTrace_append hprefix tailTrace_6234298
  have hstable : (prefixWord ++ tailWord_6234298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234298).length < 2 ^ (prefixWord ++ tailWord_6234298).sum := by decide
  have hdescent : baseEnd_6234298 < baseStart_6234298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234306 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_6234306 : Nat := 118140960795 + 6234306 * 2 ^ 59
def prefixEnd_6234306 : Nat := 4983230072969 + 3 ^ 40 * 6234306 * 2
def baseEnd_6234306 : Nat := 1067065175069663494267985

theorem tailTrace_6234306 : CollatzResearch.WordTrace tailWord_6234306 prefixEnd_6234306 1067065175069663494267985 := by
  unfold tailWord_6234306
  simp only [CollatzResearch.WordTrace]
  refine ⟨56845955038045392885512693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151589213434787714361367181 56845955038045392885512693)
  ·
    refine ⟨5329308284816755583016815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56845955038045392885512693 5329308284816755583016815)
    ·
      refine ⟨7993962427225133374525223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329308284816755583016815 7993962427225133374525223)
      ·
        refine ⟨11990943640837700061787835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7993962427225133374525223 11990943640837700061787835)
        ·
          refine ⟨17986415461256550092681753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11990943640837700061787835 17986415461256550092681753)
          ·
            refine ⟨13489811595942412569511315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17986415461256550092681753 13489811595942412569511315)
            ·
              refine ⟨20234717393913618854266973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13489811595942412569511315 20234717393913618854266973)
              ·
                refine ⟨7588019022717607070350115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20234717393913618854266973 7588019022717607070350115)
                ·
                  refine ⟨11382028534076410605525173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7588019022717607070350115 11382028534076410605525173)
                  ·
                    refine ⟨1067065175069663494267985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11382028534076410605525173 1067065175069663494267985)
                    ·
                      rfl

theorem cell23_6234306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_6234306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234306 prefixEnd_6234306 := by exact prefixLift 6234306
  have htrace : WordTrace (prefixWord ++ tailWord_6234306) baseStart_6234306 baseEnd_6234306 := by
    simpa [prefixWord, tailWord_6234306, baseEnd_6234306] using wordTrace_append hprefix tailTrace_6234306
  have hstable : (prefixWord ++ tailWord_6234306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234306).length < 2 ^ (prefixWord ++ tailWord_6234306).sum := by decide
  have hdescent : baseEnd_6234306 < baseStart_6234306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234349 : List Nat := [1, 5, 1, 2, 3, 2, 2, 7]
def baseStart_6234349 : Nat := 118140960795 + 6234349 * 2 ^ 59
def prefixEnd_6234349 : Nat := 4983230072969 + 3 ^ 40 * 6234349 * 2
def baseEnd_6234349 : Nat := 118563614995449400539491

theorem tailTrace_6234349 : CollatzResearch.WordTrace tailWord_6234349 prefixEnd_6234349 118563614995449400539491 := by
  unfold tailWord_6234349
  simp only [CollatzResearch.WordTrace]
  refine ⟨227385388491025789885866101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151590258994017193257244067 227385388491025789885866101)
  ·
    refine ⟨21317380171033667801799947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227385388491025789885866101 21317380171033667801799947)
    ·
      refine ⟨31976070256550501702699921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21317380171033667801799947 31976070256550501702699921)
      ·
        refine ⟨23982052692412876277024941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31976070256550501702699921 23982052692412876277024941)
        ·
          refine ⟨8993269759654828603884353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23982052692412876277024941 8993269759654828603884353)
          ·
            refine ⟨6744952319741121452913265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8993269759654828603884353 6744952319741121452913265)
            ·
              refine ⟨5058714239805841089684949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6744952319741121452913265 5058714239805841089684949)
              ·
                refine ⟨118563614995449400539491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5058714239805841089684949 118563614995449400539491)
                ·
                  rfl

theorem cell23_6234349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 7].length) (baseStart_6234349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234349 prefixEnd_6234349 := by exact prefixLift 6234349
  have htrace : WordTrace (prefixWord ++ tailWord_6234349) baseStart_6234349 baseEnd_6234349 := by
    simpa [prefixWord, tailWord_6234349, baseEnd_6234349] using wordTrace_append hprefix tailTrace_6234349
  have hstable : (prefixWord ++ tailWord_6234349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234349).length < 2 ^ (prefixWord ++ tailWord_6234349).sum := by decide
  have hdescent : baseEnd_6234349 < baseStart_6234349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234352 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 3, 3, 2]
def baseStart_6234352 : Nat := 118140960795 + 6234352 * 2 ^ 59
def prefixEnd_6234352 : Nat := 4983230072969 + 3 ^ 40 * 6234352 * 2
def baseEnd_6234352 : Nat := 3201219145319097302828743

theorem tailTrace_6234352 : CollatzResearch.WordTrace tailWord_6234352 prefixEnd_6234352 3201219145319097302828743 := by
  unfold tailWord_6234352
  simp only [CollatzResearch.WordTrace]
  refine ⟨113692748955007460699112655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151590331940009947598816873 113692748955007460699112655)
  ·
    refine ⟨170539123432511191048668983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113692748955007460699112655 170539123432511191048668983)
    ·
      refine ⟨255808685148766786573003475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170539123432511191048668983 255808685148766786573003475)
      ·
        refine ⟨383713027723150179859505213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255808685148766786573003475 383713027723150179859505213)
        ·
          refine ⟨143892385396181317447314455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383713027723150179859505213 143892385396181317447314455)
          ·
            refine ⟨215838578094271976170971683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143892385396181317447314455 215838578094271976170971683)
            ·
              refine ⟨323757867141407964256457525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215838578094271976170971683 323757867141407964256457525)
              ·
                refine ⟨30352300044506996649042893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323757867141407964256457525 30352300044506996649042893)
                ·
                  refine ⟨11382112516690123743391085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30352300044506996649042893 11382112516690123743391085)
                  ·
                    refine ⟨4268292193758796403771657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11382112516690123743391085 4268292193758796403771657)
                    ·
                      refine ⟨3201219145319097302828743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268292193758796403771657 3201219145319097302828743)
                      ·
                        rfl

theorem cell23_6234352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 3, 2].length) (baseStart_6234352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234352 prefixEnd_6234352 := by exact prefixLift 6234352
  have htrace : WordTrace (prefixWord ++ tailWord_6234352) baseStart_6234352 baseEnd_6234352 := by
    simpa [prefixWord, tailWord_6234352, baseEnd_6234352] using wordTrace_append hprefix tailTrace_6234352
  have hstable : (prefixWord ++ tailWord_6234352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234352).length < 2 ^ (prefixWord ++ tailWord_6234352).sum := by decide
  have hdescent : baseEnd_6234352 < baseStart_6234352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234369 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_6234369 : Nat := 118140960795 + 6234369 * 2 ^ 59
def prefixEnd_6234369 : Nat := 4983230072969 + 3 ^ 40 * 6234369 * 2
def baseEnd_6234369 : Nat := 3201227874490223736316165

theorem tailTrace_6234369 : CollatzResearch.WordTrace tailWord_6234369 prefixEnd_6234369 3201227874490223736316165 := by
  unfold tailWord_6234369
  simp only [CollatzResearch.WordTrace]
  refine ⟨227386117950953333301594161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151590745300635555534396107 227386117950953333301594161)
  ·
    refine ⟨170539588463214999976195621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227386117950953333301594161 170539588463214999976195621)
    ·
      refine ⟨31976172836852812495536679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170539588463214999976195621 31976172836852812495536679)
      ·
        refine ⟨47964259255279218743305019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31976172836852812495536679 47964259255279218743305019)
        ·
          refine ⟨71946388882918828114957529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47964259255279218743305019 71946388882918828114957529)
          ·
            refine ⟨53959791662189121086218147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71946388882918828114957529 53959791662189121086218147)
            ·
              refine ⟨80939687493283681629327221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53959791662189121086218147 80939687493283681629327221)
              ·
                refine ⟨7588095702495345152749427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80939687493283681629327221 7588095702495345152749427)
                ·
                  refine ⟨11382143553743017729124141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7588095702495345152749427 11382143553743017729124141)
                  ·
                    refine ⟨4268303832653631648421553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11382143553743017729124141 4268303832653631648421553)
                    ·
                      refine ⟨3201227874490223736316165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268303832653631648421553 3201227874490223736316165)
                      ·
                        rfl

theorem cell23_6234369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_6234369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234369 prefixEnd_6234369 := by exact prefixLift 6234369
  have htrace : WordTrace (prefixWord ++ tailWord_6234369) baseStart_6234369 baseEnd_6234369 := by
    simpa [prefixWord, tailWord_6234369, baseEnd_6234369] using wordTrace_append hprefix tailTrace_6234369
  have hstable : (prefixWord ++ tailWord_6234369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234369).length < 2 ^ (prefixWord ++ tailWord_6234369).sum := by decide
  have hdescent : baseEnd_6234369 < baseStart_6234369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234395 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 4]
def baseStart_6234395 : Nat := 118140960795 + 6234395 * 2 ^ 59
def prefixEnd_6234395 : Nat := 4983230072969 + 3 ^ 40 * 6234395 * 2
def baseEnd_6234395 : Nat := 3201241224987240634591045

theorem tailTrace_6234395 : CollatzResearch.WordTrace tailWord_6234395 prefixEnd_6234395 3201241224987240634591045 := by
  unfold tailWord_6234395
  simp only [CollatzResearch.WordTrace]
  refine ⟨227387066248859139742040639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151591377499239426494693759 227387066248859139742040639)
  ·
    refine ⟨341080599373288709613060959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227387066248859139742040639 341080599373288709613060959)
    ·
      refine ⟨511620899059933064419591439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341080599373288709613060959 511620899059933064419591439)
      ·
        refine ⟨767431348589899596629387159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511620899059933064419591439 767431348589899596629387159)
        ·
          refine ⟨1151147022884849394944080739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767431348589899596629387159 1151147022884849394944080739)
          ·
            refine ⟨1726720534327274092416121109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151147022884849394944080739 1726720534327274092416121109)
            ·
              refine ⟨80940025046590973082005677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1726720534327274092416121109 80940025046590973082005677)
              ·
                refine ⟨30352509392471614905752129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80940025046590973082005677 30352509392471614905752129)
                ·
                  refine ⟨22764382044353711179314097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30352509392471614905752129 22764382044353711179314097)
                  ·
                    refine ⟨17073286533265283384485573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22764382044353711179314097 17073286533265283384485573)
                    ·
                      refine ⟨3201241224987240634591045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17073286533265283384485573 3201241224987240634591045)
                      ·
                        rfl

theorem cell23_6234395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 4].length) (baseStart_6234395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234395 prefixEnd_6234395 := by exact prefixLift 6234395
  have htrace : WordTrace (prefixWord ++ tailWord_6234395) baseStart_6234395 baseEnd_6234395 := by
    simpa [prefixWord, tailWord_6234395, baseEnd_6234395] using wordTrace_append hprefix tailTrace_6234395
  have hstable : (prefixWord ++ tailWord_6234395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234395).length < 2 ^ (prefixWord ++ tailWord_6234395).sum := by decide
  have hdescent : baseEnd_6234395 < baseStart_6234395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234402 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_6234402 : Nat := 118140960795 + 6234402 * 2 ^ 59
def prefixEnd_6234402 : Nat := 4983230072969 + 3 ^ 40 * 6234402 * 2
def baseEnd_6234402 : Nat := 3201244819351822107203513

theorem tailTrace_6234402 : CollatzResearch.WordTrace tailWord_6234402 prefixEnd_6234402 3201244819351822107203513 := by
  unfold tailWord_6234402
  simp only [CollatzResearch.WordTrace]
  refine ⟨56846830389958444984386365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151591547706555853291696973 56846830389958444984386365)
  ·
    refine ⟨21317561396234416869144887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56846830389958444984386365 21317561396234416869144887)
    ·
      refine ⟨31976342094351625303717331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21317561396234416869144887 31976342094351625303717331)
      ·
        refine ⟨47964513141527437955575997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31976342094351625303717331 47964513141527437955575997)
        ·
          refine ⟨17986692428072789233340999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47964513141527437955575997 17986692428072789233340999)
          ·
            refine ⟨26980038642109183850011499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17986692428072789233340999 26980038642109183850011499)
            ·
              refine ⟨40470057963163775775017249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26980038642109183850011499 40470057963163775775017249)
              ·
                refine ⟨30352543472372831831262937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40470057963163775775017249 30352543472372831831262937)
                ·
                  refine ⟨22764407604279623873447203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30352543472372831831262937 22764407604279623873447203)
                  ·
                    refine ⟨34146611406419435810170805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22764407604279623873447203 34146611406419435810170805)
                    ·
                      refine ⟨3201244819351822107203513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34146611406419435810170805 3201244819351822107203513)
                      ·
                        rfl

theorem cell23_6234402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_6234402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234402 prefixEnd_6234402 := by exact prefixLift 6234402
  have htrace : WordTrace (prefixWord ++ tailWord_6234402) baseStart_6234402 baseEnd_6234402 := by
    simpa [prefixWord, tailWord_6234402, baseEnd_6234402] using wordTrace_append hprefix tailTrace_6234402
  have hstable : (prefixWord ++ tailWord_6234402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234402).length < 2 ^ (prefixWord ++ tailWord_6234402).sum := by decide
  have hdescent : baseEnd_6234402 < baseStart_6234402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234469 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_6234469 : Nat := 118140960795 + 6234469 * 2 ^ 59
def prefixEnd_6234469 : Nat := 4983230072969 + 3 ^ 40 * 6234469 * 2
def baseEnd_6234469 : Nat := 1067093074185224448355235

theorem tailTrace_6234469 : CollatzResearch.WordTrace tailWord_6234469 prefixEnd_6234469 1067093074185224448355235 := by
  unfold tailWord_6234469
  simp only [CollatzResearch.WordTrace]
  refine ⟨227389765250591050380234461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151593176833727366920156307 227389765250591050380234461)
  ·
    refine ⟨85271161968971643892587923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227389765250591050380234461 85271161968971643892587923)
    ·
      refine ⟨127906742953457465838881885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85271161968971643892587923 127906742953457465838881885)
      ·
        refine ⟨47965028607546549689580707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127906742953457465838881885 47965028607546549689580707)
        ·
          refine ⟨71947542911319824534371061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47965028607546549689580707 71947542911319824534371061)
          ·
            refine ⟨6745082147936233550097287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71947542911319824534371061 6745082147936233550097287)
            ·
              refine ⟨10117623221904350325145931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6745082147936233550097287 10117623221904350325145931)
              ·
                refine ⟨15176434832856525487718897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10117623221904350325145931 15176434832856525487718897)
                ·
                  refine ⟨11382326124642394115789173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15176434832856525487718897 11382326124642394115789173)
                  ·
                    refine ⟨1067093074185224448355235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11382326124642394115789173 1067093074185224448355235)
                    ·
                      rfl

theorem cell23_6234469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_6234469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234469 prefixEnd_6234469 := by exact prefixLift 6234469
  have htrace : WordTrace (prefixWord ++ tailWord_6234469) baseStart_6234469 baseEnd_6234469 := by
    simpa [prefixWord, tailWord_6234469, baseEnd_6234469] using wordTrace_append hprefix tailTrace_6234469
  have hstable : (prefixWord ++ tailWord_6234469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234469).length < 2 ^ (prefixWord ++ tailWord_6234469).sum := by decide
  have hdescent : baseEnd_6234469 < baseStart_6234469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234495 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 8]
def baseStart_6234495 : Nat := 118140960795 + 6234495 * 2 ^ 59
def prefixEnd_6234495 : Nat := 4983230072969 + 3 ^ 40 * 6234495 * 2
def baseEnd_6234495 : Nat := 355699174783632249260065

theorem tailTrace_6234495 : CollatzResearch.WordTrace tailWord_6234495 prefixEnd_6234495 355699174783632249260065 := by
  unfold tailWord_6234495
  simp only [CollatzResearch.WordTrace]
  refine ⟨227390713548496856820680939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151593809032331237880453959 227390713548496856820680939)
  ·
    refine ⟨341086070322745285231021409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227390713548496856820680939 341086070322745285231021409)
    ·
      refine ⟨255814552742058963923266057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341086070322745285231021409 255814552742058963923266057)
      ·
        refine ⟨191860914556544222942449543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255814552742058963923266057 191860914556544222942449543)
        ·
          refine ⟨287791371834816334413674315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191860914556544222942449543 287791371834816334413674315)
          ·
            refine ⟨431687057752224501620511473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287791371834816334413674315 431687057752224501620511473)
            ·
              refine ⟨323765293314168376215383605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431687057752224501620511473 323765293314168376215383605)
              ·
                refine ⟨30352996248203285270192213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323765293314168376215383605 30352996248203285270192213)
                ·
                  refine ⟨355699174783632249260065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30352996248203285270192213 355699174783632249260065)
                  ·
                    rfl

theorem cell23_6234495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 8].length) (baseStart_6234495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234495 prefixEnd_6234495 := by exact prefixLift 6234495
  have htrace : WordTrace (prefixWord ++ tailWord_6234495) baseStart_6234495 baseEnd_6234495 := by
    simpa [prefixWord, tailWord_6234495, baseEnd_6234495] using wordTrace_append hprefix tailTrace_6234495
  have hstable : (prefixWord ++ tailWord_6234495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234495).length < 2 ^ (prefixWord ++ tailWord_6234495).sum := by decide
  have hdescent : baseEnd_6234495 < baseStart_6234495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234526 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_6234526 : Nat := 118140960795 + 6234526 * 2 ^ 59
def prefixEnd_6234526 : Nat := 4983230072969 + 3 ^ 40 * 6234526 * 2
def baseEnd_6234526 : Nat := 3201308490952979622052943

theorem tailTrace_6234526 : CollatzResearch.WordTrace tailWord_6234526 prefixEnd_6234526 3201308490952979622052943 := by
  unfold tailWord_6234526
  simp only [CollatzResearch.WordTrace]
  refine ⟨28423980526423068639382429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151594562807589699410039621 28423980526423068639382429)
  ·
    refine ⟨10658992697408650739768411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28423980526423068639382429 10658992697408650739768411)
    ·
      refine ⟨15988489046112976109652617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10658992697408650739768411 15988489046112976109652617)
      ·
        refine ⟨11991366784584732082239463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15988489046112976109652617 11991366784584732082239463)
        ·
          refine ⟨17987050176877098123359195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11991366784584732082239463 17987050176877098123359195)
          ·
            refine ⟨26980575265315647185038793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17987050176877098123359195 26980575265315647185038793)
            ·
              refine ⟨20235431448986735388779095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26980575265315647185038793 20235431448986735388779095)
              ·
                refine ⟨30353147173480103083168643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20235431448986735388779095 30353147173480103083168643)
                ·
                  refine ⟨45529720760220154624752965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30353147173480103083168643 45529720760220154624752965)
                  ·
                    refine ⟨8536822642541278992141181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45529720760220154624752965 8536822642541278992141181)
                    ·
                      refine ⟨3201308490952979622052943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8536822642541278992141181 3201308490952979622052943)
                      ·
                        rfl

theorem cell23_6234526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_6234526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234526 prefixEnd_6234526 := by exact prefixLift 6234526
  have htrace : WordTrace (prefixWord ++ tailWord_6234526) baseStart_6234526 baseEnd_6234526 := by
    simpa [prefixWord, tailWord_6234526, baseEnd_6234526] using wordTrace_append hprefix tailTrace_6234526
  have hstable : (prefixWord ++ tailWord_6234526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234526).length < 2 ^ (prefixWord ++ tailWord_6234526).sum := by decide
  have hdescent : baseEnd_6234526 < baseStart_6234526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234589 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_6234589 : Nat := 118140960795 + 6234589 * 2 ^ 59
def prefixEnd_6234589 : Nat := 4983230072969 + 3 ^ 40 * 6234589 * 2
def baseEnd_6234589 : Nat := 1067113613411404291855051

theorem tailTrace_6234589 : CollatzResearch.WordTrace tailWord_6234589 prefixEnd_6234589 1067113613411404291855051 := by
  unfold tailWord_6234589
  simp only [CollatzResearch.WordTrace]
  refine ⟨227394142010156310874602821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151596094673437540583068547 227394142010156310874602821)
  ·
    refine ⟨42636401626904308288988029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227394142010156310874602821 42636401626904308288988029)
    ·
      refine ⟨15988650610089115608370511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42636401626904308288988029 15988650610089115608370511)
      ·
        refine ⟨23982975915133673412555767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15988650610089115608370511 23982975915133673412555767)
        ·
          refine ⟨35974463872700510118833651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23982975915133673412555767 35974463872700510118833651)
          ·
            refine ⟨53961695809050765178250477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35974463872700510118833651 53961695809050765178250477)
            ·
              refine ⟨20235635928394036941843929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53961695809050765178250477 20235635928394036941843929)
              ·
                refine ⟨15176726946295527706382947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20235635928394036941843929 15176726946295527706382947)
                ·
                  refine ⟨22765090419443291559574421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15176726946295527706382947 22765090419443291559574421)
                  ·
                    refine ⟨1067113613411404291855051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22765090419443291559574421 1067113613411404291855051)
                    ·
                      rfl

theorem cell23_6234589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_6234589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234589 prefixEnd_6234589 := by exact prefixLift 6234589
  have htrace : WordTrace (prefixWord ++ tailWord_6234589) baseStart_6234589 baseEnd_6234589 := by
    simpa [prefixWord, tailWord_6234589, baseEnd_6234589] using wordTrace_append hprefix tailTrace_6234589
  have hstable : (prefixWord ++ tailWord_6234589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234589).length < 2 ^ (prefixWord ++ tailWord_6234589).sum := by decide
  have hdescent : baseEnd_6234589 < baseStart_6234589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234602 : List Nat := [3, 1, 3, 1, 3, 12]
def baseStart_6234602 : Nat := 118140960795 + 6234602 * 2 ^ 59
def prefixEnd_6234602 : Nat := 4983230072969 + 3 ^ 40 * 6234602 * 2
def baseEnd_6234602 : Nat := 13174269611040005451451

theorem tailTrace_6234602 : CollatzResearch.WordTrace tailWord_6234602 prefixEnd_6234602 13174269611040005451451 := by
  unfold tailWord_6234602
  simp only [CollatzResearch.WordTrace]
  refine ⟨56848654039777303523706515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151596410772739476063217373 56848654039777303523706515)
  ·
    refine ⟨85272981059665955285559773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56848654039777303523706515 85272981059665955285559773)
    ·
      refine ⟨31977367897374733232084915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85272981059665955285559773 31977367897374733232084915)
      ·
        refine ⟨47966051846062099848127373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31977367897374733232084915 47966051846062099848127373)
        ·
          refine ⟨17987269442273287443047765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47966051846062099848127373 17987269442273287443047765)
          ·
            refine ⟨13174269611040005451451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17987269442273287443047765 13174269611040005451451)
            ·
              rfl

theorem cell23_6234602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 12].length) (baseStart_6234602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234602 prefixEnd_6234602 := by exact prefixLift 6234602
  have htrace : WordTrace (prefixWord ++ tailWord_6234602) baseStart_6234602 baseEnd_6234602 := by
    simpa [prefixWord, tailWord_6234602, baseEnd_6234602] using wordTrace_append hprefix tailTrace_6234602
  have hstable : (prefixWord ++ tailWord_6234602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234602).length < 2 ^ (prefixWord ++ tailWord_6234602).sum := by decide
  have hdescent : baseEnd_6234602 < baseStart_6234602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234606 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_6234606 : Nat := 118140960795 + 6234606 * 2 ^ 59
def prefixEnd_6234606 : Nat := 4983230072969 + 3 ^ 40 * 6234606 * 2
def baseEnd_6234606 : Nat := 1067116523135113103017525

theorem tailTrace_6234606 : CollatzResearch.WordTrace tailWord_6234606 prefixEnd_6234606 1067116523135113103017525 := by
  unfold tailWord_6234606
  simp only [CollatzResearch.WordTrace]
  refine ⟨28424345256386840347246459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151596508034063148518647781 28424345256386840347246459)
  ·
    refine ⟨42636517884580260520869689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28424345256386840347246459 42636517884580260520869689)
    ·
      refine ⟨31977388413435195390652267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42636517884580260520869689 31977388413435195390652267)
      ·
        refine ⟨47966082620152793085978401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31977388413435195390652267 47966082620152793085978401)
        ·
          refine ⟨35974561965114594814483801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47966082620152793085978401 35974561965114594814483801)
          ·
            refine ⟨26980921473835946110862851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35974561965114594814483801 26980921473835946110862851)
            ·
              refine ⟨40471382210753919166294277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26980921473835946110862851 40471382210753919166294277)
              ·
                refine ⟨7588384164516359843680177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40471382210753919166294277 7588384164516359843680177)
                ·
                  refine ⟨5691288123387269882760133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7588384164516359843680177 5691288123387269882760133)
                  ·
                    refine ⟨1067116523135113103017525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691288123387269882760133 1067116523135113103017525)
                    ·
                      rfl

theorem cell23_6234606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_6234606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234606 prefixEnd_6234606 := by exact prefixLift 6234606
  have htrace : WordTrace (prefixWord ++ tailWord_6234606) baseStart_6234606 baseEnd_6234606 := by
    simpa [prefixWord, tailWord_6234606, baseEnd_6234606] using wordTrace_append hprefix tailTrace_6234606
  have hstable : (prefixWord ++ tailWord_6234606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234606).length < 2 ^ (prefixWord ++ tailWord_6234606).sum := by decide
  have hdescent : baseEnd_6234606 < baseStart_6234606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234629 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_6234629 : Nat := 118140960795 + 6234629 * 2 ^ 59
def prefixEnd_6234629 : Nat := 4983230072969 + 3 ^ 40 * 6234629 * 2
def baseEnd_6234629 : Nat := 3201361379460392719064969

theorem tailTrace_6234629 : CollatzResearch.WordTrace tailWord_6234629 prefixEnd_6234629 3201361379460392719064969 := by
  unfold tailWord_6234629
  simp only [CollatzResearch.WordTrace]
  refine ⟨227395600930011397706058941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151597067286674265137372627 227395600930011397706058941)
  ·
    refine ⟨85273350348754274139772103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227395600930011397706058941 85273350348754274139772103)
    ·
      refine ⟨127910025523131411209658155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85273350348754274139772103 127910025523131411209658155)
      ·
        refine ⟨191865038284697116814487233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127910025523131411209658155 191865038284697116814487233)
        ·
          refine ⟨143898778713522837610865425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191865038284697116814487233 143898778713522837610865425)
          ·
            refine ⟨107924084035142128208149069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143898778713522837610865425 107924084035142128208149069)
            ·
              refine ⟨40471531513178298078055901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107924084035142128208149069 40471531513178298078055901)
              ·
                refine ⟨15176824317441861779270963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40471531513178298078055901 15176824317441861779270963)
                ·
                  refine ⟨22765236476162792668906445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15176824317441861779270963 22765236476162792668906445)
                  ·
                    refine ⟨8536963678561047250839917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22765236476162792668906445 8536963678561047250839917)
                    ·
                      refine ⟨3201361379460392719064969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8536963678561047250839917 3201361379460392719064969)
                      ·
                        rfl

theorem cell23_6234629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_6234629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234629 prefixEnd_6234629 := by exact prefixLift 6234629
  have htrace : WordTrace (prefixWord ++ tailWord_6234629) baseStart_6234629 baseEnd_6234629 := by
    simpa [prefixWord, tailWord_6234629, baseEnd_6234629] using wordTrace_append hprefix tailTrace_6234629
  have hstable : (prefixWord ++ tailWord_6234629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234629).length < 2 ^ (prefixWord ++ tailWord_6234629).sum := by decide
  have hdescent : baseEnd_6234629 < baseStart_6234629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234630 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6234630 : Nat := 118140960795 + 6234630 * 2 ^ 59
def prefixEnd_6234630 : Nat := 4983230072969 + 3 ^ 40 * 6234630 * 2
def baseEnd_6234630 : Nat := 3201361892941047215152465

theorem tailTrace_6234630 : CollatzResearch.WordTrace tailWord_6234630 prefixEnd_6234630 3201361892941047215152465 := by
  unfold tailWord_6234630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106113668843992964901417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151597091602005183251230229 7106113668843992964901417)
  ·
    refine ⟨5329585251632994723676063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7106113668843992964901417 5329585251632994723676063)
    ·
      refine ⟨7994377877449492085514095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329585251632994723676063 7994377877449492085514095)
      ·
        refine ⟨11991566816174238128271143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7994377877449492085514095 11991566816174238128271143)
        ·
          refine ⟨17987350224261357192406715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11991566816174238128271143 17987350224261357192406715)
          ·
            refine ⟨26981025336392035788610073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17987350224261357192406715 26981025336392035788610073)
            ·
              refine ⟨20235769002294026841457555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26981025336392035788610073 20235769002294026841457555)
              ·
                refine ⟨30353653503441040262186333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20235769002294026841457555 30353653503441040262186333)
                ·
                  refine ⟨11382620063790390098319875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30353653503441040262186333 11382620063790390098319875)
                  ·
                    refine ⟨17073930095685585147479813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11382620063790390098319875 17073930095685585147479813)
                    ·
                      refine ⟨3201361892941047215152465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17073930095685585147479813 3201361892941047215152465)
                      ·
                        rfl

theorem cell23_6234630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6234630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234630 prefixEnd_6234630 := by exact prefixLift 6234630
  have htrace : WordTrace (prefixWord ++ tailWord_6234630) baseStart_6234630 baseEnd_6234630 := by
    simpa [prefixWord, tailWord_6234630, baseEnd_6234630] using wordTrace_append hprefix tailTrace_6234630
  have hstable : (prefixWord ++ tailWord_6234630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234630).length < 2 ^ (prefixWord ++ tailWord_6234630).sum := by decide
  have hdescent : baseEnd_6234630 < baseStart_6234630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234632 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 4, 7]
def baseStart_6234632 : Nat := 118140960795 + 6234632 * 2 ^ 59
def prefixEnd_6234632 : Nat := 4983230072969 + 3 ^ 40 * 6234632 * 2
def baseEnd_6234632 : Nat := 1067120973300785402442485

theorem tailTrace_6234632 : CollatzResearch.WordTrace tailWord_6234632 prefixEnd_6234632 1067120973300785402442485 := by
  unfold tailWord_6234632
  simp only [CollatzResearch.WordTrace]
  refine ⟨113697855174500264609209075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151597140232667019478945433 113697855174500264609209075)
  ·
    refine ⟨170546782761750396913813613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113697855174500264609209075 170546782761750396913813613)
    ·
      refine ⟨63955043535656398842680105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170546782761750396913813613 63955043535656398842680105)
      ·
        refine ⟨47966282651742299132010079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63955043535656398842680105 47966282651742299132010079)
        ·
          refine ⟨71949423977613448698015119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47966282651742299132010079 71949423977613448698015119)
          ·
            refine ⟨107924135966420173047022679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71949423977613448698015119 107924135966420173047022679)
            ·
              refine ⟨161886203949630259570534019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107924135966420173047022679 161886203949630259570534019)
              ·
                refine ⟨242829305924445389355801029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161886203949630259570534019 242829305924445389355801029)
                ·
                  refine ⟨45530494860833510504212693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242829305924445389355801029 45530494860833510504212693)
                  ·
                    refine ⟨1067120973300785402442485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45530494860833510504212693 1067120973300785402442485)
                    ·
                      rfl

theorem cell23_6234632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_6234632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234632 prefixEnd_6234632 := by exact prefixLift 6234632
  have htrace : WordTrace (prefixWord ++ tailWord_6234632) baseStart_6234632 baseEnd_6234632 := by
    simpa [prefixWord, tailWord_6234632, baseEnd_6234632] using wordTrace_append hprefix tailTrace_6234632
  have hstable : (prefixWord ++ tailWord_6234632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234632).length < 2 ^ (prefixWord ++ tailWord_6234632).sum := by decide
  have hdescent : baseEnd_6234632 < baseStart_6234632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234647 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6234647 : Nat := 118140960795 + 6234647 * 2 ^ 59
def prefixEnd_6234647 : Nat := 4983230072969 + 3 ^ 40 * 6234647 * 2
def baseEnd_6234647 : Nat := 3201370622112173648639887

theorem tailTrace_6234647 : CollatzResearch.WordTrace tailWord_6234647 prefixEnd_6234647 3201370622112173648639887 := by
  unfold tailWord_6234647
  simp only [CollatzResearch.WordTrace]
  refine ⟨227396257443946186780214195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151597504962630791186809463 227396257443946186780214195)
  ·
    refine ⟨341094386165919280170321293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227396257443946186780214195 341094386165919280170321293)
    ·
      refine ⟨127910394812219730063870485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341094386165919280170321293 127910394812219730063870485)
      ·
        refine ⟨5995799756822799846743929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 127910394812219730063870485 5995799756822799846743929)
        ·
          refine ⟨4496849817617099885057947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5995799756822799846743929 4496849817617099885057947)
          ·
            refine ⟨6745274726425649827586921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496849817617099885057947 6745274726425649827586921)
            ·
              refine ⟨5058956044819237370690191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6745274726425649827586921 5058956044819237370690191)
              ·
                refine ⟨7588434067228856056035287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5058956044819237370690191 7588434067228856056035287)
                ·
                  refine ⟨11382651100843284084052931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7588434067228856056035287 11382651100843284084052931)
                  ·
                    refine ⟨17073976651264926126079397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11382651100843284084052931 17073976651264926126079397)
                    ·
                      refine ⟨3201370622112173648639887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17073976651264926126079397 3201370622112173648639887)
                      ·
                        rfl

theorem cell23_6234647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6234647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234647 prefixEnd_6234647 := by exact prefixLift 6234647
  have htrace : WordTrace (prefixWord ++ tailWord_6234647) baseStart_6234647 baseEnd_6234647 := by
    simpa [prefixWord, tailWord_6234647, baseEnd_6234647] using wordTrace_append hprefix tailTrace_6234647
  have hstable : (prefixWord ++ tailWord_6234647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234647).length < 2 ^ (prefixWord ++ tailWord_6234647).sum := by decide
  have hdescent : baseEnd_6234647 < baseStart_6234647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234719 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 3]
def baseStart_6234719 : Nat := 118140960795 + 6234719 * 2 ^ 59
def prefixEnd_6234719 : Nat := 4983230072969 + 3 ^ 40 * 6234719 * 2
def baseEnd_6234719 : Nat := 3201407592719297366939555

theorem tailTrace_6234719 : CollatzResearch.WordTrace tailWord_6234719 prefixEnd_6234719 3201407592719297366939555 := by
  unfold tailWord_6234719
  simp only [CollatzResearch.WordTrace]
  refine ⟨227398883499685343076835211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151599255666456895384556807 227398883499685343076835211)
  ·
    refine ⟨341098325249528014615252817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227398883499685343076835211 341098325249528014615252817)
    ·
      refine ⟨255823743937146010961439613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341098325249528014615252817 255823743937146010961439613)
      ·
        refine ⟨95933903976429754110539855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255823743937146010961439613 95933903976429754110539855)
        ·
          refine ⟨143900855964644631165809783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95933903976429754110539855 143900855964644631165809783)
          ·
            refine ⟨215851283946966946748714675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143900855964644631165809783 215851283946966946748714675)
            ·
              refine ⟨323776925920450420123072013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215851283946966946748714675 323776925920450420123072013)
              ·
                refine ⟨121416347220168907546152005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323776925920450420123072013 121416347220168907546152005)
                ·
                  refine ⟨22765565103781670164903501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121416347220168907546152005 22765565103781670164903501)
                  ·
                    refine ⟨8537086913918126311838813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22765565103781670164903501 8537086913918126311838813)
                    ·
                      refine ⟨3201407592719297366939555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8537086913918126311838813 3201407592719297366939555)
                      ·
                        rfl

theorem cell23_6234719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_6234719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234719 prefixEnd_6234719 := by exact prefixLift 6234719
  have htrace : WordTrace (prefixWord ++ tailWord_6234719) baseStart_6234719 baseEnd_6234719 := by
    simpa [prefixWord, tailWord_6234719, baseEnd_6234719] using wordTrace_append hprefix tailTrace_6234719
  have hstable : (prefixWord ++ tailWord_6234719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234719).length < 2 ^ (prefixWord ++ tailWord_6234719).sum := by decide
  have hdescent : baseEnd_6234719 < baseStart_6234719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234754 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6234754 : Nat := 118140960795 + 6234754 * 2 ^ 59
def prefixEnd_6234754 : Nat := 4983230072969 + 3 ^ 40 * 6234754 * 2
def baseEnd_6234754 : Nat := 3201425564542204730001895

theorem tailTrace_6234754 : CollatzResearch.WordTrace tailWord_6234754 prefixEnd_6234754 3201425564542204730001895 := by
  unfold tailWord_6234754
  simp only [CollatzResearch.WordTrace]
  refine ⟨56850040013639636013589829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151600106703039029369572877 56850040013639636013589829)
  ·
    refine ⟨10659382502557431752548093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56850040013639636013589829 10659382502557431752548093)
    ·
      refine ⟨3997268438459036907205535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10659382502557431752548093 3997268438459036907205535)
      ·
        refine ⟨5995902657688555360808303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997268438459036907205535 5995902657688555360808303)
        ·
          refine ⟨8993853986532833041212455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5995902657688555360808303 8993853986532833041212455)
          ·
            refine ⟨13490780979799249561818683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8993853986532833041212455 13490780979799249561818683)
            ·
              refine ⟨20236171469698874342728025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13490780979799249561818683 20236171469698874342728025)
              ·
                refine ⟨15177128602274155757046019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20236171469698874342728025 15177128602274155757046019)
                ·
                  refine ⟨22765692903411233635569029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15177128602274155757046019 22765692903411233635569029)
                  ·
                    refine ⟨4268567419389606306669193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22765692903411233635569029 4268567419389606306669193)
                    ·
                      refine ⟨3201425564542204730001895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268567419389606306669193 3201425564542204730001895)
                      ·
                        rfl

theorem cell23_6234754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6234754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234754 prefixEnd_6234754 := by exact prefixLift 6234754
  have htrace : WordTrace (prefixWord ++ tailWord_6234754) baseStart_6234754 baseEnd_6234754 := by
    simpa [prefixWord, tailWord_6234754, baseEnd_6234754] using wordTrace_append hprefix tailTrace_6234754
  have hstable : (prefixWord ++ tailWord_6234754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234754).length < 2 ^ (prefixWord ++ tailWord_6234754).sum := by decide
  have hdescent : baseEnd_6234754 < baseStart_6234754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234756 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_6234756 : Nat := 118140960795 + 6234756 * 2 ^ 59
def prefixEnd_6234756 : Nat := 4983230072969 + 3 ^ 40 * 6234756 * 2
def baseEnd_6234756 : Nat := 1067142197167837907392295

theorem tailTrace_6234756 : CollatzResearch.WordTrace tailWord_6234756 prefixEnd_6234756 1067142197167837907392295 := by
  unfold tailWord_6234756
  simp only [CollatzResearch.WordTrace]
  refine ⟨113700116500275649197966061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151600155333700865597288081 113700116500275649197966061)
  ·
    refine ⟨42637543687603368449237273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113700116500275649197966061 42637543687603368449237273)
    ·
      refine ⟨31978157765702526336927955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42637543687603368449237273 31978157765702526336927955)
      ·
        refine ⟨47967236648553789505391933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31978157765702526336927955 47967236648553789505391933)
        ·
          refine ⟨17987713743207671064521975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47967236648553789505391933 17987713743207671064521975)
          ·
            refine ⟨26981570614811506596782963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17987713743207671064521975 26981570614811506596782963)
            ·
              refine ⟨40472355922217259895174445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26981570614811506596782963 40472355922217259895174445)
              ·
                refine ⟨15177133470831472460690417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40472355922217259895174445 15177133470831472460690417)
                ·
                  refine ⟨11382850103123604345517813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15177133470831472460690417 11382850103123604345517813)
                  ·
                    refine ⟨1067142197167837907392295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11382850103123604345517813 1067142197167837907392295)
                    ·
                      rfl

theorem cell23_6234756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_6234756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234756 prefixEnd_6234756 := by exact prefixLift 6234756
  have htrace : WordTrace (prefixWord ++ tailWord_6234756) baseStart_6234756 baseEnd_6234756 := by
    simpa [prefixWord, tailWord_6234756, baseEnd_6234756] using wordTrace_append hprefix tailTrace_6234756
  have hstable : (prefixWord ++ tailWord_6234756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234756).length < 2 ^ (prefixWord ++ tailWord_6234756).sum := by decide
  have hdescent : baseEnd_6234756 < baseStart_6234756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234776 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6234776 : Nat := 118140960795 + 6234776 * 2 ^ 59
def prefixEnd_6234776 : Nat := 4983230072969 + 3 ^ 40 * 6234776 * 2
def baseEnd_6234776 : Nat := 3201436861116603643926793

theorem tailTrace_6234776 : CollatzResearch.WordTrace tailWord_6234776 prefixEnd_6234776 3201436861116603643926793 := by
  unfold tailWord_6234776
  simp only [CollatzResearch.WordTrace]
  refine ⟨113700481230239420905830091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151600641640319227874440121 113700481230239420905830091)
  ·
    refine ⟨170550721845359131358745137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113700481230239420905830091 170550721845359131358745137)
    ·
      refine ⟨127913041384019348519058853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170550721845359131358745137 127913041384019348519058853)
      ·
        refine ⟨23983695259503627847323535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127913041384019348519058853 23983695259503627847323535)
        ·
          refine ⟨35975542889255441770985303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23983695259503627847323535 35975542889255441770985303)
          ·
            refine ⟨53963314333883162656477955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35975542889255441770985303 53963314333883162656477955)
            ·
              refine ⟨80944971500824743984716933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53963314333883162656477955 80944971500824743984716933)
              ·
                refine ⟨15177182156404639497134425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80944971500824743984716933 15177182156404639497134425)
                ·
                  refine ⟨11382886617303479622850819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15177182156404639497134425 11382886617303479622850819)
                  ·
                    refine ⟨17074329925955219434276229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11382886617303479622850819 17074329925955219434276229)
                    ·
                      refine ⟨3201436861116603643926793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17074329925955219434276229 3201436861116603643926793)
                      ·
                        rfl

theorem cell23_6234776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6234776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234776 prefixEnd_6234776 := by exact prefixLift 6234776
  have htrace : WordTrace (prefixWord ++ tailWord_6234776) baseStart_6234776 baseEnd_6234776 := by
    simpa [prefixWord, tailWord_6234776, baseEnd_6234776] using wordTrace_append hprefix tailTrace_6234776
  have hstable : (prefixWord ++ tailWord_6234776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234776).length < 2 ^ (prefixWord ++ tailWord_6234776).sum := by decide
  have hdescent : baseEnd_6234776 < baseStart_6234776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234789 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_6234789 : Nat := 118140960795 + 6234789 * 2 ^ 59
def prefixEnd_6234789 : Nat := 4983230072969 + 3 ^ 40 * 6234789 * 2
def baseEnd_6234789 : Nat := 3201443536365112093064233

theorem tailTrace_6234789 : CollatzResearch.WordTrace tailWord_6234789 prefixEnd_6234789 3201443536365112093064233 := by
  unfold tailWord_6234789
  simp only [CollatzResearch.WordTrace]
  refine ⟨227401436609431745031883421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151600957739621163354588947 227401436609431745031883421)
  ·
    refine ⟨85275538728536904386956283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227401436609431745031883421 85275538728536904386956283)
    ·
      refine ⟨127913308092805356580434425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85275538728536904386956283 127913308092805356580434425)
      ·
        refine ⟨95934981069604017435325819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127913308092805356580434425 95934981069604017435325819)
        ·
          refine ⟨143902471604406026152988729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95934981069604017435325819 143902471604406026152988729)
          ·
            refine ⟨107926853703304519614741547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143902471604406026152988729 107926853703304519614741547)
            ·
              refine ⟨161890280554956779422112321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107926853703304519614741547 161890280554956779422112321)
              ·
                refine ⟨121417710416217584566584241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161890280554956779422112321 121417710416217584566584241)
                ·
                  refine ⟨91063282812163188424938181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121417710416217584566584241 91063282812163188424938181)
                  ·
                    refine ⟨17074365527280597829675909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91063282812163188424938181 17074365527280597829675909)
                    ·
                      refine ⟨3201443536365112093064233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17074365527280597829675909 3201443536365112093064233)
                      ·
                        rfl

theorem cell23_6234789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_6234789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234789 prefixEnd_6234789 := by exact prefixLift 6234789
  have htrace : WordTrace (prefixWord ++ tailWord_6234789) baseStart_6234789 baseEnd_6234789 := by
    simpa [prefixWord, tailWord_6234789, baseEnd_6234789] using wordTrace_append hprefix tailTrace_6234789
  have hstable : (prefixWord ++ tailWord_6234789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234789).length < 2 ^ (prefixWord ++ tailWord_6234789).sum := by decide
  have hdescent : baseEnd_6234789 < baseStart_6234789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234813 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_6234813 : Nat := 118140960795 + 6234813 * 2 ^ 59
def prefixEnd_6234813 : Nat := 4983230072969 + 3 ^ 40 * 6234813 * 2
def baseEnd_6234813 : Nat := 3201455859900819999164123

theorem tailTrace_6234813 : CollatzResearch.WordTrace tailWord_6234813 prefixEnd_6234813 3201455859900819999164123 := by
  unfold tailWord_6234813
  simp only [CollatzResearch.WordTrace]
  refine ⟨227402311961344797130757093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151601541307563198087171395 227402311961344797130757093)
  ·
    refine ⟨42637933492752149462016955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227402311961344797130757093 42637933492752149462016955)
    ·
      refine ⟨63956900239128224193025433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42637933492752149462016955 63956900239128224193025433)
      ·
        refine ⟨47967675179346168144769075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63956900239128224193025433 47967675179346168144769075)
        ·
          refine ⟨71951512769019252217153613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47967675179346168144769075 71951512769019252217153613)
          ·
            refine ⟨26981817288382219581432605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71951512769019252217153613 26981817288382219581432605)
            ·
              refine ⟨10118181483143332343037227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26981817288382219581432605 10118181483143332343037227)
              ·
                refine ⟨15177272224714998514555841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10118181483143332343037227 15177272224714998514555841)
                ·
                  refine ⟨11382954168536248885916881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15177272224714998514555841 11382954168536248885916881)
                  ·
                    refine ⟨8537215626402186664437661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11382954168536248885916881 8537215626402186664437661)
                    ·
                      refine ⟨3201455859900819999164123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8537215626402186664437661 3201455859900819999164123)
                      ·
                        rfl

theorem cell23_6234813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_6234813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234813 prefixEnd_6234813 := by exact prefixLift 6234813
  have htrace : WordTrace (prefixWord ++ tailWord_6234813) baseStart_6234813 baseEnd_6234813 := by
    simpa [prefixWord, tailWord_6234813, baseEnd_6234813] using wordTrace_append hprefix tailTrace_6234813
  have hstable : (prefixWord ++ tailWord_6234813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234813).length < 2 ^ (prefixWord ++ tailWord_6234813).sum := by decide
  have hdescent : baseEnd_6234813 < baseStart_6234813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234820 : List Nat := [2, 3, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_6234820 : Nat := 118140960795 + 6234820 * 2 ^ 59
def prefixEnd_6234820 : Nat := 4983230072969 + 3 ^ 40 * 6234820 * 2
def baseEnd_6234820 : Nat := 1067153151421800490592197

theorem tailTrace_6234820 : CollatzResearch.WordTrace tailWord_6234820 prefixEnd_6234820 1067153151421800490592197 := by
  unfold tailWord_6234820
  simp only [CollatzResearch.WordTrace]
  refine ⟨113701283636159718663130957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151601711514879624884174609 113701283636159718663130957)
  ·
    refine ⟨42637981363559894498674109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113701283636159718663130957 42637981363559894498674109)
    ·
      refine ⟨15989243011334960437002791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42637981363559894498674109 15989243011334960437002791)
      ·
        refine ⟨23983864517002440655504187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15989243011334960437002791 23983864517002440655504187)
        ·
          refine ⟨35975796775503660983256281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23983864517002440655504187 35975796775503660983256281)
          ·
            refine ⟨26981847581627745737442211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35975796775503660983256281 26981847581627745737442211)
            ·
              refine ⟨40472771372441618606163317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26981847581627745737442211 40472771372441618606163317)
              ·
                refine ⟨3794322316166401744327811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40472771372441618606163317 3794322316166401744327811)
                ·
                  refine ⟨5691483474249602616491717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794322316166401744327811 5691483474249602616491717)
                  ·
                    refine ⟨1067153151421800490592197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691483474249602616491717 1067153151421800490592197)
                    ·
                      rfl

theorem cell23_6234820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_6234820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234820 prefixEnd_6234820 := by exact prefixLift 6234820
  have htrace : WordTrace (prefixWord ++ tailWord_6234820) baseStart_6234820 baseEnd_6234820 := by
    simpa [prefixWord, tailWord_6234820, baseEnd_6234820] using wordTrace_append hprefix tailTrace_6234820
  have hstable : (prefixWord ++ tailWord_6234820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234820).length < 2 ^ (prefixWord ++ tailWord_6234820).sum := by decide
  have hdescent : baseEnd_6234820 < baseStart_6234820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234853 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 1, 5, 2]
def baseStart_6234853 : Nat := 118140960795 + 6234853 * 2 ^ 59
def prefixEnd_6234853 : Nat := 4983230072969 + 3 ^ 40 * 6234853 * 2
def baseEnd_6234853 : Nat := 3201476399126999842663939

theorem tailTrace_6234853 : CollatzResearch.WordTrace tailWord_6234853 prefixEnd_6234853 3201476399126999842663939 := by
  unfold tailWord_6234853
  simp only [CollatzResearch.WordTrace]
  refine ⟨227403770881199883962213213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151602513920799922641475475 227403770881199883962213213)
  ·
    refine ⟨85276414080449956485829955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227403770881199883962213213 85276414080449956485829955)
    ·
      refine ⟨127914621120674934728744933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85276414080449956485829955 127914621120674934728744933)
      ·
        refine ⟨23983991460126550261639675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127914621120674934728744933 23983991460126550261639675)
        ·
          refine ⟨35975987190189825392459513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23983991460126550261639675 35975987190189825392459513)
          ·
            refine ⟨26981990392642369044344635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35975987190189825392459513 26981990392642369044344635)
            ·
              refine ⟨40472985588963553566516953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26981990392642369044344635 40472985588963553566516953)
              ·
                refine ⟨30354739191722665174887715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40472985588963553566516953 30354739191722665174887715)
                ·
                  refine ⟨45532108787583997762331573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30354739191722665174887715 45532108787583997762331573)
                  ·
                    refine ⟨4268635198835999790218585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45532108787583997762331573 4268635198835999790218585)
                    ·
                      refine ⟨3201476399126999842663939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268635198835999790218585 3201476399126999842663939)
                      ·
                        rfl

theorem cell23_6234853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_6234853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234853 prefixEnd_6234853 := by exact prefixLift 6234853
  have htrace : WordTrace (prefixWord ++ tailWord_6234853) baseStart_6234853 baseEnd_6234853 := by
    simpa [prefixWord, tailWord_6234853, baseEnd_6234853] using wordTrace_append hprefix tailTrace_6234853
  have hstable : (prefixWord ++ tailWord_6234853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234853).length < 2 ^ (prefixWord ++ tailWord_6234853).sum := by decide
  have hdescent : baseEnd_6234853 < baseStart_6234853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234863 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 1, 5]
def baseStart_6234863 : Nat := 118140960795 + 6234863 * 2 ^ 59
def prefixEnd_6234863 : Nat := 4983230072969 + 3 ^ 40 * 6234863 * 2
def baseEnd_6234863 : Nat := 1067160511311181601179631

theorem tailTrace_6234863 : CollatzResearch.WordTrace tailWord_6234863 prefixEnd_6234863 1067160511311181601179631 := by
  unfold tailWord_6234863
  simp only [CollatzResearch.WordTrace]
  refine ⟨227404135611163655670077243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151602757074109103780051495 227404135611163655670077243)
  ·
    refine ⟨341106203416745483505115865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227404135611163655670077243 341106203416745483505115865)
    ·
      refine ⟨255829652562559112628836899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341106203416745483505115865 255829652562559112628836899)
      ·
        refine ⟨383744478843838668943255349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255829652562559112628836899 383744478843838668943255349)
        ·
          refine ⟨35976044891609875213430189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 383744478843838668943255349 35976044891609875213430189)
          ·
            refine ⟨13491016834353703205036321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35976044891609875213430189 13491016834353703205036321)
            ·
              refine ⟨10118262625765277403777241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13491016834353703205036321 10118262625765277403777241)
              ·
                refine ⟨7588696969323958052832931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10118262625765277403777241 7588696969323958052832931)
                ·
                  refine ⟨11383045453985937079249397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7588696969323958052832931 11383045453985937079249397)
                  ·
                    refine ⟨1067160511311181601179631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11383045453985937079249397 1067160511311181601179631)
                    ·
                      rfl

theorem cell23_6234863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 5].length) (baseStart_6234863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234863 prefixEnd_6234863 := by exact prefixLift 6234863
  have htrace : WordTrace (prefixWord ++ tailWord_6234863) baseStart_6234863 baseEnd_6234863 := by
    simpa [prefixWord, tailWord_6234863, baseEnd_6234863] using wordTrace_append hprefix tailTrace_6234863
  have hstable : (prefixWord ++ tailWord_6234863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234863).length < 2 ^ (prefixWord ++ tailWord_6234863).sum := by decide
  have hdescent : baseEnd_6234863 < baseStart_6234863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234870 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_6234870 : Nat := 118140960795 + 6234870 * 2 ^ 59
def prefixEnd_6234870 : Nat := 4983230072969 + 3 ^ 40 * 6234870 * 2
def baseEnd_6234870 : Nat := 3201485128298126276151361

theorem tailTrace_6234870 : CollatzResearch.WordTrace tailWord_6234870 prefixEnd_6234870 3201485128298126276151361 := by
  unfold tailWord_6234870
  simp only [CollatzResearch.WordTrace]
  refine ⟨14212774432633643491598879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151602927281425530577054709 14212774432633643491598879)
  ·
    refine ⟨21319161648950465237398319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14212774432633643491598879 21319161648950465237398319)
    ·
      refine ⟨31978742473425697856097479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21319161648950465237398319 31978742473425697856097479)
      ·
        refine ⟨47968113710138546784146219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31978742473425697856097479 47968113710138546784146219)
        ·
          refine ⟨71952170565207820176219329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47968113710138546784146219 71952170565207820176219329)
          ·
            refine ⟨53964127923905865132164497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71952170565207820176219329 53964127923905865132164497)
            ·
              refine ⟨40473095942929398849123373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53964127923905865132164497 40473095942929398849123373)
              ·
                refine ⟨15177410978598524568421265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40473095942929398849123373 15177410978598524568421265)
                ·
                  refine ⟨11383058233948893426315949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15177410978598524568421265 11383058233948893426315949)
                  ·
                    refine ⟨4268646837730835034868481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11383058233948893426315949 4268646837730835034868481)
                    ·
                      refine ⟨3201485128298126276151361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268646837730835034868481 3201485128298126276151361)
                      ·
                        rfl

theorem cell23_6234870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_6234870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234870 prefixEnd_6234870 := by exact prefixLift 6234870
  have htrace : WordTrace (prefixWord ++ tailWord_6234870) baseStart_6234870 baseEnd_6234870 := by
    simpa [prefixWord, tailWord_6234870, baseEnd_6234870] using wordTrace_append hprefix tailTrace_6234870
  have hstable : (prefixWord ++ tailWord_6234870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234870).length < 2 ^ (prefixWord ++ tailWord_6234870).sum := by decide
  have hdescent : baseEnd_6234870 < baseStart_6234870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234889 : List Nat := [1, 2, 1, 1, 3, 2, 13]
def baseStart_6234889 : Nat := 118140960795 + 6234889 * 2 ^ 59
def prefixEnd_6234889 : Nat := 4983230072969 + 3 ^ 40 * 6234889 * 2
def baseEnd_6234889 : Nat := 39524628202846440763133

theorem tailTrace_6234889 : CollatzResearch.WordTrace tailWord_6234889 prefixEnd_6234889 39524628202846440763133 := by
  unfold tailWord_6234889
  simp only [CollatzResearch.WordTrace]
  refine ⟨227405083909069462110523721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151603389272712974740349147 227405083909069462110523721)
  ·
    refine ⟨170553812931802096582892791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227405083909069462110523721 170553812931802096582892791)
    ·
      refine ⟨255830719397703144874339187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170553812931802096582892791 255830719397703144874339187)
      ·
        refine ⟨383746079096554717311508781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255830719397703144874339187 383746079096554717311508781)
        ·
          refine ⟨143904779661208018991815793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383746079096554717311508781 143904779661208018991815793)
          ·
            refine ⟨107928584745906014243861845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143904779661208018991815793 107928584745906014243861845)
            ·
              refine ⟨39524628202846440763133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 107928584745906014243861845 39524628202846440763133)
              ·
                rfl

theorem cell23_6234889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 13].length) (baseStart_6234889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234889 prefixEnd_6234889 := by exact prefixLift 6234889
  have htrace : WordTrace (prefixWord ++ tailWord_6234889) baseStart_6234889 baseEnd_6234889 := by
    simpa [prefixWord, tailWord_6234889, baseEnd_6234889] using wordTrace_append hprefix tailTrace_6234889
  have hstable : (prefixWord ++ tailWord_6234889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234889).length < 2 ^ (prefixWord ++ tailWord_6234889).sum := by decide
  have hdescent : baseEnd_6234889 < baseStart_6234889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234906 : List Nat := [3, 1, 1, 3, 2, 1, 4, 8]
def baseStart_6234906 : Nat := 118140960795 + 6234906 * 2 ^ 59
def prefixEnd_6234906 : Nat := 4983230072969 + 3 ^ 40 * 6234906 * 2
def baseEnd_6234906 : Nat := 118574207911173634640785

theorem tailTrace_6234906 : CollatzResearch.WordTrace tailWord_6234906 prefixEnd_6234906 118574207911173634640785 := by
  unfold tailWord_6234906
  simp only [CollatzResearch.WordTrace]
  refine ⟨56851425987501968503473143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151603802633338582675928381 56851425987501968503473143)
  ·
    refine ⟨85277138981252952755209715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56851425987501968503473143 85277138981252952755209715)
    ·
      refine ⟨127915708471879429132814573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85277138981252952755209715 127915708471879429132814573)
      ·
        refine ⟨47968390676954785924805465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127915708471879429132814573 47968390676954785924805465)
        ·
          refine ⟨35976293007716089443604099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47968390676954785924805465 35976293007716089443604099)
          ·
            refine ⟨53964439511574134165406149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35976293007716089443604099 53964439511574134165406149)
            ·
              refine ⟨10118332408420150156013653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53964439511574134165406149 10118332408420150156013653)
              ·
                refine ⟨118574207911173634640785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10118332408420150156013653 118574207911173634640785)
                ·
                  rfl

theorem cell23_6234906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 8].length) (baseStart_6234906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234906 prefixEnd_6234906 := by exact prefixLift 6234906
  have htrace : WordTrace (prefixWord ++ tailWord_6234906) baseStart_6234906 baseEnd_6234906 := by
    simpa [prefixWord, tailWord_6234906, baseEnd_6234906] using wordTrace_append hprefix tailTrace_6234906
  have hstable : (prefixWord ++ tailWord_6234906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234906).length < 2 ^ (prefixWord ++ tailWord_6234906).sum := by decide
  have hdescent : baseEnd_6234906 < baseStart_6234906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234933 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_6234933 : Nat := 118140960795 + 6234933 * 2 ^ 59
def prefixEnd_6234933 : Nat := 4983230072969 + 3 ^ 40 * 6234933 * 2
def baseEnd_6234933 : Nat := 3201517477579359529663571

theorem tailTrace_6234933 : CollatzResearch.WordTrace tailWord_6234933 prefixEnd_6234933 3201517477579359529663571 := by
  unfold tailWord_6234933
  simp only [CollatzResearch.WordTrace]
  refine ⟨227406688720910057625125453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151604459147273371750083635 227406688720910057625125453)
  ·
    refine ⟨85277508270341271609422045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227406688720910057625125453 85277508270341271609422045)
    ·
      refine ⟨31979065601377976853533267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85277508270341271609422045 31979065601377976853533267)
      ·
        refine ⟨47968598402066965280299901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31979065601377976853533267 47968598402066965280299901)
        ·
          refine ⟨17988224400775111980112463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47968598402066965280299901 17988224400775111980112463)
          ·
            refine ⟨26982336601162667970168695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17988224400775111980112463 26982336601162667970168695)
            ·
              refine ⟨40473504901744001955253043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26982336601162667970168695 40473504901744001955253043)
              ·
                refine ⟨60710257352616002932879565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40473504901744001955253043 60710257352616002932879565)
                ·
                  refine ⟨22766346507231001099829837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60710257352616002932879565 22766346507231001099829837)
                  ·
                    refine ⟨8537379940211625412436189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22766346507231001099829837 8537379940211625412436189)
                    ·
                      refine ⟨3201517477579359529663571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8537379940211625412436189 3201517477579359529663571)
                      ·
                        rfl

theorem cell23_6234933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_6234933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234933 prefixEnd_6234933 := by exact prefixLift 6234933
  have htrace : WordTrace (prefixWord ++ tailWord_6234933) baseStart_6234933 baseEnd_6234933 := by
    simpa [prefixWord, tailWord_6234933, baseEnd_6234933] using wordTrace_append hprefix tailTrace_6234933
  have hstable : (prefixWord ++ tailWord_6234933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234933).length < 2 ^ (prefixWord ++ tailWord_6234933).sum := by decide
  have hdescent : baseEnd_6234933 < baseStart_6234933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234934 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6234934 : Nat := 118140960795 + 6234934 * 2 ^ 59
def prefixEnd_6234934 : Nat := 4983230072969 + 3 ^ 40 * 6234934 * 2
def baseEnd_6234934 : Nat := 3201517991060014025751067

theorem tailTrace_6234934 : CollatzResearch.WordTrace tailWord_6234934 prefixEnd_6234934 3201517991060014025751067 := by
  unfold tailWord_6234934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14212920324619152174744491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151604483462604289863941237 14212920324619152174744491)
  ·
    refine ⟨21319380486928728262116737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14212920324619152174744491 21319380486928728262116737)
    ·
      refine ⟨15989535365196546196587553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21319380486928728262116737 15989535365196546196587553)
      ·
        refine ⟨11992151523897409647440665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15989535365196546196587553 11992151523897409647440665)
        ·
          refine ⟨8994113642923057235580499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11992151523897409647440665 8994113642923057235580499)
          ·
            refine ⟨13491170464384585853370749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8994113642923057235580499 13491170464384585853370749)
            ·
              refine ⟨5059188924144219695014031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13491170464384585853370749 5059188924144219695014031)
              ·
                refine ⟨7588783386216329542521047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059188924144219695014031 7588783386216329542521047)
                ·
                  refine ⟨11383175079324494313781571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7588783386216329542521047 11383175079324494313781571)
                  ·
                    refine ⟨17074762618986741470672357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11383175079324494313781571 17074762618986741470672357)
                    ·
                      refine ⟨3201517991060014025751067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17074762618986741470672357 3201517991060014025751067)
                      ·
                        rfl

theorem cell23_6234934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6234934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234934 prefixEnd_6234934 := by exact prefixLift 6234934
  have htrace : WordTrace (prefixWord ++ tailWord_6234934) baseStart_6234934 baseEnd_6234934 := by
    simpa [prefixWord, tailWord_6234934, baseEnd_6234934] using wordTrace_append hprefix tailTrace_6234934
  have hstable : (prefixWord ++ tailWord_6234934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234934).length < 2 ^ (prefixWord ++ tailWord_6234934).sum := by decide
  have hdescent : baseEnd_6234934 < baseStart_6234934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6234957 : List Nat := [1, 6, 1, 2, 3, 1, 1, 8]
def baseStart_6234957 : Nat := 118140960795 + 6234957 * 2 ^ 59
def prefixEnd_6234957 : Nat := 4983230072969 + 3 ^ 40 * 6234957 * 2
def baseEnd_6234957 : Nat := 118575177819076571694943

theorem tailTrace_6234957 : CollatzResearch.WordTrace tailWord_6234957 prefixEnd_6234957 118575177819076571694943 := by
  unfold tailWord_6234957
  simp only [CollatzResearch.WordTrace]
  refine ⟨227407564072823109723999125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151605042715215406482666083 227407564072823109723999125)
  ·
    refine ⟨10659729565913583268312459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 227407564072823109723999125 10659729565913583268312459)
    ·
      refine ⟨15989594348870374902468689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10659729565913583268312459 15989594348870374902468689)
      ·
        refine ⟨11992195761652781176851517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15989594348870374902468689 11992195761652781176851517)
        ·
          refine ⟨4497073410619792941319319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11992195761652781176851517 4497073410619792941319319)
          ·
            refine ⟨6745610115929689411978979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497073410619792941319319 6745610115929689411978979)
            ·
              refine ⟨10118415173894534117968469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6745610115929689411978979 10118415173894534117968469)
              ·
                refine ⟨118575177819076571694943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10118415173894534117968469 118575177819076571694943)
                ·
                  rfl

theorem cell23_6234957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 8].length) (baseStart_6234957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6234957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6234957 prefixEnd_6234957 := by exact prefixLift 6234957
  have htrace : WordTrace (prefixWord ++ tailWord_6234957) baseStart_6234957 baseEnd_6234957 := by
    simpa [prefixWord, tailWord_6234957, baseEnd_6234957] using wordTrace_append hprefix tailTrace_6234957
  have hstable : (prefixWord ++ tailWord_6234957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6234957).length < 2 ^ (prefixWord ++ tailWord_6234957).sum := by decide
  have hdescent : baseEnd_6234957 < baseStart_6234957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6234957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235007 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 2, 2, 2]
def baseStart_6235007 : Nat := 118140960795 + 6235007 * 2 ^ 59
def prefixEnd_6235007 : Nat := 4983230072969 + 3 ^ 40 * 6235007 * 2
def baseEnd_6235007 : Nat := 3201555475147792240138231

theorem tailTrace_6235007 : CollatzResearch.WordTrace tailWord_6235007 prefixEnd_6235007 3201555475147792240138231 := by
  unfold tailWord_6235007
  simp only [CollatzResearch.WordTrace]
  refine ⟨227409387722641968263319275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151606258481761312175546183 227409387722641968263319275)
  ·
    refine ⟨341114081583962952394978913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227409387722641968263319275 341114081583962952394978913)
    ·
      refine ⟨255835561187972214296234185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341114081583962952394978913 255835561187972214296234185)
      ·
        refine ⟨191876670890979160722175639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255835561187972214296234185 191876670890979160722175639)
        ·
          refine ⟨287815006336468741083263459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191876670890979160722175639 287815006336468741083263459)
          ·
            refine ⟨431722509504703111624895189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287815006336468741083263459 431722509504703111624895189)
            ·
              refine ⟨10118496316516479178708481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 431722509504703111624895189 10118496316516479178708481)
              ·
                refine ⟨7588872237387359384031361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10118496316516479178708481 7588872237387359384031361)
                ·
                  refine ⟨5691654178040519538023521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7588872237387359384031361 5691654178040519538023521)
                  ·
                    refine ⟨4268740633530389653517641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5691654178040519538023521 4268740633530389653517641)
                    ·
                      refine ⟨3201555475147792240138231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268740633530389653517641 3201555475147792240138231)
                      ·
                        rfl

theorem cell23_6235007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_6235007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235007 prefixEnd_6235007 := by exact prefixLift 6235007
  have htrace : WordTrace (prefixWord ++ tailWord_6235007) baseStart_6235007 baseEnd_6235007 := by
    simpa [prefixWord, tailWord_6235007, baseEnd_6235007] using wordTrace_append hprefix tailTrace_6235007
  have hstable : (prefixWord ++ tailWord_6235007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235007).length < 2 ^ (prefixWord ++ tailWord_6235007).sum := by decide
  have hdescent : baseEnd_6235007 < baseStart_6235007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235013 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 7]
def baseStart_6235013 : Nat := 118140960795 + 6235013 * 2 ^ 59
def prefixEnd_6235013 : Nat := 4983230072969 + 3 ^ 40 * 6235013 * 2
def baseEnd_6235013 : Nat := 355728728447968801851467

theorem tailTrace_6235013 : CollatzResearch.WordTrace tailWord_6235013 prefixEnd_6235013 355728728447968801851467 := by
  unfold tailWord_6235013
  simp only [CollatzResearch.WordTrace]
  refine ⟨227409606560620231288037693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151606404373746820858691795 227409606560620231288037693)
  ·
    refine ⟨85278602460232586733014135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227409606560620231288037693 85278602460232586733014135)
    ·
      refine ⟨127917903690348880099521203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85278602460232586733014135 127917903690348880099521203)
      ·
        refine ⟨191876855535523320149281805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127917903690348880099521203 191876855535523320149281805)
        ·
          refine ⟨71953820825821245055980677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191876855535523320149281805 71953820825821245055980677)
          ·
            refine ⟨13491341404841483447996377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71953820825821245055980677 13491341404841483447996377)
            ·
              refine ⟨10118506053631112585997283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13491341404841483447996377 10118506053631112585997283)
              ·
                refine ⟨15177759080446668878995925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10118506053631112585997283 15177759080446668878995925)
                ·
                  refine ⟨355728728447968801851467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15177759080446668878995925 355728728447968801851467)
                  ·
                    rfl

theorem cell23_6235013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_6235013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235013 prefixEnd_6235013 := by exact prefixLift 6235013
  have htrace : WordTrace (prefixWord ++ tailWord_6235013) baseStart_6235013 baseEnd_6235013 := by
    simpa [prefixWord, tailWord_6235013, baseEnd_6235013] using wordTrace_append hprefix tailTrace_6235013
  have hstable : (prefixWord ++ tailWord_6235013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235013).length < 2 ^ (prefixWord ++ tailWord_6235013).sum := by decide
  have hdescent : baseEnd_6235013 < baseStart_6235013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235063 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_6235063 : Nat := 118140960795 + 6235063 * 2 ^ 59
def prefixEnd_6235063 : Nat := 4983230072969 + 3 ^ 40 * 6235063 * 2
def baseEnd_6235063 : Nat := 3201584230064444021037973

theorem tailTrace_6235063 : CollatzResearch.WordTrace tailWord_6235063 prefixEnd_6235063 3201584230064444021037973 := by
  unfold tailWord_6235063
  simp only [CollatzResearch.WordTrace]
  refine ⟨227411430210439089827357843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151607620140292726551571895 227411430210439089827357843)
  ·
    refine ⟨341117145315658634741036765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227411430210439089827357843 341117145315658634741036765)
    ·
      refine ⟨127918929493371988027888787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341117145315658634741036765 127918929493371988027888787)
      ·
        refine ⟨191878394240057982041833181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127918929493371988027888787 191878394240057982041833181)
        ·
          refine ⟨71954397840021743265687443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191878394240057982041833181 71954397840021743265687443)
          ·
            refine ⟨107931596760032614898531165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71954397840021743265687443 107931596760032614898531165)
            ·
              refine ⟨40474348785012230586949187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107931596760032614898531165 40474348785012230586949187)
              ·
                refine ⟨60711523177518345880423781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40474348785012230586949187 60711523177518345880423781)
                ·
                  refine ⟨11383410595784689852579459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60711523177518345880423781 11383410595784689852579459)
                  ·
                    refine ⟨17075115893677034778869189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11383410595784689852579459 17075115893677034778869189)
                    ·
                      refine ⟨3201584230064444021037973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17075115893677034778869189 3201584230064444021037973)
                      ·
                        rfl

theorem cell23_6235063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_6235063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235063 prefixEnd_6235063 := by exact prefixLift 6235063
  have htrace : WordTrace (prefixWord ++ tailWord_6235063) baseStart_6235063 baseEnd_6235063 := by
    simpa [prefixWord, tailWord_6235063, baseEnd_6235063] using wordTrace_append hprefix tailTrace_6235063
  have hstable : (prefixWord ++ tailWord_6235063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235063).length < 2 ^ (prefixWord ++ tailWord_6235063).sum := by decide
  have hdescent : baseEnd_6235063 < baseStart_6235063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235107 : List Nat := [1, 1, 1, 6, 1, 1, 2, 5, 1, 4]
def baseStart_6235107 : Nat := 118140960795 + 6235107 * 2 ^ 59
def prefixEnd_6235107 : Nat := 4983230072969 + 3 ^ 40 * 6235107 * 2
def baseEnd_6235107 : Nat := 1067202274404413949629257

theorem tailTrace_6235107 : CollatzResearch.WordTrace tailWord_6235107 prefixEnd_6235107 1067202274404413949629257 := by
  unfold tailWord_6235107
  simp only [CollatzResearch.WordTrace]
  refine ⟨227413035022279685341959575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151608690014853123561306383 227413035022279685341959575)
  ·
    refine ⟨341119552533419528012939363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227413035022279685341959575 341119552533419528012939363)
    ·
      refine ⟨511679328800129292019409045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341119552533419528012939363 511679328800129292019409045)
      ·
        refine ⟨23984968537506060563409799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 511679328800129292019409045 23984968537506060563409799)
        ·
          refine ⟨35977452806259090845114699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23984968537506060563409799 35977452806259090845114699)
          ·
            refine ⟨53966179209388636267672049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35977452806259090845114699 53966179209388636267672049)
            ·
              refine ⟨40474634407041477200754037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53966179209388636267672049 40474634407041477200754037)
              ·
                refine ⟨3794496975660138487570691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40474634407041477200754037 3794496975660138487570691)
                ·
                  refine ⟨5691745463490207731356037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794496975660138487570691 5691745463490207731356037)
                  ·
                    refine ⟨1067202274404413949629257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691745463490207731356037 1067202274404413949629257)
                    ·
                      rfl

theorem cell23_6235107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 1, 4].length) (baseStart_6235107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235107 prefixEnd_6235107 := by exact prefixLift 6235107
  have htrace : WordTrace (prefixWord ++ tailWord_6235107) baseStart_6235107 baseEnd_6235107 := by
    simpa [prefixWord, tailWord_6235107, baseEnd_6235107] using wordTrace_append hprefix tailTrace_6235107
  have hstable : (prefixWord ++ tailWord_6235107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235107).length < 2 ^ (prefixWord ++ tailWord_6235107).sum := by decide
  have hdescent : baseEnd_6235107 < baseStart_6235107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235130 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_6235130 : Nat := 118140960795 + 6235130 * 2 ^ 59
def prefixEnd_6235130 : Nat := 4983230072969 + 3 ^ 40 * 6235130 * 2
def baseEnd_6235130 : Nat := 3201618633268295258900165

theorem tailTrace_6235130 : CollatzResearch.WordTrace tailWord_6235130 prefixEnd_6235130 3201618633268295258900165 := by
  unfold tailWord_6235130
  simp only [CollatzResearch.WordTrace]
  refine ⟨56853468475299090067511711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151609249267464240180031229 56853468475299090067511711)
  ·
    refine ⟨85280202712948635101267567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56853468475299090067511711 85280202712948635101267567)
    ·
      refine ⟨127920304069422952651901351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85280202712948635101267567 127920304069422952651901351)
      ·
        refine ⟨191880456104134428977852027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127920304069422952651901351 191880456104134428977852027)
        ·
          refine ⟨287820684156201643466778041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191880456104134428977852027 287820684156201643466778041)
          ·
            refine ⟨215865513117151232600083531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287820684156201643466778041 215865513117151232600083531)
            ·
              refine ⟨323798269675726848900125297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215865513117151232600083531 323798269675726848900125297)
              ·
                refine ⟨242848702256795136675093973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323798269675726848900125297 242848702256795136675093973)
                ·
                  refine ⟨5691766459143636015822515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 242848702256795136675093973 5691766459143636015822515)
                  ·
                    refine ⟨8537649688715454023733773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5691766459143636015822515 8537649688715454023733773)
                    ·
                      refine ⟨3201618633268295258900165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8537649688715454023733773 3201618633268295258900165)
                      ·
                        rfl

theorem cell23_6235130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_6235130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235130 prefixEnd_6235130 := by exact prefixLift 6235130
  have htrace : WordTrace (prefixWord ++ tailWord_6235130) baseStart_6235130 baseEnd_6235130 := by
    simpa [prefixWord, tailWord_6235130, baseEnd_6235130] using wordTrace_append hprefix tailTrace_6235130
  have hstable : (prefixWord ++ tailWord_6235130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235130).length < 2 ^ (prefixWord ++ tailWord_6235130).sum := by decide
  have hdescent : baseEnd_6235130 < baseStart_6235130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235143 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_6235143 : Nat := 118140960795 + 6235143 * 2 ^ 59
def prefixEnd_6235143 : Nat := 4983230072969 + 3 ^ 40 * 6235143 * 2
def baseEnd_6235143 : Nat := 3201625308516803708037605

theorem tailTrace_6235143 : CollatzResearch.WordTrace tailWord_6235143 prefixEnd_6235143 3201625308516803708037605 := by
  unfold tailWord_6235143
  simp only [CollatzResearch.WordTrace]
  refine ⟨227414348050149263490270083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151609565366766175660180055 227414348050149263490270083)
  ·
    refine ⟨341121522075223895235405125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227414348050149263490270083 341121522075223895235405125)
    ·
      refine ⟨63960285389104480356638461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341121522075223895235405125 63960285389104480356638461)
      ·
        refine ⟨23985107020914180133739423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63960285389104480356638461 23985107020914180133739423)
        ·
          refine ⟨35977660531371270200609135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23985107020914180133739423 35977660531371270200609135)
          ·
            refine ⟨53966490797056905300913703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35977660531371270200609135 53966490797056905300913703)
            ·
              refine ⟨80949736195585357951370555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53966490797056905300913703 80949736195585357951370555)
              ·
                refine ⟨121424604293378036927055833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80949736195585357951370555 121424604293378036927055833)
                ·
                  refine ⟨91068453220033527695291875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121424604293378036927055833 91068453220033527695291875)
                  ·
                    refine ⟨136602679830050291542937813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91068453220033527695291875 136602679830050291542937813)
                    ·
                      refine ⟨3201625308516803708037605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136602679830050291542937813 3201625308516803708037605)
                      ·
                        rfl

theorem cell23_6235143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_6235143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235143 prefixEnd_6235143 := by exact prefixLift 6235143
  have htrace : WordTrace (prefixWord ++ tailWord_6235143) baseStart_6235143 baseEnd_6235143 := by
    simpa [prefixWord, tailWord_6235143, baseEnd_6235143] using wordTrace_append hprefix tailTrace_6235143
  have hstable : (prefixWord ++ tailWord_6235143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235143).length < 2 ^ (prefixWord ++ tailWord_6235143).sum := by decide
  have hdescent : baseEnd_6235143 < baseStart_6235143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235147 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 3]
def baseStart_6235147 : Nat := 118140960795 + 6235147 * 2 ^ 59
def prefixEnd_6235147 : Nat := 4983230072969 + 3 ^ 40 * 6235147 * 2
def baseEnd_6235147 : Nat := 3201627362439421692387587

theorem tailTrace_6235147 : CollatzResearch.WordTrace tailWord_6235147 prefixEnd_6235147 3201627362439421692387587 := by
  unfold tailWord_6235147
  simp only [CollatzResearch.WordTrace]
  refine ⟨227414493942134772173415695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151609662628089848115610463 227414493942134772173415695)
  ·
    refine ⟨341121740913202158260123543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227414493942134772173415695 341121740913202158260123543)
    ·
      refine ⟨511682611369803237390185315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341121740913202158260123543 511682611369803237390185315)
      ·
        refine ⟨767523917054704856085277973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511682611369803237390185315 767523917054704856085277973)
        ·
          refine ⟨35977683611939290128997405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 767523917054704856085277973 35977683611939290128997405)
          ·
            refine ⟨13491631354477233798374027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35977683611939290128997405 13491631354477233798374027)
            ·
              refine ⟨20237447031715850697561041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13491631354477233798374027 20237447031715850697561041)
              ·
                refine ⟨15178085273786888023170781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20237447031715850697561041 15178085273786888023170781)
                ·
                  refine ⟨5691781977670083008689043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15178085273786888023170781 5691781977670083008689043)
                  ·
                    refine ⟨8537672966505124513033565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5691781977670083008689043 8537672966505124513033565)
                    ·
                      refine ⟨3201627362439421692387587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8537672966505124513033565 3201627362439421692387587)
                      ·
                        rfl

theorem cell23_6235147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 3].length) (baseStart_6235147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235147 prefixEnd_6235147 := by exact prefixLift 6235147
  have htrace : WordTrace (prefixWord ++ tailWord_6235147) baseStart_6235147 baseEnd_6235147 := by
    simpa [prefixWord, tailWord_6235147, baseEnd_6235147] using wordTrace_append hprefix tailTrace_6235147
  have hstable : (prefixWord ++ tailWord_6235147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235147).length < 2 ^ (prefixWord ++ tailWord_6235147).sum := by decide
  have hdescent : baseEnd_6235147 < baseStart_6235147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235150 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_6235150 : Nat := 118140960795 + 6235150 * 2 ^ 59
def prefixEnd_6235150 : Nat := 4983230072969 + 3 ^ 40 * 6235150 * 2
def baseEnd_6235150 : Nat := 1067209634293795060216691

theorem tailTrace_6235150 : CollatzResearch.WordTrace tailWord_6235150 prefixEnd_6235150 1067209634293795060216691 := by
  unfold tailWord_6235150
  simp only [CollatzResearch.WordTrace]
  refine ⟨28426825420140487960721863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151609735574082602457183269 28426825420140487960721863)
  ·
    refine ⟨42640238130210731941082795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28426825420140487960721863 42640238130210731941082795)
    ·
      refine ⟨63960357195316097911624193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42640238130210731941082795 63960357195316097911624193)
      ·
        refine ⟨47970267896487073433718145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63960357195316097911624193 47970267896487073433718145)
        ·
          refine ⟨35977700922365305075288609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47970267896487073433718145 35977700922365305075288609)
          ·
            refine ⟨26983275691773978806466457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35977700922365305075288609 26983275691773978806466457)
            ·
              refine ⟨20237456768830484104849843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26983275691773978806466457 20237456768830484104849843)
              ·
                refine ⟨30356185153245726157274765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20237456768830484104849843 30356185153245726157274765)
                ·
                  refine ⟨11383569432467147308978037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30356185153245726157274765 11383569432467147308978037)
                  ·
                    refine ⟨1067209634293795060216691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11383569432467147308978037 1067209634293795060216691)
                    ·
                      rfl

theorem cell23_6235150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_6235150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235150 prefixEnd_6235150 := by exact prefixLift 6235150
  have htrace : WordTrace (prefixWord ++ tailWord_6235150) baseStart_6235150 baseEnd_6235150 := by
    simpa [prefixWord, tailWord_6235150, baseEnd_6235150] using wordTrace_append hprefix tailTrace_6235150
  have hstable : (prefixWord ++ tailWord_6235150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235150).length < 2 ^ (prefixWord ++ tailWord_6235150).sum := by decide
  have hdescent : baseEnd_6235150 < baseStart_6235150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235157 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_6235157 : Nat := 118140960795 + 6235157 * 2 ^ 59
def prefixEnd_6235157 : Nat := 4983230072969 + 3 ^ 40 * 6235157 * 2
def baseEnd_6235157 : Nat := 3201632497245966653262541

theorem tailTrace_6235157 : CollatzResearch.WordTrace tailWord_6235157 prefixEnd_6235157 3201632497245966653262541 := by
  unfold tailWord_6235157
  simp only [CollatzResearch.WordTrace]
  refine ⟨227414858672098543881279725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151609905781399029254186483 227414858672098543881279725)
  ·
    refine ⟨85280572002036953955479897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227414858672098543881279725 85280572002036953955479897)
    ·
      refine ⟨63960429001527715466609923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85280572002036953955479897 63960429001527715466609923)
      ·
        refine ⟨95940643502291573199914885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63960429001527715466609923 95940643502291573199914885)
        ·
          refine ⟨17988870656679669974984041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95940643502291573199914885 17988870656679669974984041)
          ·
            refine ⟨13491652992509752481238031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17988870656679669974984041 13491652992509752481238031)
            ·
              refine ⟨20237479488764628721857047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13491652992509752481238031 20237479488764628721857047)
              ·
                refine ⟨30356219233146943082785571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20237479488764628721857047 30356219233146943082785571)
                ·
                  refine ⟨45534328849720414624178357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30356219233146943082785571 45534328849720414624178357)
                  ·
                    refine ⟨4268843329661288871016721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45534328849720414624178357 4268843329661288871016721)
                    ·
                      refine ⟨3201632497245966653262541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268843329661288871016721 3201632497245966653262541)
                      ·
                        rfl

theorem cell23_6235157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_6235157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235157 prefixEnd_6235157 := by exact prefixLift 6235157
  have htrace : WordTrace (prefixWord ++ tailWord_6235157) baseStart_6235157 baseEnd_6235157 := by
    simpa [prefixWord, tailWord_6235157, baseEnd_6235157] using wordTrace_append hprefix tailTrace_6235157
  have hstable : (prefixWord ++ tailWord_6235157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235157).length < 2 ^ (prefixWord ++ tailWord_6235157).sum := by decide
  have hdescent : baseEnd_6235157 < baseStart_6235157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235167 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 1, 5]
def baseStart_6235167 : Nat := 118140960795 + 6235167 * 2 ^ 59
def prefixEnd_6235167 : Nat := 4983230072969 + 3 ^ 40 * 6235167 * 2
def baseEnd_6235167 : Nat := 1067212544017503871379165

theorem tailTrace_6235167 : CollatzResearch.WordTrace tailWord_6235167 prefixEnd_6235167 1067212544017503871379165 := by
  unfold tailWord_6235167
  simp only [CollatzResearch.WordTrace]
  refine ⟨227415223402062315589143755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151610148934708210392762503 227415223402062315589143755)
  ·
    refine ⟨341122835103093473383715633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227415223402062315589143755 341122835103093473383715633)
    ·
      refine ⟨255842126327320105037786725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341122835103093473383715633 255842126327320105037786725)
      ·
        refine ⟨47970398686372519694585011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255842126327320105037786725 47970398686372519694585011)
        ·
          refine ⟨71955598029558779541877517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47970398686372519694585011 71955598029558779541877517)
          ·
            refine ⟨26983349261084542328204069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71955598029558779541877517 26983349261084542328204069)
            ·
              refine ⟨5059377986453351686538263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26983349261084542328204069 5059377986453351686538263)
              ·
                refine ⟨7589066979680027529807395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059377986453351686538263 7589066979680027529807395)
                ·
                  refine ⟨11383600469520041294711093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7589066979680027529807395 11383600469520041294711093)
                  ·
                    refine ⟨1067212544017503871379165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11383600469520041294711093 1067212544017503871379165)
                    ·
                      rfl

theorem cell23_6235167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 1, 5].length) (baseStart_6235167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235167 prefixEnd_6235167 := by exact prefixLift 6235167
  have htrace : WordTrace (prefixWord ++ tailWord_6235167) baseStart_6235167 baseEnd_6235167 := by
    simpa [prefixWord, tailWord_6235167, baseEnd_6235167] using wordTrace_append hprefix tailTrace_6235167
  have hstable : (prefixWord ++ tailWord_6235167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235167).length < 2 ^ (prefixWord ++ tailWord_6235167).sum := by decide
  have hdescent : baseEnd_6235167 < baseStart_6235167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235180 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_6235180 : Nat := 118140960795 + 6235180 * 2 ^ 59
def prefixEnd_6235180 : Nat := 4983230072969 + 3 ^ 40 * 6235180 * 2
def baseEnd_6235180 : Nat := 1067214769100340021091645

theorem tailTrace_6235180 : CollatzResearch.WordTrace tailWord_6235180 prefixEnd_6235180 1067214769100340021091645 := by
  unfold tailWord_6235180
  simp only [CollatzResearch.WordTrace]
  refine ⟨113707848775507609404683497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151610465034010145872911329 113707848775507609404683497)
  ·
    refine ⟨85280886581630707053512623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113707848775507609404683497 85280886581630707053512623)
    ·
      refine ⟨127921329872446060580268935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85280886581630707053512623 127921329872446060580268935)
      ·
        refine ⟨191881994808669090870403403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127921329872446060580268935 191881994808669090870403403)
        ·
          refine ⟨287822992213003636305605105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191881994808669090870403403 287822992213003636305605105)
          ·
            refine ⟨215867244159752727229203829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287822992213003636305605105 215867244159752727229203829)
            ·
              refine ⟨20237554139976818177737859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 215867244159752727229203829 20237554139976818177737859)
              ·
                refine ⟨30356331209965227266606789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20237554139976818177737859 30356331209965227266606789)
                ·
                  refine ⟨5691812101868480112488773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30356331209965227266606789 5691812101868480112488773)
                  ·
                    refine ⟨1067214769100340021091645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691812101868480112488773 1067214769100340021091645)
                    ·
                      rfl

theorem cell23_6235180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_6235180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235180 prefixEnd_6235180 := by exact prefixLift 6235180
  have htrace : WordTrace (prefixWord ++ tailWord_6235180) baseStart_6235180 baseEnd_6235180 := by
    simpa [prefixWord, tailWord_6235180, baseEnd_6235180] using wordTrace_append hprefix tailTrace_6235180
  have hstable : (prefixWord ++ tailWord_6235180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235180).length < 2 ^ (prefixWord ++ tailWord_6235180).sum := by decide
  have hdescent : baseEnd_6235180 < baseStart_6235180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235197 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_6235197 : Nat := 118140960795 + 6235197 * 2 ^ 59
def prefixEnd_6235197 : Nat := 4983230072969 + 3 ^ 40 * 6235197 * 2
def baseEnd_6235197 : Nat := 1067217678824048832254119

theorem tailTrace_6235197 : CollatzResearch.WordTrace tailWord_6235197 prefixEnd_6235197 1067217678824048832254119 := by
  unfold tailWord_6235197
  simp only [CollatzResearch.WordTrace]
  refine ⟨227416317591953630712735845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151610878394635753808490563 227416317591953630712735845)
  ·
    refine ⟨42640559548491305758637971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227416317591953630712735845 42640559548491305758637971)
    ·
      refine ⟨63960839322736958637956957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42640559548491305758637971 63960839322736958637956957)
      ·
        refine ⟨23985314746026359489233859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63960839322736958637956957 23985314746026359489233859)
        ·
          refine ⟨35977972119039539233850789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23985314746026359489233859 35977972119039539233850789)
          ·
            refine ⟨6745869772319913606347023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35977972119039539233850789 6745869772319913606347023)
            ·
              refine ⟨10118804658479870409520535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6745869772319913606347023 10118804658479870409520535)
              ·
                refine ⟨15178206987719805614280803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10118804658479870409520535 15178206987719805614280803)
                ·
                  refine ⟨22767310481579708421421205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15178206987719805614280803 22767310481579708421421205)
                  ·
                    refine ⟨1067217678824048832254119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22767310481579708421421205 1067217678824048832254119)
                    ·
                      rfl

theorem cell23_6235197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_6235197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235197 prefixEnd_6235197 := by exact prefixLift 6235197
  have htrace : WordTrace (prefixWord ++ tailWord_6235197) baseStart_6235197 baseEnd_6235197 := by
    simpa [prefixWord, tailWord_6235197, baseEnd_6235197] using wordTrace_append hprefix tailTrace_6235197
  have hstable : (prefixWord ++ tailWord_6235197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235197).length < 2 ^ (prefixWord ++ tailWord_6235197).sum := by decide
  have hdescent : baseEnd_6235197 < baseStart_6235197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235207 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_6235207 : Nat := 118140960795 + 6235207 * 2 ^ 59
def prefixEnd_6235207 : Nat := 4983230072969 + 3 ^ 40 * 6235207 * 2
def baseEnd_6235207 : Nat := 3201658171278691457637311

theorem tailTrace_6235207 : CollatzResearch.WordTrace tailWord_6235207 prefixEnd_6235207 3201658171278691457637311 := by
  unfold tailWord_6235207
  simp only [CollatzResearch.WordTrace]
  refine ⟨227416682321917402420599875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151611121547944934947066583 227416682321917402420599875)
  ·
    refine ⟨341125023482876103630899813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227416682321917402420599875 341125023482876103630899813)
    ·
      refine ⟨63960941903039269430793715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341125023482876103630899813 63960941903039269430793715)
      ·
        refine ⟨95941412854558904146190573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63960941903039269430793715 95941412854558904146190573)
        ·
          refine ⟨35978029820459589054821465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95941412854558904146190573 35978029820459589054821465)
          ·
            refine ⟨26983522365344691791116099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35978029820459589054821465 26983522365344691791116099)
            ·
              refine ⟨40475283548017037686674149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26983522365344691791116099 40475283548017037686674149)
              ·
                refine ⟨7589115665253194566251403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40475283548017037686674149 7589115665253194566251403)
                ·
                  refine ⟨11383673497879791849377105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7589115665253194566251403 11383673497879791849377105)
                  ·
                    refine ⟨8537755123409843887032829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11383673497879791849377105 8537755123409843887032829)
                    ·
                      refine ⟨3201658171278691457637311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8537755123409843887032829 3201658171278691457637311)
                      ·
                        rfl

theorem cell23_6235207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_6235207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235207 prefixEnd_6235207 := by exact prefixLift 6235207
  have htrace : WordTrace (prefixWord ++ tailWord_6235207) baseStart_6235207 baseEnd_6235207 := by
    simpa [prefixWord, tailWord_6235207, baseEnd_6235207] using wordTrace_append hprefix tailTrace_6235207
  have hstable : (prefixWord ++ tailWord_6235207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235207).length < 2 ^ (prefixWord ++ tailWord_6235207).sum := by decide
  have hdescent : baseEnd_6235207 < baseStart_6235207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235210 : List Nat := [3, 1, 2, 1, 1, 2, 6, 7]
def baseStart_6235210 : Nat := 118140960795 + 6235210 * 2 ^ 59
def prefixEnd_6235210 : Nat := 4983230072969 + 3 ^ 40 * 6235210 * 2
def baseEnd_6235210 : Nat := 118579989322987220218511

theorem tailTrace_6235210 : CollatzResearch.WordTrace tailWord_6235210 prefixEnd_6235210 118579989322987220218511 := by
  unfold tailWord_6235210
  simp only [CollatzResearch.WordTrace]
  refine ⟨56854197935226633483239771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151611194493937689288639389 56854197935226633483239771)
  ·
    refine ⟨85281296902839950224859657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56854197935226633483239771 85281296902839950224859657)
    ·
      refine ⟨63960972677129962668644743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85281296902839950224859657 63960972677129962668644743)
      ·
        refine ⟨95941459015694944002967115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63960972677129962668644743 95941459015694944002967115)
        ·
          refine ⟨143912188523542416004450673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95941459015694944002967115 143912188523542416004450673)
          ·
            refine ⟨107934141392656812003338005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143912188523542416004450673 107934141392656812003338005)
            ·
              refine ⟨5059412877780788062656469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107934141392656812003338005 5059412877780788062656469)
              ·
                refine ⟨118579989322987220218511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5059412877780788062656469 118579989322987220218511)
                ·
                  rfl

theorem cell23_6235210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 7].length) (baseStart_6235210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235210 prefixEnd_6235210 := by exact prefixLift 6235210
  have htrace : WordTrace (prefixWord ++ tailWord_6235210) baseStart_6235210 baseEnd_6235210 := by
    simpa [prefixWord, tailWord_6235210, baseEnd_6235210] using wordTrace_append hprefix tailTrace_6235210
  have hstable : (prefixWord ++ tailWord_6235210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235210).length < 2 ^ (prefixWord ++ tailWord_6235210).sum := by decide
  have hdescent : baseEnd_6235210 < baseStart_6235210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235223 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 1, 9]
def baseStart_6235223 : Nat := 118140960795 + 6235223 * 2 ^ 59
def prefixEnd_6235223 : Nat := 4983230072969 + 3 ^ 40 * 6235223 * 2
def baseEnd_6235223 : Nat := 1067222128989721131679079

theorem tailTrace_6235223 : CollatzResearch.WordTrace tailWord_6235223 prefixEnd_6235223 1067222128989721131679079 := by
  unfold tailWord_6235223
  simp only [CollatzResearch.WordTrace]
  refine ⟨227417265889859437153182323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151611510593239624768788215 227417265889859437153182323)
  ·
    refine ⟨341125898834789155729773485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227417265889859437153182323 341125898834789155729773485)
    ·
      refine ⟨127922212063045933398665057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341125898834789155729773485 127922212063045933398665057)
      ·
        refine ⟨95941659047284450048998793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127922212063045933398665057 95941659047284450048998793)
        ·
          refine ⟨71956244285463337536749095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95941659047284450048998793 71956244285463337536749095)
          ·
            refine ⟨107934366428195006305123643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71956244285463337536749095 107934366428195006305123643)
            ·
              refine ⟨161901549642292509457685465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107934366428195006305123643 161901549642292509457685465)
              ·
                refine ⟨121426162231719382093264099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161901549642292509457685465 121426162231719382093264099)
                ·
                  refine ⟨182139243347579073139896149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121426162231719382093264099 182139243347579073139896149)
                  ·
                    refine ⟨1067222128989721131679079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 182139243347579073139896149 1067222128989721131679079)
                    ·
                      rfl

theorem cell23_6235223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_6235223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235223 prefixEnd_6235223 := by exact prefixLift 6235223
  have htrace : WordTrace (prefixWord ++ tailWord_6235223) baseStart_6235223 baseEnd_6235223 := by
    simpa [prefixWord, tailWord_6235223, baseEnd_6235223] using wordTrace_append hprefix tailTrace_6235223
  have hstable : (prefixWord ++ tailWord_6235223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235223).length < 2 ^ (prefixWord ++ tailWord_6235223).sum := by decide
  have hdescent : baseEnd_6235223 < baseStart_6235223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235237 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_6235237 : Nat := 118140960795 + 6235237 * 2 ^ 59
def prefixEnd_6235237 : Nat := 4983230072969 + 3 ^ 40 * 6235237 * 2
def baseEnd_6235237 : Nat := 3201673575698326340262173

theorem tailTrace_6235237 : CollatzResearch.WordTrace tailWord_6235237 prefixEnd_6235237 3201673575698326340262173 := by
  unfold tailWord_6235237
  simp only [CollatzResearch.WordTrace]
  refine ⟨227417776511808717544191965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151611851007872478362794643 227417776511808717544191965)
  ·
    refine ⟨85281666191928269079071987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227417776511808717544191965 85281666191928269079071987)
    ·
      refine ⟨127922499287892403618607981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85281666191928269079071987 127922499287892403618607981)
      ·
        refine ⟨47970937232959651356977993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127922499287892403618607981 47970937232959651356977993)
        ·
          refine ⟨35978202924719738517733495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47970937232959651356977993 35978202924719738517733495)
          ·
            refine ⟨53967304387079607776600243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35978202924719738517733495 53967304387079607776600243)
            ·
              refine ⟨80950956580619411664900365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53967304387079607776600243 80950956580619411664900365)
              ·
                refine ⟨30356608717732279374337637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80950956580619411664900365 30356608717732279374337637)
                ·
                  refine ⟨5691864134574802382688307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30356608717732279374337637 5691864134574802382688307)
                  ·
                    refine ⟨8537796201862203574032461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5691864134574802382688307 8537796201862203574032461)
                    ·
                      refine ⟨3201673575698326340262173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8537796201862203574032461 3201673575698326340262173)
                      ·
                        rfl

theorem cell23_6235237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_6235237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235237 prefixEnd_6235237 := by exact prefixLift 6235237
  have htrace : WordTrace (prefixWord ++ tailWord_6235237) baseStart_6235237 baseEnd_6235237 := by
    simpa [prefixWord, tailWord_6235237, baseEnd_6235237] using wordTrace_append hprefix tailTrace_6235237
  have hstable : (prefixWord ++ tailWord_6235237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235237).length < 2 ^ (prefixWord ++ tailWord_6235237).sum := by decide
  have hdescent : baseEnd_6235237 < baseStart_6235237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235247 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 3, 3, 2]
def baseStart_6235247 : Nat := 118140960795 + 6235247 * 2 ^ 59
def prefixEnd_6235247 : Nat := 4983230072969 + 3 ^ 40 * 6235247 * 2
def baseEnd_6235247 : Nat := 3201678710504871301137127

theorem tailTrace_6235247 : CollatzResearch.WordTrace tailWord_6235247 prefixEnd_6235247 3201678710504871301137127 := by
  unfold tailWord_6235247
  simp only [CollatzResearch.WordTrace]
  refine ⟨227418141241772489252055995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151612094161181659501370663 227418141241772489252055995)
  ·
    refine ⟨341127211862658733878083993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227418141241772489252055995 341127211862658733878083993)
    ·
      refine ⟨255845408896994050408562995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341127211862658733878083993 255845408896994050408562995)
      ·
        refine ⟨383768113345491075612844493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255845408896994050408562995 383768113345491075612844493)
        ·
          refine ⟨143913042504559153354816685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383768113345491075612844493 143913042504559153354816685)
          ·
            refine ⟨53967390939209682508056257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143913042504559153354816685 53967390939209682508056257)
            ·
              refine ⟨40475543204407261881042193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53967390939209682508056257 40475543204407261881042193)
              ·
                refine ⟨30356657403305446410781645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40475543204407261881042193 30356657403305446410781645)
                ·
                  refine ⟨11383746526239542404043117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30356657403305446410781645 11383746526239542404043117)
                  ·
                    refine ⟨4268904947339828401516169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11383746526239542404043117 4268904947339828401516169)
                    ·
                      refine ⟨3201678710504871301137127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268904947339828401516169 3201678710504871301137127)
                      ·
                        rfl

theorem cell23_6235247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 3, 2].length) (baseStart_6235247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235247 prefixEnd_6235247 := by exact prefixLift 6235247
  have htrace : WordTrace (prefixWord ++ tailWord_6235247) baseStart_6235247 baseEnd_6235247 := by
    simpa [prefixWord, tailWord_6235247, baseEnd_6235247] using wordTrace_append hprefix tailTrace_6235247
  have hstable : (prefixWord ++ tailWord_6235247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235247).length < 2 ^ (prefixWord ++ tailWord_6235247).sum := by decide
  have hdescent : baseEnd_6235247 < baseStart_6235247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235263 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_6235263 : Nat := 118140960795 + 6235263 * 2 ^ 59
def prefixEnd_6235263 : Nat := 4983230072969 + 3 ^ 40 * 6235263 * 2
def baseEnd_6235263 : Nat := 3201686926195343238537053

theorem tailTrace_6235263 : CollatzResearch.WordTrace tailWord_6235263 prefixEnd_6235263 3201686926195343238537053 := by
  unfold tailWord_6235263
  simp only [CollatzResearch.WordTrace]
  refine ⟨227418724809714523984638443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151612483206476349323092295 227418724809714523984638443)
  ·
    refine ⟨341128087214571785976957665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227418724809714523984638443 341128087214571785976957665)
    ·
      refine ⟨255846065410928839482718249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341128087214571785976957665 255846065410928839482718249)
      ·
        refine ⟨191884549058196629612038687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255846065410928839482718249 191884549058196629612038687)
        ·
          refine ⟨287826823587294944418058031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191884549058196629612038687 287826823587294944418058031)
          ·
            refine ⟨431740235380942416627087047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287826823587294944418058031 431740235380942416627087047)
            ·
              refine ⟨647610353071413624940630571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431740235380942416627087047 647610353071413624940630571)
              ·
                refine ⟨971415529607120437410945857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647610353071413624940630571 971415529607120437410945857)
                ·
                  refine ⟨728561647205340328058209393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971415529607120437410945857 728561647205340328058209393)
                  ·
                    refine ⟨546421235404005246043657045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 728561647205340328058209393 546421235404005246043657045)
                    ·
                      refine ⟨3201686926195343238537053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 546421235404005246043657045 3201686926195343238537053)
                      ·
                        rfl

theorem cell23_6235263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_6235263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235263 prefixEnd_6235263 := by exact prefixLift 6235263
  have htrace : WordTrace (prefixWord ++ tailWord_6235263) baseStart_6235263 baseEnd_6235263 := by
    simpa [prefixWord, tailWord_6235263, baseEnd_6235263] using wordTrace_append hprefix tailTrace_6235263
  have hstable : (prefixWord ++ tailWord_6235263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235263).length < 2 ^ (prefixWord ++ tailWord_6235263).sum := by decide
  have hdescent : baseEnd_6235263 < baseStart_6235263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235264 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 1, 3, 2]
def baseStart_6235264 : Nat := 118140960795 + 6235264 * 2 ^ 59
def prefixEnd_6235264 : Nat := 4983230072969 + 3 ^ 40 * 6235264 * 2
def baseEnd_6235264 : Nat := 3201687439675997734624549

theorem tailTrace_6235264 : CollatzResearch.WordTrace tailWord_6235264 prefixEnd_6235264 3201687439675997734624549 := by
  unfold tailWord_6235264
  simp only [CollatzResearch.WordTrace]
  refine ⟨113709380641355450577712423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151612507521807267436949897 113709380641355450577712423)
  ·
    refine ⟨170564070962033175866568635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113709380641355450577712423 170564070962033175866568635)
    ·
      refine ⟨255846106443049763799852953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170564070962033175866568635 255846106443049763799852953)
      ·
        refine ⟨191884579832287322849889715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255846106443049763799852953 191884579832287322849889715)
        ·
          refine ⟨287826869748430984274834573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191884579832287322849889715 287826869748430984274834573)
          ·
            refine ⟨107935076155661619103062965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287826869748430984274834573 107935076155661619103062965)
            ·
              refine ⟨10118913389593276790912153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107935076155661619103062965 10118913389593276790912153)
              ·
                refine ⟨7589185042194957593184115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10118913389593276790912153 7589185042194957593184115)
                ·
                  refine ⟨11383777563292436389776173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7589185042194957593184115 11383777563292436389776173)
                  ·
                    refine ⟨4268916586234663646166065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11383777563292436389776173 4268916586234663646166065)
                    ·
                      refine ⟨3201687439675997734624549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4268916586234663646166065 3201687439675997734624549)
                      ·
                        rfl

theorem cell23_6235264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_6235264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235264 prefixEnd_6235264 := by exact prefixLift 6235264
  have htrace : WordTrace (prefixWord ++ tailWord_6235264) baseStart_6235264 baseEnd_6235264 := by
    simpa [prefixWord, tailWord_6235264, baseEnd_6235264] using wordTrace_append hprefix tailTrace_6235264
  have hstable : (prefixWord ++ tailWord_6235264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235264).length < 2 ^ (prefixWord ++ tailWord_6235264).sum := by decide
  have hdescent : baseEnd_6235264 < baseStart_6235264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235404 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_6235404 : Nat := 118140960795 + 6235404 * 2 ^ 59
def prefixEnd_6235404 : Nat := 4983230072969 + 3 ^ 40 * 6235404 * 2
def baseEnd_6235404 : Nat := 3201759326967627186873905

theorem tailTrace_6235404 : CollatzResearch.WordTrace tailWord_6235404 prefixEnd_6235404 3201759326967627186873905 := by
  unfold tailWord_6235404
  simp only [CollatzResearch.WordTrace]
  refine ⟨113711933751101852532760633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151615911668135803377014177 113711933751101852532760633)
  ·
    refine ⟨85283950313326389399570475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113711933751101852532760633 85283950313326389399570475)
    ·
      refine ⟨127925925469989584099355713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85283950313326389399570475 127925925469989584099355713)
      ·
        refine ⟨95944444102492188074516785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127925925469989584099355713 95944444102492188074516785)
        ·
          refine ⟨71958333076869141055887589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95944444102492188074516785 71958333076869141055887589)
          ·
            refine ⟨13492187451912963947978923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71958333076869141055887589 13492187451912963947978923)
            ·
              refine ⟨20238281177869445921968385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13492187451912963947978923 20238281177869445921968385)
              ·
                refine ⟨15178710883402084441476289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20238281177869445921968385 15178710883402084441476289)
                ·
                  refine ⟨11384033162551563331107217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15178710883402084441476289 11384033162551563331107217)
                  ·
                    refine ⟨8538024871913672498330413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11384033162551563331107217 8538024871913672498330413)
                    ·
                      refine ⟨3201759326967627186873905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538024871913672498330413 3201759326967627186873905)
                      ·
                        rfl

theorem cell23_6235404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_6235404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235404 prefixEnd_6235404 := by exact prefixLift 6235404
  have htrace : WordTrace (prefixWord ++ tailWord_6235404) baseStart_6235404 baseEnd_6235404 := by
    simpa [prefixWord, tailWord_6235404, baseEnd_6235404] using wordTrace_append hprefix tailTrace_6235404
  have hstable : (prefixWord ++ tailWord_6235404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235404).length < 2 ^ (prefixWord ++ tailWord_6235404).sum := by decide
  have hdescent : baseEnd_6235404 < baseStart_6235404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235424 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 6]
def baseStart_6235424 : Nat := 118140960795 + 6235424 * 2 ^ 59
def prefixEnd_6235424 : Nat := 4983230072969 + 3 ^ 40 * 6235424 * 2
def baseEnd_6235424 : Nat := 355752177397857456513757

theorem tailTrace_6235424 : CollatzResearch.WordTrace tailWord_6235424 prefixEnd_6235424 355752177397857456513757 := by
  unfold tailWord_6235424
  simp only [CollatzResearch.WordTrace]
  refine ⟨113712298481065624240624663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151616397974754165654166217 113712298481065624240624663)
  ·
    refine ⟨170568447721598436360936995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113712298481065624240624663 170568447721598436360936995)
    ·
      refine ⟨255852671582397654541405493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170568447721598436360936995 255852671582397654541405493)
      ·
        refine ⟨23986187960849780113256765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255852671582397654541405493 23986187960849780113256765)
        ·
          refine ⟨8994820485318667542471287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23986187960849780113256765 8994820485318667542471287)
          ·
            refine ⟨13492230727978001313706931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8994820485318667542471287 13492230727978001313706931)
            ·
              refine ⟨20238346091967001970560397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13492230727978001313706931 20238346091967001970560397)
              ·
                refine ⟨7589379784487625738960149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20238346091967001970560397 7589379784487625738960149)
                ·
                  refine ⟨355752177397857456513757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7589379784487625738960149 355752177397857456513757)
                  ·
                    rfl

theorem cell23_6235424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 6].length) (baseStart_6235424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235424 prefixEnd_6235424 := by exact prefixLift 6235424
  have htrace : WordTrace (prefixWord ++ tailWord_6235424) baseStart_6235424 baseEnd_6235424 := by
    simpa [prefixWord, tailWord_6235424, baseEnd_6235424] using wordTrace_append hprefix tailTrace_6235424
  have hstable : (prefixWord ++ tailWord_6235424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235424).length < 2 ^ (prefixWord ++ tailWord_6235424).sum := by decide
  have hdescent : baseEnd_6235424 < baseStart_6235424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235462 : List Nat := [6, 1, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_6235462 : Nat := 118140960795 + 6235462 * 2 ^ 59
def prefixEnd_6235462 : Nat := 4983230072969 + 3 ^ 40 * 6235462 * 2
def baseEnd_6235462 : Nat := 1067263036281862653316213

theorem tailTrace_6235462 : CollatzResearch.WordTrace tailWord_6235462 prefixEnd_6235462 1067263036281862653316213 := by
  unfold tailWord_6235462
  simp only [CollatzResearch.WordTrace]
  refine ⟨7107061966749799405347895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151617321957329053980755093 7107061966749799405347895)
  ·
    refine ⟨10660592950124699108021843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7107061966749799405347895 10660592950124699108021843)
    ·
      refine ⟨15990889425187048662032765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10660592950124699108021843 15990889425187048662032765)
      ·
        refine ⟨5996583534445143248262287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15990889425187048662032765 5996583534445143248262287)
        ·
          refine ⟨8994875301667714872393431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5996583534445143248262287 8994875301667714872393431)
          ·
            refine ⟨13492312952501572308590147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8994875301667714872393431 13492312952501572308590147)
            ·
              refine ⟨20238469428752358462885221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13492312952501572308590147 20238469428752358462885221)
              ·
                refine ⟨3794713017891067211790979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20238469428752358462885221 3794713017891067211790979)
                ·
                  refine ⟨5692069526836600817686469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794713017891067211790979 5692069526836600817686469)
                  ·
                    refine ⟨1067263036281862653316213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692069526836600817686469 1067263036281862653316213)
                    ·
                      rfl

theorem cell23_6235462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_6235462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235462 prefixEnd_6235462 := by exact prefixLift 6235462
  have htrace : WordTrace (prefixWord ++ tailWord_6235462) baseStart_6235462 baseEnd_6235462 := by
    simpa [prefixWord, tailWord_6235462, baseEnd_6235462] using wordTrace_append hprefix tailTrace_6235462
  have hstable : (prefixWord ++ tailWord_6235462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235462).length < 2 ^ (prefixWord ++ tailWord_6235462).sum := by decide
  have hdescent : baseEnd_6235462 < baseStart_6235462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235467 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 8, 4]
def baseStart_6235467 : Nat := 118140960795 + 6235467 * 2 ^ 59
def prefixEnd_6235467 : Nat := 4983230072969 + 3 ^ 40 * 6235467 * 2
def baseEnd_6235467 : Nat := 1067263892082953480128705

theorem tailTrace_6235467 : CollatzResearch.WordTrace tailWord_6235467 prefixEnd_6235467 1067263892082953480128705 := by
  unfold tailWord_6235467
  simp only [CollatzResearch.WordTrace]
  refine ⟨227426165300975466825064655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151617443533983644550043103 227426165300975466825064655)
  ·
    refine ⟨341139247951463200237596983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227426165300975466825064655 341139247951463200237596983)
    ·
      refine ⟨511708871927194800356395475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341139247951463200237596983 511708871927194800356395475)
      ·
        refine ⟨767563307890792200534593213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511708871927194800356395475 767563307890792200534593213)
        ·
          refine ⟨287836240459047075200472455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767563307890792200534593213 287836240459047075200472455)
          ·
            refine ⟨431754360688570612800708683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287836240459047075200472455 431754360688570612800708683)
            ·
              refine ⟨647631541032855919201063025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431754360688570612800708683 647631541032855919201063025)
              ·
                refine ⟨485723655774641939400797269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647631541032855919201063025 485723655774641939400797269)
                ·
                  refine ⟨5692074091109085227353093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 485723655774641939400797269 5692074091109085227353093)
                  ·
                    refine ⟨1067263892082953480128705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692074091109085227353093 1067263892082953480128705)
                    ·
                      rfl

theorem cell23_6235467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 4].length) (baseStart_6235467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235467 prefixEnd_6235467 := by exact prefixLift 6235467
  have htrace : WordTrace (prefixWord ++ tailWord_6235467) baseStart_6235467 baseEnd_6235467 := by
    simpa [prefixWord, tailWord_6235467, baseEnd_6235467] using wordTrace_append hprefix tailTrace_6235467
  have hstable : (prefixWord ++ tailWord_6235467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235467).length < 2 ^ (prefixWord ++ tailWord_6235467).sum := by decide
  have hdescent : baseEnd_6235467 < baseStart_6235467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235468 : List Nat := [2, 2, 1, 3, 2, 3, 1, 4, 1, 1, 3]
def baseStart_6235468 : Nat := 118140960795 + 6235468 * 2 ^ 59
def prefixEnd_6235468 : Nat := 4983230072969 + 3 ^ 40 * 6235468 * 2
def baseEnd_6235468 : Nat := 3201792189729514936473611

theorem tailTrace_6235468 : CollatzResearch.WordTrace tailWord_6235468 prefixEnd_6235468 3201792189729514936473611 := by
  unfold tailWord_6235468
  simp only [CollatzResearch.WordTrace]
  refine ⟨113713100886985921997925529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151617467849314562663900705 113713100886985921997925529)
  ·
    refine ⟨85284825665239441498444147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113713100886985921997925529 85284825665239441498444147)
    ·
      refine ⟨127927238497859162247666221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85284825665239441498444147 127927238497859162247666221)
      ·
        refine ⟨47972714436697185842874833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127927238497859162247666221 47972714436697185842874833)
        ·
          refine ⟨35979535827522889382156125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47972714436697185842874833 35979535827522889382156125)
          ·
            refine ⟨13492325935321083518308547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35979535827522889382156125 13492325935321083518308547)
            ·
              refine ⟨20238488902981625277462821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13492325935321083518308547 20238488902981625277462821)
              ·
                refine ⟨3794716669309054739524279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20238488902981625277462821 3794716669309054739524279)
                ·
                  refine ⟨5692075003963582109286419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794716669309054739524279 5692075003963582109286419)
                  ·
                    refine ⟨8538112505945373163929629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692075003963582109286419 8538112505945373163929629)
                    ·
                      refine ⟨3201792189729514936473611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538112505945373163929629 3201792189729514936473611)
                      ·
                        rfl

theorem cell23_6235468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_6235468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235468 prefixEnd_6235468 := by exact prefixLift 6235468
  have htrace : WordTrace (prefixWord ++ tailWord_6235468) baseStart_6235468 baseEnd_6235468 := by
    simpa [prefixWord, tailWord_6235468, baseEnd_6235468] using wordTrace_append hprefix tailTrace_6235468
  have hstable : (prefixWord ++ tailWord_6235468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235468).length < 2 ^ (prefixWord ++ tailWord_6235468).sum := by decide
  have hdescent : baseEnd_6235468 < baseStart_6235468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235474 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_6235474 : Nat := 118140960795 + 6235474 * 2 ^ 59
def prefixEnd_6235474 : Nat := 4983230072969 + 3 ^ 40 * 6235474 * 2
def baseEnd_6235474 : Nat := 3201795270613441912998583

theorem tailTrace_6235474 : CollatzResearch.WordTrace tailWord_6235474 prefixEnd_6235474 3201795270613441912998583 := by
  unfold tailWord_6235474
  simp only [CollatzResearch.WordTrace]
  refine ⟨56856605152987526755142369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151617613741300071347046317 56856605152987526755142369)
  ·
    refine ⟨42642453864740645066356777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56856605152987526755142369 42642453864740645066356777)
    ·
      refine ⟨31981840398555483799767583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42642453864740645066356777 31981840398555483799767583)
      ·
        refine ⟨47972760597833225699651375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31981840398555483799767583 47972760597833225699651375)
        ·
          refine ⟨71959140896749838549477063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47972760597833225699651375 71959140896749838549477063)
          ·
            refine ⟨107938711345124757824215595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71959140896749838549477063 107938711345124757824215595)
            ·
              refine ⟨161908067017687136736323393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107938711345124757824215595 161908067017687136736323393)
              ·
                refine ⟨121431050263265352552242545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161908067017687136736323393 121431050263265352552242545)
                ·
                  refine ⟨91073287697449014414181909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121431050263265352552242545 91073287697449014414181909)
                  ·
                    refine ⟨4269060360817922550664777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 91073287697449014414181909 4269060360817922550664777)
                    ·
                      refine ⟨3201795270613441912998583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269060360817922550664777 3201795270613441912998583)
                      ·
                        rfl

theorem cell23_6235474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_6235474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235474 prefixEnd_6235474 := by exact prefixLift 6235474
  have htrace : WordTrace (prefixWord ++ tailWord_6235474) baseStart_6235474 baseEnd_6235474 := by
    simpa [prefixWord, tailWord_6235474, baseEnd_6235474] using wordTrace_append hprefix tailTrace_6235474
  have hstable : (prefixWord ++ tailWord_6235474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235474).length < 2 ^ (prefixWord ++ tailWord_6235474).sum := by decide
  have hdescent : baseEnd_6235474 < baseStart_6235474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235491 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 5, 2, 2]
def baseStart_6235491 : Nat := 118140960795 + 6235491 * 2 ^ 59
def prefixEnd_6235491 : Nat := 4983230072969 + 3 ^ 40 * 6235491 * 2
def baseEnd_6235491 : Nat := 3201803999784568346486005

theorem tailTrace_6235491 : CollatzResearch.WordTrace tailWord_6235491 prefixEnd_6235491 3201803999784568346486005 := by
  unfold tailWord_6235491
  simp only [CollatzResearch.WordTrace]
  refine ⟨227427040652888518923938327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151618027101925679282625551 227427040652888518923938327)
  ·
    refine ⟨341140560979332778385907491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227427040652888518923938327 341140560979332778385907491)
    ·
      refine ⟨511710841468999167578861237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341140560979332778385907491 511710841468999167578861237)
      ·
        refine ⟨47972891387718671960518241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 511710841468999167578861237 47972891387718671960518241)
        ·
          refine ⟨35979668540789003970388681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47972891387718671960518241 35979668540789003970388681)
          ·
            refine ⟨26984751405591752977791511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35979668540789003970388681 26984751405591752977791511)
            ·
              refine ⟨40477127108387629466687267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26984751405591752977791511 40477127108387629466687267)
              ·
                refine ⟨60715690662581444200030901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40477127108387629466687267 60715690662581444200030901)
                ·
                  refine ⟨5692095999617010393752897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60715690662581444200030901 5692095999617010393752897)
                  ·
                    refine ⟨4269071999712757795314673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5692095999617010393752897 4269071999712757795314673)
                    ·
                      refine ⟨3201803999784568346486005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269071999712757795314673 3201803999784568346486005)
                      ·
                        rfl

theorem cell23_6235491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_6235491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235491 prefixEnd_6235491 := by exact prefixLift 6235491
  have htrace : WordTrace (prefixWord ++ tailWord_6235491) baseStart_6235491 baseEnd_6235491 := by
    simpa [prefixWord, tailWord_6235491, baseEnd_6235491] using wordTrace_append hprefix tailTrace_6235491
  have hstable : (prefixWord ++ tailWord_6235491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235491).length < 2 ^ (prefixWord ++ tailWord_6235491).sum := by decide
  have hdescent : baseEnd_6235491 < baseStart_6235491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235495 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_6235495 : Nat := 118140960795 + 6235495 * 2 ^ 59
def prefixEnd_6235495 : Nat := 4983230072969 + 3 ^ 40 * 6235495 * 2
def baseEnd_6235495 : Nat := 3201806053707186330835987

theorem tailTrace_6235495 : CollatzResearch.WordTrace tailWord_6235495 prefixEnd_6235495 3201806053707186330835987 := by
  unfold tailWord_6235495
  simp only [CollatzResearch.WordTrace]
  refine ⟨227427186544874027607083939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151618124363249351738055959 227427186544874027607083939)
  ·
    refine ⟨341140779817311041410625909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227427186544874027607083939 341140779817311041410625909)
    ·
      refine ⟨31981948107872910132246179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 341140779817311041410625909 31981948107872910132246179)
      ·
        refine ⟨47972922161809365198369269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31981948107872910132246179 47972922161809365198369269)
        ·
          refine ⟨4497461452669627987347119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47972922161809365198369269 4497461452669627987347119)
          ·
            refine ⟨6746192179004441981020679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497461452669627987347119 6746192179004441981020679)
            ·
              refine ⟨10119288268506662971531019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746192179004441981020679 10119288268506662971531019)
              ·
                refine ⟨15178932402759994457296529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10119288268506662971531019 15178932402759994457296529)
                ·
                  refine ⟨11384199302069995842972397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15178932402759994457296529 11384199302069995842972397)
                  ·
                    refine ⟨4269074738276248441114649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11384199302069995842972397 4269074738276248441114649)
                    ·
                      refine ⟨3201806053707186330835987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269074738276248441114649 3201806053707186330835987)
                      ·
                        rfl

theorem cell23_6235495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_6235495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235495 prefixEnd_6235495 := by exact prefixLift 6235495
  have htrace : WordTrace (prefixWord ++ tailWord_6235495) baseStart_6235495 baseEnd_6235495 := by
    simpa [prefixWord, tailWord_6235495, baseEnd_6235495] using wordTrace_append hprefix tailTrace_6235495
  have hstable : (prefixWord ++ tailWord_6235495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235495).length < 2 ^ (prefixWord ++ tailWord_6235495).sum := by decide
  have hdescent : baseEnd_6235495 < baseStart_6235495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235502 : List Nat := [4, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_6235502 : Nat := 118140960795 + 6235502 * 2 ^ 59
def prefixEnd_6235502 : Nat := 4983230072969 + 3 ^ 40 * 6235502 * 2
def baseEnd_6235502 : Nat := 3201809648071767803448455

theorem tailTrace_6235502 : CollatzResearch.WordTrace tailWord_6235502 prefixEnd_6235502 3201809648071767803448455 := by
  unfold tailWord_6235502
  simp only [CollatzResearch.WordTrace]
  refine ⟨28428430231981083475323595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151618294570565778535059173 28428430231981083475323595)
  ·
    refine ⟨42642645347971625212985393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28428430231981083475323595 42642645347971625212985393)
    ·
      refine ⟨31981984010978718909739045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42642645347971625212985393 31981984010978718909739045)
      ·
        refine ⟨5996622002058509795576071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31981984010978718909739045 5996622002058509795576071)
        ·
          refine ⟨8994933003087764693364107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5996622002058509795576071 8994933003087764693364107)
          ·
            refine ⟨13492399504631647040046161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8994933003087764693364107 13492399504631647040046161)
            ·
              refine ⟨10119299628473735280034621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13492399504631647040046161 10119299628473735280034621)
              ·
                refine ⟨3794737360677650730012983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10119299628473735280034621 3794737360677650730012983)
                ·
                  refine ⟨5692106041016476095019475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794737360677650730012983 5692106041016476095019475)
                  ·
                    refine ⟨8538159061524714142529213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692106041016476095019475 8538159061524714142529213)
                    ·
                      refine ⟨3201809648071767803448455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538159061524714142529213 3201809648071767803448455)
                      ·
                        rfl

theorem cell23_6235502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_6235502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235502 prefixEnd_6235502 := by exact prefixLift 6235502
  have htrace : WordTrace (prefixWord ++ tailWord_6235502) baseStart_6235502 baseEnd_6235502 := by
    simpa [prefixWord, tailWord_6235502, baseEnd_6235502] using wordTrace_append hprefix tailTrace_6235502
  have hstable : (prefixWord ++ tailWord_6235502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235502).length < 2 ^ (prefixWord ++ tailWord_6235502).sum := by decide
  have hdescent : baseEnd_6235502 < baseStart_6235502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235541 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_6235541 : Nat := 118140960795 + 6235541 * 2 ^ 59
def prefixEnd_6235541 : Nat := 4983230072969 + 3 ^ 40 * 6235541 * 2
def baseEnd_6235541 : Nat := 3201829673817293150860775

theorem tailTrace_6235541 : CollatzResearch.WordTrace tailWord_6235541 prefixEnd_6235541 3201829673817293150860775 := by
  unfold tailWord_6235541
  simp only [CollatzResearch.WordTrace]
  refine ⟨227428864302707377463258477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151619242868471584975505651 227428864302707377463258477)
  ·
    refine ⟨85285824113515266548721929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227428864302707377463258477 85285824113515266548721929)
    ·
      refine ⟨63964368085136449911541447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85285824113515266548721929 63964368085136449911541447)
      ·
        refine ⟨95946552127704674867312171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63964368085136449911541447 95946552127704674867312171)
        ·
          refine ⟨143919828191557012300968257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95946552127704674867312171 143919828191557012300968257)
          ·
            refine ⟨107939871143667759225726193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143919828191557012300968257 107939871143667759225726193)
            ·
              refine ⟨80954903357750819419294645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107939871143667759225726193 80954903357750819419294645)
              ·
                refine ⟨7589522189789139320558873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80954903357750819419294645 7589522189789139320558873)
                ·
                  refine ⟨5692141642341854490419155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7589522189789139320558873 5692141642341854490419155)
                  ·
                    refine ⟨8538212463512781735628733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692141642341854490419155 8538212463512781735628733)
                    ·
                      refine ⟨3201829673817293150860775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538212463512781735628733 3201829673817293150860775)
                      ·
                        rfl

theorem cell23_6235541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_6235541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235541 prefixEnd_6235541 := by exact prefixLift 6235541
  have htrace : WordTrace (prefixWord ++ tailWord_6235541) baseStart_6235541 baseEnd_6235541 := by
    simpa [prefixWord, tailWord_6235541, baseEnd_6235541] using wordTrace_append hprefix tailTrace_6235541
  have hstable : (prefixWord ++ tailWord_6235541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235541).length < 2 ^ (prefixWord ++ tailWord_6235541).sum := by decide
  have hdescent : baseEnd_6235541 < baseStart_6235541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235548 : List Nat := [2, 2, 3, 4, 1, 2, 2, 7]
def baseStart_6235548 : Nat := 118140960795 + 6235548 * 2 ^ 59
def prefixEnd_6235548 : Nat := 4983230072969 + 3 ^ 40 * 6235548 * 2
def baseEnd_6235548 : Nat := 118586417340069430499009

theorem tailTrace_6235548 : CollatzResearch.WordTrace tailWord_6235548 prefixEnd_6235548 118586417340069430499009 := by
  unfold tailWord_6235548
  simp only [CollatzResearch.WordTrace]
  refine ⟨113714559806841008829381649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151619413075788011772508865 113714559806841008829381649)
  ·
    refine ⟨85285919855130756622036237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113714559806841008829381649 85285919855130756622036237)
    ·
      refine ⟨31982219945674033733263589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85285919855130756622036237 31982219945674033733263589)
      ·
        refine ⟨5996666239813881324986923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31982219945674033733263589 5996666239813881324986923)
        ·
          refine ⟨8994999359720821987480385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5996666239813881324986923 8994999359720821987480385)
          ·
            refine ⟨6746249519790616490610289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8994999359720821987480385 6746249519790616490610289)
            ·
              refine ⟨5059687139842962367957717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746249519790616490610289 5059687139842962367957717)
              ·
                refine ⟨118586417340069430499009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5059687139842962367957717 118586417340069430499009)
                ·
                  rfl

theorem cell23_6235548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 7].length) (baseStart_6235548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235548 prefixEnd_6235548 := by exact prefixLift 6235548
  have htrace : WordTrace (prefixWord ++ tailWord_6235548) baseStart_6235548 baseEnd_6235548 := by
    simpa [prefixWord, tailWord_6235548, baseEnd_6235548] using wordTrace_append hprefix tailTrace_6235548
  have hstable : (prefixWord ++ tailWord_6235548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235548).length < 2 ^ (prefixWord ++ tailWord_6235548).sum := by decide
  have hdescent : baseEnd_6235548 < baseStart_6235548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235554 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_6235554 : Nat := 118140960795 + 6235554 * 2 ^ 59
def prefixEnd_6235554 : Nat := 4983230072969 + 3 ^ 40 * 6235554 * 2
def baseEnd_6235554 : Nat := 3201836349065801599998215

theorem tailTrace_6235554 : CollatzResearch.WordTrace tailWord_6235554 prefixEnd_6235554 3201836349065801599998215 := by
  unfold tailWord_6235554
  simp only [CollatzResearch.WordTrace]
  refine ⟨56857334612915070170870429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151619558967773520455654477 56857334612915070170870429)
  ·
    refine ⟨21321500479843151314076411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56857334612915070170870429 21321500479843151314076411)
    ·
      refine ⟨31982250719764726971114617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21321500479843151314076411 31982250719764726971114617)
      ·
        refine ⟨23986688039823545228335963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31982250719764726971114617 23986688039823545228335963)
        ·
          refine ⟨35980032059735317842503945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23986688039823545228335963 35980032059735317842503945)
          ·
            refine ⟨26985024044801488381877959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35980032059735317842503945 26985024044801488381877959)
            ·
              refine ⟨40477536067202232572816939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26985024044801488381877959 40477536067202232572816939)
              ·
                refine ⟨60716304100803348859225409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40477536067202232572816939 60716304100803348859225409)
                ·
                  refine ⟨45537228075602511644419057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60716304100803348859225409 45537228075602511644419057)
                  ·
                    refine ⟨34152921056701883733314293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45537228075602511644419057 34152921056701883733314293)
                    ·
                      refine ⟨3201836349065801599998215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34152921056701883733314293 3201836349065801599998215)
                      ·
                        rfl

theorem cell23_6235554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_6235554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235554 prefixEnd_6235554 := by exact prefixLift 6235554
  have htrace : WordTrace (prefixWord ++ tailWord_6235554) baseStart_6235554 baseEnd_6235554 := by
    simpa [prefixWord, tailWord_6235554, baseEnd_6235554] using wordTrace_append hprefix tailTrace_6235554
  have hstable : (prefixWord ++ tailWord_6235554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235554).length < 2 ^ (prefixWord ++ tailWord_6235554).sum := by decide
  have hdescent : baseEnd_6235554 < baseStart_6235554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235557 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 4, 6]
def baseStart_6235557 : Nat := 118140960795 + 6235557 * 2 ^ 59
def prefixEnd_6235557 : Nat := 4983230072969 + 3 ^ 40 * 6235557 * 2
def baseEnd_6235557 : Nat := 1067279296502588362753567

theorem tailTrace_6235557 : CollatzResearch.WordTrace tailWord_6235557 prefixEnd_6235557 1067279296502588362753567 := by
  unfold tailWord_6235557
  simp only [CollatzResearch.WordTrace]
  refine ⟨227429447870649412195840925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151619631913766274797227283 227429447870649412195840925)
  ·
    refine ⟨85286042951493529573440347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227429447870649412195840925 85286042951493529573440347)
    ·
      refine ⟨127929064427240294360160521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85286042951493529573440347 127929064427240294360160521)
      ·
        refine ⟨95946798320430220770120391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127929064427240294360160521 95946798320430220770120391)
        ·
          refine ⟨143920197480645331155180587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95946798320430220770120391 143920197480645331155180587)
          ·
            refine ⟨215880296220967996732770881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143920197480645331155180587 215880296220967996732770881)
            ·
              refine ⟨161910222165725997549578161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215880296220967996732770881 161910222165725997549578161)
              ·
                refine ⟨121432666624294498162183621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161910222165725997549578161 121432666624294498162183621)
                ·
                  refine ⟨22768624992055218405409429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121432666624294498162183621 22768624992055218405409429)
                  ·
                    refine ⟨1067279296502588362753567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22768624992055218405409429 1067279296502588362753567)
                    ·
                      rfl

theorem cell23_6235557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_6235557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235557 prefixEnd_6235557 := by exact prefixLift 6235557
  have htrace : WordTrace (prefixWord ++ tailWord_6235557) baseStart_6235557 baseEnd_6235557 := by
    simpa [prefixWord, tailWord_6235557, baseEnd_6235557] using wordTrace_append hprefix tailTrace_6235557
  have hstable : (prefixWord ++ tailWord_6235557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235557).length < 2 ^ (prefixWord ++ tailWord_6235557).sum := by decide
  have hdescent : baseEnd_6235557 < baseStart_6235557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235586 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6235586 : Nat := 118140960795 + 6235586 * 2 ^ 59
def prefixEnd_6235586 : Nat := 4983230072969 + 3 ^ 40 * 6235586 * 2
def baseEnd_6235586 : Nat := 1067284260148915158266023

theorem tailTrace_6235586 : CollatzResearch.WordTrace tailWord_6235586 prefixEnd_6235586 1067284260148915158266023 := by
  unfold tailWord_6235586
  simp only [CollatzResearch.WordTrace]
  refine ⟨56857626396886087537161653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151620337058362900099097741 56857626396886087537161653)
  ·
    refine ⟨5330402474708070706608905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56857626396886087537161653 5330402474708070706608905)
    ·
      refine ⟨3997801856031053029956679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5330402474708070706608905 3997801856031053029956679)
      ·
        refine ⟨5996702784046579544935019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997801856031053029956679 5996702784046579544935019)
        ·
          refine ⟨8995054176069869317402529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5996702784046579544935019 8995054176069869317402529)
          ·
            refine ⟨6746290632052401988051897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8995054176069869317402529 6746290632052401988051897)
            ·
              refine ⟨5059717974039301491038923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746290632052401988051897 5059717974039301491038923)
              ·
                refine ⟨7589576961058952236558385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059717974039301491038923 7589576961058952236558385)
                ·
                  refine ⟨5692182720794214177418789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7589576961058952236558385 5692182720794214177418789)
                  ·
                    refine ⟨1067284260148915158266023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692182720794214177418789 1067284260148915158266023)
                    ·
                      rfl

theorem cell23_6235586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6235586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235586 prefixEnd_6235586 := by exact prefixLift 6235586
  have htrace : WordTrace (prefixWord ++ tailWord_6235586) baseStart_6235586 baseEnd_6235586 := by
    simpa [prefixWord, tailWord_6235586, baseEnd_6235586] using wordTrace_append hprefix tailTrace_6235586
  have hstable : (prefixWord ++ tailWord_6235586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235586).length < 2 ^ (prefixWord ++ tailWord_6235586).sum := by decide
  have hdescent : baseEnd_6235586 < baseStart_6235586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235607 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_6235607 : Nat := 118140960795 + 6235607 * 2 ^ 59
def prefixEnd_6235607 : Nat := 4983230072969 + 3 ^ 40 * 6235607 * 2
def baseEnd_6235607 : Nat := 3201863563540489892635471

theorem tailTrace_6235607 : CollatzResearch.WordTrace tailWord_6235607 prefixEnd_6235607 3201863563540489892635471 := by
  unfold tailWord_6235607
  simp only [CollatzResearch.WordTrace]
  refine ⟨227431271520468270735161075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151620847680312180490107383 227431271520468270735161075)
  ·
    refine ⟨341146907280702406102741613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227431271520468270735161075 341146907280702406102741613)
    ·
      refine ⟨127930090230263402288528105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341146907280702406102741613 127930090230263402288528105)
      ·
        refine ⟨95947567672697551716396079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127930090230263402288528105 95947567672697551716396079)
        ·
          refine ⟨143921351509046327574594119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95947567672697551716396079 143921351509046327574594119)
          ·
            refine ⟨215882027263569491361891179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143921351509046327574594119 215882027263569491361891179)
            ·
              refine ⟨323823040895354237042836769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215882027263569491361891179 323823040895354237042836769)
              ·
                refine ⟨242867280671515677782127577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323823040895354237042836769 242867280671515677782127577)
                ·
                  refine ⟨182150460503636758336595683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242867280671515677782127577 182150460503636758336595683)
                  ·
                    refine ⟨273225690755455137504893525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182150460503636758336595683 273225690755455137504893525)
                    ·
                      refine ⟨3201863563540489892635471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 273225690755455137504893525 3201863563540489892635471)
                      ·
                        rfl

theorem cell23_6235607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_6235607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235607 prefixEnd_6235607 := by exact prefixLift 6235607
  have htrace : WordTrace (prefixWord ++ tailWord_6235607) baseStart_6235607 baseEnd_6235607 := by
    simpa [prefixWord, tailWord_6235607, baseEnd_6235607] using wordTrace_append hprefix tailTrace_6235607
  have hstable : (prefixWord ++ tailWord_6235607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235607).length < 2 ^ (prefixWord ++ tailWord_6235607).sum := by decide
  have hdescent : baseEnd_6235607 < baseStart_6235607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235638 : List Nat := [5, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_6235638 : Nat := 118140960795 + 6235638 * 2 ^ 59
def prefixEnd_6235638 : Nat := 4983230072969 + 3 ^ 40 * 6235638 * 2
def baseEnd_6235638 : Nat := 355764386826753252371981

theorem tailTrace_6235638 : CollatzResearch.WordTrace tailWord_6235638 prefixEnd_6235638 355764386826753252371981 := by
  unfold tailWord_6235638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14214525136459747689346223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151621601455570642019693045 14214525136459747689346223)
  ·
    refine ⟨21321787704689621534019335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14214525136459747689346223 21321787704689621534019335)
    ·
      refine ⟨31982681557034432301029003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21321787704689621534019335 31982681557034432301029003)
      ·
        refine ⟨47974022335551648451543505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31982681557034432301029003 47974022335551648451543505)
        ·
          refine ⟨35980516751663736338657629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47974022335551648451543505 35980516751663736338657629)
          ·
            refine ⟨13492693781873901126996611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35980516751663736338657629 13492693781873901126996611)
            ·
              refine ⟨20239040672810851690494917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13492693781873901126996611 20239040672810851690494917)
              ·
                refine ⟨3794820126152034691967797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20239040672810851690494917 3794820126152034691967797)
                ·
                  refine ⟨355764386826753252371981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3794820126152034691967797 355764386826753252371981)
                  ·
                    rfl

theorem cell23_6235638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_6235638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235638 prefixEnd_6235638 := by exact prefixLift 6235638
  have htrace : WordTrace (prefixWord ++ tailWord_6235638) baseStart_6235638 baseEnd_6235638 := by
    simpa [prefixWord, tailWord_6235638, baseEnd_6235638] using wordTrace_append hprefix tailTrace_6235638
  have hstable : (prefixWord ++ tailWord_6235638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235638).length < 2 ^ (prefixWord ++ tailWord_6235638).sum := by decide
  have hdescent : baseEnd_6235638 < baseStart_6235638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235644 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_6235644 : Nat := 118140960795 + 6235644 * 2 ^ 59
def prefixEnd_6235644 : Nat := 4983230072969 + 3 ^ 40 * 6235644 * 2
def baseEnd_6235644 : Nat := 3201882562324706247872801

theorem tailTrace_6235644 : CollatzResearch.WordTrace tailWord_6235644 prefixEnd_6235644 3201882562324706247872801 := by
  unfold tailWord_6235644
  simp only [CollatzResearch.WordTrace]
  refine ⟨113716310510667113027128993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151621747347556150702838657 113716310510667113027128993)
  ·
    refine ⟨85287232883000334770346745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113716310510667113027128993 85287232883000334770346745)
    ·
      refine ⟨63965424662250251077760059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85287232883000334770346745 63965424662250251077760059)
      ·
        refine ⟨95948136993375376616640089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63965424662250251077760059 95948136993375376616640089)
        ·
          refine ⟨71961102745031532462480067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95948136993375376616640089 71961102745031532462480067)
          ·
            refine ⟨107941654117547298693720101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71961102745031532462480067 107941654117547298693720101)
            ·
              refine ⟨20239060147040118505072519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107941654117547298693720101 20239060147040118505072519)
              ·
                refine ⟨30358590220560177757608779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20239060147040118505072519 30358590220560177757608779)
                ·
                  refine ⟨45537885330840266636413169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30358590220560177757608779 45537885330840266636413169)
                  ·
                    refine ⟨34153413998130199977309877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45537885330840266636413169 34153413998130199977309877)
                    ·
                      refine ⟨3201882562324706247872801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34153413998130199977309877 3201882562324706247872801)
                      ·
                        rfl

theorem cell23_6235644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_6235644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235644 prefixEnd_6235644 := by exact prefixLift 6235644
  have htrace : WordTrace (prefixWord ++ tailWord_6235644) baseStart_6235644 baseEnd_6235644 := by
    simpa [prefixWord, tailWord_6235644, baseEnd_6235644] using wordTrace_append hprefix tailTrace_6235644
  have hstable : (prefixWord ++ tailWord_6235644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235644).length < 2 ^ (prefixWord ++ tailWord_6235644).sum := by decide
  have hdescent : baseEnd_6235644 < baseStart_6235644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235668 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6235668 : Nat := 118140960795 + 6235668 * 2 ^ 59
def prefixEnd_6235668 : Nat := 4983230072969 + 3 ^ 40 * 6235668 * 2
def baseEnd_6235668 : Nat := 1067298295286804717990897

theorem tailTrace_6235668 : CollatzResearch.WordTrace tailWord_6235668 prefixEnd_6235668 1067298295286804717990897 := by
  unfold tailWord_6235668
  simp only [CollatzResearch.WordTrace]
  refine ⟨113716748186623639076565829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151622330915498185435421105 113716748186623639076565829)
  ·
    refine ⟨21321890284991932326856093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113716748186623639076565829 21321890284991932326856093)
    ·
      refine ⟨7995708856871974622571035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21321890284991932326856093 7995708856871974622571035)
      ·
        refine ⟨11993563285307961933856553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7995708856871974622571035 11993563285307961933856553)
        ·
          refine ⟨8995172463980971450392415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11993563285307961933856553 8995172463980971450392415)
          ·
            refine ⟨13492758695971457175588623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8995172463980971450392415 13492758695971457175588623)
            ·
              refine ⟨20239138043957185763382935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13492758695971457175588623 20239138043957185763382935)
              ·
                refine ⟨30358707065935778645074403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20239138043957185763382935 30358707065935778645074403)
                ·
                  refine ⟨45538060598903667967611605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30358707065935778645074403 45538060598903667967611605)
                  ·
                    refine ⟨1067298295286804717990897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45538060598903667967611605 1067298295286804717990897)
                    ·
                      rfl

theorem cell23_6235668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6235668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235668 prefixEnd_6235668 := by exact prefixLift 6235668
  have htrace : WordTrace (prefixWord ++ tailWord_6235668) baseStart_6235668 baseEnd_6235668 := by
    simpa [prefixWord, tailWord_6235668, baseEnd_6235668] using wordTrace_append hprefix tailTrace_6235668
  have hstable : (prefixWord ++ tailWord_6235668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235668).length < 2 ^ (prefixWord ++ tailWord_6235668).sum := by decide
  have hdescent : baseEnd_6235668 < baseStart_6235668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235748 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_6235748 : Nat := 118140960795 + 6235748 * 2 ^ 59
def prefixEnd_6235748 : Nat := 4983230072969 + 3 ^ 40 * 6235748 * 2
def baseEnd_6235748 : Nat := 3201935964312773840972323

theorem tailTrace_6235748 : CollatzResearch.WordTrace tailWord_6235748 prefixEnd_6235748 3201935964312773840972323 := by
  unfold tailWord_6235748
  simp only [CollatzResearch.WordTrace]
  refine ⟨113718207106478725908021949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151624276141971634544029265 113718207106478725908021949)
  ·
    refine ⟨42644327664929522215508231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113718207106478725908021949 42644327664929522215508231)
    ·
      refine ⟨63966491497394283323262347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42644327664929522215508231 63966491497394283323262347)
      ·
        refine ⟨95949737246091424984893521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63966491497394283323262347 95949737246091424984893521)
        ·
          refine ⟨71962302934568568738670141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95949737246091424984893521 71962302934568568738670141)
          ·
            refine ⟨26985863600463213277001303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71962302934568568738670141 26985863600463213277001303)
            ·
              refine ⟨40478795400694819915501955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26985863600463213277001303 40478795400694819915501955)
              ·
                refine ⟨60718193101042229873252933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40478795400694819915501955 60718193101042229873252933)
                ·
                  refine ⟨11384661206445418101234925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60718193101042229873252933 11384661206445418101234925)
                  ·
                    refine ⟨4269247952417031787963097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11384661206445418101234925 4269247952417031787963097)
                    ·
                      refine ⟨3201935964312773840972323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269247952417031787963097 3201935964312773840972323)
                      ·
                        rfl

theorem cell23_6235748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_6235748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235748 prefixEnd_6235748 := by exact prefixLift 6235748
  have htrace : WordTrace (prefixWord ++ tailWord_6235748) baseStart_6235748 baseEnd_6235748 := by
    simpa [prefixWord, tailWord_6235748, baseEnd_6235748] using wordTrace_append hprefix tailTrace_6235748
  have hstable : (prefixWord ++ tailWord_6235748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235748).length < 2 ^ (prefixWord ++ tailWord_6235748).sum := by decide
  have hdescent : baseEnd_6235748 < baseStart_6235748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235806 : List Nat := [4, 3, 1, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_6235806 : Nat := 118140960795 + 6235806 * 2 ^ 59
def prefixEnd_6235806 : Nat := 4983230072969 + 3 ^ 40 * 6235806 * 2
def baseEnd_6235806 : Nat := 3201965746190734614047057

theorem tailTrace_6235806 : CollatzResearch.WordTrace tailWord_6235806 prefixEnd_6235806 3201965746190734614047057 := by
  unfold tailWord_6235806
  simp only [CollatzResearch.WordTrace]
  refine ⟨28429816205843415965206909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151625686431164885147770181 28429816205843415965206909)
  ·
    refine ⟨10661181077191280986952591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28429816205843415965206909 10661181077191280986952591)
    ·
      refine ⟨15991771615786921480428887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10661181077191280986952591 15991771615786921480428887)
      ·
        refine ⟨23987657423680382220643331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15991771615786921480428887 23987657423680382220643331)
        ·
          refine ⟨35981486135520573330964997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23987657423680382220643331 35981486135520573330964997)
          ·
            refine ⟨6746528650410107499555937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35981486135520573330964997 6746528650410107499555937)
            ·
              refine ⟨5059896487807580624666953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746528650410107499555937 5059896487807580624666953)
              ·
                refine ⟨3794922365855685468500215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5059896487807580624666953 3794922365855685468500215)
                ·
                  refine ⟨5692383548783528202750323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794922365855685468500215 5692383548783528202750323)
                  ·
                    refine ⟨8538575323175292304125485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692383548783528202750323 8538575323175292304125485)
                    ·
                      refine ⟨3201965746190734614047057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538575323175292304125485 3201965746190734614047057)
                      ·
                        rfl

theorem cell23_6235806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_6235806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235806 prefixEnd_6235806 := by exact prefixLift 6235806
  have htrace : WordTrace (prefixWord ++ tailWord_6235806) baseStart_6235806 baseEnd_6235806 := by
    simpa [prefixWord, tailWord_6235806, baseEnd_6235806] using wordTrace_append hprefix tailTrace_6235806
  have hstable : (prefixWord ++ tailWord_6235806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235806).length < 2 ^ (prefixWord ++ tailWord_6235806).sum := by decide
  have hdescent : baseEnd_6235806 < baseStart_6235806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235811 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 3]
def baseStart_6235811 : Nat := 118140960795 + 6235811 * 2 ^ 59
def prefixEnd_6235811 : Nat := 4983230072969 + 3 ^ 40 * 6235811 * 2
def baseEnd_6235811 : Nat := 3201968313594007094484533

theorem tailTrace_6235811 : CollatzResearch.WordTrace tailWord_6235811 prefixEnd_6235811 3201968313594007094484533 := by
  unfold tailWord_6235811
  simp only [CollatzResearch.WordTrace]
  refine ⟨227438712011729213575587287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151625808007819475717058191 227438712011729213575587287)
  ·
    refine ⟨341158068017593820363380931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227438712011729213575587287 341158068017593820363380931)
    ·
      refine ⟨511737102026390730545071397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341158068017593820363380931 511737102026390730545071397)
      ·
        refine ⟨95950706629948261977200887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 511737102026390730545071397 95950706629948261977200887)
        ·
          refine ⟨143926059944922392965801331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95950706629948261977200887 143926059944922392965801331)
          ·
            refine ⟨215889089917383589448701997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143926059944922392965801331 215889089917383589448701997)
            ·
              refine ⟨80958408719018846043263249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215889089917383589448701997 80958408719018846043263249)
              ·
                refine ⟨60718806539264134532447437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80958408719018846043263249 60718806539264134532447437)
                ·
                  refine ⟨22769552452224050449667789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60718806539264134532447437 22769552452224050449667789)
                  ·
                    refine ⟨8538582169584018918625421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22769552452224050449667789 8538582169584018918625421)
                    ·
                      refine ⟨3201968313594007094484533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538582169584018918625421 3201968313594007094484533)
                      ·
                        rfl

theorem cell23_6235811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_6235811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235811 prefixEnd_6235811 := by exact prefixLift 6235811
  have htrace : WordTrace (prefixWord ++ tailWord_6235811) baseStart_6235811 baseEnd_6235811 := by
    simpa [prefixWord, tailWord_6235811, baseEnd_6235811] using wordTrace_append hprefix tailTrace_6235811
  have hstable : (prefixWord ++ tailWord_6235811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235811).length < 2 ^ (prefixWord ++ tailWord_6235811).sum := by decide
  have hdescent : baseEnd_6235811 < baseStart_6235811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235846 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6235846 : Nat := 118140960795 + 6235846 * 2 ^ 59
def prefixEnd_6235846 : Nat := 4983230072969 + 3 ^ 40 * 6235846 * 2
def baseEnd_6235846 : Nat := 3201986285416914457546873

theorem tailTrace_6235846 : CollatzResearch.WordTrace tailWord_6235846 prefixEnd_6235846 3201986285416914457546873 := by
  unfold tailWord_6235846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7107499642706325454784731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 151626659044401609702074261 7107499642706325454784731)
  ·
    refine ⟨10661249464059488182177097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7107499642706325454784731 10661249464059488182177097)
    ·
      refine ⟨7995937098044616136632823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10661249464059488182177097 7995937098044616136632823)
      ·
        refine ⟨11993905647066924204949235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7995937098044616136632823 11993905647066924204949235)
        ·
          refine ⟨17990858470600386307423853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11993905647066924204949235 17990858470600386307423853)
          ·
            refine ⟨6746571926475144865283945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17990858470600386307423853 6746571926475144865283945)
            ·
              refine ⟨5059928944856358648962959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746571926475144865283945 5059928944856358648962959)
              ·
                refine ⟨7589893417284537973444439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059928944856358648962959 7589893417284537973444439)
                ·
                  refine ⟨11384840125926806960166659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7589893417284537973444439 11384840125926806960166659)
                  ·
                    refine ⟨17077260188890210440249989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11384840125926806960166659 17077260188890210440249989)
                    ·
                      refine ⟨3201986285416914457546873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17077260188890210440249989 3201986285416914457546873)
                      ·
                        rfl

theorem cell23_6235846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6235846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235846 prefixEnd_6235846 := by exact prefixLift 6235846
  have htrace : WordTrace (prefixWord ++ tailWord_6235846) baseStart_6235846 baseEnd_6235846 := by
    simpa [prefixWord, tailWord_6235846, baseEnd_6235846] using wordTrace_append hprefix tailTrace_6235846
  have hstable : (prefixWord ++ tailWord_6235846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235846).length < 2 ^ (prefixWord ++ tailWord_6235846).sum := by decide
  have hdescent : baseEnd_6235846 < baseStart_6235846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235879 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6235879 : Nat := 118140960795 + 6235879 * 2 ^ 59
def prefixEnd_6235879 : Nat := 4983230072969 + 3 ^ 40 * 6235879 * 2
def baseEnd_6235879 : Nat := 3202003230278512828434221

theorem tailTrace_6235879 : CollatzResearch.WordTrace tailWord_6235879 prefixEnd_6235879 3202003230278512828434221 := by
  unfold tailWord_6235879
  simp only [CollatzResearch.WordTrace]
  refine ⟨227441192175482861189062691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151627461450321907459375127 227441192175482861189062691)
  ·
    refine ⟨341161788263224291783594037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227441192175482861189062691 341161788263224291783594037)
    ·
      refine ⟨31983917649677277354711941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 341161788263224291783594037 31983917649677277354711941)
      ·
        refine ⟨5996984559314489504008489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31983917649677277354711941 5996984559314489504008489)
        ·
          refine ⟨4497738419485867128006367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5996984559314489504008489 4497738419485867128006367)
          ·
            refine ⟨6746607629228800692009551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497738419485867128006367 6746607629228800692009551)
            ·
              refine ⟨10119911443843201038014327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746607629228800692009551 10119911443843201038014327)
              ·
                refine ⟨15179867165764801557021491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10119911443843201038014327 15179867165764801557021491)
                ·
                  refine ⟨22769800748647202335532237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15179867165764801557021491 22769800748647202335532237)
                  ·
                    refine ⟨8538675280742700875824589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22769800748647202335532237 8538675280742700875824589)
                    ·
                      refine ⟨3202003230278512828434221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538675280742700875824589 3202003230278512828434221)
                      ·
                        rfl

theorem cell23_6235879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6235879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235879 prefixEnd_6235879 := by exact prefixLift 6235879
  have htrace : WordTrace (prefixWord ++ tailWord_6235879) baseStart_6235879 baseEnd_6235879 := by
    simpa [prefixWord, tailWord_6235879, baseEnd_6235879] using wordTrace_append hprefix tailTrace_6235879
  have hstable : (prefixWord ++ tailWord_6235879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235879).length < 2 ^ (prefixWord ++ tailWord_6235879).sum := by decide
  have hdescent : baseEnd_6235879 < baseStart_6235879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235891 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 7]
def baseStart_6235891 : Nat := 118140960795 + 6235891 * 2 ^ 59
def prefixEnd_6235891 : Nat := 4983230072969 + 3 ^ 40 * 6235891 * 2
def baseEnd_6235891 : Nat := 355778821338485197942685

theorem tailTrace_6235891 : CollatzResearch.WordTrace tailWord_6235891 prefixEnd_6235891 355778821338485197942685 := by
  unfold tailWord_6235891
  simp only [CollatzResearch.WordTrace]
  refine ⟨227441629851439387238499527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151627753234292924825666351 227441629851439387238499527)
  ·
    refine ⟨341162444777159080857749291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227441629851439387238499527 341162444777159080857749291)
    ·
      refine ⟨511743667165738621286623937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341162444777159080857749291 511743667165738621286623937)
      ·
        refine ⟨383807750374303965964967953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511743667165738621286623937 383807750374303965964967953)
        ·
          refine ⟨287855812780727974473725965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383807750374303965964967953 287855812780727974473725965)
          ·
            refine ⟨107945929792772990427647237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287855812780727974473725965 107945929792772990427647237)
            ·
              refine ⟨20239861836144935705183857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107945929792772990427647237 20239861836144935705183857)
              ·
                refine ⟨15179896377108701778887893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20239861836144935705183857 15179896377108701778887893)
                ·
                  refine ⟨355778821338485197942685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15179896377108701778887893 355778821338485197942685)
                  ·
                    rfl

theorem cell23_6235891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 7].length) (baseStart_6235891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235891 prefixEnd_6235891 := by exact prefixLift 6235891
  have htrace : WordTrace (prefixWord ++ tailWord_6235891) baseStart_6235891 baseEnd_6235891 := by
    simpa [prefixWord, tailWord_6235891, baseEnd_6235891] using wordTrace_append hprefix tailTrace_6235891
  have hstable : (prefixWord ++ tailWord_6235891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235891).length < 2 ^ (prefixWord ++ tailWord_6235891).sum := by decide
  have hdescent : baseEnd_6235891 < baseStart_6235891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235918 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_6235918 : Nat := 118140960795 + 6235918 * 2 ^ 59
def prefixEnd_6235918 : Nat := 4983230072969 + 3 ^ 40 * 6235918 * 2
def baseEnd_6235918 : Nat := 3202023256024038175846541

theorem tailTrace_6235918 : CollatzResearch.WordTrace tailWord_6235918 prefixEnd_6235918 3202023256024038175846541 := by
  unfold tailWord_6235918
  simp only [CollatzResearch.WordTrace]
  refine ⟨28430326827792696356216551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151628409748227713899821605 28430326827792696356216551)
  ·
    refine ⟨42645490241689044534324827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28430326827792696356216551 42645490241689044534324827)
    ·
      refine ⟨63968235362533566801487241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42645490241689044534324827 63968235362533566801487241)
      ·
        refine ⟨47976176521900175101115431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63968235362533566801487241 47976176521900175101115431)
        ·
          refine ⟨71964264782850262651673147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47976176521900175101115431 71964264782850262651673147)
          ·
            refine ⟨107946397174275393977509721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71964264782850262651673147 107946397174275393977509721)
            ·
              refine ⟨80959797880706545483132291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107946397174275393977509721 80959797880706545483132291)
              ·
                refine ⟨121439696821059818224698437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80959797880706545483132291 121439696821059818224698437)
                ·
                  refine ⟨22769943153948715917130957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121439696821059818224698437 22769943153948715917130957)
                  ·
                    refine ⟨8538728682730768468924109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22769943153948715917130957 8538728682730768468924109)
                    ·
                      refine ⟨3202023256024038175846541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538728682730768468924109 3202023256024038175846541)
                      ·
                        rfl

theorem cell23_6235918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_6235918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235918 prefixEnd_6235918 := by exact prefixLift 6235918
  have htrace : WordTrace (prefixWord ++ tailWord_6235918) baseStart_6235918 baseEnd_6235918 := by
    simpa [prefixWord, tailWord_6235918, baseEnd_6235918] using wordTrace_append hprefix tailTrace_6235918
  have hstable : (prefixWord ++ tailWord_6235918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235918).length < 2 ^ (prefixWord ++ tailWord_6235918).sum := by decide
  have hdescent : baseEnd_6235918 < baseStart_6235918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235931 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 5]
def baseStart_6235931 : Nat := 118140960795 + 6235931 * 2 ^ 59
def prefixEnd_6235931 : Nat := 4983230072969 + 3 ^ 40 * 6235931 * 2
def baseEnd_6235931 : Nat := 3202029931272546624983981

theorem tailTrace_6235931 : CollatzResearch.WordTrace tailWord_6235931 prefixEnd_6235931 3202029931272546624983981 := by
  unfold tailWord_6235931
  simp only [CollatzResearch.WordTrace]
  refine ⟨227443088771294474069955647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151628725847529649379970431 227443088771294474069955647)
  ·
    refine ⟨341164633156941711104933471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227443088771294474069955647 341164633156941711104933471)
    ·
      refine ⟨511746949735412566657400207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341164633156941711104933471 511746949735412566657400207)
      ·
        refine ⟨767620424603118849986100311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511746949735412566657400207 767620424603118849986100311)
        ·
          refine ⟨1151430636904678274979150467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767620424603118849986100311 1151430636904678274979150467)
          ·
            refine ⟨1727145955357017412468725701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151430636904678274979150467 1727145955357017412468725701)
            ·
              refine ⟨323839866629440764837886069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1727145955357017412468725701 323839866629440764837886069)
              ·
                refine ⟨30359987496510071703551819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323839866629440764837886069 30359987496510071703551819)
                ·
                  refine ⟨45539981244765107555327729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30359987496510071703551819 45539981244765107555327729)
                  ·
                    refine ⟨34154985933573830666495797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45539981244765107555327729 34154985933573830666495797)
                    ·
                      refine ⟨3202029931272546624983981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34154985933573830666495797 3202029931272546624983981)
                      ·
                        rfl

theorem cell23_6235931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 5].length) (baseStart_6235931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235931 prefixEnd_6235931 := by exact prefixLift 6235931
  have htrace : WordTrace (prefixWord ++ tailWord_6235931) baseStart_6235931 baseEnd_6235931 := by
    simpa [prefixWord, tailWord_6235931, baseEnd_6235931] using wordTrace_append hprefix tailTrace_6235931
  have hstable : (prefixWord ++ tailWord_6235931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235931).length < 2 ^ (prefixWord ++ tailWord_6235931).sum := by decide
  have hdescent : baseEnd_6235931 < baseStart_6235931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235938 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_6235938 : Nat := 118140960795 + 6235938 * 2 ^ 59
def prefixEnd_6235938 : Nat := 4983230072969 + 3 ^ 40 * 6235938 * 2
def baseEnd_6235938 : Nat := 1067344508545709365865483

theorem tailTrace_6235938 : CollatzResearch.WordTrace tailWord_6235938 prefixEnd_6235938 1067344508545709365865483 := by
  unfold tailWord_6235938
  simp only [CollatzResearch.WordTrace]
  refine ⟨56860836020567278566365117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151628896054846076176973645 56860836020567278566365117)
  ·
    refine ⟨21322813507712729462386919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56860836020567278566365117 21322813507712729462386919)
    ·
      refine ⟨31984220261569094193580379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21322813507712729462386919 31984220261569094193580379)
      ·
        refine ⟨47976330392353641290370569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31984220261569094193580379 47976330392353641290370569)
        ·
          refine ⟨35982247794265230967777927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47976330392353641290370569 35982247794265230967777927)
          ·
            refine ⟨53973371691397846451666891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35982247794265230967777927 53973371691397846451666891)
            ·
              refine ⟨80960057537096769677500337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53973371691397846451666891 80960057537096769677500337)
              ·
                refine ⟨60720043152822577258125253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80960057537096769677500337 60720043152822577258125253)
                ·
                  refine ⟨11385008091154233235898485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60720043152822577258125253 11385008091154233235898485)
                  ·
                    refine ⟨1067344508545709365865483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11385008091154233235898485 1067344508545709365865483)
                    ·
                      rfl

theorem cell23_6235938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_6235938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235938 prefixEnd_6235938 := by exact prefixLift 6235938
  have htrace : WordTrace (prefixWord ++ tailWord_6235938) baseStart_6235938 baseEnd_6235938 := by
    simpa [prefixWord, tailWord_6235938, baseEnd_6235938] using wordTrace_append hprefix tailTrace_6235938
  have hstable : (prefixWord ++ tailWord_6235938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235938).length < 2 ^ (prefixWord ++ tailWord_6235938).sum := by decide
  have hdescent : baseEnd_6235938 < baseStart_6235938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6235955 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 2, 5]
def baseStart_6235955 : Nat := 118140960795 + 6235955 * 2 ^ 59
def prefixEnd_6235955 : Nat := 4983230072969 + 3 ^ 40 * 6235955 * 2
def baseEnd_6235955 : Nat := 1067347418269418177027957

theorem tailTrace_6235955 : CollatzResearch.WordTrace tailWord_6235955 prefixEnd_6235955 1067347418269418177027957 := by
  unfold tailWord_6235955
  simp only [CollatzResearch.WordTrace]
  refine ⟨227443964123207526168829319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151629309415471684112552879 227443964123207526168829319)
  ·
    refine ⟨341165946184811289253243979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227443964123207526168829319 341165946184811289253243979)
    ·
      refine ⟨511748919277216933879865969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341165946184811289253243979 511748919277216933879865969)
      ·
        refine ⟨383811689457912700409899477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511748919277216933879865969 383811689457912700409899477)
        ·
          refine ⟨8995586471669828915857019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 383811689457912700409899477 8995586471669828915857019)
          ·
            refine ⟨13493379707504743373785529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8995586471669828915857019 13493379707504743373785529)
            ·
              refine ⟨10120034780628557530339147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13493379707504743373785529 10120034780628557530339147)
              ·
                refine ⟨15180052170942836295508721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10120034780628557530339147 15180052170942836295508721)
                ·
                  refine ⟨11385039128207127221631541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15180052170942836295508721 11385039128207127221631541)
                  ·
                    refine ⟨1067347418269418177027957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11385039128207127221631541 1067347418269418177027957)
                    ·
                      rfl

theorem cell23_6235955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 5].length) (baseStart_6235955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6235955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6235955 prefixEnd_6235955 := by exact prefixLift 6235955
  have htrace : WordTrace (prefixWord ++ tailWord_6235955) baseStart_6235955 baseEnd_6235955 := by
    simpa [prefixWord, tailWord_6235955, baseEnd_6235955] using wordTrace_append hprefix tailTrace_6235955
  have hstable : (prefixWord ++ tailWord_6235955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6235955).length < 2 ^ (prefixWord ++ tailWord_6235955).sum := by decide
  have hdescent : baseEnd_6235955 < baseStart_6235955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6235955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236002 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6236002 : Nat := 118140960795 + 6236002 * 2 ^ 59
def prefixEnd_6236002 : Nat := 4983230072969 + 3 ^ 40 * 6236002 * 2
def baseEnd_6236002 : Nat := 1067355462799671949065385

theorem tailTrace_6236002 : CollatzResearch.WordTrace tailWord_6236002 prefixEnd_6236002 1067355462799671949065385 := by
  unfold tailWord_6236002
  simp only [CollatzResearch.WordTrace]
  refine ⟨56861419588509313298947565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151630452236024835463860173 56861419588509313298947565)
  ·
    refine ⟨21323032345690992487105337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56861419588509313298947565 21323032345690992487105337)
    ·
      refine ⟨15992274259268244365329003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21323032345690992487105337 15992274259268244365329003)
      ·
        refine ⟨23988411388902366547993505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15992274259268244365329003 23988411388902366547993505)
        ·
          refine ⟨17991308541676774910995129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23988411388902366547993505 17991308541676774910995129)
          ·
            refine ⟨13493481406257581183246347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17991308541676774910995129 13493481406257581183246347)
            ·
              refine ⟨20240222109386371774869521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13493481406257581183246347 20240222109386371774869521)
              ·
                refine ⟨15180166582039778831152141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20240222109386371774869521 15180166582039778831152141)
                ·
                  refine ⟨5692562468264917061682053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15180166582039778831152141 5692562468264917061682053)
                  ·
                    refine ⟨1067355462799671949065385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692562468264917061682053 1067355462799671949065385)
                    ·
                      rfl

theorem cell23_6236002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6236002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236002 prefixEnd_6236002 := by exact prefixLift 6236002
  have htrace : WordTrace (prefixWord ++ tailWord_6236002) baseStart_6236002 baseEnd_6236002 := by
    simpa [prefixWord, tailWord_6236002, baseEnd_6236002] using wordTrace_append hprefix tailTrace_6236002
  have hstable : (prefixWord ++ tailWord_6236002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236002).length < 2 ^ (prefixWord ++ tailWord_6236002).sum := by decide
  have hdescent : baseEnd_6236002 < baseStart_6236002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236012 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_6236012 : Nat := 118140960795 + 6236012 * 2 ^ 59
def prefixEnd_6236012 : Nat := 4983230072969 + 3 ^ 40 * 6236012 * 2
def baseEnd_6236012 : Nat := 3202071523205560808071109

theorem tailTrace_6236012 : CollatzResearch.WordTrace tailWord_6236012 prefixEnd_6236012 3202071523205560808071109 := by
  unfold tailWord_6236012
  simp only [CollatzResearch.WordTrace]
  refine ⟨113723021542000512451827145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151630695389334016602436193 113723021542000512451827145)
  ·
    refine ⟨85292266156500384338870359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113723021542000512451827145 85292266156500384338870359)
    ·
      refine ⟨127938399234750576508305539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85292266156500384338870359 127938399234750576508305539)
      ·
        refine ⟨191907598852125864762458309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127938399234750576508305539 191907598852125864762458309)
        ·
          refine ⟨35982674784773599642960933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191907598852125864762458309 35982674784773599642960933)
          ·
            refine ⟨6746751522145049933055175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35982674784773599642960933 6746751522145049933055175)
            ·
              refine ⟨10120127283217574899582763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746751522145049933055175 10120127283217574899582763)
              ·
                refine ⟨15180190924826362349374145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10120127283217574899582763 15180190924826362349374145)
                ·
                  refine ⟨11385143193619771762030609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15180190924826362349374145 11385143193619771762030609)
                  ·
                    refine ⟨8538857395214828821522957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11385143193619771762030609 8538857395214828821522957)
                    ·
                      refine ⟨3202071523205560808071109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538857395214828821522957 3202071523205560808071109)
                      ·
                        rfl

theorem cell23_6236012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_6236012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236012 prefixEnd_6236012 := by exact prefixLift 6236012
  have htrace : WordTrace (prefixWord ++ tailWord_6236012) baseStart_6236012 baseEnd_6236012 := by
    simpa [prefixWord, tailWord_6236012, baseEnd_6236012] using wordTrace_append hprefix tailTrace_6236012
  have hstable : (prefixWord ++ tailWord_6236012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236012).length < 2 ^ (prefixWord ++ tailWord_6236012).sum := by decide
  have hdescent : baseEnd_6236012 < baseStart_6236012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236025 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 3]
def baseStart_6236025 : Nat := 118140960795 + 6236025 * 2 ^ 59
def prefixEnd_6236025 : Nat := 4983230072969 + 3 ^ 40 * 6236025 * 2
def baseEnd_6236025 : Nat := 3202078198454069257208549

theorem tailTrace_6236025 : CollatzResearch.WordTrace tailWord_6236025 prefixEnd_6236025 3202078198454069257208549 := by
  unfold tailWord_6236025
  simp only [CollatzResearch.WordTrace]
  refine ⟨227446517232953928123877529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151631011488635952082585019 227446517232953928123877529)
  ·
    refine ⟨170584887924715446092908147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227446517232953928123877529 170584887924715446092908147)
    ·
      refine ⟨255877331887073169139362221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170584887924715446092908147 255877331887073169139362221)
      ·
        refine ⟨95953999457652438427260833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255877331887073169139362221 95953999457652438427260833)
        ·
          refine ⟨71965499593239328820445625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95953999457652438427260833 71965499593239328820445625)
          ·
            refine ⟨53974124694929496615334219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71965499593239328820445625 53974124694929496615334219)
            ·
              refine ⟨80961187042394244923001329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53974124694929496615334219 80961187042394244923001329)
              ·
                refine ⟨60720890281795683692250997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80961187042394244923001329 60720890281795683692250997)
                ·
                  refine ⟨5692583463918345346148531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60720890281795683692250997 5692583463918345346148531)
                  ·
                    refine ⟨8538875195877518019222797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692583463918345346148531 8538875195877518019222797)
                    ·
                      refine ⟨3202078198454069257208549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8538875195877518019222797 3202078198454069257208549)
                      ·
                        rfl

theorem cell23_6236025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_6236025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236025 prefixEnd_6236025 := by exact prefixLift 6236025
  have htrace : WordTrace (prefixWord ++ tailWord_6236025) baseStart_6236025 baseEnd_6236025 := by
    simpa [prefixWord, tailWord_6236025, baseEnd_6236025] using wordTrace_append hprefix tailTrace_6236025
  have hstable : (prefixWord ++ tailWord_6236025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236025).length < 2 ^ (prefixWord ++ tailWord_6236025).sum := by decide
  have hdescent : baseEnd_6236025 < baseStart_6236025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236052 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_6236052 : Nat := 118140960795 + 6236052 * 2 ^ 59
def prefixEnd_6236052 : Nat := 4983230072969 + 3 ^ 40 * 6236052 * 2
def baseEnd_6236052 : Nat := 3202092062431740651570925

theorem tailTrace_6236052 : CollatzResearch.WordTrace tailWord_6236052 prefixEnd_6236052 3202092062431740651570925 := by
  unfold tailWord_6236052
  simp only [CollatzResearch.WordTrace]
  refine ⟨113723751001928055867555205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151631668002570741156740273 113723751001928055867555205)
  ·
    refine ⟨21323203312861510475166601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113723751001928055867555205 21323203312861510475166601)
    ·
      refine ⟨15992402484646132856374951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21323203312861510475166601 15992402484646132856374951)
      ·
        refine ⟨23988603726969199284562427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15992402484646132856374951 23988603726969199284562427)
        ·
          refine ⟨35982905590453798926843641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23988603726969199284562427 35982905590453798926843641)
          ·
            refine ⟨26987179192840349195132731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35982905590453798926843641 26987179192840349195132731)
            ·
              refine ⟨40480768789260523792699097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26987179192840349195132731 40480768789260523792699097)
              ·
                refine ⟨30360576591945392844524323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40480768789260523792699097 30360576591945392844524323)
                ·
                  refine ⟨45540864887918089266786485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30360576591945392844524323 45540864887918089266786485)
                  ·
                    refine ⟨4269456083242320868761233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45540864887918089266786485 4269456083242320868761233)
                    ·
                      refine ⟨3202092062431740651570925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269456083242320868761233 3202092062431740651570925)
                      ·
                        rfl

theorem cell23_6236052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_6236052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236052 prefixEnd_6236052 := by exact prefixLift 6236052
  have htrace : WordTrace (prefixWord ++ tailWord_6236052) baseStart_6236052 baseEnd_6236052 := by
    simpa [prefixWord, tailWord_6236052, baseEnd_6236052] using wordTrace_append hprefix tailTrace_6236052
  have hstable : (prefixWord ++ tailWord_6236052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236052).length < 2 ^ (prefixWord ++ tailWord_6236052).sum := by decide
  have hdescent : baseEnd_6236052 < baseStart_6236052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236082 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2]
def baseStart_6236082 : Nat := 118140960795 + 6236082 * 2 ^ 59
def prefixEnd_6236082 : Nat := 4983230072969 + 3 ^ 40 * 6236082 * 2
def baseEnd_6236082 : Nat := 3202107466851375534195787

theorem tailTrace_6236082 : CollatzResearch.WordTrace tailWord_6236082 prefixEnd_6236082 3202107466851375534195787 := by
  unfold tailWord_6236082
  simp only [CollatzResearch.WordTrace]
  refine ⟨56862149048436856714675625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151632397462498284572468333 56862149048436856714675625)
  ·
    refine ⟨42646611786327642536006719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56862149048436856714675625 42646611786327642536006719)
    ·
      refine ⟨63969917679491463804010079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42646611786327642536006719 63969917679491463804010079)
      ·
        refine ⟨95954876519237195706015119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63969917679491463804010079 95954876519237195706015119)
        ·
          refine ⟨143932314778855793559022679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95954876519237195706015119 143932314778855793559022679)
          ·
            refine ⟨215898472168283690338534019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143932314778855793559022679 215898472168283690338534019)
            ·
              refine ⟨323847708252425535507801029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215898472168283690338534019 323847708252425535507801029)
              ·
                refine ⟨60721445297329787907712693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323847708252425535507801029 60721445297329787907712693)
                ·
                  refine ⟨5692635496624667616348065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60721445297329787907712693 5692635496624667616348065)
                  ·
                    refine ⟨4269476622468500712261049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5692635496624667616348065 4269476622468500712261049)
                    ·
                      refine ⟨3202107466851375534195787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269476622468500712261049 3202107466851375534195787)
                      ·
                        rfl

theorem cell23_6236082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_6236082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236082 prefixEnd_6236082 := by exact prefixLift 6236082
  have htrace : WordTrace (prefixWord ++ tailWord_6236082) baseStart_6236082 baseEnd_6236082 := by
    simpa [prefixWord, tailWord_6236082, baseEnd_6236082] using wordTrace_append hprefix tailTrace_6236082
  have hstable : (prefixWord ++ tailWord_6236082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236082).length < 2 ^ (prefixWord ++ tailWord_6236082).sum := by decide
  have hdescent : baseEnd_6236082 < baseStart_6236082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236085 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_6236085 : Nat := 118140960795 + 6236085 * 2 ^ 59
def prefixEnd_6236085 : Nat := 4983230072969 + 3 ^ 40 * 6236085 * 2
def baseEnd_6236085 : Nat := 3202109007293339022458273

theorem tailTrace_6236085 : CollatzResearch.WordTrace tailWord_6236085 prefixEnd_6236085 3202109007293339022458273 := by
  unfold tailWord_6236085
  simp only [CollatzResearch.WordTrace]
  refine ⟨227448705612736558371061709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151632470408491038914041139 227448705612736558371061709)
  ·
    refine ⟨85293264604776209389148141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227448705612736558371061709 85293264604776209389148141)
    ·
      refine ⟨31984974226791078520930553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85293264604776209389148141 31984974226791078520930553)
      ·
        refine ⟨23988730670093308890697915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31984974226791078520930553 23988730670093308890697915)
        ·
          refine ⟨35983096005139963336046873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23988730670093308890697915 35983096005139963336046873)
          ·
            refine ⟨26987322003854972502035155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35983096005139963336046873 26987322003854972502035155)
            ·
              refine ⟨40480983005782458753052733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26987322003854972502035155 40480983005782458753052733)
              ·
                refine ⟨15180368627168422032394775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40480983005782458753052733 15180368627168422032394775)
                ·
                  refine ⟨22770552940752633048592163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15180368627168422032394775 22770552940752633048592163)
                  ·
                    refine ⟨34155829411128949572888245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22770552940752633048592163 34155829411128949572888245)
                    ·
                      refine ⟨3202109007293339022458273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34155829411128949572888245 3202109007293339022458273)
                      ·
                        rfl

theorem cell23_6236085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_6236085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236085 prefixEnd_6236085 := by exact prefixLift 6236085
  have htrace : WordTrace (prefixWord ++ tailWord_6236085) baseStart_6236085 baseEnd_6236085 := by
    simpa [prefixWord, tailWord_6236085, baseEnd_6236085] using wordTrace_append hprefix tailTrace_6236085
  have hstable : (prefixWord ++ tailWord_6236085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236085).length < 2 ^ (prefixWord ++ tailWord_6236085).sum := by decide
  have hdescent : baseEnd_6236085 < baseStart_6236085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236128 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_6236128 : Nat := 118140960795 + 6236128 * 2 ^ 59
def prefixEnd_6236128 : Nat := 4983230072969 + 3 ^ 40 * 6236128 * 2
def baseEnd_6236128 : Nat := 3202131086961482354220575

theorem tailTrace_6236128 : CollatzResearch.WordTrace tailWord_6236128 prefixEnd_6236128 3202131086961482354220575 := by
  unfold tailWord_6236128
  simp only [CollatzResearch.WordTrace]
  refine ⟨113725136975790388357438519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151633515967720517809918025 113725136975790388357438519)
  ·
    refine ⟨170587705463685582536157779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113725136975790388357438519 170587705463685582536157779)
    ·
      refine ⟨255881558195528373804236669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170587705463685582536157779 255881558195528373804236669)
      ·
        refine ⟨95955584323323140176588751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255881558195528373804236669 95955584323323140176588751)
        ·
          refine ⟨143933376484984710264883127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95955584323323140176588751 143933376484984710264883127)
          ·
            refine ⟨215900064727477065397324691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143933376484984710264883127 215900064727477065397324691)
            ·
              refine ⟨323850097091215598095987037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215900064727477065397324691 323850097091215598095987037)
              ·
                refine ⟨121443786409205849285995139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323850097091215598095987037 121443786409205849285995139)
                ·
                  refine ⟨182165679613808773928992709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121443786409205849285995139 182165679613808773928992709)
                  ·
                    refine ⟨34156064927589145111686133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 182165679613808773928992709 34156064927589145111686133)
                    ·
                      refine ⟨3202131086961482354220575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34156064927589145111686133 3202131086961482354220575)
                      ·
                        rfl

theorem cell23_6236128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_6236128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236128 prefixEnd_6236128 := by exact prefixLift 6236128
  have htrace : WordTrace (prefixWord ++ tailWord_6236128) baseStart_6236128 baseEnd_6236128 := by
    simpa [prefixWord, tailWord_6236128, baseEnd_6236128] using wordTrace_append hprefix tailTrace_6236128
  have hstable : (prefixWord ++ tailWord_6236128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236128).length < 2 ^ (prefixWord ++ tailWord_6236128).sum := by decide
  have hdescent : baseEnd_6236128 < baseStart_6236128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236165 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_6236165 : Nat := 118140960795 + 6236165 * 2 ^ 59
def prefixEnd_6236165 : Nat := 4983230072969 + 3 ^ 40 * 6236165 * 2
def baseEnd_6236165 : Nat := 1067383361915232903152635

theorem tailTrace_6236165 : CollatzResearch.WordTrace tailWord_6236165 prefixEnd_6236165 1067383361915232903152635 := by
  unfold tailWord_6236165
  simp only [CollatzResearch.WordTrace]
  refine ⟨227451623452446732033973949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151634415634964488022649299 227451623452446732033973949)
  ·
    refine ⟨85294358794667524512740231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227451623452446732033973949 85294358794667524512740231)
    ·
      refine ⟨127941538192001286769110347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85294358794667524512740231 127941538192001286769110347)
      ·
        refine ⟨191912307288001930153665521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127941538192001286769110347 191912307288001930153665521)
        ·
          refine ⟨143934230466001447615249141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191912307288001930153665521 143934230466001447615249141)
          ·
            refine ⟨13493834106187635713929607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143934230466001447615249141 13493834106187635713929607)
            ·
              refine ⟨20240751159281453570894411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13493834106187635713929607 20240751159281453570894411)
              ·
                refine ⟨30361126738922180356341617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20240751159281453570894411 30361126738922180356341617)
                ·
                  refine ⟨22770845054191635267256213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30361126738922180356341617 22770845054191635267256213)
                  ·
                    refine ⟨1067383361915232903152635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22770845054191635267256213 1067383361915232903152635)
                    ·
                      rfl

theorem cell23_6236165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_6236165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236165 prefixEnd_6236165 := by exact prefixLift 6236165
  have htrace : WordTrace (prefixWord ++ tailWord_6236165) baseStart_6236165 baseEnd_6236165 := by
    simpa [prefixWord, tailWord_6236165, baseEnd_6236165] using wordTrace_append hprefix tailTrace_6236165
  have hstable : (prefixWord ++ tailWord_6236165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236165).length < 2 ^ (prefixWord ++ tailWord_6236165).sum := by decide
  have hdescent : baseEnd_6236165 < baseStart_6236165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236189 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_6236189 : Nat := 118140960795 + 6236189 * 2 ^ 59
def prefixEnd_6236189 : Nat := 4983230072969 + 3 ^ 40 * 6236189 * 2
def baseEnd_6236189 : Nat := 3202162409281406615557795

theorem tailTrace_6236189 : CollatzResearch.WordTrace tailWord_6236189 prefixEnd_6236189 3202162409281406615557795 := by
  unfold tailWord_6236189
  simp only [CollatzResearch.WordTrace]
  refine ⟨227452498804359784132847621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151634999202906522755231747 227452498804359784132847621)
  ·
    refine ⟨42647343525817459524908929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227452498804359784132847621 42647343525817459524908929)
    ·
      refine ⟨31985507644363094643681697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42647343525817459524908929 31985507644363094643681697)
      ·
        refine ⟨23989130733272320982761273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31985507644363094643681697 23989130733272320982761273)
        ·
          refine ⟨17991848049954240737070955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23989130733272320982761273 17991848049954240737070955)
          ·
            refine ⟨26987772074931361105606433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17991848049954240737070955 26987772074931361105606433)
            ·
              refine ⟨20240829056198520829204825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26987772074931361105606433 20240829056198520829204825)
              ·
                refine ⟨15180621792148890621903619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20240829056198520829204825 15180621792148890621903619)
                ·
                  refine ⟨22770932688223335932855429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15180621792148890621903619 22770932688223335932855429)
                  ·
                    refine ⟨4269549879041875487410393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22770932688223335932855429 4269549879041875487410393)
                    ·
                      refine ⟨3202162409281406615557795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269549879041875487410393 3202162409281406615557795)
                      ·
                        rfl

theorem cell23_6236189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_6236189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236189 prefixEnd_6236189 := by exact prefixLift 6236189
  have htrace : WordTrace (prefixWord ++ tailWord_6236189) baseStart_6236189 baseEnd_6236189 := by
    simpa [prefixWord, tailWord_6236189, baseEnd_6236189] using wordTrace_append hprefix tailTrace_6236189
  have hstable : (prefixWord ++ tailWord_6236189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236189).length < 2 ^ (prefixWord ++ tailWord_6236189).sum := by decide
  have hdescent : baseEnd_6236189 < baseStart_6236189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236193 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_6236193 : Nat := 118140960795 + 6236193 * 2 ^ 59
def prefixEnd_6236193 : Nat := 4983230072969 + 3 ^ 40 * 6236193 * 2
def baseEnd_6236193 : Nat := 3202164463204024599907777

theorem tailTrace_6236193 : CollatzResearch.WordTrace tailWord_6236193 prefixEnd_6236193 3202164463204024599907777 := by
  unfold tailWord_6236193
  simp only [CollatzResearch.WordTrace]
  refine ⟨227452644696345292815993233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151635096464230195210662155 227452644696345292815993233)
  ·
    refine ⟨170589483522258969611994925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227452644696345292815993233 170589483522258969611994925)
    ·
      refine ⟨63971056320847113604498097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170589483522258969611994925 63971056320847113604498097)
      ·
        refine ⟨47978292240635335203373573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63971056320847113604498097 47978292240635335203373573)
        ·
          refine ⟨8995929795119125350632545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47978292240635335203373573 8995929795119125350632545)
          ·
            refine ⟨6746947346339344012974409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8995929795119125350632545 6746947346339344012974409)
            ·
              refine ⟨5060210509754508009730807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746947346339344012974409 5060210509754508009730807)
              ·
                refine ⟨7590315764631762014596211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060210509754508009730807 7590315764631762014596211)
                ·
                  refine ⟨11385473646947643021894317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7590315764631762014596211 11385473646947643021894317)
                  ·
                    refine ⟨4269552617605366133210369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11385473646947643021894317 4269552617605366133210369)
                    ·
                      refine ⟨3202164463204024599907777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269552617605366133210369 3202164463204024599907777)
                      ·
                        rfl

theorem cell23_6236193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_6236193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236193 prefixEnd_6236193 := by exact prefixLift 6236193
  have htrace : WordTrace (prefixWord ++ tailWord_6236193) baseStart_6236193 baseEnd_6236193 := by
    simpa [prefixWord, tailWord_6236193, baseEnd_6236193] using wordTrace_append hprefix tailTrace_6236193
  have hstable : (prefixWord ++ tailWord_6236193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236193).length < 2 ^ (prefixWord ++ tailWord_6236193).sum := by decide
  have hdescent : baseEnd_6236193 < baseStart_6236193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236200 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6236200 : Nat := 118140960795 + 6236200 * 2 ^ 59
def prefixEnd_6236200 : Nat := 4983230072969 + 3 ^ 40 * 6236200 * 2
def baseEnd_6236200 : Nat := 3202168057568606072520245

theorem tailTrace_6236200 : CollatzResearch.WordTrace tailWord_6236200 prefixEnd_6236200 3202168057568606072520245 := by
  unfold tailWord_6236200
  simp only [CollatzResearch.WordTrace]
  refine ⟨113726450003659966505749027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151635266671546622007665369 113726450003659966505749027)
  ·
    refine ⟨170589675005489949758623541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113726450003659966505749027 170589675005489949758623541)
    ·
      refine ⟨15992782031764682789870957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170589675005489949758623541 15992782031764682789870957)
      ·
        refine ⟨5997293261911756046201609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15992782031764682789870957 5997293261911756046201609)
        ·
          refine ⟨4497969946433817034651207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5997293261911756046201609 4497969946433817034651207)
          ·
            refine ⟨6746954919650725551976811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497969946433817034651207 6746954919650725551976811)
            ·
              refine ⟨10120432379476088327965217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6746954919650725551976811 10120432379476088327965217)
              ·
                refine ⟨7590324284607066245973913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10120432379476088327965217 7590324284607066245973913)
                ·
                  refine ⟨5692743213455299684480435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590324284607066245973913 5692743213455299684480435)
                  ·
                    refine ⟨8539114820182949526720653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692743213455299684480435 8539114820182949526720653)
                    ·
                      refine ⟨3202168057568606072520245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8539114820182949526720653 3202168057568606072520245)
                      ·
                        rfl

theorem cell23_6236200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6236200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236200 prefixEnd_6236200 := by exact prefixLift 6236200
  have htrace : WordTrace (prefixWord ++ tailWord_6236200) baseStart_6236200 baseEnd_6236200 := by
    simpa [prefixWord, tailWord_6236200, baseEnd_6236200] using wordTrace_append hprefix tailTrace_6236200
  have hstable : (prefixWord ++ tailWord_6236200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236200).length < 2 ^ (prefixWord ++ tailWord_6236200).sum := by decide
  have hdescent : baseEnd_6236200 < baseStart_6236200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236202 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_6236202 : Nat := 118140960795 + 6236202 * 2 ^ 59
def prefixEnd_6236202 : Nat := 4983230072969 + 3 ^ 40 * 6236202 * 2
def baseEnd_6236202 : Nat := 3202169084529915064695235

theorem tailTrace_6236202 : CollatzResearch.WordTrace tailWord_6236202 prefixEnd_6236202 3202169084529915064695235 := by
  unfold tailWord_6236202
  simp only [CollatzResearch.WordTrace]
  refine ⟨56863243238328171838267715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151635315302208458235380573 56863243238328171838267715)
  ·
    refine ⟨85294864857492257757401573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56863243238328171838267715 85294864857492257757401573)
    ·
      refine ⟨15992787160779798329512795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85294864857492257757401573 15992787160779798329512795)
      ·
        refine ⟨23989180741169697494269193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15992787160779798329512795 23989180741169697494269193)
        ·
          refine ⟨17991885555877273120701895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23989180741169697494269193 17991885555877273120701895)
          ·
            refine ⟨26987828333815909681052843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17991885555877273120701895 26987828333815909681052843)
            ·
              refine ⟨40481742500723864521579265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26987828333815909681052843 40481742500723864521579265)
              ·
                refine ⟨30361306875542898391184449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40481742500723864521579265 30361306875542898391184449)
                ·
                  refine ⟨22770980156657173793388337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30361306875542898391184449 22770980156657173793388337)
                  ·
                    refine ⟨17078235117492880345041253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22770980156657173793388337 17078235117492880345041253)
                    ·
                      refine ⟨3202169084529915064695235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17078235117492880345041253 3202169084529915064695235)
                      ·
                        rfl

theorem cell23_6236202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_6236202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236202 prefixEnd_6236202 := by exact prefixLift 6236202
  have htrace : WordTrace (prefixWord ++ tailWord_6236202) baseStart_6236202 baseEnd_6236202 := by
    simpa [prefixWord, tailWord_6236202, baseEnd_6236202] using wordTrace_append hprefix tailTrace_6236202
  have hstable : (prefixWord ++ tailWord_6236202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236202).length < 2 ^ (prefixWord ++ tailWord_6236202).sum := by decide
  have hdescent : baseEnd_6236202 < baseStart_6236202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236206 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_6236206 : Nat := 118140960795 + 6236206 * 2 ^ 59
def prefixEnd_6236206 : Nat := 4983230072969 + 3 ^ 40 * 6236206 * 2
def baseEnd_6236206 : Nat := 3202171138452533049045217

theorem tailTrace_6236206 : CollatzResearch.WordTrace tailWord_6236206 prefixEnd_6236206 3202171138452533049045217 := by
  unfold tailWord_6236206
  simp only [CollatzResearch.WordTrace]
  refine ⟨28431639855662274504527059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151635412563532130690810981 28431639855662274504527059)
  ·
    refine ⟨42647459783493411756790589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28431639855662274504527059 42647459783493411756790589)
    ·
      refine ⟨15992797418810029408796471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42647459783493411756790589 15992797418810029408796471)
      ·
        refine ⟨23989196128215044113194707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15992797418810029408796471 23989196128215044113194707)
        ·
          refine ⟨35983794192322566169792061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23989196128215044113194707 35983794192322566169792061)
          ·
            refine ⟨13493922822120962313672023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35983794192322566169792061 13493922822120962313672023)
            ·
              refine ⟨20240884233181443470508035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13493922822120962313672023 20240884233181443470508035)
              ·
                refine ⟨30361326349772165205762053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20240884233181443470508035 30361326349772165205762053)
                ·
                  refine ⟨5692748690582280976080385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30361326349772165205762053 5692748690582280976080385)
                  ·
                    refine ⟨4269561517936710732060289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5692748690582280976080385 4269561517936710732060289)
                    ·
                      refine ⟨3202171138452533049045217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269561517936710732060289 3202171138452533049045217)
                      ·
                        rfl

theorem cell23_6236206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_6236206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236206 prefixEnd_6236206 := by exact prefixLift 6236206
  have htrace : WordTrace (prefixWord ++ tailWord_6236206) baseStart_6236206 baseEnd_6236206 := by
    simpa [prefixWord, tailWord_6236206, baseEnd_6236206] using wordTrace_append hprefix tailTrace_6236206
  have hstable : (prefixWord ++ tailWord_6236206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236206).length < 2 ^ (prefixWord ++ tailWord_6236206).sum := by decide
  have hdescent : baseEnd_6236206 < baseStart_6236206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236306 : List Nat := [3, 2, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_6236306 : Nat := 118140960795 + 6236306 * 2 ^ 59
def prefixEnd_6236306 : Nat := 4983230072969 + 3 ^ 40 * 6236306 * 2
def baseEnd_6236306 : Nat := 1067407495505994219264919

theorem tailTrace_6236306 : CollatzResearch.WordTrace tailWord_6236306 prefixEnd_6236306 1067407495505994219264919 := by
  unfold tailWord_6236306
  simp only [CollatzResearch.WordTrace]
  refine ⟨56864191536233978278714193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151637844096623942076571181 56864191536233978278714193)
  ·
    refine ⟨42648143652175483709035645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56864191536233978278714193 42648143652175483709035645)
    ·
      refine ⟨15993053869565806390888367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42648143652175483709035645 15993053869565806390888367)
      ·
        refine ⟨23989580804348709586332551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15993053869565806390888367 23989580804348709586332551)
        ·
          refine ⟨35984371206523064379498827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23989580804348709586332551 35984371206523064379498827)
          ·
            refine ⟨53976556809784596569248241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35984371206523064379498827 53976556809784596569248241)
            ·
              refine ⟨40482417607338447426936181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53976556809784596569248241 40482417607338447426936181)
              ·
                refine ⟨3795226650687979446275267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40482417607338447426936181 3795226650687979446275267)
                ·
                  refine ⟨5692839976031969169412901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795226650687979446275267 5692839976031969169412901)
                  ·
                    refine ⟨1067407495505994219264919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692839976031969169412901 1067407495505994219264919)
                    ·
                      rfl

theorem cell23_6236306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_6236306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236306 prefixEnd_6236306 := by exact prefixLift 6236306
  have htrace : WordTrace (prefixWord ++ tailWord_6236306) baseStart_6236306 baseEnd_6236306 := by
    simpa [prefixWord, tailWord_6236306, baseEnd_6236306] using wordTrace_append hprefix tailTrace_6236306
  have hstable : (prefixWord ++ tailWord_6236306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236306).length < 2 ^ (prefixWord ++ tailWord_6236306).sum := by decide
  have hdescent : baseEnd_6236306 < baseStart_6236306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236319 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 6]
def baseStart_6236319 : Nat := 118140960795 + 6236319 * 2 ^ 59
def prefixEnd_6236319 : Nat := 4983230072969 + 3 ^ 40 * 6236319 * 2
def baseEnd_6236319 : Nat := 355803240196276789659133

theorem tailTrace_6236319 : CollatzResearch.WordTrace tailWord_6236319 prefixEnd_6236319 355803240196276789659133 := by
  unfold tailWord_6236319
  simp only [CollatzResearch.WordTrace]
  refine ⟨227457240293888816335080011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151638160195925877556720007 227457240293888816335080011)
  ·
    refine ⟨341185860440833224502620017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227457240293888816335080011 341185860440833224502620017)
    ·
      refine ⟨255889395330624918376965013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341185860440833224502620017 255889395330624918376965013)
      ·
        refine ⟨11994815406123043048920235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255889395330624918376965013 11994815406123043048920235)
        ·
          refine ⟨17992223109184564573380353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11994815406123043048920235 17992223109184564573380353)
          ·
            refine ⟨13494167331888423430035265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17992223109184564573380353 13494167331888423430035265)
            ·
              refine ⟨10120625498916317572526449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13494167331888423430035265 10120625498916317572526449)
              ·
                refine ⟨7590469124187238179394837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10120625498916317572526449 7590469124187238179394837)
                ·
                  refine ⟨355803240196276789659133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7590469124187238179394837 355803240196276789659133)
                  ·
                    rfl

theorem cell23_6236319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 6].length) (baseStart_6236319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236319 prefixEnd_6236319 := by exact prefixLift 6236319
  have htrace : WordTrace (prefixWord ++ tailWord_6236319) baseStart_6236319 baseEnd_6236319 := by
    simpa [prefixWord, tailWord_6236319, baseEnd_6236319] using wordTrace_append hprefix tailTrace_6236319
  have hstable : (prefixWord ++ tailWord_6236319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236319).length < 2 ^ (prefixWord ++ tailWord_6236319).sum := by decide
  have hdescent : baseEnd_6236319 < baseStart_6236319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236340 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6236340 : Nat := 118140960795 + 6236340 * 2 ^ 59
def prefixEnd_6236340 : Nat := 4983230072969 + 3 ^ 40 * 6236340 * 2
def baseEnd_6236340 : Nat := 1067413314953411841589867

theorem tailTrace_6236340 : CollatzResearch.WordTrace tailWord_6236340 prefixEnd_6236340 1067413314953411841589867 := by
  unfold tailWord_6236340
  simp only [CollatzResearch.WordTrace]
  refine ⟨113729003113406368460797237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151638670817875157947729649 113729003113406368460797237)
  ·
    refine ⟨10662094041881847043199741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113729003113406368460797237 10662094041881847043199741)
    ·
      refine ⟨3998285265705692641199903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10662094041881847043199741 3998285265705692641199903)
      ·
        refine ⟨5997427898558538961799855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3998285265705692641199903 5997427898558538961799855)
        ·
          refine ⟨8996141847837808442699783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5997427898558538961799855 8996141847837808442699783)
          ·
            refine ⟨13494212771756712664049675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8996141847837808442699783 13494212771756712664049675)
            ·
              refine ⟨20241319157635068996074513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13494212771756712664049675 20241319157635068996074513)
              ·
                refine ⟨15180989368226301747055885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20241319157635068996074513 15180989368226301747055885)
                ·
                  refine ⟨5692871013084863155145957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15180989368226301747055885 5692871013084863155145957)
                  ·
                    refine ⟨1067413314953411841589867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692871013084863155145957 1067413314953411841589867)
                    ·
                      rfl

theorem cell23_6236340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6236340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236340 prefixEnd_6236340 := by exact prefixLift 6236340
  have htrace : WordTrace (prefixWord ++ tailWord_6236340) baseStart_6236340 baseEnd_6236340 := by
    simpa [prefixWord, tailWord_6236340, baseEnd_6236340] using wordTrace_append hprefix tailTrace_6236340
  have hstable : (prefixWord ++ tailWord_6236340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236340).length < 2 ^ (prefixWord ++ tailWord_6236340).sum := by decide
  have hdescent : baseEnd_6236340 < baseStart_6236340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236356 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_6236356 : Nat := 118140960795 + 6236356 * 2 ^ 59
def prefixEnd_6236356 : Nat := 4983230072969 + 3 ^ 40 * 6236356 * 2
def baseEnd_6236356 : Nat := 3202248160550707462169527

theorem tailTrace_6236356 : CollatzResearch.WordTrace tailWord_6236356 prefixEnd_6236356 3202248160550707462169527 := by
  unfold tailWord_6236356
  simp only [CollatzResearch.WordTrace]
  refine ⟨113729294897377385827088461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151639059863169847769451281 113729294897377385827088461)
  ·
    refine ⟨42648485586516519685158173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113729294897377385827088461 42648485586516519685158173)
    ·
      refine ⟨15993182094943694881934315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42648485586516519685158173 15993182094943694881934315)
      ·
        refine ⟨23989773142415542322901473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15993182094943694881934315 23989773142415542322901473)
        ·
          refine ⟨17992329856811656742176105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23989773142415542322901473 17992329856811656742176105)
          ·
            refine ⟨13494247392608742556632079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17992329856811656742176105 13494247392608742556632079)
            ·
              refine ⟨20241371088913113834948119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13494247392608742556632079 20241371088913113834948119)
              ·
                refine ⟨30362056633369670752422179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20241371088913113834948119 30362056633369670752422179)
                ·
                  refine ⟨45543084950054506128633269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30362056633369670752422179 45543084950054506128633269)
                  ·
                    refine ⟨4269664214067609949559369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45543084950054506128633269 4269664214067609949559369)
                    ·
                      refine ⟨3202248160550707462169527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269664214067609949559369 3202248160550707462169527)
                      ·
                        rfl

theorem cell23_6236356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_6236356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236356 prefixEnd_6236356 := by exact prefixLift 6236356
  have htrace : WordTrace (prefixWord ++ tailWord_6236356) baseStart_6236356 baseEnd_6236356 := by
    simpa [prefixWord, tailWord_6236356, baseEnd_6236356] using wordTrace_append hprefix tailTrace_6236356
  have hstable : (prefixWord ++ tailWord_6236356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236356).length < 2 ^ (prefixWord ++ tailWord_6236356).sum := by decide
  have hdescent : baseEnd_6236356 < baseStart_6236356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236362 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_6236362 : Nat := 118140960795 + 6236362 * 2 ^ 59
def prefixEnd_6236362 : Nat := 4983230072969 + 3 ^ 40 * 6236362 * 2
def baseEnd_6236362 : Nat := 1067417080478211479564833

theorem tailTrace_6236362 : CollatzResearch.WordTrace tailWord_6236362 prefixEnd_6236362 1067417080478211479564833 := by
  unfold tailWord_6236362
  simp only [CollatzResearch.WordTrace]
  refine ⟨56864702158183258669723835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151639205755155356452596893 56864702158183258669723835)
  ·
    refine ⟨85297053237274888004585753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56864702158183258669723835 85297053237274888004585753)
    ·
      refine ⟨63972789927956166003439315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85297053237274888004585753 63972789927956166003439315)
      ·
        refine ⟨95959184891934249005158973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63972789927956166003439315 95959184891934249005158973)
        ·
          refine ⟨35984694334475343376934615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95959184891934249005158973 35984694334475343376934615)
          ·
            refine ⟨53977041501713015065401923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35984694334475343376934615 53977041501713015065401923)
            ·
              refine ⟨80965562252569522598102885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53977041501713015065401923 80965562252569522598102885)
              ·
                refine ⟨15181042922356785487144291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80965562252569522598102885 15181042922356785487144291)
                ·
                  refine ⟨22771564383535178230716437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15181042922356785487144291 22771564383535178230716437)
                  ·
                    refine ⟨1067417080478211479564833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22771564383535178230716437 1067417080478211479564833)
                    ·
                      rfl

theorem cell23_6236362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_6236362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236362 prefixEnd_6236362 := by exact prefixLift 6236362
  have htrace : WordTrace (prefixWord ++ tailWord_6236362) baseStart_6236362 baseEnd_6236362 := by
    simpa [prefixWord, tailWord_6236362, baseEnd_6236362] using wordTrace_append hprefix tailTrace_6236362
  have hstable : (prefixWord ++ tailWord_6236362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236362).length < 2 ^ (prefixWord ++ tailWord_6236362).sum := by decide
  have hdescent : baseEnd_6236362 < baseStart_6236362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236366 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_6236366 : Nat := 118140960795 + 6236366 * 2 ^ 59
def prefixEnd_6236366 : Nat := 4983230072969 + 3 ^ 40 * 6236366 * 2
def baseEnd_6236366 : Nat := 1067417765119084141014827

theorem tailTrace_6236366 : CollatzResearch.WordTrace tailWord_6236366 prefixEnd_6236366 1067417765119084141014827 := by
  unfold tailWord_6236366
  simp only [CollatzResearch.WordTrace]
  refine ⟨28432369315589817920255119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151639303016479028908027301 28432369315589817920255119)
  ·
    refine ⟨42648553973384726880382679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28432369315589817920255119 42648553973384726880382679)
    ·
      refine ⟨63972830960077090320574019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42648553973384726880382679 63972830960077090320574019)
      ·
        refine ⟨95959246440115635480861029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63972830960077090320574019 95959246440115635480861029)
        ·
          refine ⟨17992358707521681652661443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95959246440115635480861029 17992358707521681652661443)
          ·
            refine ⟨26988538061282522478992165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17992358707521681652661443 26988538061282522478992165)
            ·
              refine ⟨5060350886490472964811031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26988538061282522478992165 5060350886490472964811031)
              ·
                refine ⟨7590526329735709447216547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060350886490472964811031 7590526329735709447216547)
                ·
                  refine ⟨11385789494603564170824821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7590526329735709447216547 11385789494603564170824821)
                  ·
                    refine ⟨1067417765119084141014827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11385789494603564170824821 1067417765119084141014827)
                    ·
                      rfl

theorem cell23_6236366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_6236366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236366 prefixEnd_6236366 := by exact prefixLift 6236366
  have htrace : WordTrace (prefixWord ++ tailWord_6236366) baseStart_6236366 baseEnd_6236366 := by
    simpa [prefixWord, tailWord_6236366, baseEnd_6236366] using wordTrace_append hprefix tailTrace_6236366
  have hstable : (prefixWord ++ tailWord_6236366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236366).length < 2 ^ (prefixWord ++ tailWord_6236366).sum := by decide
  have hdescent : baseEnd_6236366 < baseStart_6236366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236380 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6236380 : Nat := 118140960795 + 6236380 * 2 ^ 59
def prefixEnd_6236380 : Nat := 4983230072969 + 3 ^ 40 * 6236380 * 2
def baseEnd_6236380 : Nat := 3202260484086415368269417

theorem tailTrace_6236380 : CollatzResearch.WordTrace tailWord_6236380 prefixEnd_6236380 3202260484086415368269417 := by
  unfold tailWord_6236380
  simp only [CollatzResearch.WordTrace]
  refine ⟨113729732573333911876525297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151639643431111882502033729 113729732573333911876525297)
  ·
    refine ⟨85297299430000433907393973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113729732573333911876525297 85297299430000433907393973)
    ·
      refine ⟨7996621821562540678818185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85297299430000433907393973 7996621821562540678818185)
      ·
        refine ⟨5997466366171905509113639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7996621821562540678818185 5997466366171905509113639)
        ·
          refine ⟨8996199549257858263670459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5997466366171905509113639 8996199549257858263670459)
          ·
            refine ⟨13494299323886787395505689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8996199549257858263670459 13494299323886787395505689)
            ·
              refine ⟨10120724492915090546629267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13494299323886787395505689 10120724492915090546629267)
              ·
                refine ⟨15181086739372635819943901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10120724492915090546629267 15181086739372635819943901)
                ·
                  refine ⟨5692907527264738432478963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15181086739372635819943901 5692907527264738432478963)
                  ·
                    refine ⟨8539361290897107648718445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692907527264738432478963 8539361290897107648718445)
                    ·
                      refine ⟨3202260484086415368269417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8539361290897107648718445 3202260484086415368269417)
                      ·
                        rfl

theorem cell23_6236380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6236380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236380 prefixEnd_6236380 := by exact prefixLift 6236380
  have htrace : WordTrace (prefixWord ++ tailWord_6236380) baseStart_6236380 baseEnd_6236380 := by
    simpa [prefixWord, tailWord_6236380, baseEnd_6236380] using wordTrace_append hprefix tailTrace_6236380
  have hstable : (prefixWord ++ tailWord_6236380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236380).length < 2 ^ (prefixWord ++ tailWord_6236380).sum := by decide
  have hdescent : baseEnd_6236380 < baseStart_6236380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236389 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6236389 : Nat := 118140960795 + 6236389 * 2 ^ 59
def prefixEnd_6236389 : Nat := 4983230072969 + 3 ^ 40 * 6236389 * 2
def baseEnd_6236389 : Nat := 3202265105412305833056875

theorem tailTrace_6236389 : CollatzResearch.WordTrace tailWord_6236389 prefixEnd_6236389 3202265105412305833056875 := by
  unfold tailWord_6236389
  simp only [CollatzResearch.WordTrace]
  refine ⟨227459793403635218290128221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151639862269090145526752147 227459793403635218290128221)
  ·
    refine ⟨85297422526363206858798083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227459793403635218290128221 85297422526363206858798083)
    ·
      refine ⟨127946133789544810288197125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85297422526363206858798083 127946133789544810288197125)
      ·
        refine ⟨23989900085539651929036961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127946133789544810288197125 23989900085539651929036961)
        ·
          refine ⟨17992425064154738946777721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23989900085539651929036961 17992425064154738946777721)
          ·
            refine ⟨13494318798116054210083291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17992425064154738946777721 13494318798116054210083291)
            ·
              refine ⟨20241478197174081315124937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13494318798116054210083291 20241478197174081315124937)
              ·
                refine ⟨15181108647880560986343703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20241478197174081315124937 15181108647880560986343703)
                ·
                  refine ⟨22771662971820841479515555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15181108647880560986343703 22771662971820841479515555)
                  ·
                    refine ⟨34157494457731262219273333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22771662971820841479515555 34157494457731262219273333)
                    ·
                      refine ⟨3202265105412305833056875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34157494457731262219273333 3202265105412305833056875)
                      ·
                        rfl

theorem cell23_6236389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6236389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236389 prefixEnd_6236389 := by exact prefixLift 6236389
  have htrace : WordTrace (prefixWord ++ tailWord_6236389) baseStart_6236389 baseEnd_6236389 := by
    simpa [prefixWord, tailWord_6236389, baseEnd_6236389] using wordTrace_append hprefix tailTrace_6236389
  have hstable : (prefixWord ++ tailWord_6236389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236389).length < 2 ^ (prefixWord ++ tailWord_6236389).sum := by decide
  have hdescent : baseEnd_6236389 < baseStart_6236389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236396 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_6236396 : Nat := 118140960795 + 6236396 * 2 ^ 59
def prefixEnd_6236396 : Nat := 4983230072969 + 3 ^ 40 * 6236396 * 2
def baseEnd_6236396 : Nat := 1067422899925629101889781

theorem tailTrace_6236396 : CollatzResearch.WordTrace tailWord_6236396 prefixEnd_6236396 1067422899925629101889781 := by
  unfold tailWord_6236396
  simp only [CollatzResearch.WordTrace]
  refine ⟨113730024357304929242816521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151640032476406572323755361 113730024357304929242816521)
  ·
    refine ⟨85297518267978696932112391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113730024357304929242816521 85297518267978696932112391)
    ·
      refine ⟨127946277401968045398168587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85297518267978696932112391 127946277401968045398168587)
      ·
        refine ⟨191919416102952068097252881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127946277401968045398168587 191919416102952068097252881)
        ·
          refine ⟨143939562077214051072939661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191919416102952068097252881 143939562077214051072939661)
          ·
            refine ⟨53977335778955269152352373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143939562077214051072939661 53977335778955269152352373)
            ·
              refine ⟨5060375229277056483033035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53977335778955269152352373 5060375229277056483033035)
              ·
                refine ⟨7590562843915584724549553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060375229277056483033035 7590562843915584724549553)
                ·
                  refine ⟨5692922132936688543412165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590562843915584724549553 5692922132936688543412165)
                  ·
                    refine ⟨1067422899925629101889781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5692922132936688543412165 1067422899925629101889781)
                    ·
                      rfl

theorem cell23_6236396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_6236396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236396 prefixEnd_6236396 := by exact prefixLift 6236396
  have htrace : WordTrace (prefixWord ++ tailWord_6236396) baseStart_6236396 baseEnd_6236396 := by
    simpa [prefixWord, tailWord_6236396, baseEnd_6236396] using wordTrace_append hprefix tailTrace_6236396
  have hstable : (prefixWord ++ tailWord_6236396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236396).length < 2 ^ (prefixWord ++ tailWord_6236396).sum := by decide
  have hdescent : baseEnd_6236396 < baseStart_6236396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236399 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 4]
def baseStart_6236399 : Nat := 118140960795 + 6236399 * 2 ^ 59
def prefixEnd_6236399 : Nat := 4983230072969 + 3 ^ 40 * 6236399 * 2
def baseEnd_6236399 : Nat := 3202270240218850793931829

theorem tailTrace_6236399 : CollatzResearch.WordTrace tailWord_6236399 prefixEnd_6236399 3202270240218850793931829 := by
  unfold tailWord_6236399
  simp only [CollatzResearch.WordTrace]
  refine ⟨227460158133598989997992251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151640105422399326665328167 227460158133598989997992251)
  ·
    refine ⟨341190237200398484996988377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227460158133598989997992251 341190237200398484996988377)
    ·
      refine ⟨255892677900298863747741283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341190237200398484996988377 255892677900298863747741283)
      ·
        refine ⟨383839016850448295621611925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255892677900298863747741283 383839016850448295621611925)
        ·
          refine ⟨17992453914864763857263059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 383839016850448295621611925 17992453914864763857263059)
          ·
            refine ⟨26988680872297145785894589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17992453914864763857263059 26988680872297145785894589)
            ·
              refine ⟨10120755327111429669710471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26988680872297145785894589 10120755327111429669710471)
              ·
                refine ⟨15181132990667144504565707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10120755327111429669710471 15181132990667144504565707)
                ·
                  refine ⟨22771699486000716756848561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15181132990667144504565707 22771699486000716756848561)
                  ·
                    refine ⟨17078774614500537567636421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22771699486000716756848561 17078774614500537567636421)
                    ·
                      refine ⟨3202270240218850793931829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17078774614500537567636421 3202270240218850793931829)
                      ·
                        rfl

theorem cell23_6236399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_6236399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236399 prefixEnd_6236399 := by exact prefixLift 6236399
  have htrace : WordTrace (prefixWord ++ tailWord_6236399) baseStart_6236399 baseEnd_6236399 := by
    simpa [prefixWord, tailWord_6236399, baseEnd_6236399] using wordTrace_append hprefix tailTrace_6236399
  have hstable : (prefixWord ++ tailWord_6236399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236399).length < 2 ^ (prefixWord ++ tailWord_6236399).sum := by decide
  have hdescent : baseEnd_6236399 < baseStart_6236399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236406 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_6236406 : Nat := 118140960795 + 6236406 * 2 ^ 59
def prefixEnd_6236406 : Nat := 4983230072969 + 3 ^ 40 * 6236406 * 2
def baseEnd_6236406 : Nat := 3202273834583432266544297

theorem tailTrace_6236406 : CollatzResearch.WordTrace tailWord_6236406 prefixEnd_6236406 3202273834583432266544297 := by
  unfold tailWord_6236406
  simp only [CollatzResearch.WordTrace]
  refine ⟨14216275840285851887093567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151640275629715753462331381 14216275840285851887093567)
  ·
    refine ⟨21324413760428777830640351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14216275840285851887093567 21324413760428777830640351)
    ·
      refine ⟨31986620640643166745960527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21324413760428777830640351 31986620640643166745960527)
      ·
        refine ⟨47979930960964750118940791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31986620640643166745960527 47979930960964750118940791)
        ·
          refine ⟨71969896441447125178411187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47979930960964750118940791 71969896441447125178411187)
          ·
            refine ⟨107954844662170687767616781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71969896441447125178411187 107954844662170687767616781)
            ·
              refine ⟨40483066748314007912856293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107954844662170687767616781 40483066748314007912856293)
              ·
                refine ⟨7590575015308876483660555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40483066748314007912856293 7590575015308876483660555)
                ·
                  refine ⟨11385862522963314725490833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7590575015308876483660555 11385862522963314725490833)
                  ·
                    refine ⟨8539396892222486044118125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11385862522963314725490833 8539396892222486044118125)
                    ·
                      refine ⟨3202273834583432266544297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8539396892222486044118125 3202273834583432266544297)
                      ·
                        rfl

theorem cell23_6236406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_6236406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236406 prefixEnd_6236406 := by exact prefixLift 6236406
  have htrace : WordTrace (prefixWord ++ tailWord_6236406) baseStart_6236406 baseEnd_6236406 := by
    simpa [prefixWord, tailWord_6236406, baseEnd_6236406] using wordTrace_append hprefix tailTrace_6236406
  have hstable : (prefixWord ++ tailWord_6236406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236406).length < 2 ^ (prefixWord ++ tailWord_6236406).sum := by decide
  have hdescent : baseEnd_6236406 < baseStart_6236406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236419 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 3]
def baseStart_6236419 : Nat := 118140960795 + 6236419 * 2 ^ 59
def prefixEnd_6236419 : Nat := 4983230072969 + 3 ^ 40 * 6236419 * 2
def baseEnd_6236419 : Nat := 3202280509831940715681737

theorem tailTrace_6236419 : CollatzResearch.WordTrace tailWord_6236419 prefixEnd_6236419 3202280509831940715681737 := by
  unfold tailWord_6236419
  simp only [CollatzResearch.WordTrace]
  refine ⟨227460887593526533413720311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151640591729017688942480207 227460887593526533413720311)
  ·
    refine ⟨341191331390289800120580467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227460887593526533413720311 341191331390289800120580467)
    ·
      refine ⟨511786997085434700180870701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341191331390289800120580467 511786997085434700180870701)
      ·
        refine ⟨191920123907038012567826513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 511786997085434700180870701 191920123907038012567826513)
        ·
          refine ⟨143940092930278509425869885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191920123907038012567826513 143940092930278509425869885)
          ·
            refine ⟨53977534848854441034701207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143940092930278509425869885 53977534848854441034701207)
            ·
              refine ⟨80966302273281661552051811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53977534848854441034701207 80966302273281661552051811)
              ·
                refine ⟨121449453409922492328077717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80966302273281661552051811 121449453409922492328077717)
                ·
                  refine ⟨5692943128590116827878643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 121449453409922492328077717 5692943128590116827878643)
                  ·
                    refine ⟨8539414692885175241817965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692943128590116827878643 8539414692885175241817965)
                    ·
                      refine ⟨3202280509831940715681737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8539414692885175241817965 3202280509831940715681737)
                      ·
                        rfl

theorem cell23_6236419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_6236419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236419 prefixEnd_6236419 := by exact prefixLift 6236419
  have htrace : WordTrace (prefixWord ++ tailWord_6236419) baseStart_6236419 baseEnd_6236419 := by
    simpa [prefixWord, tailWord_6236419, baseEnd_6236419] using wordTrace_append hprefix tailTrace_6236419
  have hstable : (prefixWord ++ tailWord_6236419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236419).length < 2 ^ (prefixWord ++ tailWord_6236419).sum := by decide
  have hdescent : baseEnd_6236419 < baseStart_6236419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236453 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_6236453 : Nat := 118140960795 + 6236453 * 2 ^ 59
def prefixEnd_6236453 : Nat := 4983230072969 + 3 ^ 40 * 6236453 * 2
def baseEnd_6236453 : Nat := 3202297968174193582656581

theorem tailTrace_6236453 : CollatzResearch.WordTrace tailWord_6236453 prefixEnd_6236453 3202297968174193582656581 := by
  unfold tailWord_6236453
  simp only [CollatzResearch.WordTrace]
  refine ⟨227462127675403357220458013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151641418450268904813638675 227462127675403357220458013)
  ·
    refine ⟨85298297878276258957671755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227462127675403357220458013 85298297878276258957671755)
    ·
      refine ⟨127947446817414388436507633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85298297878276258957671755 127947446817414388436507633)
      ·
        refine ⟨95960585113060791327380725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127947446817414388436507633 95960585113060791327380725)
        ·
          refine ⟨8996304854349449186941943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95960585113060791327380725 8996304854349449186941943)
          ·
            refine ⟨13494457281524173780412915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8996304854349449186941943 13494457281524173780412915)
            ·
              refine ⟨20241685922286260670619373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13494457281524173780412915 20241685922286260670619373)
              ·
                refine ⟨7590632220857347751482265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20241685922286260670619373 7590632220857347751482265)
                ·
                  refine ⟨5692974165643010813611699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590632220857347751482265 5692974165643010813611699)
                  ·
                    refine ⟨8539461248464516220417549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692974165643010813611699 8539461248464516220417549)
                    ·
                      refine ⟨3202297968174193582656581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8539461248464516220417549 3202297968174193582656581)
                      ·
                        rfl

theorem cell23_6236453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_6236453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236453 prefixEnd_6236453 := by exact prefixLift 6236453
  have htrace : WordTrace (prefixWord ++ tailWord_6236453) baseStart_6236453 baseEnd_6236453 := by
    simpa [prefixWord, tailWord_6236453, baseEnd_6236453] using wordTrace_append hprefix tailTrace_6236453
  have hstable : (prefixWord ++ tailWord_6236453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236453).length < 2 ^ (prefixWord ++ tailWord_6236453).sum := by decide
  have hdescent : baseEnd_6236453 < baseStart_6236453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236476 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_6236476 : Nat := 118140960795 + 6236476 * 2 ^ 59
def prefixEnd_6236476 : Nat := 4983230072969 + 3 ^ 40 * 6236476 * 2
def baseEnd_6236476 : Nat := 3202309778229246992668975

theorem tailTrace_6236476 : CollatzResearch.WordTrace tailWord_6236476 prefixEnd_6236476 3202309778229246992668975 := by
  unfold tailWord_6236476
  simp only [CollatzResearch.WordTrace]
  refine ⟨113731483277160016074272641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151641977702880021432363521 113731483277160016074272641)
  ·
    refine ⟨85298612457870012055704481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113731483277160016074272641 85298612457870012055704481)
    ·
      refine ⟨63973959343402509041778361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85298612457870012055704481 63973959343402509041778361)
      ·
        refine ⟨47980469507551881781333771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63973959343402509041778361 47980469507551881781333771)
        ·
          refine ⟨71970704261327822672000657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47980469507551881781333771 71970704261327822672000657)
          ·
            refine ⟨53978028195995867004000493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71970704261327822672000657 53978028195995867004000493)
            ·
              refine ⟨20241760573498450126500185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53978028195995867004000493 20241760573498450126500185)
              ·
                refine ⟨15181320430123837594875139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20241760573498450126500185 15181320430123837594875139)
                ·
                  refine ⟨22771980645185756392312709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15181320430123837594875139 22771980645185756392312709)
                  ·
                    refine ⟨4269746370972329323558633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22771980645185756392312709 4269746370972329323558633)
                    ·
                      refine ⟨3202309778229246992668975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269746370972329323558633 3202309778229246992668975)
                      ·
                        rfl

theorem cell23_6236476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_6236476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236476 prefixEnd_6236476 := by exact prefixLift 6236476
  have htrace : WordTrace (prefixWord ++ tailWord_6236476) baseStart_6236476 baseEnd_6236476 := by
    simpa [prefixWord, tailWord_6236476, baseEnd_6236476] using wordTrace_append hprefix tailTrace_6236476
  have hstable : (prefixWord ++ tailWord_6236476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236476).length < 2 ^ (prefixWord ++ tailWord_6236476).sum := by decide
  have hdescent : baseEnd_6236476 < baseStart_6236476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236533 : List Nat := [1, 3, 4, 1, 2, 2, 2, 3, 5]
def baseStart_6236533 : Nat := 118140960795 + 6236533 * 2 ^ 59
def prefixEnd_6236533 : Nat := 4983230072969 + 3 ^ 40 * 6236533 * 2
def baseEnd_6236533 : Nat := 355815449625172585517357

theorem tailTrace_6236533 : CollatzResearch.WordTrace tailWord_6236533 prefixEnd_6236533 355815449625172585517357 := by
  unfold tailWord_6236533
  simp only [CollatzResearch.WordTrace]
  refine ⟨227465045515113530883370253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151643363676742353922246835 227465045515113530883370253)
  ·
    refine ⟨85299392068167574081263845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227465045515113530883370253 85299392068167574081263845)
    ·
      refine ⟨15993636012781420140236971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85299392068167574081263845 15993636012781420140236971)
      ·
        refine ⟨23990454019172130210355457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15993636012781420140236971 23990454019172130210355457)
        ·
          refine ⟨17992840514379097657766593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23990454019172130210355457 17992840514379097657766593)
          ·
            refine ⟨13494630385784323243324945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17992840514379097657766593 13494630385784323243324945)
            ·
              refine ⟨10120972789338242432493709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13494630385784323243324945 10120972789338242432493709)
              ·
                refine ⟨3795364796001840912185141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10120972789338242432493709 3795364796001840912185141)
                ·
                  refine ⟨355815449625172585517357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3795364796001840912185141 355815449625172585517357)
                  ·
                    rfl

theorem cell23_6236533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_6236533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236533 prefixEnd_6236533 := by exact prefixLift 6236533
  have htrace : WordTrace (prefixWord ++ tailWord_6236533) baseStart_6236533 baseEnd_6236533 := by
    simpa [prefixWord, tailWord_6236533, baseEnd_6236533] using wordTrace_append hprefix tailTrace_6236533
  have hstable : (prefixWord ++ tailWord_6236533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236533).length < 2 ^ (prefixWord ++ tailWord_6236533).sum := by decide
  have hdescent : baseEnd_6236533 < baseStart_6236533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236549 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_6236549 : Nat := 118140960795 + 6236549 * 2 ^ 59
def prefixEnd_6236549 : Nat := 4983230072969 + 3 ^ 40 * 6236549 * 2
def baseEnd_6236549 : Nat := 3202347262317025207056139

theorem tailTrace_6236549 : CollatzResearch.WordTrace tailWord_6236549 prefixEnd_6236549 3202347262317025207056139 := by
  unfold tailWord_6236549
  simp only [CollatzResearch.WordTrace]
  refine ⟨227465629083055565615952701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151643752722037043743968467 227465629083055565615952701)
  ·
    refine ⟨85299610906145837105982263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227465629083055565615952701 85299610906145837105982263)
    ·
      refine ⟨127949416359218755658973395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85299610906145837105982263 127949416359218755658973395)
      ·
        refine ⟨191924124538828133488460093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127949416359218755658973395 191924124538828133488460093)
        ·
          refine ⟨71971546702060550058172535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191924124538828133488460093 71971546702060550058172535)
          ·
            refine ⟨107957320053090825087258803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71971546702060550058172535 107957320053090825087258803)
            ·
              refine ⟨161935980079636237630888205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107957320053090825087258803 161935980079636237630888205)
              ·
                refine ⟨60725992529863589111583077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161935980079636237630888205 60725992529863589111583077)
                ·
                  refine ⟨11386123599349422958421827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60725992529863589111583077 11386123599349422958421827)
                  ·
                    refine ⟨17079185399024134437632741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11386123599349422958421827 17079185399024134437632741)
                    ·
                      refine ⟨3202347262317025207056139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17079185399024134437632741 3202347262317025207056139)
                      ·
                        rfl

theorem cell23_6236549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_6236549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236549 prefixEnd_6236549 := by exact prefixLift 6236549
  have htrace : WordTrace (prefixWord ++ tailWord_6236549) baseStart_6236549 baseEnd_6236549 := by
    simpa [prefixWord, tailWord_6236549, baseEnd_6236549] using wordTrace_append hprefix tailTrace_6236549
  have hstable : (prefixWord ++ tailWord_6236549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236549).length < 2 ^ (prefixWord ++ tailWord_6236549).sum := by decide
  have hdescent : baseEnd_6236549 < baseStart_6236549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236569 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 3]
def baseStart_6236569 : Nat := 118140960795 + 6236569 * 2 ^ 59
def prefixEnd_6236569 : Nat := 4983230072969 + 3 ^ 40 * 6236569 * 2
def baseEnd_6236569 : Nat := 3202357531930115128806047

theorem tailTrace_6236569 : CollatzResearch.WordTrace tailWord_6236569 prefixEnd_6236569 3202357531930115128806047 := by
  unfold tailWord_6236569
  simp only [CollatzResearch.WordTrace]
  refine ⟨227466358542983109031680761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151644239028655406021120507 227466358542983109031680761)
  ·
    refine ⟨170599768907237331773760571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227466358542983109031680761 170599768907237331773760571)
    ·
      refine ⟨255899653360855997660640857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170599768907237331773760571 255899653360855997660640857)
      ·
        refine ⟨191924740020641998245480643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255899653360855997660640857 191924740020641998245480643)
        ·
          refine ⟨287887110030962997368220965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191924740020641998245480643 287887110030962997368220965)
          ·
            refine ⟨53978833130805562006541431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287887110030962997368220965 53978833130805562006541431)
            ·
              refine ⟨80968249696208343009812147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53978833130805562006541431 80968249696208343009812147)
              ·
                refine ⟨121452374544312514514718221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80968249696208343009812147 121452374544312514514718221)
                ·
                  refine ⟨45544640454117192943019333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121452374544312514514718221 45544640454117192943019333)
                  ·
                    refine ⟨8539620085146973676816125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45544640454117192943019333 8539620085146973676816125)
                    ·
                      refine ⟨3202357531930115128806047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8539620085146973676816125 3202357531930115128806047)
                      ·
                        rfl

theorem cell23_6236569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_6236569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236569 prefixEnd_6236569 := by exact prefixLift 6236569
  have htrace : WordTrace (prefixWord ++ tailWord_6236569) baseStart_6236569 baseEnd_6236569 := by
    simpa [prefixWord, tailWord_6236569, baseEnd_6236569] using wordTrace_append hprefix tailTrace_6236569
  have hstable : (prefixWord ++ tailWord_6236569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236569).length < 2 ^ (prefixWord ++ tailWord_6236569).sum := by decide
  have hdescent : baseEnd_6236569 < baseStart_6236569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236576 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 3, 4]
def baseStart_6236576 : Nat := 118140960795 + 6236576 * 2 ^ 59
def prefixEnd_6236576 : Nat := 4983230072969 + 3 ^ 40 * 6236576 * 2
def baseEnd_6236576 : Nat := 1067453708764898867139505

theorem tailTrace_6236576 : CollatzResearch.WordTrace tailWord_6236576 prefixEnd_6236576 1067453708764898867139505 := by
  unfold tailWord_6236576
  simp only [CollatzResearch.WordTrace]
  refine ⟨113733306926978874613592791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151644409235971832818123721 113733306926978874613592791)
  ·
    refine ⟨170599960390468311920389187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113733306926978874613592791 170599960390468311920389187)
    ·
      refine ⟨255899940585702467880583781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170599960390468311920389187 255899940585702467880583781)
      ·
        refine ⟨47981238859819212727609459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 255899940585702467880583781 47981238859819212727609459)
        ·
          refine ⟨71971858289728819091414189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47981238859819212727609459 71971858289728819091414189)
          ·
            refine ⟨26989446858648307159280321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71971858289728819091414189 26989446858648307159280321)
            ·
              refine ⟨20242085143986230369460241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26989446858648307159280321 20242085143986230369460241)
              ·
                refine ⟨15181563857989672777095181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20242085143986230369460241 15181563857989672777095181)
                ·
                  refine ⟨5693086446746127291410693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15181563857989672777095181 5693086446746127291410693)
                  ·
                    refine ⟨1067453708764898867139505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693086446746127291410693 1067453708764898867139505)
                    ·
                      rfl

theorem cell23_6236576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 3, 4].length) (baseStart_6236576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236576 prefixEnd_6236576 := by exact prefixLift 6236576
  have htrace : WordTrace (prefixWord ++ tailWord_6236576) baseStart_6236576 baseEnd_6236576 := by
    simpa [prefixWord, tailWord_6236576, baseEnd_6236576] using wordTrace_append hprefix tailTrace_6236576
  have hstable : (prefixWord ++ tailWord_6236576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236576).length < 2 ^ (prefixWord ++ tailWord_6236576).sum := by decide
  have hdescent : baseEnd_6236576 < baseStart_6236576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236619 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 3, 5]
def baseStart_6236619 : Nat := 118140960795 + 6236619 * 2 ^ 59
def prefixEnd_6236619 : Nat := 4983230072969 + 3 ^ 40 * 6236619 * 2
def baseEnd_6236619 : Nat := 1067461068654279977726939

theorem tailTrace_6236619 : CollatzResearch.WordTrace tailWord_6236619 prefixEnd_6236619 1067461068654279977726939 := by
  unfold tailWord_6236619
  simp only [CollatzResearch.WordTrace]
  refine ⟨227468182192801967571000911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151645454795201311714000607 227468182192801967571000911)
  ·
    refine ⟨341202273289202951356501367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227468182192801967571000911 341202273289202951356501367)
    ·
      refine ⟨511803409933804427034752051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341202273289202951356501367 511803409933804427034752051)
      ·
        refine ⟨767705114900706640552128077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511803409933804427034752051 767705114900706640552128077)
        ·
          refine ⟨287889418087764990207048029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767705114900706640552128077 287889418087764990207048029)
          ·
            refine ⟨107958531782911871327643011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287889418087764990207048029 107958531782911871327643011)
            ·
              refine ⟨161937797674367806991464517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107958531782911871327643011 161937797674367806991464517)
              ·
                refine ⟨30363337063943963810899597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161937797674367806991464517 30363337063943963810899597)
                ·
                  refine ⟨11386251398978986429087349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30363337063943963810899597 11386251398978986429087349)
                  ·
                    refine ⟨1067461068654279977726939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11386251398978986429087349 1067461068654279977726939)
                    ·
                      rfl

theorem cell23_6236619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 5].length) (baseStart_6236619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236619 prefixEnd_6236619 := by exact prefixLift 6236619
  have htrace : WordTrace (prefixWord ++ tailWord_6236619) baseStart_6236619 baseEnd_6236619 := by
    simpa [prefixWord, tailWord_6236619, baseEnd_6236619] using wordTrace_append hprefix tailTrace_6236619
  have hstable : (prefixWord ++ tailWord_6236619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236619).length < 2 ^ (prefixWord ++ tailWord_6236619).sum := by decide
  have hdescent : baseEnd_6236619 < baseStart_6236619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236661 : List Nat := [1, 3, 5, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6236661 : Nat := 118140960795 + 6236661 * 2 ^ 59
def prefixEnd_6236661 : Nat := 4983230072969 + 3 ^ 40 * 6236661 * 2
def baseEnd_6236661 : Nat := 1067468257383442922951875

theorem tailTrace_6236661 : CollatzResearch.WordTrace tailWord_6236661 prefixEnd_6236661 1067468257383442922951875 := by
  unfold tailWord_6236661
  simp only [CollatzResearch.WordTrace]
  refine ⟨227469714058649808744029837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151646476039099872496019891 227469714058649808744029837)
  ·
    refine ⟨85301142771993678279011189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227469714058649808744029837 85301142771993678279011189)
    ·
      refine ⟨7996982134874407338657299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85301142771993678279011189 7996982134874407338657299)
      ·
        refine ⟨11995473202311611007985949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7996982134874407338657299 11995473202311611007985949)
        ·
          refine ⟨4498302450866854127994731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11995473202311611007985949 4498302450866854127994731)
          ·
            refine ⟨6747453676300281191992097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4498302450866854127994731 6747453676300281191992097)
            ·
              refine ⟨5060590257225210893994073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6747453676300281191992097 5060590257225210893994073)
              ·
                refine ⟨3795442692918908170495555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060590257225210893994073 3795442692918908170495555)
                ·
                  refine ⟨5693164039378362255743333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795442692918908170495555 5693164039378362255743333)
                  ·
                    refine ⟨1067468257383442922951875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693164039378362255743333 1067468257383442922951875)
                    ·
                      rfl

theorem cell23_6236661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6236661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236661 prefixEnd_6236661 := by exact prefixLift 6236661
  have htrace : WordTrace (prefixWord ++ tailWord_6236661) baseStart_6236661 baseEnd_6236661 := by
    simpa [prefixWord, tailWord_6236661, baseEnd_6236661] using wordTrace_append hprefix tailTrace_6236661
  have hstable : (prefixWord ++ tailWord_6236661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236661).length < 2 ^ (prefixWord ++ tailWord_6236661).sum := by decide
  have hdescent : baseEnd_6236661 < baseStart_6236661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236683 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 2, 4]
def baseStart_6236683 : Nat := 118140960795 + 6236683 * 2 ^ 59
def prefixEnd_6236683 : Nat := 4983230072969 + 3 ^ 40 * 6236683 * 2
def baseEnd_6236683 : Nat := 1067472022908242560926841

theorem tailTrace_6236683 : CollatzResearch.WordTrace tailWord_6236683 prefixEnd_6236683 1067472022908242560926841 := by
  unfold tailWord_6236683
  simp only [CollatzResearch.WordTrace]
  refine ⟨227470516464570106501330703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151647010976380071000887135 227470516464570106501330703)
  ·
    refine ⟨341205774696855159751996055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227470516464570106501330703 341205774696855159751996055)
    ·
      refine ⟨511808662045282739627994083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341205774696855159751996055 511808662045282739627994083)
      ·
        refine ⟨767712993067924109441991125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511808662045282739627994083 767712993067924109441991125)
        ·
          refine ⟨17993273275029471315046667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 767712993067924109441991125 17993273275029471315046667)
          ·
            refine ⟨26989909912544206972570001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17993273275029471315046667 26989909912544206972570001)
            ·
              refine ⟨20242432434408155229427501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26989909912544206972570001 20242432434408155229427501)
              ·
                refine ⟨7590912162903058211035313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20242432434408155229427501 7590912162903058211035313)
                ·
                  refine ⟨5693184122177293658276485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590912162903058211035313 5693184122177293658276485)
                  ·
                    refine ⟨1067472022908242560926841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693184122177293658276485 1067472022908242560926841)
                    ·
                      rfl

theorem cell23_6236683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 4].length) (baseStart_6236683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236683 prefixEnd_6236683 := by exact prefixLift 6236683
  have htrace : WordTrace (prefixWord ++ tailWord_6236683) baseStart_6236683 baseEnd_6236683 := by
    simpa [prefixWord, tailWord_6236683, baseEnd_6236683] using wordTrace_append hprefix tailTrace_6236683
  have hstable : (prefixWord ++ tailWord_6236683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236683).length < 2 ^ (prefixWord ++ tailWord_6236683).sum := by decide
  have hdescent : baseEnd_6236683 < baseStart_6236683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236693 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_6236693 : Nat := 118140960795 + 6236693 * 2 ^ 59
def prefixEnd_6236693 : Nat := 4983230072969 + 3 ^ 40 * 6236693 * 2
def baseEnd_6236693 : Nat := 3202421203531272643655477

theorem tailTrace_6236693 : CollatzResearch.WordTrace tailWord_6236693 prefixEnd_6236693 3202421203531272643655477 := by
  unfold tailWord_6236693
  simp only [CollatzResearch.WordTrace]
  refine ⟨227470881194533878209194733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151647254129689252139463155 227470881194533878209194733)
  ·
    refine ⟨85301580447950204328448025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227470881194533878209194733 85301580447950204328448025)
    ·
      refine ⟨63976185335962653246336019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85301580447950204328448025 63976185335962653246336019)
      ·
        refine ⟨95964278003943979869504029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63976185335962653246336019 95964278003943979869504029)
        ·
          refine ⟨35986604251478992451064011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95964278003943979869504029 35986604251478992451064011)
          ·
            refine ⟨53979906377218488676596017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35986604251478992451064011 53979906377218488676596017)
            ·
              refine ⟨40484929782913866507447013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53979906377218488676596017 40484929782913866507447013)
              ·
                refine ⟨7590924334296349970146315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40484929782913866507447013 7590924334296349970146315)
                ·
                  refine ⟨11386386501444524955219473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7590924334296349970146315 11386386501444524955219473)
                  ·
                    refine ⟨8539789876083393716414605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11386386501444524955219473 8539789876083393716414605)
                    ·
                      refine ⟨3202421203531272643655477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8539789876083393716414605 3202421203531272643655477)
                      ·
                        rfl

theorem cell23_6236693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_6236693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236693 prefixEnd_6236693 := by exact prefixLift 6236693
  have htrace : WordTrace (prefixWord ++ tailWord_6236693) baseStart_6236693 baseEnd_6236693 := by
    simpa [prefixWord, tailWord_6236693, baseEnd_6236693] using wordTrace_append hprefix tailTrace_6236693
  have hstable : (prefixWord ++ tailWord_6236693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236693).length < 2 ^ (prefixWord ++ tailWord_6236693).sum := by decide
  have hdescent : baseEnd_6236693 < baseStart_6236693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236707 : List Nat := [1, 1, 1, 4, 4, 1, 1, 5, 1, 2, 2]
def baseStart_6236707 : Nat := 118140960795 + 6236707 * 2 ^ 59
def prefixEnd_6236707 : Nat := 4983230072969 + 3 ^ 40 * 6236707 * 2
def baseEnd_6236707 : Nat := 3202428392260435588880413

theorem tailTrace_6236707 : CollatzResearch.WordTrace tailWord_6236707 prefixEnd_6236707 3202428392260435588880413 := by
  unfold tailWord_6236707
  simp only [CollatzResearch.WordTrace]
  refine ⟨227471391816483158600204375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151647594544322105733469583 227471391816483158600204375)
  ·
    refine ⟨341207087724724737900306563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227471391816483158600204375 341207087724724737900306563)
    ·
      refine ⟨511810631587087106850459845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341207087724724737900306563 511810631587087106850459845)
      ·
        refine ⟨95964493422578832534461221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 511810631587087106850459845 95964493422578832534461221)
        ·
          refine ⟨17993342516733531100211479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95964493422578832534461221 17993342516733531100211479)
          ·
            refine ⟨26990013775100296650317219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17993342516733531100211479 26990013775100296650317219)
            ·
              refine ⟨40485020662650444975475829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26990013775100296650317219 40485020662650444975475829)
              ·
                refine ⟨3795470687123479216450859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40485020662650444975475829 3795470687123479216450859)
                ·
                  refine ⟨5693206030685218824676289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795470687123479216450859 5693206030685218824676289)
                  ·
                    refine ⟨4269904523013914118507217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5693206030685218824676289 4269904523013914118507217)
                    ·
                      refine ⟨3202428392260435588880413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269904523013914118507217 3202428392260435588880413)
                      ·
                        rfl

theorem cell23_6236707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_6236707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236707 prefixEnd_6236707 := by exact prefixLift 6236707
  have htrace : WordTrace (prefixWord ++ tailWord_6236707) baseStart_6236707 baseEnd_6236707 := by
    simpa [prefixWord, tailWord_6236707, baseEnd_6236707] using wordTrace_append hprefix tailTrace_6236707
  have hstable : (prefixWord ++ tailWord_6236707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236707).length < 2 ^ (prefixWord ++ tailWord_6236707).sum := by decide
  have hdescent : baseEnd_6236707 < baseStart_6236707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236723 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 3]
def baseStart_6236723 : Nat := 118140960795 + 6236723 * 2 ^ 59
def prefixEnd_6236723 : Nat := 4983230072969 + 3 ^ 40 * 6236723 * 2
def baseEnd_6236723 : Nat := 3202436607950907526280339

theorem tailTrace_6236723 : CollatzResearch.WordTrace tailWord_6236723 prefixEnd_6236723 3202436607950907526280339 := by
  unfold tailWord_6236723
  simp only [CollatzResearch.WordTrace]
  refine ⟨227471975384425193332786823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151647983589616795555191215 227471975384425193332786823)
  ·
    refine ⟨341207963076637789999180235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227471975384425193332786823 341207963076637789999180235)
    ·
      refine ⟨511811944614956684998770353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341207963076637789999180235 511811944614956684998770353)
      ·
        refine ⟨383858958461217513749077765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511811944614956684998770353 383858958461217513749077765)
        ·
          refine ⟨71973554711478283827952081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 383858958461217513749077765 71973554711478283827952081)
          ·
            refine ⟨53980166033608712870964061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71973554711478283827952081 53980166033608712870964061)
            ·
              refine ⟨20242562262603267326611523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53980166033608712870964061 20242562262603267326611523)
              ·
                refine ⟨30363843393904900989917285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20242562262603267326611523 30363843393904900989917285)
                ·
                  refine ⟨5693220636357168935609491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30363843393904900989917285 5693220636357168935609491)
                  ·
                    refine ⟨8539830954535753403414237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5693220636357168935609491 8539830954535753403414237)
                    ·
                      refine ⟨3202436607950907526280339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8539830954535753403414237 3202436607950907526280339)
                      ·
                        rfl

theorem cell23_6236723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 3].length) (baseStart_6236723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236723 prefixEnd_6236723 := by exact prefixLift 6236723
  have htrace : WordTrace (prefixWord ++ tailWord_6236723) baseStart_6236723 baseEnd_6236723 := by
    simpa [prefixWord, tailWord_6236723, baseEnd_6236723] using wordTrace_append hprefix tailTrace_6236723
  have hstable : (prefixWord ++ tailWord_6236723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236723).length < 2 ^ (prefixWord ++ tailWord_6236723).sum := by decide
  have hdescent : baseEnd_6236723 < baseStart_6236723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236734 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_6236734 : Nat := 118140960795 + 6236734 * 2 ^ 59
def prefixEnd_6236734 : Nat := 4983230072969 + 3 ^ 40 * 6236734 * 2
def baseEnd_6236734 : Nat := 1067480752079368994414263

theorem tailTrace_6236734 : CollatzResearch.WordTrace tailWord_6236734 prefixEnd_6236734 1067480752079368994414263 := by
  unfold tailWord_6236734
  simp only [CollatzResearch.WordTrace]
  refine ⟨28434047073423167776429657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151648251058256894807624837 28434047073423167776429657)
  ·
    refine ⟨21325535305067375832322243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28434047073423167776429657 21325535305067375832322243)
    ·
      refine ⟨31988302957601063748483365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21325535305067375832322243 31988302957601063748483365)
      ·
        refine ⟨5997806804550199452840631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31988302957601063748483365 5997806804550199452840631)
        ·
          refine ⟨8996710206825299179260947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5997806804550199452840631 8996710206825299179260947)
          ·
            refine ⟨13495065310237948768891421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8996710206825299179260947 13495065310237948768891421)
            ·
              refine ⟨5060649491339230788334283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13495065310237948768891421 5060649491339230788334283)
              ·
                refine ⟨7590974237008846182501425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5060649491339230788334283 7590974237008846182501425)
                ·
                  refine ⟨5693230677756634636876069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7590974237008846182501425 5693230677756634636876069)
                  ·
                    refine ⟨1067480752079368994414263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693230677756634636876069 1067480752079368994414263)
                    ·
                      rfl

theorem cell23_6236734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_6236734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236734 prefixEnd_6236734 := by exact prefixLift 6236734
  have htrace : WordTrace (prefixWord ++ tailWord_6236734) baseStart_6236734 baseEnd_6236734 := by
    simpa [prefixWord, tailWord_6236734, baseEnd_6236734] using wordTrace_append hprefix tailTrace_6236734
  have hstable : (prefixWord ++ tailWord_6236734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236734).length < 2 ^ (prefixWord ++ tailWord_6236734).sum := by decide
  have hdescent : baseEnd_6236734 < baseStart_6236734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236750 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_6236750 : Nat := 118140960795 + 6236750 * 2 ^ 59
def prefixEnd_6236750 : Nat := 4983230072969 + 3 ^ 40 * 6236750 * 2
def baseEnd_6236750 : Nat := 3202450471928578920642715

theorem tailTrace_6236750 : CollatzResearch.WordTrace tailWord_6236750 prefixEnd_6236750 3202450471928578920642715 := by
  unfold tailWord_6236750
  simp only [CollatzResearch.WordTrace]
  refine ⟨28434120019415922118002463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151648640103551584629346469 28434120019415922118002463)
  ·
    refine ⟨42651180029123883177003695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28434120019415922118002463 42651180029123883177003695)
    ·
      refine ⟨63976770043685824765505543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42651180029123883177003695 63976770043685824765505543)
      ·
        refine ⟨95965155065528737148258315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63976770043685824765505543 95965155065528737148258315)
        ·
          refine ⟨143947732598293105722387473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95965155065528737148258315 143947732598293105722387473)
          ·
            refine ⟨107960799448719829291790605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143947732598293105722387473 107960799448719829291790605)
            ·
              refine ⟨40485299793269935984421477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107960799448719829291790605 40485299793269935984421477)
              ·
                refine ⟨7590993711238112997079027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40485299793269935984421477 7590993711238112997079027)
                ·
                  refine ⟨11386490566857169495618541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7590993711238112997079027 11386490566857169495618541)
                  ·
                    refine ⟨4269933962571438560856953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11386490566857169495618541 4269933962571438560856953)
                    ·
                      refine ⟨3202450471928578920642715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269933962571438560856953 3202450471928578920642715)
                      ·
                        rfl

theorem cell23_6236750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_6236750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236750 prefixEnd_6236750 := by exact prefixLift 6236750
  have htrace : WordTrace (prefixWord ++ tailWord_6236750) baseStart_6236750 baseEnd_6236750 := by
    simpa [prefixWord, tailWord_6236750, baseEnd_6236750] using wordTrace_append hprefix tailTrace_6236750
  have hstable : (prefixWord ++ tailWord_6236750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236750).length < 2 ^ (prefixWord ++ tailWord_6236750).sum := by decide
  have hdescent : baseEnd_6236750 < baseStart_6236750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236780 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 4, 2, 2]
def baseStart_6236780 : Nat := 118140960795 + 6236780 * 2 ^ 59
def prefixEnd_6236780 : Nat := 4983230072969 + 3 ^ 40 * 6236780 * 2
def baseEnd_6236780 : Nat := 3202465876348213803267577

theorem tailTrace_6236780 : CollatzResearch.WordTrace tailWord_6236780 prefixEnd_6236780 3202465876348213803267577 := by
  unfold tailWord_6236780
  simp only [CollatzResearch.WordTrace]
  refine ⟨113737027172609346033805897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151649369563479128045074529 113737027172609346033805897)
  ·
    refine ⟨85302770379457009525354423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113737027172609346033805897 85302770379457009525354423)
    ·
      refine ⟨127954155569185514288031635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85302770379457009525354423 127954155569185514288031635)
      ·
        refine ⟨191931233353778271432047453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127954155569185514288031635 191931233353778271432047453)
        ·
          refine ⟨71974212507666851787017795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191931233353778271432047453 71974212507666851787017795)
          ·
            refine ⟨107961318761500277680526693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71974212507666851787017795 107961318761500277680526693)
            ·
              refine ⟨20242747267781302065098755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107961318761500277680526693 20242747267781302065098755)
              ·
                refine ⟨30364120901671953097648133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20242747267781302065098755 30364120901671953097648133)
                ·
                  refine ⟨5693272669063491205809025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30364120901671953097648133 5693272669063491205809025)
                  ·
                    refine ⟨4269954501797618404356769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5693272669063491205809025 4269954501797618404356769)
                    ·
                      refine ⟨3202465876348213803267577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4269954501797618404356769 3202465876348213803267577)
                      ·
                        rfl

theorem cell23_6236780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_6236780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236780 prefixEnd_6236780 := by exact prefixLift 6236780
  have htrace : WordTrace (prefixWord ++ tailWord_6236780) baseStart_6236780 baseEnd_6236780 := by
    simpa [prefixWord, tailWord_6236780, baseEnd_6236780] using wordTrace_append hprefix tailTrace_6236780
  have hstable : (prefixWord ++ tailWord_6236780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236780).length < 2 ^ (prefixWord ++ tailWord_6236780).sum := by decide
  have hdescent : baseEnd_6236780 < baseStart_6236780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236830 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_6236830 : Nat := 118140960795 + 6236830 * 2 ^ 59
def prefixEnd_6236830 : Nat := 4983230072969 + 3 ^ 40 * 6236830 * 2
def baseEnd_6236830 : Nat := 3202491550380938607642347

theorem tailTrace_6236830 : CollatzResearch.WordTrace tailWord_6236830 prefixEnd_6236830 3202491550380938607642347 := by
  unfold tailWord_6236830
  simp only [CollatzResearch.WordTrace]
  refine ⟨28434484749379693825866493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151650585330025033737954629 28434484749379693825866493)
  ·
    refine ⟨10662931781017385184699935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28434484749379693825866493 10662931781017385184699935)
    ·
      refine ⟨15994397671526077777049903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10662931781017385184699935 15994397671526077777049903)
      ·
        refine ⟨23991596507289116665574855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15994397671526077777049903 23991596507289116665574855)
        ·
          refine ⟨35987394760933674998362283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23991596507289116665574855 35987394760933674998362283)
          ·
            refine ⟨53981092141400512497543425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35987394760933674998362283 53981092141400512497543425)
            ·
              refine ⟨40485819106050384373157569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53981092141400512497543425 40485819106050384373157569)
              ·
                refine ⟨30364364329537788279868177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40485819106050384373157569 30364364329537788279868177)
                ·
                  refine ⟨22773273247153341209901133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30364364329537788279868177 22773273247153341209901133)
                  ·
                    refine ⟨8539977467682502953712925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22773273247153341209901133 8539977467682502953712925)
                    ·
                      refine ⟨3202491550380938607642347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8539977467682502953712925 3202491550380938607642347)
                      ·
                        rfl

theorem cell23_6236830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_6236830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236830 prefixEnd_6236830 := by exact prefixLift 6236830
  have htrace : WordTrace (prefixWord ++ tailWord_6236830) baseStart_6236830 baseEnd_6236830 := by
    simpa [prefixWord, tailWord_6236830, baseEnd_6236830] using wordTrace_append hprefix tailTrace_6236830
  have hstable : (prefixWord ++ tailWord_6236830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236830).length < 2 ^ (prefixWord ++ tailWord_6236830).sum := by decide
  have hdescent : baseEnd_6236830 < baseStart_6236830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236863 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 5, 4]
def baseStart_6236863 : Nat := 118140960795 + 6236863 * 2 ^ 59
def prefixEnd_6236863 : Nat := 4983230072969 + 3 ^ 40 * 6236863 * 2
def baseEnd_6236863 : Nat := 1067502831747512326176565

theorem tailTrace_6236863 : CollatzResearch.WordTrace tailWord_6236863 prefixEnd_6236863 1067502831747512326176565 := by
  unfold tailWord_6236863
  simp only [CollatzResearch.WordTrace]
  refine ⟨227477081603917997242883243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151651387735945331495255495 227477081603917997242883243)
  ·
    refine ⟨341215622405876995864324865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227477081603917997242883243 341215622405876995864324865)
    ·
      refine ⟨255911716804407746898243649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341215622405876995864324865 255911716804407746898243649)
      ·
        refine ⟨191933787603305810173682737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255911716804407746898243649 191933787603305810173682737)
        ·
          refine ⟨143950340702479357630262053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191933787603305810173682737 143950340702479357630262053)
          ·
            refine ⟨26990688881714879555674135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143950340702479357630262053 26990688881714879555674135)
            ·
              refine ⟨40486033322572319333511203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26990688881714879555674135 40486033322572319333511203)
              ·
                refine ⟨60729049983858479000266805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40486033322572319333511203 60729049983858479000266805)
                ·
                  refine ⟨5693348435986732406275013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60729049983858479000266805 5693348435986732406275013)
                  ·
                    refine ⟨1067502831747512326176565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693348435986732406275013 1067502831747512326176565)
                    ·
                      rfl

theorem cell23_6236863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 4].length) (baseStart_6236863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236863 prefixEnd_6236863 := by exact prefixLift 6236863
  have htrace : WordTrace (prefixWord ++ tailWord_6236863) baseStart_6236863 baseEnd_6236863 := by
    simpa [prefixWord, tailWord_6236863, baseEnd_6236863] using wordTrace_append hprefix tailTrace_6236863
  have hstable : (prefixWord ++ tailWord_6236863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236863).length < 2 ^ (prefixWord ++ tailWord_6236863).sum := by decide
  have hdescent : baseEnd_6236863 < baseStart_6236863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236897 : List Nat := [1, 2, 3, 1, 4, 1, 2, 4, 1, 4]
def baseStart_6236897 : Nat := 118140960795 + 6236897 * 2 ^ 59
def prefixEnd_6236897 : Nat := 4983230072969 + 3 ^ 40 * 6236897 * 2
def baseEnd_6236897 : Nat := 1067508651194929948501513

theorem tailTrace_6236897 : CollatzResearch.WordTrace tailWord_6236897 prefixEnd_6236897 1067508651194929948501513 := by
  unfold tailWord_6236897
  simp only [CollatzResearch.WordTrace]
  refine ⟨227478321685794821049620945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151652214457196547366413963 227478321685794821049620945)
  ·
    refine ⟨170608741264346115787215709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227478321685794821049620945 170608741264346115787215709)
    ·
      refine ⟨63978277974129793420205891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170608741264346115787215709 63978277974129793420205891)
      ·
        refine ⟨95967416961194690130308837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63978277974129793420205891 95967416961194690130308837)
        ·
          refine ⟨17993890680224004399432907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95967416961194690130308837 17993890680224004399432907)
          ·
            refine ⟨26990836020336006599149361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17993890680224004399432907 26990836020336006599149361)
            ·
              refine ⟨20243127015252004949362021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26990836020336006599149361 20243127015252004949362021)
              ·
                refine ⟨3795586315359750928005379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20243127015252004949362021 3795586315359750928005379)
                ·
                  refine ⟨5693379473039626392008069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795586315359750928005379 5693379473039626392008069)
                  ·
                    refine ⟨1067508651194929948501513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693379473039626392008069 1067508651194929948501513)
                    ·
                      rfl

theorem cell23_6236897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_6236897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236897 prefixEnd_6236897 := by exact prefixLift 6236897
  have htrace : WordTrace (prefixWord ++ tailWord_6236897) baseStart_6236897 baseEnd_6236897 := by
    simpa [prefixWord, tailWord_6236897, baseEnd_6236897] using wordTrace_append hprefix tailTrace_6236897
  have hstable : (prefixWord ++ tailWord_6236897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236897).length < 2 ^ (prefixWord ++ tailWord_6236897).sum := by decide
  have hdescent : baseEnd_6236897 < baseStart_6236897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236920 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_6236920 : Nat := 118140960795 + 6236920 * 2 ^ 59
def prefixEnd_6236920 : Nat := 4983230072969 + 3 ^ 40 * 6236920 * 2
def baseEnd_6236920 : Nat := 3202537763639843255516933

theorem tailTrace_6236920 : CollatzResearch.WordTrace tailWord_6236920 prefixEnd_6236920 3202537763639843255516933 := by
  unfold tailWord_6236920
  simp only [CollatzResearch.WordTrace]
  refine ⟨113739580282355747988854107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151652773709807663985138809 113739580282355747988854107)
  ·
    refine ⟨170609370423533621983281161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113739580282355747988854107 170609370423533621983281161)
    ·
      refine ⟨127957027817650216487460871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170609370423533621983281161 127957027817650216487460871)
      ·
        refine ⟨191935541726475324731191307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127957027817650216487460871 191935541726475324731191307)
        ·
          refine ⟨287903312589712987096786961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191935541726475324731191307 287903312589712987096786961)
          ·
            refine ⟨215927484442284740322590221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287903312589712987096786961 215927484442284740322590221)
            ·
              refine ⟨80972806665856777620971333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 215927484442284740322590221 80972806665856777620971333)
              ·
                refine ⟨15182401249848145803932125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80972806665856777620971333 15182401249848145803932125)
                ·
                  refine ⟨5693400468693054676474547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15182401249848145803932125 5693400468693054676474547)
                  ·
                    refine ⟨8540100703039582014711821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5693400468693054676474547 8540100703039582014711821)
                    ·
                      refine ⟨3202537763639843255516933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540100703039582014711821 3202537763639843255516933)
                      ·
                        rfl

theorem cell23_6236920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_6236920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236920 prefixEnd_6236920 := by exact prefixLift 6236920
  have htrace : WordTrace (prefixWord ++ tailWord_6236920) baseStart_6236920 baseEnd_6236920 := by
    simpa [prefixWord, tailWord_6236920, baseEnd_6236920] using wordTrace_append hprefix tailTrace_6236920
  have hstable : (prefixWord ++ tailWord_6236920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236920).length < 2 ^ (prefixWord ++ tailWord_6236920).sum := by decide
  have hdescent : baseEnd_6236920 < baseStart_6236920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236963 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 3]
def baseStart_6236963 : Nat := 118140960795 + 6236963 * 2 ^ 59
def prefixEnd_6236963 : Nat := 4983230072969 + 3 ^ 40 * 6236963 * 2
def baseEnd_6236963 : Nat := 3202559843307986587279235

theorem tailTrace_6236963 : CollatzResearch.WordTrace tailWord_6236963 prefixEnd_6236963 3202559843307986587279235 := by
  unfold tailWord_6236963
  simp only [CollatzResearch.WordTrace]
  refine ⟨227480728903555714321523543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151653819269037142881015695 227480728903555714321523543)
  ·
    refine ⟨341221093355333571482285315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227480728903555714321523543 341221093355333571482285315)
    ·
      refine ⟨511831640033000357223427973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341221093355333571482285315 511831640033000357223427973)
      ·
        refine ⟨95968432506187566979392745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 511831640033000357223427973 95968432506187566979392745)
        ·
          refine ⟨71976324379640675234544559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95968432506187566979392745 71976324379640675234544559)
          ·
            refine ⟨107964486569461012851816839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71976324379640675234544559 107964486569461012851816839)
            ·
              refine ⟨161946729854191519277725259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107964486569461012851816839 161946729854191519277725259)
              ·
                refine ⟨242920094781287278916587889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161946729854191519277725259 242920094781287278916587889)
                ·
                  refine ⟨182190071085965459187440917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242920094781287278916587889 182190071085965459187440917)
                  ·
                    refine ⟨8540159582154630899411293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 182190071085965459187440917 8540159582154630899411293)
                    ·
                      refine ⟨3202559843307986587279235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540159582154630899411293 3202559843307986587279235)
                      ·
                        rfl

theorem cell23_6236963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_6236963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236963 prefixEnd_6236963 := by exact prefixLift 6236963
  have htrace : WordTrace (prefixWord ++ tailWord_6236963) baseStart_6236963 baseEnd_6236963 := by
    simpa [prefixWord, tailWord_6236963, baseEnd_6236963] using wordTrace_append hprefix tailTrace_6236963
  have hstable : (prefixWord ++ tailWord_6236963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236963).length < 2 ^ (prefixWord ++ tailWord_6236963).sum := by decide
  have hdescent : baseEnd_6236963 < baseStart_6236963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236974 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_6236974 : Nat := 118140960795 + 6236974 * 2 ^ 59
def prefixEnd_6236974 : Nat := 4983230072969 + 3 ^ 40 * 6236974 * 2
def baseEnd_6236974 : Nat := 1067521830531728681413895

theorem tailTrace_6236974 : CollatzResearch.WordTrace tailWord_6236974 prefixEnd_6236974 1067521830531728681413895 := by
  unfold tailWord_6236974
  simp only [CollatzResearch.WordTrace]
  refine ⟨28435141263314482900021747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151654086737677242133449317 28435141263314482900021747)
  ·
    refine ⟨42652711894971724350032621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28435141263314482900021747 42652711894971724350032621)
    ·
      refine ⟨15994766960614396631262233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42652711894971724350032621 15994766960614396631262233)
      ·
        refine ⟨11996075220460797473446675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15994766960614396631262233 11996075220460797473446675)
        ·
          refine ⟨17994112830691196210170013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11996075220460797473446675 17994112830691196210170013)
          ·
            refine ⟨6747792311509198578813755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17994112830691196210170013 6747792311509198578813755)
            ·
              refine ⟨10121688467263797868220633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747792311509198578813755 10121688467263797868220633)
              ·
                refine ⟨7591266350447848401165475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10121688467263797868220633 7591266350447848401165475)
                ·
                  refine ⟨11386899525671772601748213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7591266350447848401165475 11386899525671772601748213)
                  ·
                    refine ⟨1067521830531728681413895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11386899525671772601748213 1067521830531728681413895)
                    ·
                      rfl

theorem cell23_6236974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_6236974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236974 prefixEnd_6236974 := by exact prefixLift 6236974
  have htrace : WordTrace (prefixWord ++ tailWord_6236974) baseStart_6236974 baseEnd_6236974 := by
    simpa [prefixWord, tailWord_6236974, baseEnd_6236974] using wordTrace_append hprefix tailTrace_6236974
  have hstable : (prefixWord ++ tailWord_6236974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236974).length < 2 ^ (prefixWord ++ tailWord_6236974).sum := by decide
  have hdescent : baseEnd_6236974 < baseStart_6236974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6236977 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 5, 2, 2]
def baseStart_6236977 : Nat := 118140960795 + 6236977 * 2 ^ 59
def prefixEnd_6236977 : Nat := 4983230072969 + 3 ^ 40 * 6236977 * 2
def baseEnd_6236977 : Nat := 3202567032037149532504171

theorem tailTrace_6236977 : CollatzResearch.WordTrace tailWord_6236977 prefixEnd_6236977 3202567032037149532504171 := by
  unfold tailWord_6236977
  simp only [CollatzResearch.WordTrace]
  refine ⟨227481239525504994712533185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151654159683669996475022123 227481239525504994712533185)
  ·
    refine ⟨170610929644128746034399889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227481239525504994712533185 170610929644128746034399889)
    ·
      refine ⟨127958197233096559525799917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170610929644128746034399889 127958197233096559525799917)
      ·
        refine ⟨47984323962411209822174969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127958197233096559525799917 47984323962411209822174969)
        ·
          refine ⟨35988242971808407366631227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47984323962411209822174969 35988242971808407366631227)
          ·
            refine ⟨53982364457712611049946841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35988242971808407366631227 53982364457712611049946841)
            ·
              refine ⟨40486773343284458287460131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53982364457712611049946841 40486773343284458287460131)
              ·
                refine ⟨60730160014926687431190197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40486773343284458287460131 60730160014926687431190197)
                ·
                  refine ⟨5693452501399376946674081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60730160014926687431190197 5693452501399376946674081)
                  ·
                    refine ⟨4270089376049532710005561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5693452501399376946674081 4270089376049532710005561)
                    ·
                      refine ⟨3202567032037149532504171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270089376049532710005561 3202567032037149532504171)
                      ·
                        rfl

theorem cell23_6236977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_6236977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6236977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6236977 prefixEnd_6236977 := by exact prefixLift 6236977
  have htrace : WordTrace (prefixWord ++ tailWord_6236977) baseStart_6236977 baseEnd_6236977 := by
    simpa [prefixWord, tailWord_6236977, baseEnd_6236977] using wordTrace_append hprefix tailTrace_6236977
  have hstable : (prefixWord ++ tailWord_6236977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6236977).length < 2 ^ (prefixWord ++ tailWord_6236977).sum := by decide
  have hdescent : baseEnd_6236977 < baseStart_6236977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6236977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237005 : List Nat := [1, 6, 1, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6237005 : Nat := 118140960795 + 6237005 * 2 ^ 59
def prefixEnd_6237005 : Nat := 4983230072969 + 3 ^ 40 * 6237005 * 2
def baseEnd_6237005 : Nat := 3202581409495475422954043

theorem tailTrace_6237005 : CollatzResearch.WordTrace tailWord_6237005 prefixEnd_6237005 3202581409495475422954043 := by
  unfold tailWord_6237005
  simp only [CollatzResearch.WordTrace]
  refine ⟨227482260769403555494552469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151654840512935703663034979 227482260769403555494552469)
  ·
    refine ⟨10663230973565791663807147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 227482260769403555494552469 10663230973565791663807147)
    ·
      refine ⟨15994846460348687495710721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10663230973565791663807147 15994846460348687495710721)
      ·
        refine ⟨11996134845261515621783041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15994846460348687495710721 11996134845261515621783041)
        ·
          refine ⟨8997101133946136716337281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11996134845261515621783041 8997101133946136716337281)
          ·
            refine ⟨6747825850459602537252961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8997101133946136716337281 6747825850459602537252961)
            ·
              refine ⟨5060869387844701902939721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6747825850459602537252961 5060869387844701902939721)
              ·
                refine ⟨3795652040883526427204791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5060869387844701902939721 3795652040883526427204791)
                ·
                  refine ⟨5693478061325289640807187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795652040883526427204791 5693478061325289640807187)
                  ·
                    refine ⟨8540217091987934461210781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5693478061325289640807187 8540217091987934461210781)
                    ·
                      refine ⟨3202581409495475422954043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540217091987934461210781 3202581409495475422954043)
                      ·
                        rfl

theorem cell23_6237005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6237005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237005 prefixEnd_6237005 := by exact prefixLift 6237005
  have htrace : WordTrace (prefixWord ++ tailWord_6237005) baseStart_6237005 baseEnd_6237005 := by
    simpa [prefixWord, tailWord_6237005, baseEnd_6237005] using wordTrace_append hprefix tailTrace_6237005
  have hstable : (prefixWord ++ tailWord_6237005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237005).length < 2 ^ (prefixWord ++ tailWord_6237005).sum := by decide
  have hdescent : baseEnd_6237005 < baseStart_6237005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237010 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_6237010 : Nat := 118140960795 + 6237010 * 2 ^ 59
def prefixEnd_6237010 : Nat := 4983230072969 + 3 ^ 40 * 6237010 * 2
def baseEnd_6237010 : Nat := 3202583976898747903391519

theorem tailTrace_6237010 : CollatzResearch.WordTrace tailWord_6237010 prefixEnd_6237010 3202583976898747903391519 := by
  unfold tailWord_6237010
  simp only [CollatzResearch.WordTrace]
  refine ⟨56870610783596360337121121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151654962089590294232322989 56870610783596360337121121)
  ·
    refine ⟨42652958087697270252840841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56870610783596360337121121 42652958087697270252840841)
    ·
      refine ⟨31989718565772952689630631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42652958087697270252840841 31989718565772952689630631)
      ·
        refine ⟨47984577848659429034445947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31989718565772952689630631 47984577848659429034445947)
        ·
          refine ⟨71976866772989143551668921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47984577848659429034445947 71976866772989143551668921)
          ·
            refine ⟨53982650079741857663751691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71976866772989143551668921 53982650079741857663751691)
            ·
              refine ⟨80973975119612786495627537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53982650079741857663751691 80973975119612786495627537)
              ·
                refine ⟨60730481339709589871720653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80973975119612786495627537 60730481339709589871720653)
                ·
                  refine ⟨22773930502391096201895245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60730481339709589871720653 22773930502391096201895245)
                  ·
                    refine ⟨8540223938396661075710717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22773930502391096201895245 8540223938396661075710717)
                    ·
                      refine ⟨3202583976898747903391519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540223938396661075710717 3202583976898747903391519)
                      ·
                        rfl

theorem cell23_6237010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_6237010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237010 prefixEnd_6237010 := by exact prefixLift 6237010
  have htrace : WordTrace (prefixWord ++ tailWord_6237010) baseStart_6237010 baseEnd_6237010 := by
    simpa [prefixWord, tailWord_6237010, baseEnd_6237010] using wordTrace_append hprefix tailTrace_6237010
  have hstable : (prefixWord ++ tailWord_6237010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237010).length < 2 ^ (prefixWord ++ tailWord_6237010).sum := by decide
  have hdescent : baseEnd_6237010 < baseStart_6237010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237013 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_6237013 : Nat := 118140960795 + 6237013 * 2 ^ 59
def prefixEnd_6237013 : Nat := 4983230072969 + 3 ^ 40 * 6237013 * 2
def baseEnd_6237013 : Nat := 1067528505780237130551335

theorem tailTrace_6237013 : CollatzResearch.WordTrace tailWord_6237013 prefixEnd_6237013 1067528505780237130551335 := by
  unfold tailWord_6237013
  simp only [CollatzResearch.WordTrace]
  refine ⟨227482552553374572860843693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151655035035583048573895795 227482552553374572860843693)
  ·
    refine ⟨85305957207515464822816385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227482552553374572860843693 85305957207515464822816385)
    ·
      refine ⟨63979467905636598617112289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85305957207515464822816385 63979467905636598617112289)
      ·
        refine ⟨47984600929227448962834217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63979467905636598617112289 47984600929227448962834217)
        ·
          refine ⟨35988450696920586722125663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47984600929227448962834217 35988450696920586722125663)
          ·
            refine ⟨53982676045380880083188495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35988450696920586722125663 53982676045380880083188495)
            ·
              refine ⟨80974014068071320124782743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53982676045380880083188495 80974014068071320124782743)
              ·
                refine ⟨121461021102106980187174115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80974014068071320124782743 121461021102106980187174115)
                ·
                  refine ⟨182191531653160470280761173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121461021102106980187174115 182191531653160470280761173)
                  ·
                    refine ⟨1067528505780237130551335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 182191531653160470280761173 1067528505780237130551335)
                    ·
                      rfl

theorem cell23_6237013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_6237013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237013 prefixEnd_6237013 := by exact prefixLift 6237013
  have htrace : WordTrace (prefixWord ++ tailWord_6237013) baseStart_6237013 baseEnd_6237013 := by
    simpa [prefixWord, tailWord_6237013, baseEnd_6237013] using wordTrace_append hprefix tailTrace_6237013
  have hstable : (prefixWord ++ tailWord_6237013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237013).length < 2 ^ (prefixWord ++ tailWord_6237013).sum := by decide
  have hdescent : baseEnd_6237013 < baseStart_6237013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237027 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 3]
def baseStart_6237027 : Nat := 118140960795 + 6237027 * 2 ^ 59
def prefixEnd_6237027 : Nat := 4983230072969 + 3 ^ 40 * 6237027 * 2
def baseEnd_6237027 : Nat := 3202592706069874336878941

theorem tailTrace_6237027 : CollatzResearch.WordTrace tailWord_6237027 prefixEnd_6237027 3202592706069874336878941 := by
  unfold tailWord_6237027
  simp only [CollatzResearch.WordTrace]
  refine ⟨227483063175323853251853335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151655375450215902167902223 227483063175323853251853335)
  ·
    refine ⟨341224594762985779877780003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227483063175323853251853335 341224594762985779877780003)
    ·
      refine ⟨511836892144478669816670005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341224594762985779877780003 511836892144478669816670005)
      ·
        refine ⟨47984708638544875295312813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 511836892144478669816670005 47984708638544875295312813)
        ·
          refine ⟨17994265739454328235742305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47984708638544875295312813 17994265739454328235742305)
          ·
            refine ⟨13495699304590746176806729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17994265739454328235742305 13495699304590746176806729)
            ·
              refine ⟨10121774478443059632605047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13495699304590746176806729 10121774478443059632605047)
              ·
                refine ⟨15182661717664589448907571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10121774478443059632605047 15182661717664589448907571)
                ·
                  refine ⟨22773992576496884173361357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15182661717664589448907571 22773992576496884173361357)
                  ·
                    refine ⟨8540247216186331565010509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22773992576496884173361357 8540247216186331565010509)
                    ·
                      refine ⟨3202592706069874336878941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540247216186331565010509 3202592706069874336878941)
                      ·
                        rfl

theorem cell23_6237027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_6237027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237027 prefixEnd_6237027 := by exact prefixLift 6237027
  have htrace : WordTrace (prefixWord ++ tailWord_6237027) baseStart_6237027 baseEnd_6237027 := by
    simpa [prefixWord, tailWord_6237027, baseEnd_6237027] using wordTrace_append hprefix tailTrace_6237027
  have hstable : (prefixWord ++ tailWord_6237027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237027).length < 2 ^ (prefixWord ++ tailWord_6237027).sum := by decide
  have hdescent : baseEnd_6237027 < baseStart_6237027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237078 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6237078 : Nat := 118140960795 + 6237078 * 2 ^ 59
def prefixEnd_6237078 : Nat := 4983230072969 + 3 ^ 40 * 6237078 * 2
def baseEnd_6237078 : Nat := 3202618893583253637341207

theorem tailTrace_6237078 : CollatzResearch.WordTrace tailWord_6237078 prefixEnd_6237078 3202618893583253637341207 := by
  unfold tailWord_6237078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14217807706133693060122493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151656615532092725974639925 14217807706133693060122493)
  ·
    refine ⟨5331677889800134897545935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14217807706133693060122493 5331677889800134897545935)
    ·
      refine ⟨7997516834700202346318903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5331677889800134897545935 7997516834700202346318903)
      ·
        refine ⟨11996275252050303519478355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7997516834700202346318903 11996275252050303519478355)
        ·
          refine ⟨17994412878075455279217533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11996275252050303519478355 17994412878075455279217533)
          ·
            refine ⟨6747904829278295729706575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17994412878075455279217533 6747904829278295729706575)
            ·
              refine ⟨10121857243917443594559863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6747904829278295729706575 10121857243917443594559863)
              ·
                refine ⟨15182785865876165391839795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10121857243917443594559863 15182785865876165391839795)
                ·
                  refine ⟨22774178798814248087759693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15182785865876165391839795 22774178798814248087759693)
                  ·
                    refine ⟨8540317049555343032909885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22774178798814248087759693 8540317049555343032909885)
                    ·
                      refine ⟨3202618893583253637341207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540317049555343032909885 3202618893583253637341207)
                      ·
                        rfl

theorem cell23_6237078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6237078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237078 prefixEnd_6237078 := by exact prefixLift 6237078
  have htrace : WordTrace (prefixWord ++ tailWord_6237078) baseStart_6237078 baseEnd_6237078 := by
    simpa [prefixWord, tailWord_6237078, baseEnd_6237078] using wordTrace_append hprefix tailTrace_6237078
  have hstable : (prefixWord ++ tailWord_6237078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237078).length < 2 ^ (prefixWord ++ tailWord_6237078).sum := by decide
  have hdescent : baseEnd_6237078 < baseStart_6237078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237120 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 4, 5]
def baseStart_6237120 : Nat := 118140960795 + 6237120 * 2 ^ 59
def prefixEnd_6237120 : Nat := 4983230072969 + 3 ^ 40 * 6237120 * 2
def baseEnd_6237120 : Nat := 1067546819923580824338671

theorem tailTrace_6237120 : CollatzResearch.WordTrace tailWord_6237120 prefixEnd_6237120 1067546819923580824338671 := by
  unfold tailWord_6237120
  simp only [CollatzResearch.WordTrace]
  refine ⟨113743227581993465067494407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151657636775991286756659209 113743227581993465067494407)
  ·
    refine ⟨170614841372990197601241611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113743227581993465067494407 170614841372990197601241611)
    ·
      refine ⟨255922262059485296401862417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170614841372990197601241611 255922262059485296401862417)
      ·
        refine ⟨191941696544613972301396813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255922262059485296401862417 191941696544613972301396813)
        ·
          refine ⟨71978136204230239613023805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191941696544613972301396813 71978136204230239613023805)
          ·
            refine ⟨26991801076586339854883927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71978136204230239613023805 26991801076586339854883927)
            ·
              refine ⟨40487701614879509782325891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26991801076586339854883927 40487701614879509782325891)
              ·
                refine ⟨60731552422319264673488837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40487701614879509782325891 60731552422319264673488837)
                ·
                  refine ⟨11387166079184862126279157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60731552422319264673488837 11387166079184862126279157)
                  ·
                    refine ⟨1067546819923580824338671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11387166079184862126279157 1067546819923580824338671)
                    ·
                      rfl

theorem cell23_6237120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_6237120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237120 prefixEnd_6237120 := by exact prefixLift 6237120
  have htrace : WordTrace (prefixWord ++ tailWord_6237120) baseStart_6237120 baseEnd_6237120 := by
    simpa [prefixWord, tailWord_6237120, baseEnd_6237120] using wordTrace_append hprefix tailTrace_6237120
  have hstable : (prefixWord ++ tailWord_6237120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237120).length < 2 ^ (prefixWord ++ tailWord_6237120).sum := by decide
  have hdescent : baseEnd_6237120 < baseStart_6237120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237154 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6237154 : Nat := 118140960795 + 6237154 * 2 ^ 59
def prefixEnd_6237154 : Nat := 4983230072969 + 3 ^ 40 * 6237154 * 2
def baseEnd_6237154 : Nat := 1067552639370998446663619

theorem tailTrace_6237154 : CollatzResearch.WordTrace tailWord_6237154 prefixEnd_6237154 1067552639370998446663619 := by
  unfold tailWord_6237154
  simp only [CollatzResearch.WordTrace]
  refine ⟨56871923811465938485431629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151658463497242502627817677 56871923811465938485431629)
  ·
    refine ⟨21326971429299726932036861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56871923811465938485431629 21326971429299726932036861)
    ·
      refine ⟨7997614285987397599513823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21326971429299726932036861 7997614285987397599513823)
      ·
        refine ⟨11996421428981096399270735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7997614285987397599513823 11996421428981096399270735)
        ·
          refine ⟨17994632143471644598906103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11996421428981096399270735 17994632143471644598906103)
          ·
            refine ⟨26991948215207466898359155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17994632143471644598906103 26991948215207466898359155)
            ·
              refine ⟨40487922322811200347538733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26991948215207466898359155 40487922322811200347538733)
              ·
                refine ⟨15182970871054200130327025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40487922322811200347538733 15182970871054200130327025)
                ·
                  refine ⟨11387228153290650097745269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15182970871054200130327025 11387228153290650097745269)
                  ·
                    refine ⟨1067552639370998446663619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11387228153290650097745269 1067552639370998446663619)
                    ·
                      rfl

theorem cell23_6237154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6237154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237154 prefixEnd_6237154 := by exact prefixLift 6237154
  have htrace : WordTrace (prefixWord ++ tailWord_6237154) baseStart_6237154 baseEnd_6237154 := by
    simpa [prefixWord, tailWord_6237154, baseEnd_6237154] using wordTrace_append hprefix tailTrace_6237154
  have hstable : (prefixWord ++ tailWord_6237154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237154).length < 2 ^ (prefixWord ++ tailWord_6237154).sum := by decide
  have hdescent : baseEnd_6237154 < baseStart_6237154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237174 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6237174 : Nat := 118140960795 + 6237174 * 2 ^ 59
def prefixEnd_6237174 : Nat := 4983230072969 + 3 ^ 40 * 6237174 * 2
def baseEnd_6237174 : Nat := 3202668187726085261740765

theorem tailTrace_6237174 : CollatzResearch.WordTrace tailWord_6237174 prefixEnd_6237174 3202668187726085261740765 := by
  unfold tailWord_6237174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14218026544111956084840911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151658949803860864904969717 14218026544111956084840911)
  ·
    refine ⟨21327039816167934127261367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14218026544111956084840911 21327039816167934127261367)
    ·
      refine ⟨31990559724251901190892051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21327039816167934127261367 31990559724251901190892051)
      ·
        refine ⟨47985839586377851786338077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31990559724251901190892051 47985839586377851786338077)
        ·
          refine ⟨17994689844891694419876779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47985839586377851786338077 17994689844891694419876779)
          ·
            refine ⟨26992034767337541629815169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17994689844891694419876779 26992034767337541629815169)
            ·
              refine ⟨20244026075503156222361377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26992034767337541629815169 20244026075503156222361377)
              ·
                refine ⟨15183019556627367166771033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20244026075503156222361377 15183019556627367166771033)
                ·
                  refine ⟨11387264667470525375078275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15183019556627367166771033 11387264667470525375078275)
                  ·
                    refine ⟨17080897001205788062617413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11387264667470525375078275 17080897001205788062617413)
                    ·
                      refine ⟨3202668187726085261740765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17080897001205788062617413 3202668187726085261740765)
                      ·
                        rfl

theorem cell23_6237174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6237174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237174 prefixEnd_6237174 := by exact prefixLift 6237174
  have htrace : WordTrace (prefixWord ++ tailWord_6237174) baseStart_6237174 baseEnd_6237174 := by
    simpa [prefixWord, tailWord_6237174, baseEnd_6237174] using wordTrace_append hprefix tailTrace_6237174
  have hstable : (prefixWord ++ tailWord_6237174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237174).length < 2 ^ (prefixWord ++ tailWord_6237174).sum := by decide
  have hdescent : baseEnd_6237174 < baseStart_6237174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237177 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 3]
def baseStart_6237177 : Nat := 118140960795 + 6237177 * 2 ^ 59
def prefixEnd_6237177 : Nat := 4983230072969 + 3 ^ 40 * 6237177 * 2
def baseEnd_6237177 : Nat := 3202669728168048750003251

theorem tailTrace_6237177 : CollatzResearch.WordTrace tailWord_6237177 prefixEnd_6237177 3202669728168048750003251 := by
  unfold tailWord_6237177
  simp only [CollatzResearch.WordTrace]
  refine ⟨227488534124780428869813785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151659022749853619246542523 227488534124780428869813785)
  ·
    refine ⟨170616400593585321652360339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227488534124780428869813785 170616400593585321652360339)
    ·
      refine ⟨255924600890377982478540509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170616400593585321652360339 255924600890377982478540509)
      ·
        refine ⟨95971725333891743429452691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255924600890377982478540509 95971725333891743429452691)
        ·
          refine ⟨143957588000837615144179037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95971725333891743429452691 143957588000837615144179037)
          ·
            refine ⟨53984095500314105679067139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143957588000837615144179037 53984095500314105679067139)
            ·
              refine ⟨80976143250471158518600709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53984095500314105679067139 80976143250471158518600709)
              ·
                refine ⟨15183026859463342222237633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80976143250471158518600709 15183026859463342222237633)
                ·
                  refine ⟨11387270144597506666678225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15183026859463342222237633 11387270144597506666678225)
                  ·
                    refine ⟨8540452608448130000008669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11387270144597506666678225 8540452608448130000008669)
                    ·
                      refine ⟨3202669728168048750003251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540452608448130000008669 3202669728168048750003251)
                      ·
                        rfl

theorem cell23_6237177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_6237177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237177 prefixEnd_6237177 := by exact prefixLift 6237177
  have htrace : WordTrace (prefixWord ++ tailWord_6237177) baseStart_6237177 baseEnd_6237177 := by
    simpa [prefixWord, tailWord_6237177, baseEnd_6237177] using wordTrace_append hprefix tailTrace_6237177
  have hstable : (prefixWord ++ tailWord_6237177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237177).length < 2 ^ (prefixWord ++ tailWord_6237177).sum := by decide
  have hdescent : baseEnd_6237177 < baseStart_6237177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237227 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 1, 5]
def baseStart_6237227 : Nat := 118140960795 + 6237227 * 2 ^ 59
def prefixEnd_6237227 : Nat := 4983230072969 + 3 ^ 40 * 6237227 * 2
def baseEnd_6237227 : Nat := 1067565134066924518126007

theorem tailTrace_6237227 : CollatzResearch.WordTrace tailWord_6237227 prefixEnd_6237227 1067565134066924518126007 := by
  unfold tailWord_6237227
  simp only [CollatzResearch.WordTrace]
  refine ⟨227490357774599287409133935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151660238516399524939422623 227490357774599287409133935)
  ·
    refine ⟨341235536661898931113700903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227490357774599287409133935 341235536661898931113700903)
    ·
      refine ⟨511853304992848396670551355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341235536661898931113700903 511853304992848396670551355)
      ·
        refine ⟨767779957489272595005827033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511853304992848396670551355 767779957489272595005827033)
        ·
          refine ⟨575834968116954446254370275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767779957489272595005827033 575834968116954446254370275)
          ·
            refine ⟨863752452175431669381555413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575834968116954446254370275 863752452175431669381555413)
            ·
              refine ⟨20244198097861679751130205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 863752452175431669381555413 20244198097861679751130205)
              ·
                refine ⟨7591574286698129906673827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20244198097861679751130205 7591574286698129906673827)
                ·
                  refine ⟨11387361430047194860010741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7591574286698129906673827 11387361430047194860010741)
                  ·
                    refine ⟨1067565134066924518126007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11387361430047194860010741 1067565134066924518126007)
                    ·
                      rfl

theorem cell23_6237227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 5].length) (baseStart_6237227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237227 prefixEnd_6237227 := by exact prefixLift 6237227
  have htrace : WordTrace (prefixWord ++ tailWord_6237227) baseStart_6237227 baseEnd_6237227 := by
    simpa [prefixWord, tailWord_6237227, baseEnd_6237227] using wordTrace_append hprefix tailTrace_6237227
  have hstable : (prefixWord ++ tailWord_6237227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237227).length < 2 ^ (prefixWord ++ tailWord_6237227).sum := by decide
  have hdescent : baseEnd_6237227 < baseStart_6237227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237234 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2]
def baseStart_6237234 : Nat := 118140960795 + 6237234 * 2 ^ 59
def prefixEnd_6237234 : Nat := 4983230072969 + 3 ^ 40 * 6237234 * 2
def baseEnd_6237234 : Nat := 3202698996565355026990489

theorem tailTrace_6237234 : CollatzResearch.WordTrace tailWord_6237234 prefixEnd_6237234 3202698996565355026990489 := by
  unfold tailWord_6237234
  simp only [CollatzResearch.WordTrace]
  refine ⟨56872653271393481901159689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151660408723715951736425837 56872653271393481901159689)
  ·
    refine ⟨42654489953545111425869767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56872653271393481901159689 42654489953545111425869767)
    ·
      refine ⟨63981734930317667138804651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42654489953545111425869767 63981734930317667138804651)
      ·
        refine ⟨95972602395476500708206977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63981734930317667138804651 95972602395476500708206977)
        ·
          refine ⟨71979451796607375531155233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95972602395476500708206977 71979451796607375531155233)
          ·
            refine ⟨53984588847455531648366425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71979451796607375531155233 53984588847455531648366425)
            ·
              refine ⟨40488441635591648736274819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53984588847455531648366425 40488441635591648736274819)
              ·
                refine ⟨60732662453387473104412229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40488441635591648736274819 60732662453387473104412229)
                ·
                  refine ⟨11387374210010151207077293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60732662453387473104412229 11387374210010151207077293)
                  ·
                    refine ⟨4270265328753806702653985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11387374210010151207077293 4270265328753806702653985)
                    ·
                      refine ⟨3202698996565355026990489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270265328753806702653985 3202698996565355026990489)
                      ·
                        rfl

theorem cell23_6237234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_6237234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237234 prefixEnd_6237234 := by exact prefixLift 6237234
  have htrace : WordTrace (prefixWord ++ tailWord_6237234) baseStart_6237234 baseEnd_6237234 := by
    simpa [prefixWord, tailWord_6237234, baseEnd_6237234] using wordTrace_append hprefix tailTrace_6237234
  have hstable : (prefixWord ++ tailWord_6237234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237234).length < 2 ^ (prefixWord ++ tailWord_6237234).sum := by decide
  have hdescent : baseEnd_6237234 < baseStart_6237234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237241 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 3]
def baseStart_6237241 : Nat := 118140960795 + 6237241 * 2 ^ 59
def prefixEnd_6237241 : Nat := 4983230072969 + 3 ^ 40 * 6237241 * 2
def baseEnd_6237241 : Nat := 3202702590929936499602957

theorem tailTrace_6237241 : CollatzResearch.WordTrace tailWord_6237241 prefixEnd_6237241 3202702590929936499602957 := by
  unfold tailWord_6237241
  simp only [CollatzResearch.WordTrace]
  refine ⟨227490868396548567800143577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151660578931032378533429051 227490868396548567800143577)
  ·
    refine ⟨170618151297411425850107683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227490868396548567800143577 170618151297411425850107683)
    ·
      refine ⟨255927226946117138775161525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170618151297411425850107683 255927226946117138775161525)
      ·
        refine ⟨23993177526198481760171393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 255927226946117138775161525 23993177526198481760171393)
        ·
          refine ⟨17994883144648861320128545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23993177526198481760171393 17994883144648861320128545)
          ·
            refine ⟨13496162358486645990096409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17994883144648861320128545 13496162358486645990096409)
            ·
              refine ⟨10122121768864984492572307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13496162358486645990096409 10122121768864984492572307)
              ·
                refine ⟨15183182653297476738858461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10122121768864984492572307 15183182653297476738858461)
                ·
                  refine ⟨5693693494986553777071923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15183182653297476738858461 5693693494986553777071923)
                  ·
                    refine ⟨8540540242479830665607885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5693693494986553777071923 8540540242479830665607885)
                    ·
                      refine ⟨3202702590929936499602957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540540242479830665607885 3202702590929936499602957)
                      ·
                        rfl

theorem cell23_6237241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_6237241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237241 prefixEnd_6237241 := by exact prefixLift 6237241
  have htrace : WordTrace (prefixWord ++ tailWord_6237241) baseStart_6237241 baseEnd_6237241 := by
    simpa [prefixWord, tailWord_6237241, baseEnd_6237241] using wordTrace_append hprefix tailTrace_6237241
  have hstable : (prefixWord ++ tailWord_6237241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237241).length < 2 ^ (prefixWord ++ tailWord_6237241).sum := by decide
  have hdescent : baseEnd_6237241 < baseStart_6237241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237261 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_6237261 : Nat := 118140960795 + 6237261 * 2 ^ 59
def prefixEnd_6237261 : Nat := 4983230072969 + 3 ^ 40 * 6237261 * 2
def baseEnd_6237261 : Nat := 1067570953514342140450955

theorem tailTrace_6237261 : CollatzResearch.WordTrace tailWord_6237261 prefixEnd_6237261 1067570953514342140450955 := by
  unfold tailWord_6237261
  simp only [CollatzResearch.WordTrace]
  refine ⟨227491597856476111215871637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151661065237650740810581091 227491597856476111215871637)
  ·
    refine ⟨10663668649522317713243983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 227491597856476111215871637 10663668649522317713243983)
    ·
      refine ⟨15995502974283476569865975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10663668649522317713243983 15995502974283476569865975)
      ·
        refine ⟨23993254461425214854798963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15995502974283476569865975 23993254461425214854798963)
        ·
          refine ⟨35989881692137822282198445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23993254461425214854798963 35989881692137822282198445)
          ·
            refine ⟨13496205634551683355824417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35989881692137822282198445 13496205634551683355824417)
            ·
              refine ⟨10122154225913762516868313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13496205634551683355824417 10122154225913762516868313)
              ·
                refine ⟨7591615669435321887651235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10122154225913762516868313 7591615669435321887651235)
                ·
                  refine ⟨11387423504152982831476853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7591615669435321887651235 11387423504152982831476853)
                  ·
                    refine ⟨1067570953514342140450955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11387423504152982831476853 1067570953514342140450955)
                    ·
                      rfl

theorem cell23_6237261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_6237261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237261 prefixEnd_6237261 := by exact prefixLift 6237261
  have htrace : WordTrace (prefixWord ++ tailWord_6237261) baseStart_6237261 baseEnd_6237261 := by
    simpa [prefixWord, tailWord_6237261, baseEnd_6237261] using wordTrace_append hprefix tailTrace_6237261
  have hstable : (prefixWord ++ tailWord_6237261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237261).length < 2 ^ (prefixWord ++ tailWord_6237261).sum := by decide
  have hdescent : baseEnd_6237261 < baseStart_6237261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237278 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_6237278 : Nat := 118140960795 + 6237278 * 2 ^ 59
def prefixEnd_6237278 : Nat := 4983230072969 + 3 ^ 40 * 6237278 * 2
def baseEnd_6237278 : Nat := 1067573863238050951613429

theorem tailTrace_6237278 : CollatzResearch.WordTrace tailWord_6237278 prefixEnd_6237278 1067573863238050951613429 := by
  unfold tailWord_6237278
  simp only [CollatzResearch.WordTrace]
  refine ⟨28436527237176815389905061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151661478598276348746160325 28436527237176815389905061)
  ·
    refine ⟨5331848856970652885607199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28436527237176815389905061 5331848856970652885607199)
    ·
      refine ⟨7997773285455979328410799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5331848856970652885607199 7997773285455979328410799)
      ·
        refine ⟨11996659928183968992616199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7997773285455979328410799 11996659928183968992616199)
        ·
          refine ⟨17994989892275953488924299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11996659928183968992616199 17994989892275953488924299)
          ·
            refine ⟨26992484838413930233386449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17994989892275953488924299 26992484838413930233386449)
            ·
              refine ⟨20244363628810447675039837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26992484838413930233386449 20244363628810447675039837)
              ·
                refine ⟨7591636360803917878139939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20244363628810447675039837 7591636360803917878139939)
                ·
                  refine ⟨11387454541205876817209909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7591636360803917878139939 11387454541205876817209909)
                  ·
                    refine ⟨1067573863238050951613429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11387454541205876817209909 1067573863238050951613429)
                    ·
                      rfl

theorem cell23_6237278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_6237278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237278 prefixEnd_6237278 := by exact prefixLift 6237278
  have htrace : WordTrace (prefixWord ++ tailWord_6237278) baseStart_6237278 baseEnd_6237278 := by
    simpa [prefixWord, tailWord_6237278, baseEnd_6237278] using wordTrace_append hprefix tailTrace_6237278
  have hstable : (prefixWord ++ tailWord_6237278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237278).length < 2 ^ (prefixWord ++ tailWord_6237278).sum := by decide
  have hdescent : baseEnd_6237278 < baseStart_6237278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237287 : List Nat := [1, 1, 5, 1, 1, 5, 9]
def baseStart_6237287 : Nat := 118140960795 + 6237287 * 2 ^ 59
def prefixEnd_6237287 : Nat := 4983230072969 + 3 ^ 40 * 6237287 * 2
def baseEnd_6237287 : Nat := 39539829765926460736145

theorem tailTrace_6237287 : CollatzResearch.WordTrace tailWord_6237287 prefixEnd_6237287 39539829765926460736145 := by
  unfold tailWord_6237287
  simp only [CollatzResearch.WordTrace]
  refine ⟨227492546154381917656318115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151661697436254611770878743 227492546154381917656318115)
  ·
    refine ⟨341238819231572876484477173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227492546154381917656318115 341238819231572876484477173)
    ·
      refine ⟨31991139302959957170419735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 341238819231572876484477173 31991139302959957170419735)
      ·
        refine ⟨47986708954439935755629603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31991139302959957170419735 47986708954439935755629603)
        ·
          refine ⟨71980063431659903633444405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47986708954439935755629603 71980063431659903633444405)
          ·
            refine ⟨6748130946718115965635413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71980063431659903633444405 6748130946718115965635413)
            ·
              refine ⟨39539829765926460736145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6748130946718115965635413 39539829765926460736145)
              ·
                rfl

theorem cell23_6237287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 9].length) (baseStart_6237287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237287 prefixEnd_6237287 := by exact prefixLift 6237287
  have htrace : WordTrace (prefixWord ++ tailWord_6237287) baseStart_6237287 baseEnd_6237287 := by
    simpa [prefixWord, tailWord_6237287, baseEnd_6237287] using wordTrace_append hprefix tailTrace_6237287
  have hstable : (prefixWord ++ tailWord_6237287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237287).length < 2 ^ (prefixWord ++ tailWord_6237287).sum := by decide
  have hdescent : baseEnd_6237287 < baseStart_6237287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237297 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_6237297 : Nat := 118140960795 + 6237297 * 2 ^ 59
def prefixEnd_6237297 : Nat := 4983230072969 + 3 ^ 40 * 6237297 * 2
def baseEnd_6237297 : Nat := 3202731345846588280502699

theorem tailTrace_6237297 : CollatzResearch.WordTrace tailWord_6237297 prefixEnd_6237297 3202731345846588280502699 := by
  unfold tailWord_6237297
  simp only [CollatzResearch.WordTrace]
  refine ⟨227492910884345689364182145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151661940589563792909454763 227492910884345689364182145)
  ·
    refine ⟨170619683163259267023136609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227492910884345689364182145 170619683163259267023136609)
    ·
      refine ⟨127964762372444450267352457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170619683163259267023136609 127964762372444450267352457)
      ·
        refine ⟨95973571779333337700514343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127964762372444450267352457 95973571779333337700514343)
        ·
          refine ⟨143960357669000006550771515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95973571779333337700514343 143960357669000006550771515)
          ·
            refine ⟨215940536503500009826157273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143960357669000006550771515 215940536503500009826157273)
            ·
              refine ⟨161955402377625007369617955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215940536503500009826157273 161955402377625007369617955)
              ·
                refine ⟨242933103566437511054426933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161955402377625007369617955 242933103566437511054426933)
                ·
                  refine ⟨22774978459353516661352525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 242933103566437511054426933 22774978459353516661352525)
                  ·
                    refine ⟨8540616922257568748007197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22774978459353516661352525 8540616922257568748007197)
                    ·
                      refine ⟨3202731345846588280502699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540616922257568748007197 3202731345846588280502699)
                      ·
                        rfl

theorem cell23_6237297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_6237297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237297 prefixEnd_6237297 := by exact prefixLift 6237297
  have htrace : WordTrace (prefixWord ++ tailWord_6237297) baseStart_6237297 baseEnd_6237297 := by
    simpa [prefixWord, tailWord_6237297, baseEnd_6237297] using wordTrace_append hprefix tailTrace_6237297
  have hstable : (prefixWord ++ tailWord_6237297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237297).length < 2 ^ (prefixWord ++ tailWord_6237297).sum := by decide
  have hdescent : baseEnd_6237297 < baseStart_6237297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237348 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_6237348 : Nat := 118140960795 + 6237348 * 2 ^ 59
def prefixEnd_6237348 : Nat := 4983230072969 + 3 ^ 40 * 6237348 * 2
def baseEnd_6237348 : Nat := 3202757533359967580964965

theorem tailTrace_6237348 : CollatzResearch.WordTrace tailWord_6237348 prefixEnd_6237348 3202757533359967580964965 := by
  unfold tailWord_6237348
  simp only [CollatzResearch.WordTrace]
  refine ⟨113747385503580462537144349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151663180671440616716192465 113747385503580462537144349)
  ·
    refine ⟨42655269563842673451429131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113747385503580462537144349 42655269563842673451429131)
    ·
      refine ⟨63982904345764010177143697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42655269563842673451429131 63982904345764010177143697)
      ·
        refine ⟨47987178259323007632857773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63982904345764010177143697 47987178259323007632857773)
        ·
          refine ⟨17995191847246127862321665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47987178259323007632857773 17995191847246127862321665)
          ·
            refine ⟨13496393885434595896741249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17995191847246127862321665 13496393885434595896741249)
            ·
              refine ⟨10122295414075946922555937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13496393885434595896741249 10122295414075946922555937)
              ·
                refine ⟨7591721560556960191916953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10122295414075946922555937 7591721560556960191916953)
                ·
                  refine ⟨5693791170417720143937715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7591721560556960191916953 5693791170417720143937715)
                  ·
                    refine ⟨8540686755626580215906573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5693791170417720143937715 8540686755626580215906573)
                    ·
                      refine ⟨3202757533359967580964965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540686755626580215906573 3202757533359967580964965)
                      ·
                        rfl

theorem cell23_6237348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_6237348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237348 prefixEnd_6237348 := by exact prefixLift 6237348
  have htrace : WordTrace (prefixWord ++ tailWord_6237348) baseStart_6237348 baseEnd_6237348 := by
    simpa [prefixWord, tailWord_6237348, baseEnd_6237348] using wordTrace_append hprefix tailTrace_6237348
  have hstable : (prefixWord ++ tailWord_6237348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237348).length < 2 ^ (prefixWord ++ tailWord_6237348).sum := by decide
  have hdescent : baseEnd_6237348 < baseStart_6237348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237405 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_6237405 : Nat := 118140960795 + 6237405 * 2 ^ 59
def prefixEnd_6237405 : Nat := 4983230072969 + 3 ^ 40 * 6237405 * 2
def baseEnd_6237405 : Nat := 3202786801757273857952203

theorem tailTrace_6237405 : CollatzResearch.WordTrace tailWord_6237405 prefixEnd_6237405 3202786801757273857952203 := by
  unfold tailWord_6237405
  simp only [CollatzResearch.WordTrace]
  refine ⟨227496849967954423809113669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151664566645302949206075779 227496849967954423809113669)
  ·
    refine ⟨42655659368991454464208813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227496849967954423809113669 42655659368991454464208813)
    ·
      refine ⟨15995872263371795424078305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42655659368991454464208813 15995872263371795424078305)
      ·
        refine ⟨11996904197528846568058729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15995872263371795424078305 11996904197528846568058729)
        ·
          refine ⟨8997678148146634926044047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11996904197528846568058729 8997678148146634926044047)
          ·
            refine ⟨13496517222219952389066071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8997678148146634926044047 13496517222219952389066071)
            ·
              refine ⟨20244775833329928583599107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13496517222219952389066071 20244775833329928583599107)
              ·
                refine ⟨30367163749994892875398661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20244775833329928583599107 30367163749994892875398661)
                ·
                  refine ⟨5693843203124042414137249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30367163749994892875398661 5693843203124042414137249)
                  ·
                    refine ⟨4270382402343031810602937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5693843203124042414137249 4270382402343031810602937)
                    ·
                      refine ⟨3202786801757273857952203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270382402343031810602937 3202786801757273857952203)
                      ·
                        rfl

theorem cell23_6237405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_6237405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237405 prefixEnd_6237405 := by exact prefixLift 6237405
  have htrace : WordTrace (prefixWord ++ tailWord_6237405) baseStart_6237405 baseEnd_6237405 := by
    simpa [prefixWord, tailWord_6237405, baseEnd_6237405] using wordTrace_append hprefix tailTrace_6237405
  have hstable : (prefixWord ++ tailWord_6237405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237405).length < 2 ^ (prefixWord ++ tailWord_6237405).sum := by decide
  have hdescent : baseEnd_6237405 < baseStart_6237405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237421 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_6237421 : Nat := 118140960795 + 6237421 * 2 ^ 59
def prefixEnd_6237421 : Nat := 4983230072969 + 3 ^ 40 * 6237421 * 2
def baseEnd_6237421 : Nat := 3202795017447745795352129

theorem tailTrace_6237421 : CollatzResearch.WordTrace tailWord_6237421 prefixEnd_6237421 3202795017447745795352129 := by
  unfold tailWord_6237421
  simp only [CollatzResearch.WordTrace]
  refine ⟨227497433535896458541696117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151664955690597639027797411 227497433535896458541696117)
  ·
    refine ⟨21327884393990292988284011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227497433535896458541696117 21327884393990292988284011)
    ·
      refine ⟨31991826590985439482426017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21327884393990292988284011 31991826590985439482426017)
      ·
        refine ⟨23993869943239079611819513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31991826590985439482426017 23993869943239079611819513)
        ·
          refine ⟨17995402457429309708864635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23993869943239079611819513 17995402457429309708864635)
          ·
            refine ⟨26993103686143964563296953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17995402457429309708864635 26993103686143964563296953)
            ·
              refine ⟨20244827764607973422472715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26993103686143964563296953 20244827764607973422472715)
              ·
                refine ⟨30367241646911960133709073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20244827764607973422472715 30367241646911960133709073)
                ·
                  refine ⟨22775431235183970100281805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30367241646911960133709073 22775431235183970100281805)
                  ·
                    refine ⟨8540786713193988787605677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22775431235183970100281805 8540786713193988787605677)
                    ·
                      refine ⟨3202795017447745795352129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8540786713193988787605677 3202795017447745795352129)
                      ·
                        rfl

theorem cell23_6237421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_6237421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237421 prefixEnd_6237421 := by exact prefixLift 6237421
  have htrace : WordTrace (prefixWord ++ tailWord_6237421) baseStart_6237421 baseEnd_6237421 := by
    simpa [prefixWord, tailWord_6237421, baseEnd_6237421] using wordTrace_append hprefix tailTrace_6237421
  have hstable : (prefixWord ++ tailWord_6237421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237421).length < 2 ^ (prefixWord ++ tailWord_6237421).sum := by decide
  have hdescent : baseEnd_6237421 < baseStart_6237421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237538 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6237538 : Nat := 118140960795 + 6237538 * 2 ^ 59
def prefixEnd_6237538 : Nat := 4983230072969 + 3 ^ 40 * 6237538 * 2
def baseEnd_6237538 : Nat := 3202855094684321837589091

theorem tailTrace_6237538 : CollatzResearch.WordTrace tailWord_6237538 prefixEnd_6237538 3202855094684321837589091 := by
  unfold tailWord_6237538
  simp only [CollatzResearch.WordTrace]
  refine ⟨56875425219118146880926317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151667800584315058349136845 56875425219118146880926317)
  ·
    refine ⟨21328284457169305080347369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56875425219118146880926317 21328284457169305080347369)
    ·
      refine ⟨15996213342876978810260527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21328284457169305080347369 15996213342876978810260527)
      ·
        refine ⟨23994320014315468215390791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15996213342876978810260527 23994320014315468215390791)
        ·
          refine ⟨35991480021473202323086187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23994320014315468215390791 35991480021473202323086187)
          ·
            refine ⟨53987220032209803484629281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35991480021473202323086187 53987220032209803484629281)
            ·
              refine ⟨40490415024157352613471961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53987220032209803484629281 40490415024157352613471961)
              ·
                refine ⟨30367811268118014460103971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40490415024157352613471961 30367811268118014460103971)
                ·
                  refine ⟨45551716902177021690155957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30367811268118014460103971 45551716902177021690155957)
                  ·
                    refine ⟨4270473459579095783452121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45551716902177021690155957 4270473459579095783452121)
                    ·
                      refine ⟨3202855094684321837589091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270473459579095783452121 3202855094684321837589091)
                      ·
                        rfl

theorem cell23_6237538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6237538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237538 prefixEnd_6237538 := by exact prefixLift 6237538
  have htrace : WordTrace (prefixWord ++ tailWord_6237538) baseStart_6237538 baseEnd_6237538 := by
    simpa [prefixWord, tailWord_6237538, baseEnd_6237538] using wordTrace_append hprefix tailTrace_6237538
  have hstable : (prefixWord ++ tailWord_6237538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237538).length < 2 ^ (prefixWord ++ tailWord_6237538).sum := by decide
  have hdescent : baseEnd_6237538 < baseStart_6237538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237551 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 4]
def baseStart_6237551 : Nat := 118140960795 + 6237551 * 2 ^ 59
def prefixEnd_6237551 : Nat := 4983230072969 + 3 ^ 40 * 6237551 * 2
def baseEnd_6237551 : Nat := 3202861769932830286726531

theorem tailTrace_6237551 : CollatzResearch.WordTrace tailWord_6237551 prefixEnd_6237551 3202861769932830286726531 := by
  unfold tailWord_6237551
  simp only [CollatzResearch.WordTrace]
  refine ⟨227502175025425490743928507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151668116683616993829285671 227502175025425490743928507)
  ·
    refine ⟨341253262538138236115892761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227502175025425490743928507 341253262538138236115892761)
    ·
      refine ⟨255939946903603677086919571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341253262538138236115892761 255939946903603677086919571)
      ·
        refine ⟨383909920355405515630379357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255939946903603677086919571 383909920355405515630379357)
        ·
          refine ⟨143966220133277068361392259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383909920355405515630379357 143966220133277068361392259)
          ·
            refine ⟨215949330199915602542088389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143966220133277068361392259 215949330199915602542088389)
            ·
              refine ⟨40490499412484175476641573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 215949330199915602542088389 40490499412484175476641573)
              ·
                refine ⟨7591968639840782901870295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40490499412484175476641573 7591968639840782901870295)
                ·
                  refine ⟨11387952959761174352805443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7591968639840782901870295 11387952959761174352805443)
                  ·
                    refine ⟨17081929439641761529208165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11387952959761174352805443 17081929439641761529208165)
                    ·
                      refine ⟨3202861769932830286726531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17081929439641761529208165 3202861769932830286726531)
                      ·
                        rfl

theorem cell23_6237551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 4].length) (baseStart_6237551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237551 prefixEnd_6237551 := by exact prefixLift 6237551
  have htrace : WordTrace (prefixWord ++ tailWord_6237551) baseStart_6237551 baseEnd_6237551 := by
    simpa [prefixWord, tailWord_6237551, baseEnd_6237551] using wordTrace_append hprefix tailTrace_6237551
  have hstable : (prefixWord ++ tailWord_6237551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237551).length < 2 ^ (prefixWord ++ tailWord_6237551).sum := by decide
  have hdescent : baseEnd_6237551 < baseStart_6237551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237588 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6237588 : Nat := 118140960795 + 6237588 * 2 ^ 59
def prefixEnd_6237588 : Nat := 4983230072969 + 3 ^ 40 * 6237588 * 2
def baseEnd_6237588 : Nat := 3202880768717046641963861

theorem tailTrace_6237588 : CollatzResearch.WordTrace tailWord_6237588 prefixEnd_6237588 3202880768717046641963861 := by
  unfold tailWord_6237588
  simp only [CollatzResearch.WordTrace]
  refine ⟨113751762263145723031512709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151669016350860964042016945 113751762263145723031512709)
  ·
    refine ⟨21328455424339823068408633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113751762263145723031512709 21328455424339823068408633)
    ·
      refine ⟨15996341568254867301306475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21328455424339823068408633 15996341568254867301306475)
      ·
        refine ⟨23994512352382300951959713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15996341568254867301306475 23994512352382300951959713)
        ·
          refine ⟨17995884264286725713969785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23994512352382300951959713 17995884264286725713969785)
          ·
            refine ⟨13496913198215044285477339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17995884264286725713969785 13496913198215044285477339)
            ·
              refine ⟨20245369797322566428216009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13496913198215044285477339 20245369797322566428216009)
              ·
                refine ⟨15184027347991924821162007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20245369797322566428216009 15184027347991924821162007)
                ·
                  refine ⟨22776041021987887231743011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15184027347991924821162007 22776041021987887231743011)
                  ·
                    refine ⟨34164061532981830847614517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22776041021987887231743011 34164061532981830847614517)
                    ·
                      refine ⟨3202880768717046641963861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34164061532981830847614517 3202880768717046641963861)
                      ·
                        rfl

theorem cell23_6237588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6237588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237588 prefixEnd_6237588 := by exact prefixLift 6237588
  have htrace : WordTrace (prefixWord ++ tailWord_6237588) baseStart_6237588 baseEnd_6237588 := by
    simpa [prefixWord, tailWord_6237588, baseEnd_6237588] using wordTrace_append hprefix tailTrace_6237588
  have hstable : (prefixWord ++ tailWord_6237588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237588).length < 2 ^ (prefixWord ++ tailWord_6237588).sum := by decide
  have hdescent : baseEnd_6237588 < baseStart_6237588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237608 : List Nat := [2, 1, 6, 1, 2, 1, 1, 9]
def baseStart_6237608 : Nat := 118140960795 + 6237608 * 2 ^ 59
def prefixEnd_6237608 : Nat := 4983230072969 + 3 ^ 40 * 6237608 * 2
def baseEnd_6237608 : Nat := 118625594012227280137547

theorem tailTrace_6237608 : CollatzResearch.WordTrace tailWord_6237608 prefixEnd_6237608 118625594012227280137547 := by
  unfold tailWord_6237608
  simp only [CollatzResearch.WordTrace]
  refine ⟨113752126993109494739376739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151669502657479326319168985 113752126993109494739376739)
  ·
    refine ⟨170628190489664242109065109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113752126993109494739376739 170628190489664242109065109)
    ·
      refine ⟨7998196429203011348862427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170628190489664242109065109 7998196429203011348862427)
      ·
        refine ⟨11997294643804517023293641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7998196429203011348862427 11997294643804517023293641)
        ·
          refine ⟨8997970982853387767470231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11997294643804517023293641 8997970982853387767470231)
          ·
            refine ⟨13496956474280081651205347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8997970982853387767470231 13496956474280081651205347)
            ·
              refine ⟨20245434711420122476808021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13496956474280081651205347 20245434711420122476808021)
              ·
                refine ⟨118625594012227280137547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20245434711420122476808021 118625594012227280137547)
                ·
                  rfl

theorem cell23_6237608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 9].length) (baseStart_6237608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237608 prefixEnd_6237608 := by exact prefixLift 6237608
  have htrace : WordTrace (prefixWord ++ tailWord_6237608) baseStart_6237608 baseEnd_6237608 := by
    simpa [prefixWord, tailWord_6237608, baseEnd_6237608] using wordTrace_append hprefix tailTrace_6237608
  have hstable : (prefixWord ++ tailWord_6237608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237608).length < 2 ^ (prefixWord ++ tailWord_6237608).sum := by decide
  have hdescent : baseEnd_6237608 < baseStart_6237608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237636 : List Nat := [2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6237636 : Nat := 118140960795 + 6237636 * 2 ^ 59
def prefixEnd_6237636 : Nat := 4983230072969 + 3 ^ 40 * 6237636 * 2
def baseEnd_6237636 : Nat := 3202905415788462454163641

theorem tailTrace_6237636 : CollatzResearch.WordTrace tailWord_6237636 prefixEnd_6237636 3202905415788462454163641 := by
  unfold tailWord_6237636
  simp only [CollatzResearch.WordTrace]
  refine ⟨113752637615058775130386381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151670183486745033507181841 113752637615058775130386381)
  ·
    refine ⟨42657239105647040673894893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113752637615058775130386381 42657239105647040673894893)
    ·
      refine ⟨15996464664617640252710585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42657239105647040673894893 15996464664617640252710585)
      ·
        refine ⟨11997348498463230189532939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15996464664617640252710585 11997348498463230189532939)
        ·
          refine ⟨17996022747694845284299409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11997348498463230189532939 17996022747694845284299409)
          ·
            refine ⟨13497017060771133963224557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17996022747694845284299409 13497017060771133963224557)
            ·
              refine ⟨5061381397789175236209209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13497017060771133963224557 5061381397789175236209209)
              ·
                refine ⟨3796036048341881427156907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5061381397789175236209209 3796036048341881427156907)
                ·
                  refine ⟨5694054072512822140735361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3796036048341881427156907 5694054072512822140735361)
                  ·
                    refine ⟨4270540554384616605551521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5694054072512822140735361 4270540554384616605551521)
                    ·
                      refine ⟨3202905415788462454163641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270540554384616605551521 3202905415788462454163641)
                      ·
                        rfl

theorem cell23_6237636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6237636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237636 prefixEnd_6237636 := by exact prefixLift 6237636
  have htrace : WordTrace (prefixWord ++ tailWord_6237636) baseStart_6237636 baseEnd_6237636 := by
    simpa [prefixWord, tailWord_6237636, baseEnd_6237636] using wordTrace_append hprefix tailTrace_6237636
  have hstable : (prefixWord ++ tailWord_6237636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237636).length < 2 ^ (prefixWord ++ tailWord_6237636).sum := by decide
  have hdescent : baseEnd_6237636 < baseStart_6237636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237652 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_6237652 : Nat := 118140960795 + 6237652 * 2 ^ 59
def prefixEnd_6237652 : Nat := 4983230072969 + 3 ^ 40 * 6237652 * 2
def baseEnd_6237652 : Nat := 3202913631478934391563567

theorem tailTrace_6237652 : CollatzResearch.WordTrace tailWord_6237652 prefixEnd_6237652 3202913631478934391563567 := by
  unfold tailWord_6237652
  simp only [CollatzResearch.WordTrace]
  refine ⟨113752929399029792496677605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151670572532039723328903473 113752929399029792496677605)
  ·
    refine ⟨21328674262318086093127051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113752929399029792496677605 21328674262318086093127051)
    ·
      refine ⟨31993011393477129139690577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21328674262318086093127051 31993011393477129139690577)
      ·
        refine ⟨23994758545107846854767933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31993011393477129139690577 23994758545107846854767933)
        ·
          refine ⟨8998034454415442570537975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23994758545107846854767933 8998034454415442570537975)
          ·
            refine ⟨13497051681623163855806963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8998034454415442570537975 13497051681623163855806963)
            ·
              refine ⟨20245577522434745783710445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13497051681623163855806963 20245577522434745783710445)
              ·
                refine ⟨7592091570913029668891417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20245577522434745783710445 7592091570913029668891417)
                ·
                  refine ⟨5694068678184772251668563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7592091570913029668891417 5694068678184772251668563)
                  ·
                    refine ⟨8541103017277158377502845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5694068678184772251668563 8541103017277158377502845)
                    ·
                      refine ⟨3202913631478934391563567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8541103017277158377502845 3202913631478934391563567)
                      ·
                        rfl

theorem cell23_6237652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_6237652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237652 prefixEnd_6237652 := by exact prefixLift 6237652
  have htrace : WordTrace (prefixWord ++ tailWord_6237652) baseStart_6237652 baseEnd_6237652 := by
    simpa [prefixWord, tailWord_6237652, baseEnd_6237652] using wordTrace_append hprefix tailTrace_6237652
  have hstable : (prefixWord ++ tailWord_6237652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237652).length < 2 ^ (prefixWord ++ tailWord_6237652).sum := by decide
  have hdescent : baseEnd_6237652 < baseStart_6237652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237691 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 3]
def baseStart_6237691 : Nat := 118140960795 + 6237691 * 2 ^ 59
def prefixEnd_6237691 : Nat := 4983230072969 + 3 ^ 40 * 6237691 * 2
def baseEnd_6237691 : Nat := 3202933657224459738975887

theorem tailTrace_6237691 : CollatzResearch.WordTrace tailWord_6237691 prefixEnd_6237691 3202933657224459738975887 := by
  unfold tailWord_6237691
  simp only [CollatzResearch.WordTrace]
  refine ⟨227507281244918294654024927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151671520829945529769349951 227507281244918294654024927)
  ·
    refine ⟨341260921867377441981037391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227507281244918294654024927 341260921867377441981037391)
    ·
      refine ⟨511891382801066162971556087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341260921867377441981037391 511891382801066162971556087)
      ·
        refine ⟨767837074201599244457334131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511891382801066162971556087 767837074201599244457334131)
        ·
          refine ⟨1151755611302398866686001197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767837074201599244457334131 1151755611302398866686001197)
          ·
            refine ⟨431908354238399575007250449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1151755611302398866686001197 431908354238399575007250449)
            ·
              refine ⟨323931265678799681255437837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431908354238399575007250449 323931265678799681255437837)
              ·
                refine ⟨121474224629549880470789189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 323931265678799681255437837 121474224629549880470789189)
                ·
                  refine ⟨22776417118040602588272973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121474224629549880470789189 22776417118040602588272973)
                  ·
                    refine ⟨8541156419265225970602365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22776417118040602588272973 8541156419265225970602365)
                    ·
                      refine ⟨3202933657224459738975887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8541156419265225970602365 3202933657224459738975887)
                      ·
                        rfl

theorem cell23_6237691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 3].length) (baseStart_6237691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237691 prefixEnd_6237691 := by exact prefixLift 6237691
  have htrace : WordTrace (prefixWord ++ tailWord_6237691) baseStart_6237691 baseEnd_6237691 := by
    simpa [prefixWord, tailWord_6237691, baseEnd_6237691] using wordTrace_append hprefix tailTrace_6237691
  have hstable : (prefixWord ++ tailWord_6237691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237691).length < 2 ^ (prefixWord ++ tailWord_6237691).sum := by decide
  have hdescent : baseEnd_6237691 < baseStart_6237691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237728 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 1, 7]
def baseStart_6237728 : Nat := 118140960795 + 6237728 * 2 ^ 59
def prefixEnd_6237728 : Nat := 4983230072969 + 3 ^ 40 * 6237728 * 2
def baseEnd_6237728 : Nat := 1067650885336225364737739

theorem tailTrace_6237728 : CollatzResearch.WordTrace tailWord_6237728 prefixEnd_6237728 1067650885336225364737739 := by
  unfold tailWord_6237728
  simp only [CollatzResearch.WordTrace]
  refine ⟨113754315372892124986560919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151672420497189499982081225 113754315372892124986560919)
  ·
    refine ⟨170631473059338187479841379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113754315372892124986560919 170631473059338187479841379)
    ·
      refine ⟨255947209589007281219762069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170631473059338187479841379 255947209589007281219762069)
      ·
        refine ⟨11997525449484716307176347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 255947209589007281219762069 11997525449484716307176347)
        ·
          refine ⟨17996288174227074460764521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11997525449484716307176347 17996288174227074460764521)
          ·
            refine ⟨13497216130670305845573391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17996288174227074460764521 13497216130670305845573391)
            ·
              refine ⟨20245824196005458768360087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13497216130670305845573391 20245824196005458768360087)
              ·
                refine ⟨30368736294008188152540131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20245824196005458768360087 30368736294008188152540131)
                ·
                  refine ⟨45553104441012282228810197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30368736294008188152540131 45553104441012282228810197)
                  ·
                    refine ⟨1067650885336225364737739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45553104441012282228810197 1067650885336225364737739)
                    ·
                      rfl

theorem cell23_6237728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_6237728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237728 prefixEnd_6237728 := by exact prefixLift 6237728
  have htrace : WordTrace (prefixWord ++ tailWord_6237728) baseStart_6237728 baseEnd_6237728 := by
    simpa [prefixWord, tailWord_6237728, baseEnd_6237728] using wordTrace_append hprefix tailTrace_6237728
  have hstable : (prefixWord ++ tailWord_6237728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237728).length < 2 ^ (prefixWord ++ tailWord_6237728).sum := by decide
  have hdescent : baseEnd_6237728 < baseStart_6237728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237788 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 8]
def baseStart_6237788 : Nat := 118140960795 + 6237788 * 2 ^ 59
def prefixEnd_6237788 : Nat := 4983230072969 + 3 ^ 40 * 6237788 * 2
def baseEnd_6237788 : Nat := 355887051649771762162549

theorem tailTrace_6237788 : CollatzResearch.WordTrace tailWord_6237788 prefixEnd_6237788 355887051649771762162549 := by
  unfold tailWord_6237788
  simp only [CollatzResearch.WordTrace]
  refine ⟨113755409562783440110153009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151673879417044586813537345 113755409562783440110153009)
  ·
    refine ⟨85316557172087580082614757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113755409562783440110153009 85316557172087580082614757)
    ·
      refine ⟨15996854469766421265490267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85316557172087580082614757 15996854469766421265490267)
      ·
        refine ⟨23995281704649631898235401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15996854469766421265490267 23995281704649631898235401)
        ·
          refine ⟨17996461278487223923676551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23995281704649631898235401 17996461278487223923676551)
          ·
            refine ⟨26994691917730835885514827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17996461278487223923676551 26994691917730835885514827)
            ·
              refine ⟨40492037876596253828272241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26994691917730835885514827 40492037876596253828272241)
              ·
                refine ⟨30369028407447190371204181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40492037876596253828272241 30369028407447190371204181)
                ·
                  refine ⟨355887051649771762162549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30369028407447190371204181 355887051649771762162549)
                  ·
                    rfl

theorem cell23_6237788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_6237788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237788 prefixEnd_6237788 := by exact prefixLift 6237788
  have htrace : WordTrace (prefixWord ++ tailWord_6237788) baseStart_6237788 baseEnd_6237788 := by
    simpa [prefixWord, tailWord_6237788, baseEnd_6237788] using wordTrace_append hprefix tailTrace_6237788
  have hstable : (prefixWord ++ tailWord_6237788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237788).length < 2 ^ (prefixWord ++ tailWord_6237788).sum := by decide
  have hdescent : baseEnd_6237788 < baseStart_6237788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237848 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 3, 6]
def baseStart_6237848 : Nat := 118140960795 + 6237848 * 2 ^ 59
def prefixEnd_6237848 : Nat := 4983230072969 + 3 ^ 40 * 6237848 * 2
def baseEnd_6237848 : Nat := 1067671424562405208237555

theorem tailTrace_6237848 : CollatzResearch.WordTrace tailWord_6237848 prefixEnd_6237848 1067671424562405208237555 := by
  unfold tailWord_6237848
  simp only [CollatzResearch.WordTrace]
  refine ⟨113756503752674755233745099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151675338336899673644993465 113756503752674755233745099)
  ·
    refine ⟨170634755629012132850617649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113756503752674755233745099 170634755629012132850617649)
    ·
      refine ⟨127976066721759099637963237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170634755629012132850617649 127976066721759099637963237)
      ·
        refine ⟨23995512510329831182118107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127976066721759099637963237 23995512510329831182118107)
        ·
          refine ⟨35993268765494746773177161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23995512510329831182118107 35993268765494746773177161)
          ·
            refine ⟨26994951574121060079882871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35993268765494746773177161 26994951574121060079882871)
            ·
              refine ⟨40492427361181590119824307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26994951574121060079882871 40492427361181590119824307)
              ·
                refine ⟨60738641041772385179736461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40492427361181590119824307 60738641041772385179736461)
                ·
                  refine ⟨22776990390664644442401173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60738641041772385179736461 22776990390664644442401173)
                  ·
                    refine ⟨1067671424562405208237555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22776990390664644442401173 1067671424562405208237555)
                    ·
                      rfl

theorem cell23_6237848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_6237848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237848 prefixEnd_6237848 := by exact prefixLift 6237848
  have htrace : WordTrace (prefixWord ++ tailWord_6237848) baseStart_6237848 baseEnd_6237848 := by
    simpa [prefixWord, tailWord_6237848, baseEnd_6237848] using wordTrace_append hprefix tailTrace_6237848
  have hstable : (prefixWord ++ tailWord_6237848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237848).length < 2 ^ (prefixWord ++ tailWord_6237848).sum := by decide
  have hdescent : baseEnd_6237848 < baseStart_6237848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237885 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_6237885 : Nat := 118140960795 + 6237885 * 2 ^ 59
def prefixEnd_6237885 : Nat := 4983230072969 + 3 ^ 40 * 6237885 * 2
def baseEnd_6237885 : Nat := 3203033272471431979949995

theorem tailTrace_6237885 : CollatzResearch.WordTrace tailWord_6237885 prefixEnd_6237885 3203033272471431979949995 := by
  unfold tailWord_6237885
  simp only [CollatzResearch.WordTrace]
  refine ⟨227514357006215465786587109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151676238004143643857724739 227514357006215465786587109)
  ·
    refine ⟨42658941938665399834985083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227514357006215465786587109 42658941938665399834985083)
    ·
      refine ⟨63988412907998099752477625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42658941938665399834985083 63988412907998099752477625)
      ·
        refine ⟨47991309680998574814358219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63988412907998099752477625 47991309680998574814358219)
        ·
          refine ⟨71986964521497862221537329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47991309680998574814358219 71986964521497862221537329)
          ·
            refine ⟨53990223391123396666152997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71986964521497862221537329 53990223391123396666152997)
            ·
              refine ⟨10123166885835636874903687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53990223391123396666152997 10123166885835636874903687)
              ·
                refine ⟨15184750328753455312355531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10123166885835636874903687 15184750328753455312355531)
                ·
                  refine ⟨22777125493130182968533297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15184750328753455312355531 22777125493130182968533297)
                  ·
                    refine ⟨17082844119847637226399973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22777125493130182968533297 17082844119847637226399973)
                    ·
                      refine ⟨3203033272471431979949995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17082844119847637226399973 3203033272471431979949995)
                      ·
                        rfl

theorem cell23_6237885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_6237885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237885 prefixEnd_6237885 := by exact prefixLift 6237885
  have htrace : WordTrace (prefixWord ++ tailWord_6237885) baseStart_6237885 baseEnd_6237885 := by
    simpa [prefixWord, tailWord_6237885, baseEnd_6237885] using wordTrace_append hprefix tailTrace_6237885
  have hstable : (prefixWord ++ tailWord_6237885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237885).length < 2 ^ (prefixWord ++ tailWord_6237885).sum := by decide
  have hdescent : baseEnd_6237885 < baseStart_6237885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237892 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_6237892 : Nat := 118140960795 + 6237892 * 2 ^ 59
def prefixEnd_6237892 : Nat := 4983230072969 + 3 ^ 40 * 6237892 * 2
def baseEnd_6237892 : Nat := 3203036866836013452562463

theorem tailTrace_6237892 : CollatzResearch.WordTrace tailWord_6237892 prefixEnd_6237892 3203036866836013452562463 := by
  unfold tailWord_6237892
  simp only [CollatzResearch.WordTrace]
  refine ⟨113757306158595052991045965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151676408211460070654727953 113757306158595052991045965)
  ·
    refine ⟨42658989809473144871642237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113757306158595052991045965 42658989809473144871642237)
    ·
      refine ⟨15997121178552429326865839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42658989809473144871642237 15997121178552429326865839)
      ·
        refine ⟨23995681767828643990298759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15997121178552429326865839 23995681767828643990298759)
        ·
          refine ⟨35993522651742965985448139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23995681767828643990298759 35993522651742965985448139)
          ·
            refine ⟨53990283977614448978172209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35993522651742965985448139 53990283977614448978172209)
            ·
              refine ⟨40492712983210836733629157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53990283977614448978172209 40492712983210836733629157)
              ·
                refine ⟨7592383684352031887555467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40492712983210836733629157 7592383684352031887555467)
                ·
                  refine ⟨11388575526528047831333201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7592383684352031887555467 11388575526528047831333201)
                  ·
                    refine ⟨8541431644896035873499901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11388575526528047831333201 8541431644896035873499901)
                    ·
                      refine ⟨3203036866836013452562463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8541431644896035873499901 3203036866836013452562463)
                      ·
                        rfl

theorem cell23_6237892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_6237892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237892 prefixEnd_6237892 := by exact prefixLift 6237892
  have htrace : WordTrace (prefixWord ++ tailWord_6237892) baseStart_6237892 baseEnd_6237892 := by
    simpa [prefixWord, tailWord_6237892, baseEnd_6237892] using wordTrace_append hprefix tailTrace_6237892
  have hstable : (prefixWord ++ tailWord_6237892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237892).length < 2 ^ (prefixWord ++ tailWord_6237892).sum := by decide
  have hdescent : baseEnd_6237892 < baseStart_6237892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237905 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_6237905 : Nat := 118140960795 + 6237905 * 2 ^ 59
def prefixEnd_6237905 : Nat := 4983230072969 + 3 ^ 40 * 6237905 * 2
def baseEnd_6237905 : Nat := 3203043542084521901699903

theorem tailTrace_6237905 : CollatzResearch.WordTrace tailWord_6237905 prefixEnd_6237905 3203043542084521901699903 := by
  unfold tailWord_6237905
  simp only [CollatzResearch.WordTrace]
  refine ⟨227515086466143009202315169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151676724310762006134876779 227515086466143009202315169)
  ·
    refine ⟨170636314849607256901736377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227515086466143009202315169 170636314849607256901736377)
    ·
      refine ⟨127977236137205442676302283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170636314849607256901736377 127977236137205442676302283)
      ·
        refine ⟨191965854205808164014453425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127977236137205442676302283 191965854205808164014453425)
        ·
          refine ⟨143974390654356123010840069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191965854205808164014453425 143974390654356123010840069)
          ·
            refine ⟨26995198247691773064532513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143974390654356123010840069 26995198247691773064532513)
            ·
              refine ⟨20246398685768829798399385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26995198247691773064532513 20246398685768829798399385)
              ·
                refine ⟨15184799014326622348799539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20246398685768829798399385 15184799014326622348799539)
                ·
                  refine ⟨22777198521489933523199309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15184799014326622348799539 22777198521489933523199309)
                  ·
                    refine ⟨8541449445558725071199741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22777198521489933523199309 8541449445558725071199741)
                    ·
                      refine ⟨3203043542084521901699903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8541449445558725071199741 3203043542084521901699903)
                      ·
                        rfl

theorem cell23_6237905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_6237905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237905 prefixEnd_6237905 := by exact prefixLift 6237905
  have htrace : WordTrace (prefixWord ++ tailWord_6237905) baseStart_6237905 baseEnd_6237905 := by
    simpa [prefixWord, tailWord_6237905, baseEnd_6237905] using wordTrace_append hprefix tailTrace_6237905
  have hstable : (prefixWord ++ tailWord_6237905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237905).length < 2 ^ (prefixWord ++ tailWord_6237905).sum := by decide
  have hdescent : baseEnd_6237905 < baseStart_6237905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237906 : List Nat := [3, 2, 2, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_6237906 : Nat := 118140960795 + 6237906 * 2 ^ 59
def prefixEnd_6237906 : Nat := 4983230072969 + 3 ^ 40 * 6237906 * 2
def baseEnd_6237906 : Nat := 3203044055565176397787399

theorem tailTrace_6237906 : CollatzResearch.WordTrace tailWord_6237906 prefixEnd_6237906 3203044055565176397787399 := by
  unfold tailWord_6237906
  simp only [CollatzResearch.WordTrace]
  refine ⟨56878780734784846593275393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151676748626092924248734381 56878780734784846593275393)
  ·
    refine ⟨42659085551088634944956545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56878780734784846593275393 42659085551088634944956545)
    ·
      refine ⟨31994314163316476208717409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42659085551088634944956545 31994314163316476208717409)
      ·
        refine ⟨23995735622487357156538057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31994314163316476208717409 23995735622487357156538057)
        ·
          refine ⟨17996801716865517867403543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23995735622487357156538057 17996801716865517867403543)
          ·
            refine ⟨26995202575298276801105315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17996801716865517867403543 26995202575298276801105315)
            ·
              refine ⟨40492803862947415201657973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26995202575298276801105315 40492803862947415201657973)
              ·
                refine ⟨3796200362151320175155435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40492803862947415201657973 3796200362151320175155435)
                ·
                  refine ⟨5694300543226980262733153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3796200362151320175155435 5694300543226980262733153)
                  ·
                    refine ⟨4270725407420235197049865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5694300543226980262733153 4270725407420235197049865)
                    ·
                      refine ⟨3203044055565176397787399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270725407420235197049865 3203044055565176397787399)
                      ·
                        rfl

theorem cell23_6237906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_6237906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237906 prefixEnd_6237906 := by exact prefixLift 6237906
  have htrace : WordTrace (prefixWord ++ tailWord_6237906) baseStart_6237906 baseEnd_6237906 := by
    simpa [prefixWord, tailWord_6237906, baseEnd_6237906] using wordTrace_append hprefix tailTrace_6237906
  have hstable : (prefixWord ++ tailWord_6237906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237906).length < 2 ^ (prefixWord ++ tailWord_6237906).sum := by decide
  have hdescent : baseEnd_6237906 < baseStart_6237906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237916 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6237916 : Nat := 118140960795 + 6237916 * 2 ^ 59
def prefixEnd_6237916 : Nat := 4983230072969 + 3 ^ 40 * 6237916 * 2
def baseEnd_6237916 : Nat := 1067683063457240452887451

theorem tailTrace_6237916 : CollatzResearch.WordTrace tailWord_6237916 prefixEnd_6237916 1067683063457240452887451 := by
  unfold tailWord_6237916
  simp only [CollatzResearch.WordTrace]
  refine ⟨113757743834551579040482801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151676991779402105387310401 113757743834551579040482801)
  ·
    refine ⟨85318307875913684280362101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113757743834551579040482801 85318307875913684280362101)
    ·
      refine ⟨7998591363366907901283947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85318307875913684280362101 7998591363366907901283947)
      ·
        refine ⟨11997887045050361851925921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7998591363366907901283947 11997887045050361851925921)
        ·
          refine ⟨8998415283787771388944441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11997887045050361851925921 8998415283787771388944441)
          ·
            refine ⟨6748811462840828541708331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8998415283787771388944441 6748811462840828541708331)
            ·
              refine ⟨10123217194261242812562497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6748811462840828541708331 10123217194261242812562497)
              ·
                refine ⟨7592412895695932109421873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10123217194261242812562497 7592412895695932109421873)
                ·
                  refine ⟨5694309671771949082066405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7592412895695932109421873 5694309671771949082066405)
                  ·
                    refine ⟨1067683063457240452887451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5694309671771949082066405 1067683063457240452887451)
                    ·
                      rfl

theorem cell23_6237916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6237916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237916 prefixEnd_6237916 := by exact prefixLift 6237916
  have htrace : WordTrace (prefixWord ++ tailWord_6237916) baseStart_6237916 baseEnd_6237916 := by
    simpa [prefixWord, tailWord_6237916, baseEnd_6237916] using wordTrace_append hprefix tailTrace_6237916
  have hstable : (prefixWord ++ tailWord_6237916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237916).length < 2 ^ (prefixWord ++ tailWord_6237916).sum := by decide
  have hdescent : baseEnd_6237916 < baseStart_6237916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237985 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 7]
def baseStart_6237985 : Nat := 118140960795 + 6237985 * 2 ^ 59
def prefixEnd_6237985 : Nat := 4983230072969 + 3 ^ 40 * 6237985 * 2
def baseEnd_6237985 : Nat := 355898291170764620966615

theorem tailTrace_6237985 : CollatzResearch.WordTrace tailWord_6237985 prefixEnd_6237985 355898291170764620966615 := by
  unfold tailWord_6237985
  simp only [CollatzResearch.WordTrace]
  refine ⟨227518004305853182865227409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151678669537235455243484939 227518004305853182865227409)
  ·
    refine ⟨170638503229389887148920557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227518004305853182865227409 170638503229389887148920557)
    ·
      refine ⟨63989438711021207680845209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170638503229389887148920557 63989438711021207680845209)
      ·
        refine ⟨47992079033265905760633907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63989438711021207680845209 47992079033265905760633907)
        ·
          refine ⟨71988118549898858640950861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47992079033265905760633907 71988118549898858640950861)
          ·
            refine ⟨26995544456212071990356573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71988118549898858640950861 26995544456212071990356573)
            ·
              refine ⟨10123329171079526996383715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26995544456212071990356573 10123329171079526996383715)
              ·
                refine ⟨15184993756619290494575573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10123329171079526996383715 15184993756619290494575573)
                ·
                  refine ⟨355898291170764620966615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15184993756619290494575573 355898291170764620966615)
                  ·
                    rfl

theorem cell23_6237985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 7].length) (baseStart_6237985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237985 prefixEnd_6237985 := by exact prefixLift 6237985
  have htrace : WordTrace (prefixWord ++ tailWord_6237985) baseStart_6237985 baseEnd_6237985 := by
    simpa [prefixWord, tailWord_6237985, baseEnd_6237985] using wordTrace_append hprefix tailTrace_6237985
  have hstable : (prefixWord ++ tailWord_6237985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237985).length < 2 ^ (prefixWord ++ tailWord_6237985).sum := by decide
  have hdescent : baseEnd_6237985 < baseStart_6237985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6237996 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 2, 2, 2]
def baseStart_6237996 : Nat := 118140960795 + 6237996 * 2 ^ 59
def prefixEnd_6237996 : Nat := 4983230072969 + 3 ^ 40 * 6237996 * 2
def baseEnd_6237996 : Nat := 3203090268824081045661985

theorem tailTrace_6237996 : CollatzResearch.WordTrace tailWord_6237996 prefixEnd_6237996 3203090268824081045661985 := by
  unfold tailWord_6237996
  simp only [CollatzResearch.WordTrace]
  refine ⟨113759202754406665871938921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151678937005875554495918561 113759202754406665871938921)
  ·
    refine ⟨85319402065804999403954191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113759202754406665871938921 85319402065804999403954191)
    ·
      refine ⟨127979103098707499105931287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85319402065804999403954191 127979103098707499105931287)
      ·
        refine ⟨191968654648061248658896931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127979103098707499105931287 191968654648061248658896931)
        ·
          refine ⟨287952981972091872988345397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191968654648061248658896931 287952981972091872988345397)
          ·
            refine ⟨26995592059883613092657381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 287952981972091872988345397 26995592059883613092657381)
            ·
              refine ⟨5061673511228177454873259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26995592059883613092657381 5061673511228177454873259)
              ·
                refine ⟨7592510266842266182309889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061673511228177454873259 7592510266842266182309889)
                ·
                  refine ⟨5694382700131699636732417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7592510266842266182309889 5694382700131699636732417)
                  ·
                    refine ⟨4270787025098774727549313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5694382700131699636732417 4270787025098774727549313)
                    ·
                      refine ⟨3203090268824081045661985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270787025098774727549313 3203090268824081045661985)
                      ·
                        rfl

theorem cell23_6237996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_6237996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6237996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6237996 prefixEnd_6237996 := by exact prefixLift 6237996
  have htrace : WordTrace (prefixWord ++ tailWord_6237996) baseStart_6237996 baseEnd_6237996 := by
    simpa [prefixWord, tailWord_6237996, baseEnd_6237996] using wordTrace_append hprefix tailTrace_6237996
  have hstable : (prefixWord ++ tailWord_6237996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6237996).length < 2 ^ (prefixWord ++ tailWord_6237996).sum := by decide
  have hdescent : baseEnd_6237996 < baseStart_6237996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6237996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238036 : List Nat := [2, 4, 1, 1, 3, 3, 2, 2, 5]
def baseStart_6238036 : Nat := 118140960795 + 6238036 * 2 ^ 59
def prefixEnd_6238036 : Nat := 4983230072969 + 3 ^ 40 * 6238036 * 2
def baseEnd_6238036 : Nat := 355901200894473432129089

theorem tailTrace_6238036 : CollatzResearch.WordTrace tailWord_6238036 prefixEnd_6238036 355901200894473432129089 := by
  unfold tailWord_6238036
  simp only [CollatzResearch.WordTrace]
  refine ⟨113759932214334209287666981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151679909619112279050222641 113759932214334209287666981)
  ·
    refine ⟨21329987290187664241437559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113759932214334209287666981 21329987290187664241437559)
    ·
      refine ⟨31994980935281496362156339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21329987290187664241437559 31994980935281496362156339)
      ·
        refine ⟨47992471402922244543234509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31994980935281496362156339 47992471402922244543234509)
        ·
          refine ⟨17997176776095841703712941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47992471402922244543234509 17997176776095841703712941)
          ·
            refine ⟨6748941291035940638892353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17997176776095841703712941 6748941291035940638892353)
            ·
              refine ⟨5061705968276955479169265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6748941291035940638892353 5061705968276955479169265)
              ·
                refine ⟨3796279476207716609376949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5061705968276955479169265 3796279476207716609376949)
                ·
                  refine ⟨355901200894473432129089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3796279476207716609376949 355901200894473432129089)
                  ·
                    rfl

theorem cell23_6238036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_6238036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238036 prefixEnd_6238036 := by exact prefixLift 6238036
  have htrace : WordTrace (prefixWord ++ tailWord_6238036) baseStart_6238036 baseEnd_6238036 := by
    simpa [prefixWord, tailWord_6238036, baseEnd_6238036] using wordTrace_append hprefix tailTrace_6238036
  have hstable : (prefixWord ++ tailWord_6238036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238036).length < 2 ^ (prefixWord ++ tailWord_6238036).sum := by decide
  have hdescent : baseEnd_6238036 < baseStart_6238036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238105 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 5, 5]
def baseStart_6238105 : Nat := 118140960795 + 6238105 * 2 ^ 59
def prefixEnd_6238105 : Nat := 4983230072969 + 3 ^ 40 * 6238105 * 2
def baseEnd_6238105 : Nat := 1067715412738473706399661

theorem tailTrace_6238105 : CollatzResearch.WordTrace tailWord_6238105 prefixEnd_6238105 1067715412738473706399661 := by
  unfold tailWord_6238105
  simp only [CollatzResearch.WordTrace]
  refine ⟨227522381065418443359595769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151681587376945628906397179 227522381065418443359595769)
  ·
    refine ⟨170641785799063832519696827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227522381065418443359595769 170641785799063832519696827)
    ·
      refine ⟨255962678698595748779545241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170641785799063832519696827 255962678698595748779545241)
      ·
        refine ⟨191972009023946811584658931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255962678698595748779545241 191972009023946811584658931)
        ·
          refine ⟨287958013535920217376988397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191972009023946811584658931 287958013535920217376988397)
          ·
            refine ⟨107984255075970081516370649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287958013535920217376988397 107984255075970081516370649)
            ·
              refine ⟨80988191306977561137277987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107984255075970081516370649 80988191306977561137277987)
              ·
                refine ⟨121482286960466341705916981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80988191306977561137277987 121482286960466341705916981)
                ·
                  refine ⟨11388964402543719534929717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121482286960466341705916981 11388964402543719534929717)
                  ·
                    refine ⟨1067715412738473706399661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11388964402543719534929717 1067715412738473706399661)
                    ·
                      rfl

theorem cell23_6238105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_6238105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238105 prefixEnd_6238105 := by exact prefixLift 6238105
  have htrace : WordTrace (prefixWord ++ tailWord_6238105) baseStart_6238105 baseEnd_6238105 := by
    simpa [prefixWord, tailWord_6238105, baseEnd_6238105] using wordTrace_append hprefix tailTrace_6238105
  have hstable : (prefixWord ++ tailWord_6238105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238105).length < 2 ^ (prefixWord ++ tailWord_6238105).sum := by decide
  have hdescent : baseEnd_6238105 < baseStart_6238105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238109 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 6]
def baseStart_6238109 : Nat := 118140960795 + 6238109 * 2 ^ 59
def prefixEnd_6238109 : Nat := 4983230072969 + 3 ^ 40 * 6238109 * 2
def baseEnd_6238109 : Nat := 355905365793115455949885

theorem tailTrace_6238109 : CollatzResearch.WordTrace tailWord_6238109 prefixEnd_6238109 355905365793115455949885 := by
  unfold tailWord_6238109
  simp only [CollatzResearch.WordTrace]
  refine ⟨227522526957403952042741381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151681684638269301361827587 227522526957403952042741381)
  ·
    refine ⟨42660473804513241008014009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227522526957403952042741381 42660473804513241008014009)
    ·
      refine ⟨31995355353384930756010507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42660473804513241008014009 31995355353384930756010507)
      ·
        refine ⟨47993033030077396134015761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31995355353384930756010507 47993033030077396134015761)
        ·
          refine ⟨35994774772558047100511821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47993033030077396134015761 35994774772558047100511821)
          ·
            refine ⟨13498040539709267662691933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35994774772558047100511821 13498040539709267662691933)
            ·
              refine ⟨5061765202390975373509475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13498040539709267662691933 5061765202390975373509475)
              ·
                refine ⟨7592647803586463060264213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061765202390975373509475 7592647803586463060264213)
                ·
                  refine ⟨355905365793115455949885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7592647803586463060264213 355905365793115455949885)
                  ·
                    rfl

theorem cell23_6238109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_6238109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238109 prefixEnd_6238109 := by exact prefixLift 6238109
  have htrace : WordTrace (prefixWord ++ tailWord_6238109) baseStart_6238109 baseEnd_6238109 := by
    simpa [prefixWord, tailWord_6238109, baseEnd_6238109] using wordTrace_append hprefix tailTrace_6238109
  have hstable : (prefixWord ++ tailWord_6238109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238109).length < 2 ^ (prefixWord ++ tailWord_6238109).sum := by decide
  have hdescent : baseEnd_6238109 < baseStart_6238109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238129 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 1, 5, 2]
def baseStart_6238129 : Nat := 118140960795 + 6238129 * 2 ^ 59
def prefixEnd_6238129 : Nat := 4983230072969 + 3 ^ 40 * 6238129 * 2
def baseEnd_6238129 : Nat := 3203158561751129025298873

theorem tailTrace_6238129 : CollatzResearch.WordTrace tailWord_6238129 prefixEnd_6238129 3203158561751129025298873 := by
  unfold tailWord_6238129
  simp only [CollatzResearch.WordTrace]
  refine ⟨227523256417331495458469441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151682170944887663638979627 227523256417331495458469441)
  ·
    refine ⟨170642442312998621593852081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227523256417331495458469441 170642442312998621593852081)
    ·
      refine ⟨127981831734748966195389061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170642442312998621593852081 127981831734748966195389061)
      ·
        refine ⟨23996593450265431161635449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127981831734748966195389061 23996593450265431161635449)
        ·
          refine ⟨17997445087699073371226587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23996593450265431161635449 17997445087699073371226587)
          ·
            refine ⟨26996167631548610056839881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17997445087699073371226587 26996167631548610056839881)
            ·
              refine ⟨20247125723661457542629911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26996167631548610056839881 20247125723661457542629911)
              ·
                refine ⟨30370688585492186313944867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20247125723661457542629911 30370688585492186313944867)
                ·
                  refine ⟨45556032878238279470917301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30370688585492186313944867 45556032878238279470917301)
                  ·
                    refine ⟨4270878082334838700398497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45556032878238279470917301 4270878082334838700398497)
                    ·
                      refine ⟨3203158561751129025298873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270878082334838700398497 3203158561751129025298873)
                      ·
                        rfl

theorem cell23_6238129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_6238129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238129 prefixEnd_6238129 := by exact prefixLift 6238129
  have htrace : WordTrace (prefixWord ++ tailWord_6238129) baseStart_6238129 baseEnd_6238129 := by
    simpa [prefixWord, tailWord_6238129, baseEnd_6238129] using wordTrace_append hprefix tailTrace_6238129
  have hstable : (prefixWord ++ tailWord_6238129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238129).length < 2 ^ (prefixWord ++ tailWord_6238129).sum := by decide
  have hdescent : baseEnd_6238129 < baseStart_6238129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238135 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 3, 6]
def baseStart_6238135 : Nat := 118140960795 + 6238135 * 2 ^ 59
def prefixEnd_6238135 : Nat := 4983230072969 + 3 ^ 40 * 6238135 * 2
def baseEnd_6238135 : Nat := 1067720547545018667274615

theorem tailTrace_6238135 : CollatzResearch.WordTrace tailWord_6238135 prefixEnd_6238135 1067720547545018667274615 := by
  unfold tailWord_6238135
  simp only [CollatzResearch.WordTrace]
  refine ⟨227523475255309758483187859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151682316836873172322125239 227523475255309758483187859)
  ·
    refine ⟨341285212882964637724781789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227523475255309758483187859 341285212882964637724781789)
    ·
      refine ⟨127981954831111739146793171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341285212882964637724781789 127981954831111739146793171)
      ·
        refine ⟨191972932246667608720189757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127981954831111739146793171 191972932246667608720189757)
        ·
          refine ⟨71989849592500353270071159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191972932246667608720189757 71989849592500353270071159)
          ·
            refine ⟨107984774388750529905106739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71989849592500353270071159 107984774388750529905106739)
            ·
              refine ⟨161977161583125794857660109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107984774388750529905106739 161977161583125794857660109)
              ·
                refine ⟨60741435593672173071622541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161977161583125794857660109 60741435593672173071622541)
                ·
                  refine ⟨22778038347627064901858453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60741435593672173071622541 22778038347627064901858453)
                  ·
                    refine ⟨1067720547545018667274615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22778038347627064901858453 1067720547545018667274615)
                    ·
                      rfl

theorem cell23_6238135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_6238135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238135 prefixEnd_6238135 := by exact prefixLift 6238135
  have htrace : WordTrace (prefixWord ++ tailWord_6238135) baseStart_6238135 baseEnd_6238135 := by
    simpa [prefixWord, tailWord_6238135, baseEnd_6238135] using wordTrace_append hprefix tailTrace_6238135
  have hstable : (prefixWord ++ tailWord_6238135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238135).length < 2 ^ (prefixWord ++ tailWord_6238135).sum := by decide
  have hdescent : baseEnd_6238135 < baseStart_6238135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238155 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 6]
def baseStart_6238155 : Nat := 118140960795 + 6238155 * 2 ^ 59
def prefixEnd_6238155 : Nat := 4983230072969 + 3 ^ 40 * 6238155 * 2
def baseEnd_6238155 : Nat := 3203171912248145923573753

theorem tailTrace_6238155 : CollatzResearch.WordTrace tailWord_6238155 prefixEnd_6238155 3203171912248145923573753 := by
  unfold tailWord_6238155
  simp only [CollatzResearch.WordTrace]
  refine ⟨227524204715237301898915919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151682803143491534599277279 227524204715237301898915919)
  ·
    refine ⟨341286307072855952848373879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227524204715237301898915919 341286307072855952848373879)
    ·
      refine ⟨511929460609283929272560819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341286307072855952848373879 511929460609283929272560819)
      ·
        refine ⟨767894190913925893908841229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511929460609283929272560819 767894190913925893908841229)
        ·
          refine ⟨287960321592722210215815461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767894190913925893908841229 287960321592722210215815461)
          ·
            refine ⟨53992560298635414415465399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287960321592722210215815461 53992560298635414415465399)
            ·
              refine ⟨80988840447953121623198099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53992560298635414415465399 80988840447953121623198099)
              ·
                refine ⟨121483260671929682434797149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80988840447953121623198099 121483260671929682434797149)
                ·
                  refine ⟨45556222751973630913048931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121483260671929682434797149 45556222751973630913048931)
                  ·
                    refine ⟨68334334127960446369573397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45556222751973630913048931 68334334127960446369573397)
                    ·
                      refine ⟨3203171912248145923573753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68334334127960446369573397 3203171912248145923573753)
                      ·
                        rfl

theorem cell23_6238155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_6238155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238155 prefixEnd_6238155 := by exact prefixLift 6238155
  have htrace : WordTrace (prefixWord ++ tailWord_6238155) baseStart_6238155 baseEnd_6238155 := by
    simpa [prefixWord, tailWord_6238155, baseEnd_6238155] using wordTrace_append hprefix tailTrace_6238155
  have hstable : (prefixWord ++ tailWord_6238155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238155).length < 2 ^ (prefixWord ++ tailWord_6238155).sum := by decide
  have hdescent : baseEnd_6238155 < baseStart_6238155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238173 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_6238173 : Nat := 118140960795 + 6238173 * 2 ^ 59
def prefixEnd_6238173 : Nat := 4983230072969 + 3 ^ 40 * 6238173 * 2
def baseEnd_6238173 : Nat := 1067727051633308951049557

theorem tailTrace_6238173 : CollatzResearch.WordTrace tailWord_6238173 prefixEnd_6238173 1067727051633308951049557 := by
  unfold tailWord_6238173
  simp only [CollatzResearch.WordTrace]
  refine ⟨227524861229172090973071173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151683240819448060648714115 227524861229172090973071173)
  ·
    refine ⟨42660911480469767057450845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227524861229172090973071173 42660911480469767057450845)
    ·
      refine ⟨15997841805176162646544067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42660911480469767057450845 15997841805176162646544067)
      ·
        refine ⟨23996762707764243969816101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15997841805176162646544067 23996762707764243969816101)
        ·
          refine ⟨4499393007705795744340519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23996762707764243969816101 4499393007705795744340519)
          ·
            refine ⟨6749089511558693616510779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499393007705795744340519 6749089511558693616510779)
            ·
              refine ⟨10123634267338040424766169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6749089511558693616510779 10123634267338040424766169)
              ·
                refine ⟨7592725700503530318574627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10123634267338040424766169 7592725700503530318574627)
                ·
                  refine ⟨11389088550755295477861941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7592725700503530318574627 11389088550755295477861941)
                  ·
                    refine ⟨1067727051633308951049557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11389088550755295477861941 1067727051633308951049557)
                    ·
                      rfl

theorem cell23_6238173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_6238173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238173 prefixEnd_6238173 := by exact prefixLift 6238173
  have htrace : WordTrace (prefixWord ++ tailWord_6238173) baseStart_6238173 baseEnd_6238173 := by
    simpa [prefixWord, tailWord_6238173, baseEnd_6238173] using wordTrace_append hprefix tailTrace_6238173
  have hstable : (prefixWord ++ tailWord_6238173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238173).length < 2 ^ (prefixWord ++ tailWord_6238173).sum := by decide
  have hdescent : baseEnd_6238173 < baseStart_6238173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238179 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 3]
def baseStart_6238179 : Nat := 118140960795 + 6238179 * 2 ^ 59
def prefixEnd_6238179 : Nat := 4983230072969 + 3 ^ 40 * 6238179 * 2
def baseEnd_6238179 : Nat := 3203184235783853829673643

theorem tailTrace_6238179 : CollatzResearch.WordTrace tailWord_6238179 prefixEnd_6238179 3203184235783853829673643 := by
  unfold tailWord_6238179
  simp only [CollatzResearch.WordTrace]
  refine ⟨227525080067150353997789591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151683386711433569331859727 227525080067150353997789591)
  ·
    refine ⟨341287620100725530996684387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227525080067150353997789591 341287620100725530996684387)
    ·
      refine ⟨511931430151088296495026581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341287620100725530996684387 511931430151088296495026581)
      ·
        refine ⟨23996785788332263898204371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 511931430151088296495026581 23996785788332263898204371)
        ·
          refine ⟨35995178682498395847306557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23996785788332263898204371 35995178682498395847306557)
          ·
            refine ⟨13498192005936898442739959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35995178682498395847306557 13498192005936898442739959)
            ·
              refine ⟨20247288008905347664109939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13498192005936898442739959 20247288008905347664109939)
              ·
                refine ⟨30370932013358021496164909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20247288008905347664109939 30370932013358021496164909)
                ·
                  refine ⟨11389099505009258061061841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30370932013358021496164909 11389099505009258061061841)
                  ·
                    refine ⟨8541824628756943545796381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11389099505009258061061841 8541824628756943545796381)
                    ·
                      refine ⟨3203184235783853829673643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8541824628756943545796381 3203184235783853829673643)
                      ·
                        rfl

theorem cell23_6238179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_6238179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238179 prefixEnd_6238179 := by exact prefixLift 6238179
  have htrace : WordTrace (prefixWord ++ tailWord_6238179) baseStart_6238179 baseEnd_6238179 := by
    simpa [prefixWord, tailWord_6238179, baseEnd_6238179] using wordTrace_append hprefix tailTrace_6238179
  have hstable : (prefixWord ++ tailWord_6238179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238179).length < 2 ^ (prefixWord ++ tailWord_6238179).sum := by decide
  have hdescent : baseEnd_6238179 < baseStart_6238179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238192 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 3]
def baseStart_6238192 : Nat := 118140960795 + 6238192 * 2 ^ 59
def prefixEnd_6238192 : Nat := 4983230072969 + 3 ^ 40 * 6238192 * 2
def baseEnd_6238192 : Nat := 3203190911032362278811083

theorem tailTrace_6238192 : CollatzResearch.WordTrace tailWord_6238192 prefixEnd_6238192 3203190911032362278811083 := by
  unfold tailWord_6238192
  simp only [CollatzResearch.WordTrace]
  refine ⟨113762777108051628609006415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151683702810735504812008553 113762777108051628609006415)
  ·
    refine ⟨170644165662077442913509623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113762777108051628609006415 170644165662077442913509623)
    ·
      refine ⟨255966248493116164370264435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170644165662077442913509623 255966248493116164370264435)
      ·
        refine ⟨383949372739674246555396653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255966248493116164370264435 383949372739674246555396653)
        ·
          refine ⟨143981014777377842458273745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383949372739674246555396653 143981014777377842458273745)
          ·
            refine ⟨107985761083033381843705309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143981014777377842458273745 107985761083033381843705309)
            ·
              refine ⟨40494660406137518191389491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107985761083033381843705309 40494660406137518191389491)
              ·
                refine ⟨60741990609206277287084237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40494660406137518191389491 60741990609206277287084237)
                ·
                  refine ⟨22778246478452353982656589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60741990609206277287084237 22778246478452353982656589)
                  ·
                    refine ⟨8541842429419632743496221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22778246478452353982656589 8541842429419632743496221)
                    ·
                      refine ⟨3203190911032362278811083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8541842429419632743496221 3203190911032362278811083)
                      ·
                        rfl

theorem cell23_6238192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_6238192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238192 prefixEnd_6238192 := by exact prefixLift 6238192
  have htrace : WordTrace (prefixWord ++ tailWord_6238192) baseStart_6238192 baseEnd_6238192 := by
    simpa [prefixWord, tailWord_6238192, baseEnd_6238192] using wordTrace_append hprefix tailTrace_6238192
  have hstable : (prefixWord ++ tailWord_6238192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238192).length < 2 ^ (prefixWord ++ tailWord_6238192).sum := by decide
  have hdescent : baseEnd_6238192 < baseStart_6238192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238195 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 4, 7]
def baseStart_6238195 : Nat := 118140960795 + 6238195 * 2 ^ 59
def prefixEnd_6238195 : Nat := 4983230072969 + 3 ^ 40 * 6238195 * 2
def baseEnd_6238195 : Nat := 1067730817158108589024523

theorem tailTrace_6238195 : CollatzResearch.WordTrace tailWord_6238195 prefixEnd_6238195 1067730817158108589024523 := by
  unfold tailWord_6238195
  simp only [CollatzResearch.WordTrace]
  refine ⟨227525663635092388730372039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151683775756728259153581359 227525663635092388730372039)
  ·
    refine ⟨341288495452638583095558059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227525663635092388730372039 341288495452638583095558059)
    ·
      refine ⟨511932743178957874643337089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341288495452638583095558059 511932743178957874643337089)
      ·
        refine ⟨383949557384218405982502817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511932743178957874643337089 383949557384218405982502817)
        ·
          refine ⟨287962168038163804486877113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383949557384218405982502817 287962168038163804486877113)
          ·
            refine ⟨215971626028622853365157835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287962168038163804486877113 215971626028622853365157835)
            ·
              refine ⟨323957439042934280047736753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215971626028622853365157835 323957439042934280047736753)
              ·
                refine ⟨242968079282200710035802565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323957439042934280047736753 242968079282200710035802565)
                ·
                  refine ⟨45556514865412633131712981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 242968079282200710035802565 45556514865412633131712981)
                  ·
                    refine ⟨1067730817158108589024523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45556514865412633131712981 1067730817158108589024523)
                    ·
                      rfl

theorem cell23_6238195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 7].length) (baseStart_6238195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238195 prefixEnd_6238195 := by exact prefixLift 6238195
  have htrace : WordTrace (prefixWord ++ tailWord_6238195) baseStart_6238195 baseEnd_6238195 := by
    simpa [prefixWord, tailWord_6238195, baseEnd_6238195] using wordTrace_append hprefix tailTrace_6238195
  have hstable : (prefixWord ++ tailWord_6238195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238195).length < 2 ^ (prefixWord ++ tailWord_6238195).sum := by decide
  have hdescent : baseEnd_6238195 < baseStart_6238195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238219 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 5, 3, 2]
def baseStart_6238219 : Nat := 118140960795 + 6238219 * 2 ^ 59
def prefixEnd_6238219 : Nat := 4983230072969 + 3 ^ 40 * 6238219 * 2
def baseEnd_6238219 : Nat := 3203204775010033673173459

theorem tailTrace_6238219 : CollatzResearch.WordTrace tailWord_6238219 prefixEnd_6238219 3203204775010033673173459 := by
  unfold tailWord_6238219
  simp only [CollatzResearch.WordTrace]
  refine ⟨227526538987005440829245711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151684359324670293886163807 227526538987005440829245711)
  ·
    refine ⟨341289808480508161243868567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227526538987005440829245711 341289808480508161243868567)
    ·
      refine ⟨511934712720762241865802851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341289808480508161243868567 511934712720762241865802851)
      ·
        refine ⟨767902069081143362798704277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511934712720762241865802851 767902069081143362798704277)
        ·
          refine ⟨35995409488178595131189263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 767902069081143362798704277 35995409488178595131189263)
          ·
            refine ⟨53993114232267892696783895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35995409488178595131189263 53993114232267892696783895)
            ·
              refine ⟨80989671348401839045175843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53993114232267892696783895 80989671348401839045175843)
              ·
                refine ⟨121484507022602758567763765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80989671348401839045175843 121484507022602758567763765)
                ·
                  refine ⟨11389172533369008615727853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121484507022602758567763765 11389172533369008615727853)
                  ·
                    refine ⟨4270939700013378230897945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11389172533369008615727853 4270939700013378230897945)
                    ·
                      refine ⟨3203204775010033673173459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270939700013378230897945 3203204775010033673173459)
                      ·
                        rfl

theorem cell23_6238219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 3, 2].length) (baseStart_6238219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238219 prefixEnd_6238219 := by exact prefixLift 6238219
  have htrace : WordTrace (prefixWord ++ tailWord_6238219) baseStart_6238219 baseEnd_6238219 := by
    simpa [prefixWord, tailWord_6238219, baseEnd_6238219] using wordTrace_append hprefix tailTrace_6238219
  have hstable : (prefixWord ++ tailWord_6238219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238219).length < 2 ^ (prefixWord ++ tailWord_6238219).sum := by decide
  have hdescent : baseEnd_6238219 < baseStart_6238219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238232 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_6238232 : Nat := 118140960795 + 6238232 * 2 ^ 59
def prefixEnd_6238232 : Nat := 4983230072969 + 3 ^ 40 * 6238232 * 2
def baseEnd_6238232 : Nat := 3203211450258542122310899

theorem tailTrace_6238232 : CollatzResearch.WordTrace tailWord_6238232 prefixEnd_6238232 3203211450258542122310899 := by
  unfold tailWord_6238232
  simp only [CollatzResearch.WordTrace]
  refine ⟨113763506567979172024734475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151684675423972229366312633 113763506567979172024734475)
  ·
    refine ⟨170645259851968758037101713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113763506567979172024734475 170645259851968758037101713)
    ·
      refine ⟨127983944888976568527826285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170645259851968758037101713 127983944888976568527826285)
      ·
        refine ⟨47993979333366213197934857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127983944888976568527826285 47993979333366213197934857)
        ·
          refine ⟨35995484500024659898451143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47993979333366213197934857 35995484500024659898451143)
          ·
            refine ⟨53993226750036989847676715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35995484500024659898451143 53993226750036989847676715)
            ·
              refine ⟨80989840125055484771515073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53993226750036989847676715 80989840125055484771515073)
              ·
                refine ⟨60742380093791613578636305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80989840125055484771515073 60742380093791613578636305)
                ·
                  refine ⟨45556785070343710183977229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60742380093791613578636305 45556785070343710183977229)
                  ·
                    refine ⟨17083794401378891318991461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45556785070343710183977229 17083794401378891318991461)
                    ·
                      refine ⟨3203211450258542122310899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17083794401378891318991461 3203211450258542122310899)
                      ·
                        rfl

theorem cell23_6238232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_6238232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238232 prefixEnd_6238232 := by exact prefixLift 6238232
  have htrace : WordTrace (prefixWord ++ tailWord_6238232) baseStart_6238232 baseEnd_6238232 := by
    simpa [prefixWord, tailWord_6238232, baseEnd_6238232] using wordTrace_append hprefix tailTrace_6238232
  have hstable : (prefixWord ++ tailWord_6238232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238232).length < 2 ^ (prefixWord ++ tailWord_6238232).sum := by decide
  have hdescent : baseEnd_6238232 < baseStart_6238232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238236 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_6238236 : Nat := 118140960795 + 6238236 * 2 ^ 59
def prefixEnd_6238236 : Nat := 4983230072969 + 3 ^ 40 * 6238236 * 2
def baseEnd_6238236 : Nat := 3203213504181160106660881

theorem tailTrace_6238236 : CollatzResearch.WordTrace tailWord_6238236 prefixEnd_6238236 3203213504181160106660881 := by
  unfold tailWord_6238236
  simp only [CollatzResearch.WordTrace]
  refine ⟨113763579513971926366307281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151684772685295901821743041 113763579513971926366307281)
  ·
    refine ⟨85322684635478944774730461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113763579513971926366307281 85322684635478944774730461)
    ·
      refine ⟨31996006738304604290523923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85322684635478944774730461 31996006738304604290523923)
      ·
        refine ⟨47994010107456906435785885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31996006738304604290523923 47994010107456906435785885)
        ·
          refine ⟨17997753790296339913419707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47994010107456906435785885 17997753790296339913419707)
          ·
            refine ⟨26996630685444509870129561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17997753790296339913419707 26996630685444509870129561)
            ·
              refine ⟨20247473014083382402597171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26996630685444509870129561 20247473014083382402597171)
              ·
                refine ⟨30371209521125073603895757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20247473014083382402597171 30371209521125073603895757)
                ·
                  refine ⟨11389203570421902601460909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30371209521125073603895757 11389203570421902601460909)
                  ·
                    refine ⟨4270951338908213475547841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11389203570421902601460909 4270951338908213475547841)
                    ·
                      refine ⟨3203213504181160106660881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4270951338908213475547841 3203213504181160106660881)
                      ·
                        rfl

theorem cell23_6238236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_6238236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238236 prefixEnd_6238236 := by exact prefixLift 6238236
  have htrace : WordTrace (prefixWord ++ tailWord_6238236) baseStart_6238236 baseEnd_6238236 := by
    simpa [prefixWord, tailWord_6238236, baseEnd_6238236] using wordTrace_append hprefix tailTrace_6238236
  have hstable : (prefixWord ++ tailWord_6238236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238236).length < 2 ^ (prefixWord ++ tailWord_6238236).sum := by decide
  have hdescent : baseEnd_6238236 < baseStart_6238236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238242 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_6238242 : Nat := 118140960795 + 6238242 * 2 ^ 59
def prefixEnd_6238242 : Nat := 4983230072969 + 3 ^ 40 * 6238242 * 2
def baseEnd_6238242 : Nat := 1067738861688362361061951

theorem tailTrace_6238242 : CollatzResearch.WordTrace tailWord_6238242 prefixEnd_6238242 1067738861688362361061951 := by
  unfold tailWord_6238242
  simp only [CollatzResearch.WordTrace]
  refine ⟨56881844466480528939333245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151684918577281410504888653 56881844466480528939333245)
  ·
    refine ⟨21330691674930198352249967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56881844466480528939333245 21330691674930198352249967)
    ·
      refine ⟨31996037512395297528374951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21330691674930198352249967 31996037512395297528374951)
      ·
        refine ⟨47994056268592946292562427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31996037512395297528374951 47994056268592946292562427)
        ·
          refine ⟨71991084402889419438843641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47994056268592946292562427 71991084402889419438843641)
          ·
            refine ⟨53993313302167064579132731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71991084402889419438843641 53993313302167064579132731)
            ·
              refine ⟨80989969953250596868699097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53993313302167064579132731 80989969953250596868699097)
              ·
                refine ⟨60742477464937947651524323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80989969953250596868699097 60742477464937947651524323)
                ·
                  refine ⟨91113716197406921477286485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60742477464937947651524323 91113716197406921477286485)
                  ·
                    refine ⟨1067738861688362361061951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 91113716197406921477286485 1067738861688362361061951)
                    ·
                      rfl

theorem cell23_6238242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_6238242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238242 prefixEnd_6238242 := by exact prefixLift 6238242
  have htrace : WordTrace (prefixWord ++ tailWord_6238242) baseStart_6238242 baseEnd_6238242 := by
    simpa [prefixWord, tailWord_6238242, baseEnd_6238242] using wordTrace_append hprefix tailTrace_6238242
  have hstable : (prefixWord ++ tailWord_6238242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238242).length < 2 ^ (prefixWord ++ tailWord_6238242).sum := by decide
  have hdescent : baseEnd_6238242 < baseStart_6238242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238247 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_6238247 : Nat := 118140960795 + 6238247 * 2 ^ 59
def prefixEnd_6238247 : Nat := 4983230072969 + 3 ^ 40 * 6238247 * 2
def baseEnd_6238247 : Nat := 3203219152468359563623331

theorem tailTrace_6238247 : CollatzResearch.WordTrace tailWord_6238247 prefixEnd_6238247 3203219152468359563623331 := by
  unfold tailWord_6238247
  simp only [CollatzResearch.WordTrace]
  refine ⟨227527560230904001611264995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151685040153936001074176663 227527560230904001611264995)
  ·
    refine ⟨341291340346356002416897493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227527560230904001611264995 341291340346356002416897493)
    ·
      refine ⟨7999015789367718806646035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 341291340346356002416897493 7999015789367718806646035)
      ·
        refine ⟨11998523684051578209969053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7999015789367718806646035 11998523684051578209969053)
        ·
          refine ⟨4499446381519341828738395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11998523684051578209969053 4499446381519341828738395)
          ·
            refine ⟨6749169572279012743107593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499446381519341828738395 6749169572279012743107593)
            ·
              refine ⟨5061877179209259557330695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6749169572279012743107593 5061877179209259557330695)
              ·
                refine ⟨7592815768813889335996043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061877179209259557330695 7592815768813889335996043)
                ·
                  refine ⟨11389223653220834003994065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7592815768813889335996043 11389223653220834003994065)
                  ·
                    refine ⟨8541917739915625502995549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11389223653220834003994065 8541917739915625502995549)
                    ·
                      refine ⟨3203219152468359563623331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8541917739915625502995549 3203219152468359563623331)
                      ·
                        rfl

theorem cell23_6238247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_6238247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238247 prefixEnd_6238247 := by exact prefixLift 6238247
  have htrace : WordTrace (prefixWord ++ tailWord_6238247) baseStart_6238247 baseEnd_6238247 := by
    simpa [prefixWord, tailWord_6238247, baseEnd_6238247] using wordTrace_append hprefix tailTrace_6238247
  have hstable : (prefixWord ++ tailWord_6238247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238247).length < 2 ^ (prefixWord ++ tailWord_6238247).sum := by decide
  have hdescent : baseEnd_6238247 < baseStart_6238247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238252 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_6238252 : Nat := 118140960795 + 6238252 * 2 ^ 59
def prefixEnd_6238252 : Nat := 4983230072969 + 3 ^ 40 * 6238252 * 2
def baseEnd_6238252 : Nat := 3203221719871632044060807

theorem tailTrace_6238252 : CollatzResearch.WordTrace tailWord_6238252 prefixEnd_6238252 3203221719871632044060807 := by
  unfold tailWord_6238252
  simp only [CollatzResearch.WordTrace]
  refine ⟨113763871297942943732598505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151685161730590591643464673 113763871297942943732598505)
  ·
    refine ⟨85322903473457207799448879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113763871297942943732598505 85322903473457207799448879)
    ·
      refine ⟨127984355210185811699173319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85322903473457207799448879 127984355210185811699173319)
      ·
        refine ⟨191976532815278717548759979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127984355210185811699173319 191976532815278717548759979)
        ·
          refine ⟨287964799222918076323139969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191976532815278717548759979 287964799222918076323139969)
          ·
            refine ⟨215973599417188557242354977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287964799222918076323139969 215973599417188557242354977)
            ·
              refine ⟨161980199562891417931766233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215973599417188557242354977 161980199562891417931766233)
              ·
                refine ⟨121485149672168563448824675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161980199562891417931766233 121485149672168563448824675)
                ·
                  refine ⟨182227724508252845173237013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121485149672168563448824675 182227724508252845173237013)
                  ·
                    refine ⟨8541924586324352117495485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 182227724508252845173237013 8541924586324352117495485)
                    ·
                      refine ⟨3203221719871632044060807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8541924586324352117495485 3203221719871632044060807)
                      ·
                        rfl

theorem cell23_6238252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_6238252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238252 prefixEnd_6238252 := by exact prefixLift 6238252
  have htrace : WordTrace (prefixWord ++ tailWord_6238252) baseStart_6238252 baseEnd_6238252 := by
    simpa [prefixWord, tailWord_6238252, baseEnd_6238252] using wordTrace_append hprefix tailTrace_6238252
  have hstable : (prefixWord ++ tailWord_6238252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238252).length < 2 ^ (prefixWord ++ tailWord_6238252).sum := by decide
  have hdescent : baseEnd_6238252 < baseStart_6238252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238272 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 7]
def baseStart_6238272 : Nat := 118140960795 + 6238272 * 2 ^ 59
def prefixEnd_6238272 : Nat := 4983230072969 + 3 ^ 40 * 6238272 * 2
def baseEnd_6238272 : Nat := 355914665498302440645635

theorem tailTrace_6238272 : CollatzResearch.WordTrace tailWord_6238272 prefixEnd_6238272 355914665498302440645635 := by
  unfold tailWord_6238272
  simp only [CollatzResearch.WordTrace]
  refine ⟨113764236027906715440462535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151685648037208953920616713 113764236027906715440462535)
  ·
    refine ⟨170646354041860073160693803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113764236027906715440462535 170646354041860073160693803)
    ·
      refine ⟨255969531062790109741040705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170646354041860073160693803 255969531062790109741040705)
      ·
        refine ⟨191977148297092582305780529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255969531062790109741040705 191977148297092582305780529)
        ·
          refine ⟨143982861222819436729335397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191977148297092582305780529 143982861222819436729335397)
          ·
            refine ⟨26996786479278644386750387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143982861222819436729335397 26996786479278644386750387)
            ·
              refine ⟨40495179718917966580125581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26996786479278644386750387 40495179718917966580125581)
              ·
                refine ⟨15185692394594237467547093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40495179718917966580125581 15185692394594237467547093)
                ·
                  refine ⟨355914665498302440645635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15185692394594237467547093 355914665498302440645635)
                  ·
                    rfl

theorem cell23_6238272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 7].length) (baseStart_6238272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238272 prefixEnd_6238272 := by exact prefixLift 6238272
  have htrace : WordTrace (prefixWord ++ tailWord_6238272) baseStart_6238272 baseEnd_6238272 := by
    simpa [prefixWord, tailWord_6238272, baseEnd_6238272] using wordTrace_append hprefix tailTrace_6238272
  have hstable : (prefixWord ++ tailWord_6238272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238272).length < 2 ^ (prefixWord ++ tailWord_6238272).sum := by decide
  have hdescent : baseEnd_6238272 < baseStart_6238272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238319 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 2, 5]
def baseStart_6238319 : Nat := 118140960795 + 6238319 * 2 ^ 59
def prefixEnd_6238319 : Nat := 4983230072969 + 3 ^ 40 * 6238319 * 2
def baseEnd_6238319 : Nat := 1067752041025161093974333

theorem tailTrace_6238319 : CollatzResearch.WordTrace tailWord_6238319 prefixEnd_6238319 1067752041025161093974333 := by
  unfold tailWord_6238319
  simp only [CollatzResearch.WordTrace]
  refine ⟨227530186286643157907886011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151686790857762105271924007 227530186286643157907886011)
  ·
    refine ⟨341295279429964736861829017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227530186286643157907886011 341295279429964736861829017)
    ·
      refine ⟨255971459572473552646371763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341295279429964736861829017 255971459572473552646371763)
      ·
        refine ⟨383957189358710328969557645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255971459572473552646371763 383957189358710328969557645)
        ·
          refine ⟨143983946009516373363584117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 383957189358710328969557645 143983946009516373363584117)
          ·
            refine ⟨13498494938392160002836011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143983946009516373363584117 13498494938392160002836011)
            ·
              refine ⟨20247742407588240004254017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13498494938392160002836011 20247742407588240004254017)
              ·
                refine ⟨15185806805691180003190513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20247742407588240004254017 15185806805691180003190513)
                ·
                  refine ⟨11389355104268385002392885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15185806805691180003190513 11389355104268385002392885)
                  ·
                    refine ⟨1067752041025161093974333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11389355104268385002392885 1067752041025161093974333)
                    ·
                      rfl

theorem cell23_6238319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_6238319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238319 prefixEnd_6238319 := by exact prefixLift 6238319
  have htrace : WordTrace (prefixWord ++ tailWord_6238319) baseStart_6238319 baseEnd_6238319 := by
    simpa [prefixWord, tailWord_6238319, baseEnd_6238319] using wordTrace_append hprefix tailTrace_6238319
  have hstable : (prefixWord ++ tailWord_6238319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238319).length < 2 ^ (prefixWord ++ tailWord_6238319).sum := by decide
  have hdescent : baseEnd_6238319 < baseStart_6238319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238329 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_6238329 : Nat := 118140960795 + 6238329 * 2 ^ 59
def prefixEnd_6238329 : Nat := 4983230072969 + 3 ^ 40 * 6238329 * 2
def baseEnd_6238329 : Nat := 3203261257882028242797953

theorem tailTrace_6238329 : CollatzResearch.WordTrace tailWord_6238329 prefixEnd_6238329 3203261257882028242797953 := by
  unfold tailWord_6238329
  simp only [CollatzResearch.WordTrace]
  refine ⟨227530551016606929615750041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151687034011071286410500027 227530551016606929615750041)
  ·
    refine ⟨170647913262455197211812531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227530551016606929615750041 170647913262455197211812531)
    ·
      refine ⟨255971869893682795817718797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170647913262455197211812531 255971869893682795817718797)
      ·
        refine ⟨95989451210131048431644549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255971869893682795817718797 95989451210131048431644549)
        ·
          refine ⟨17998022101899571580933353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95989451210131048431644549 17998022101899571580933353)
          ·
            refine ⟨13498516576424678685700015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17998022101899571580933353 13498516576424678685700015)
            ·
              refine ⟨20247774864637018028550023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13498516576424678685700015 20247774864637018028550023)
              ·
                refine ⟨30371662296955527042825035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20247774864637018028550023 30371662296955527042825035)
                ·
                  refine ⟨45557493445433290564237553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30371662296955527042825035 45557493445433290564237553)
                  ·
                    refine ⟨34168120084074967923178165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45557493445433290564237553 34168120084074967923178165)
                    ·
                      refine ⟨3203261257882028242797953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34168120084074967923178165 3203261257882028242797953)
                      ·
                        rfl

theorem cell23_6238329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_6238329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238329 prefixEnd_6238329 := by exact prefixLift 6238329
  have htrace : WordTrace (prefixWord ++ tailWord_6238329) baseStart_6238329 baseEnd_6238329 := by
    simpa [prefixWord, tailWord_6238329, baseEnd_6238329] using wordTrace_append hprefix tailTrace_6238329
  have hstable : (prefixWord ++ tailWord_6238329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238329).length < 2 ^ (prefixWord ++ tailWord_6238329).sum := by decide
  have hdescent : baseEnd_6238329 < baseStart_6238329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238440 : List Nat := [2, 1, 4, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_6238440 : Nat := 118140960795 + 6238440 * 2 ^ 59
def prefixEnd_6238440 : Nat := 4983230072969 + 3 ^ 40 * 6238440 * 2
def baseEnd_6238440 : Nat := 3203318254234677308509943

theorem tailTrace_6238440 : CollatzResearch.WordTrace tailWord_6238440 prefixEnd_6238440 3203318254234677308509943 := by
  unfold tailWord_6238440
  simp only [CollatzResearch.WordTrace]
  refine ⟨113767299759602397786520387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151689733012803197048693849 113767299759602397786520387)
  ·
    refine ⟨170650949639403596679780581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113767299759602397786520387 170650949639403596679780581)
    ·
      refine ⟨31997053057388174377458859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170650949639403596679780581 31997053057388174377458859)
      ·
        refine ⟨47995579586082261566188289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31997053057388174377458859 47995579586082261566188289)
        ·
          refine ⟨35996684689561696174641217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47995579586082261566188289 35996684689561696174641217)
          ·
            refine ⟨26997513517171272130980913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35996684689561696174641217 26997513517171272130980913)
            ·
              refine ⟨20248135137878454098235685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26997513517171272130980913 20248135137878454098235685)
              ·
                refine ⟨3796525338352210143419191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20248135137878454098235685 3796525338352210143419191)
                ·
                  refine ⟨5694788007528315215128787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3796525338352210143419191 5694788007528315215128787)
                  ·
                    refine ⟨8542182011292472822693181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5694788007528315215128787 8542182011292472822693181)
                    ·
                      refine ⟨3203318254234677308509943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8542182011292472822693181 3203318254234677308509943)
                      ·
                        rfl

theorem cell23_6238440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_6238440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238440 prefixEnd_6238440 := by exact prefixLift 6238440
  have htrace : WordTrace (prefixWord ++ tailWord_6238440) baseStart_6238440 baseEnd_6238440 := by
    simpa [prefixWord, tailWord_6238440, baseEnd_6238440] using wordTrace_append hprefix tailTrace_6238440
  have hstable : (prefixWord ++ tailWord_6238440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238440).length < 2 ^ (prefixWord ++ tailWord_6238440).sum := by decide
  have hdescent : baseEnd_6238440 < baseStart_6238440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238449 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_6238449 : Nat := 118140960795 + 6238449 * 2 ^ 59
def prefixEnd_6238449 : Nat := 4983230072969 + 3 ^ 40 * 6238449 * 2
def baseEnd_6238449 : Nat := 3203322875560567773297401

theorem tailTrace_6238449 : CollatzResearch.WordTrace tailWord_6238449 prefixEnd_6238449 3203322875560567773297401 := by
  unfold tailWord_6238449
  simp only [CollatzResearch.WordTrace]
  refine ⟨227534927776172190110118401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151689951850781460073412267 227534927776172190110118401)
  ·
    refine ⟨170651195832129142582588801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227534927776172190110118401 170651195832129142582588801)
    ·
      refine ⟨127988396874096856936941601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170651195832129142582588801 127988396874096856936941601)
      ·
        refine ⟨95991297655572642702706201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127988396874096856936941601 95991297655572642702706201)
        ·
          refine ⟨71993473241679482027029651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95991297655572642702706201 71993473241679482027029651)
          ·
            refine ⟨107990209862519223040544477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71993473241679482027029651 107990209862519223040544477)
            ·
              refine ⟨40496328698444708640204179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107990209862519223040544477 40496328698444708640204179)
              ·
                refine ⟨60744493047667062960306269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40496328698444708640204179 60744493047667062960306269)
                ·
                  refine ⟨22779184892875148610114851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60744493047667062960306269 22779184892875148610114851)
                  ·
                    refine ⟨34168777339312722915172277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22779184892875148610114851 34168777339312722915172277)
                    ·
                      refine ⟨3203322875560567773297401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34168777339312722915172277 3203322875560567773297401)
                      ·
                        rfl

theorem cell23_6238449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_6238449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238449 prefixEnd_6238449 := by exact prefixLift 6238449
  have htrace : WordTrace (prefixWord ++ tailWord_6238449) baseStart_6238449 baseEnd_6238449 := by
    simpa [prefixWord, tailWord_6238449, baseEnd_6238449] using wordTrace_append hprefix tailTrace_6238449
  have hstable : (prefixWord ++ tailWord_6238449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238449).length < 2 ^ (prefixWord ++ tailWord_6238449).sum := by decide
  have hdescent : baseEnd_6238449 < baseStart_6238449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238456 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 2, 4]
def baseStart_6238456 : Nat := 118140960795 + 6238456 * 2 ^ 59
def prefixEnd_6238456 : Nat := 4983230072969 + 3 ^ 40 * 6238456 * 2
def baseEnd_6238456 : Nat := 1067775489975049748636623

theorem tailTrace_6238456 : CollatzResearch.WordTrace tailWord_6238456 prefixEnd_6238456 1067775489975049748636623 := by
  unfold tailWord_6238456
  simp only [CollatzResearch.WordTrace]
  refine ⟨113767591543573415152811611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151690122058097886870415481 113767591543573415152811611)
  ·
    refine ⟨170651387315360122729217417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113767591543573415152811611 170651387315360122729217417)
    ·
      refine ⟨127988540486520092046913063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170651387315360122729217417 127988540486520092046913063)
      ·
        refine ⟨191982810729780138070369595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127988540486520092046913063 191982810729780138070369595)
        ·
          refine ⟨287974216094670207105554393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191982810729780138070369595 287974216094670207105554393)
          ·
            refine ⟨215980662071002655329165795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 287974216094670207105554393 215980662071002655329165795)
            ·
              refine ⟨323970993106503982993748693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215980662071002655329165795 323970993106503982993748693)
              ·
                refine ⟨7593070150933687101415985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 323970993106503982993748693 7593070150933687101415985)
                ·
                  refine ⟨5694802613200265326061989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7593070150933687101415985 5694802613200265326061989)
                  ·
                    refine ⟨1067775489975049748636623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5694802613200265326061989 1067775489975049748636623)
                    ·
                      rfl

theorem cell23_6238456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_6238456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238456 prefixEnd_6238456 := by exact prefixLift 6238456
  have htrace : WordTrace (prefixWord ++ tailWord_6238456) baseStart_6238456 baseEnd_6238456 := by
    simpa [prefixWord, tailWord_6238456, baseEnd_6238456] using wordTrace_append hprefix tailTrace_6238456
  have hstable : (prefixWord ++ tailWord_6238456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238456).length < 2 ^ (prefixWord ++ tailWord_6238456).sum := by decide
  have hdescent : baseEnd_6238456 < baseStart_6238456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238463 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 3, 2, 2]
def baseStart_6238463 : Nat := 118140960795 + 6238463 * 2 ^ 59
def prefixEnd_6238463 : Nat := 4983230072969 + 3 ^ 40 * 6238463 * 2
def baseEnd_6238463 : Nat := 3203330064289730718522337

theorem tailTrace_6238463 : CollatzResearch.WordTrace tailWord_6238463 prefixEnd_6238463 3203330064289730718522337 := by
  unfold tailWord_6238463
  simp only [CollatzResearch.WordTrace]
  refine ⟨227535438398121470501128043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151690292265414313667418695 227535438398121470501128043)
  ·
    refine ⟨341303157597182205751692065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227535438398121470501128043 341303157597182205751692065)
    ·
      refine ⟨255977368197886654313769049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341303157597182205751692065 255977368197886654313769049)
      ·
        refine ⟨191983026148414990735326787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255977368197886654313769049 191983026148414990735326787)
        ·
          refine ⟨287974539222622486102990181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191983026148414990735326787 287974539222622486102990181)
          ·
            refine ⟨53995226104241716144310659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 287974539222622486102990181 53995226104241716144310659)
            ·
              refine ⟨80992839156362574216465989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53995226104241716144310659 80992839156362574216465989)
              ·
                refine ⟨15186157341817982665587373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80992839156362574216465989 15186157341817982665587373)
                ·
                  refine ⟨5694809003181743499595265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15186157341817982665587373 5694809003181743499595265)
                  ·
                    refine ⟨4271106752386307624696449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5694809003181743499595265 4271106752386307624696449)
                    ·
                      refine ⟨3203330064289730718522337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4271106752386307624696449 3203330064289730718522337)
                      ·
                        rfl

theorem cell23_6238463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_6238463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238463 prefixEnd_6238463 := by exact prefixLift 6238463
  have htrace : WordTrace (prefixWord ++ tailWord_6238463) baseStart_6238463 baseEnd_6238463 := by
    simpa [prefixWord, tailWord_6238463, baseEnd_6238463] using wordTrace_append hprefix tailTrace_6238463
  have hstable : (prefixWord ++ tailWord_6238463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238463).length < 2 ^ (prefixWord ++ tailWord_6238463).sum := by decide
  have hdescent : baseEnd_6238463 < baseStart_6238463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238499 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 2, 7]
def baseStart_6238499 : Nat := 118140960795 + 6238499 * 2 ^ 59
def prefixEnd_6238499 : Nat := 4983230072969 + 3 ^ 40 * 6238499 * 2
def baseEnd_6238499 : Nat := 1067782849864430859224057

theorem tailTrace_6238499 : CollatzResearch.WordTrace tailWord_6238499 prefixEnd_6238499 1067782849864430859224057 := by
  unfold tailWord_6238499
  simp only [CollatzResearch.WordTrace]
  refine ⟨227536751425991048649438551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151691167617327365766292367 227536751425991048649438551)
  ·
    refine ⟨341305127138986572974157827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227536751425991048649438551 341305127138986572974157827)
    ·
      refine ⟨511957690708479859461236741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341305127138986572974157827 511957690708479859461236741)
      ·
        refine ⟨95992067007839973648981889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 511957690708479859461236741 95992067007839973648981889)
        ·
          refine ⟨71994050255879980236736417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95992067007839973648981889 71994050255879980236736417)
          ·
            refine ⟨53995537691909985177552313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71994050255879980236736417 53995537691909985177552313)
            ·
              refine ⟨40496653268932488883164235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53995537691909985177552313 40496653268932488883164235)
              ·
                refine ⟨60744979903398733324746353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40496653268932488883164235 60744979903398733324746353)
                ·
                  refine ⟨45558734927549049993559765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60744979903398733324746353 45558734927549049993559765)
                  ·
                    refine ⟨1067782849864430859224057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45558734927549049993559765 1067782849864430859224057)
                    ·
                      rfl

theorem cell23_6238499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 7].length) (baseStart_6238499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238499 prefixEnd_6238499 := by exact prefixLift 6238499
  have htrace : WordTrace (prefixWord ++ tailWord_6238499) baseStart_6238499 baseEnd_6238499 := by
    simpa [prefixWord, tailWord_6238499, baseEnd_6238499] using wordTrace_append hprefix tailTrace_6238499
  have hstable : (prefixWord ++ tailWord_6238499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238499).length < 2 ^ (prefixWord ++ tailWord_6238499).sum := by decide
  have hdescent : baseEnd_6238499 < baseStart_6238499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238539 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 5]
def baseStart_6238539 : Nat := 118140960795 + 6238539 * 2 ^ 59
def prefixEnd_6238539 : Nat := 4983230072969 + 3 ^ 40 * 6238539 * 2
def baseEnd_6238539 : Nat := 3203369088819472421171987

theorem tailTrace_6238539 : CollatzResearch.WordTrace tailWord_6238539 prefixEnd_6238539 3203369088819472421171987 := by
  unfold tailWord_6238539
  simp only [CollatzResearch.WordTrace]
  refine ⟨227538210345846135480894671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151692140230564090320596447 227538210345846135480894671)
  ·
    refine ⟨341307315518769203221342007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227538210345846135480894671 341307315518769203221342007)
    ·
      refine ⟨511960973278153804832013011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341307315518769203221342007 511960973278153804832013011)
      ·
        refine ⟨767941459917230707248019517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511960973278153804832013011 767941459917230707248019517)
        ·
          refine ⟨287978047468961515218007319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767941459917230707248019517 287978047468961515218007319)
          ·
            refine ⟨431967071203442272827010979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287978047468961515218007319 431967071203442272827010979)
            ·
              refine ⟨647950606805163409240516469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431967071203442272827010979 647950606805163409240516469)
              ·
                refine ⟨60745369387984069616298419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 647950606805163409240516469 60745369387984069616298419)
                ·
                  refine ⟨91118054081976104424447629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60745369387984069616298419 91118054081976104424447629)
                  ·
                    refine ⟨34169270280741039159167861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91118054081976104424447629 34169270280741039159167861)
                    ·
                      refine ⟨3203369088819472421171987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34169270280741039159167861 3203369088819472421171987)
                      ·
                        rfl

theorem cell23_6238539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_6238539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238539 prefixEnd_6238539 := by exact prefixLift 6238539
  have htrace : WordTrace (prefixWord ++ tailWord_6238539) baseStart_6238539 baseEnd_6238539 := by
    simpa [prefixWord, tailWord_6238539, baseEnd_6238539] using wordTrace_append hprefix tailTrace_6238539
  have hstable : (prefixWord ++ tailWord_6238539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238539).length < 2 ^ (prefixWord ++ tailWord_6238539).sum := by decide
  have hdescent : baseEnd_6238539 < baseStart_6238539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238570 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6238570 : Nat := 118140960795 + 6238570 * 2 ^ 59
def prefixEnd_6238570 : Nat := 4983230072969 + 3 ^ 40 * 6238570 * 2
def baseEnd_6238570 : Nat := 3203385006719761799884345

theorem tailTrace_6238570 : CollatzResearch.WordTrace tailWord_6238570 prefixEnd_6238570 3203385006719761799884345 := by
  unfold tailWord_6238570
  simp only [CollatzResearch.WordTrace]
  refine ⟨56884835252183456943818291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151692894005822551850182109 56884835252183456943818291)
  ·
    refine ⟨85327252878275185415727437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56884835252183456943818291 85327252878275185415727437)
    ·
      refine ⟨31997719829353194530897789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85327252878275185415727437 31997719829353194530897789)
      ·
        refine ⟨11999144936007447949086671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31997719829353194530897789 11999144936007447949086671)
        ·
          refine ⟨17998717404011171923630007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11999144936007447949086671 17998717404011171923630007)
          ·
            refine ⟨26998076106016757885445011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17998717404011171923630007 26998076106016757885445011)
            ·
              refine ⟨40497114159025136828167517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26998076106016757885445011 40497114159025136828167517)
              ·
                refine ⟨15186417809634426310562819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40497114159025136828167517 15186417809634426310562819)
                ·
                  refine ⟨22779626714451639465844229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15186417809634426310562819 22779626714451639465844229)
                  ·
                    refine ⟨4271180008959682399845793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22779626714451639465844229 4271180008959682399845793)
                    ·
                      refine ⟨3203385006719761799884345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4271180008959682399845793 3203385006719761799884345)
                      ·
                        rfl

theorem cell23_6238570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6238570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238570 prefixEnd_6238570 := by exact prefixLift 6238570
  have htrace : WordTrace (prefixWord ++ tailWord_6238570) baseStart_6238570 baseEnd_6238570 := by
    simpa [prefixWord, tailWord_6238570, baseEnd_6238570] using wordTrace_append hprefix tailTrace_6238570
  have hstable : (prefixWord ++ tailWord_6238570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238570).length < 2 ^ (prefixWord ++ tailWord_6238570).sum := by decide
  have hdescent : baseEnd_6238570 < baseStart_6238570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238576 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 7]
def baseStart_6238576 : Nat := 118140960795 + 6238576 * 2 ^ 59
def prefixEnd_6238576 : Nat := 4983230072969 + 3 ^ 40 * 6238576 * 2
def baseEnd_6238576 : Nat := 355932009733743197378813

theorem tailTrace_6238576 : CollatzResearch.WordTrace tailWord_6238576 prefixEnd_6238576 355932009733743197378813 := by
  unfold tailWord_6238576
  simp only [CollatzResearch.WordTrace]
  refine ⟨113769779923356045399995791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151693039897808060533327721 113769779923356045399995791)
  ·
    refine ⟨170654669885034068099993687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113769779923356045399995791 170654669885034068099993687)
    ·
      refine ⟨255982004827551102149990531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170654669885034068099993687 255982004827551102149990531)
      ·
        refine ⟨383973007241326653224985797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255982004827551102149990531 383973007241326653224985797)
        ·
          refine ⟨71994938857748747479684837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 383973007241326653224985797 71994938857748747479684837)
          ·
            refine ⟨13499051035827890152440907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71994938857748747479684837 13499051035827890152440907)
            ·
              refine ⟨20248576553741835228661361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13499051035827890152440907 20248576553741835228661361)
              ·
                refine ⟨15186432415306376421496021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20248576553741835228661361 15186432415306376421496021)
                ·
                  refine ⟨355932009733743197378813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15186432415306376421496021 355932009733743197378813)
                  ·
                    rfl

theorem cell23_6238576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 7].length) (baseStart_6238576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238576 prefixEnd_6238576 := by exact prefixLift 6238576
  have htrace : WordTrace (prefixWord ++ tailWord_6238576) baseStart_6238576 baseEnd_6238576 := by
    simpa [prefixWord, tailWord_6238576, baseEnd_6238576] using wordTrace_append hprefix tailTrace_6238576
  have hstable : (prefixWord ++ tailWord_6238576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238576).length < 2 ^ (prefixWord ++ tailWord_6238576).sum := by decide
  have hdescent : baseEnd_6238576 < baseStart_6238576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238579 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 8]
def baseStart_6238579 : Nat := 118140960795 + 6238579 * 2 ^ 59
def prefixEnd_6238579 : Nat := 4983230072969 + 3 ^ 40 * 6238579 * 2
def baseEnd_6238579 : Nat := 3203389628045652264671803

theorem tailTrace_6238579 : CollatzResearch.WordTrace tailWord_6238579 prefixEnd_6238579 3203389628045652264671803 := by
  unfold tailWord_6238579
  simp only [CollatzResearch.WordTrace]
  refine ⟨227539669265701222312350791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151693112843800814874900527 227539669265701222312350791)
  ·
    refine ⟨341309503898551833468526187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227539669265701222312350791 341309503898551833468526187)
    ·
      refine ⟨511964255847827750202789281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341309503898551833468526187 511964255847827750202789281)
      ·
        refine ⟨383973191885870812652091961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511964255847827750202789281 383973191885870812652091961)
        ·
          refine ⟨287979893914403109489068971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383973191885870812652091961 287979893914403109489068971)
          ·
            refine ⟨431969840871604664233603457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287979893914403109489068971 431969840871604664233603457)
            ·
              refine ⟨323977380653703498175202593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431969840871604664233603457 323977380653703498175202593)
              ·
                refine ⟨242983035490277623631401945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323977380653703498175202593 242983035490277623631401945)
                ·
                  refine ⟨182237276617708217723551459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242983035490277623631401945 182237276617708217723551459)
                  ·
                    refine ⟨273355914926562326585327189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182237276617708217723551459 273355914926562326585327189)
                    ·
                      refine ⟨3203389628045652264671803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 273355914926562326585327189 3203389628045652264671803)
                      ·
                        rfl

theorem cell23_6238579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_6238579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238579 prefixEnd_6238579 := by exact prefixLift 6238579
  have htrace : WordTrace (prefixWord ++ tailWord_6238579) baseStart_6238579 baseEnd_6238579 := by
    simpa [prefixWord, tailWord_6238579, baseEnd_6238579] using wordTrace_append hprefix tailTrace_6238579
  have hstable : (prefixWord ++ tailWord_6238579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238579).length < 2 ^ (prefixWord ++ tailWord_6238579).sum := by decide
  have hdescent : baseEnd_6238579 < baseStart_6238579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238586 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_6238586 : Nat := 118140960795 + 6238586 * 2 ^ 59
def prefixEnd_6238586 : Nat := 4983230072969 + 3 ^ 40 * 6238586 * 2
def baseEnd_6238586 : Nat := 3203393222410233737284271

theorem tailTrace_6238586 : CollatzResearch.WordTrace tailWord_6238586 prefixEnd_6238586 3203393222410233737284271 := by
  unfold tailWord_6238586
  simp only [CollatzResearch.WordTrace]
  refine ⟨56884981144168965626963903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151693283051117241671903741 56884981144168965626963903)
  ·
    refine ⟨85327471716253448440445855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56884981144168965626963903 85327471716253448440445855)
    ·
      refine ⟨127991207574380172660668783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85327471716253448440445855 127991207574380172660668783)
      ·
        refine ⟨191986811361570258991003175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127991207574380172660668783 191986811361570258991003175)
        ·
          refine ⟨287980217042355388486504763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191986811361570258991003175 287980217042355388486504763)
          ·
            refine ⟨431970325563533082729757145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287980217042355388486504763 431970325563533082729757145)
            ·
              refine ⟨323977744172649812047317859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431970325563533082729757145 323977744172649812047317859)
              ·
                refine ⟨485966616258974718070976789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323977744172649812047317859 485966616258974718070976789)
                ·
                  refine ⟨22779685137139439909577037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 485966616258974718070976789 22779685137139439909577037)
                  ·
                    refine ⟨8542381926427289966091389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22779685137139439909577037 8542381926427289966091389)
                    ·
                      refine ⟨3203393222410233737284271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8542381926427289966091389 3203393222410233737284271)
                      ·
                        rfl

theorem cell23_6238586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_6238586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238586 prefixEnd_6238586 := by exact prefixLift 6238586
  have htrace : WordTrace (prefixWord ++ tailWord_6238586) baseStart_6238586 baseEnd_6238586 := by
    simpa [prefixWord, tailWord_6238586, baseEnd_6238586] using wordTrace_append hprefix tailTrace_6238586
  have hstable : (prefixWord ++ tailWord_6238586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238586).length < 2 ^ (prefixWord ++ tailWord_6238586).sum := by decide
  have hdescent : baseEnd_6238586 < baseStart_6238586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238663 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_6238663 : Nat := 118140960795 + 6238663 * 2 ^ 59
def prefixEnd_6238663 : Nat := 4983230072969 + 3 ^ 40 * 6238663 * 2
def baseEnd_6238663 : Nat := 3203432760420629936021417

theorem tailTrace_6238663 : CollatzResearch.WordTrace tailWord_6238663 prefixEnd_6238663 3203432760420629936021417 := by
  unfold tailWord_6238663
  simp only [CollatzResearch.WordTrace]
  refine ⟨227542732997396904658408643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151695155331597936438939095 227542732997396904658408643)
  ·
    refine ⟨341314099496095356987612965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227542732997396904658408643 341314099496095356987612965)
    ·
      refine ⟨63996393655517879435177431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 341314099496095356987612965 63996393655517879435177431)
      ·
        refine ⟨95994590483276819152766147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63996393655517879435177431 95994590483276819152766147)
        ·
          refine ⟨143991885724915228729149221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95994590483276819152766147 143991885724915228729149221)
          ·
            refine ⟨26998478573421605386715479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143991885724915228729149221 26998478573421605386715479)
            ·
              refine ⟨40497717860132408080073219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26998478573421605386715479 40497717860132408080073219)
              ·
                refine ⟨60746576790198612120109829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40497717860132408080073219 60746576790198612120109829)
                ·
                  refine ⟨11389983148162239772520593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60746576790198612120109829 11389983148162239772520593)
                  ·
                    refine ⟨8542487361121679829390445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11389983148162239772520593 8542487361121679829390445)
                    ·
                      refine ⟨3203432760420629936021417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8542487361121679829390445 3203432760420629936021417)
                      ·
                        rfl

theorem cell23_6238663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_6238663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238663 prefixEnd_6238663 := by exact prefixLift 6238663
  have htrace : WordTrace (prefixWord ++ tailWord_6238663) baseStart_6238663 baseEnd_6238663 := by
    simpa [prefixWord, tailWord_6238663, baseEnd_6238663] using wordTrace_append hprefix tailTrace_6238663
  have hstable : (prefixWord ++ tailWord_6238663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238663).length < 2 ^ (prefixWord ++ tailWord_6238663).sum := by decide
  have hdescent : baseEnd_6238663 < baseStart_6238663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238666 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 8]
def baseStart_6238666 : Nat := 118140960795 + 6238666 * 2 ^ 59
def prefixEnd_6238666 : Nat := 4983230072969 + 3 ^ 40 * 6238666 * 2
def baseEnd_6238666 : Nat := 355937144540288158253767

theorem tailTrace_6238666 : CollatzResearch.WordTrace tailWord_6238666 prefixEnd_6238666 355937144540288158253767 := by
  unfold tailWord_6238666
  simp only [CollatzResearch.WordTrace]
  refine ⟨56885710604096509042691963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151695228277590690780511901 56885710604096509042691963)
  ·
    refine ⟨85328565906144763564037945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56885710604096509042691963 85328565906144763564037945)
    ·
      refine ⟨63996424429608572673028459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85328565906144763564037945 63996424429608572673028459)
      ·
        refine ⟨95994636644412859009542689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63996424429608572673028459 95994636644412859009542689)
        ·
          refine ⟨71995977483309644257157017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95994636644412859009542689 71995977483309644257157017)
          ·
            refine ⟨53996983112482233192867763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71995977483309644257157017 53996983112482233192867763)
            ·
              refine ⟨80995474668723349789301645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53996983112482233192867763 80995474668723349789301645)
              ·
                refine ⟨30373303000771256170988117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80995474668723349789301645 30373303000771256170988117)
                ·
                  refine ⟨355937144540288158253767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30373303000771256170988117 355937144540288158253767)
                  ·
                    rfl

theorem cell23_6238666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_6238666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238666 prefixEnd_6238666 := by exact prefixLift 6238666
  have htrace : WordTrace (prefixWord ++ tailWord_6238666) baseStart_6238666 baseEnd_6238666 := by
    simpa [prefixWord, tailWord_6238666, baseEnd_6238666] using wordTrace_append hprefix tailTrace_6238666
  have hstable : (prefixWord ++ tailWord_6238666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238666).length < 2 ^ (prefixWord ++ tailWord_6238666).sum := by decide
  have hdescent : baseEnd_6238666 < baseStart_6238666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238713 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 1, 5]
def baseStart_6238713 : Nat := 118140960795 + 6238713 * 2 ^ 59
def prefixEnd_6238713 : Nat := 4983230072969 + 3 ^ 40 * 6238713 * 2
def baseEnd_6238713 : Nat := 1067819478151118246798729

theorem tailTrace_6238713 : CollatzResearch.WordTrace tailWord_6238713 prefixEnd_6238713 1067819478151118246798729 := by
  unfold tailWord_6238713
  simp only [CollatzResearch.WordTrace]
  refine ⟨227544556647215763197728793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151696371098143842131819195 227544556647215763197728793)
  ·
    refine ⟨170658417485411822398296595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227544556647215763197728793 170658417485411822398296595)
    ·
      refine ⟨255987626228117733597444893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170658417485411822398296595 255987626228117733597444893)
      ·
        refine ⟨95995359835544150099041835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 255987626228117733597444893 95995359835544150099041835)
        ·
          refine ⟨143993039753316225148562753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95995359835544150099041835 143993039753316225148562753)
          ·
            refine ⟨107994779814987168861422065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143993039753316225148562753 107994779814987168861422065)
            ·
              refine ⟨80996084861240376646066549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107994779814987168861422065 80996084861240376646066549)
              ·
                refine ⟨7593382955741285310568739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80996084861240376646066549 7593382955741285310568739)
                ·
                  refine ⟨11390074433611927965853109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7593382955741285310568739 11390074433611927965853109)
                  ·
                    refine ⟨1067819478151118246798729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11390074433611927965853109 1067819478151118246798729)
                    ·
                      rfl

theorem cell23_6238713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_6238713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238713 prefixEnd_6238713 := by exact prefixLift 6238713
  have htrace : WordTrace (prefixWord ++ tailWord_6238713) baseStart_6238713 baseEnd_6238713 := by
    simpa [prefixWord, tailWord_6238713, baseEnd_6238713] using wordTrace_append hprefix tailTrace_6238713
  have hstable : (prefixWord ++ tailWord_6238713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238713).length < 2 ^ (prefixWord ++ tailWord_6238713).sum := by decide
  have hdescent : baseEnd_6238713 < baseStart_6238713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238760 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6238760 : Nat := 118140960795 + 6238760 * 2 ^ 59
def prefixEnd_6238760 : Nat := 4983230072969 + 3 ^ 40 * 6238760 * 2
def baseEnd_6238760 : Nat := 1067827522681372018836157

theorem tailTrace_6238760 : CollatzResearch.WordTrace tailWord_6238760 prefixEnd_6238760 1067827522681372018836157 := by
  unfold tailWord_6238760
  simp only [CollatzResearch.WordTrace]
  refine ⟨113773135439022745112344867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151697513918696993483126489 113773135439022745112344867)
  ·
    refine ⟨170659703158534117668517301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113773135439022745112344867 170659703158534117668517301)
    ·
      refine ⟨15999347171112573531423497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170659703158534117668517301 15999347171112573531423497)
      ·
        refine ⟨11999510378334430148567623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15999347171112573531423497 11999510378334430148567623)
        ·
          refine ⟨17999265567501645222851435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11999510378334430148567623 17999265567501645222851435)
          ·
            refine ⟨26998898351252467834277153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17999265567501645222851435 26998898351252467834277153)
            ·
              refine ⟨20249173763439350875707865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26998898351252467834277153 20249173763439350875707865)
              ·
                refine ⟨15186880322579513156780899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20249173763439350875707865 15186880322579513156780899)
                ·
                  refine ⟨22780320483869269735171349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15186880322579513156780899 22780320483869269735171349)
                  ·
                    refine ⟨1067827522681372018836157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22780320483869269735171349 1067827522681372018836157)
                    ·
                      rfl

theorem cell23_6238760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6238760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238760 prefixEnd_6238760 := by exact prefixLift 6238760
  have htrace : WordTrace (prefixWord ++ tailWord_6238760) baseStart_6238760 baseEnd_6238760 := by
    simpa [prefixWord, tailWord_6238760, baseEnd_6238760] using wordTrace_append hprefix tailTrace_6238760
  have hstable : (prefixWord ++ tailWord_6238760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238760).length < 2 ^ (prefixWord ++ tailWord_6238760).sum := by decide
  have hdescent : baseEnd_6238760 < baseStart_6238760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238784 : List Nat := [2, 1, 1, 2, 2, 2, 4, 4, 1, 2, 2]
def baseStart_6238784 : Nat := 118140960795 + 6238784 * 2 ^ 59
def prefixEnd_6238784 : Nat := 4983230072969 + 3 ^ 40 * 6238784 * 2
def baseEnd_6238784 : Nat := 3203494891579823962608361

theorem tailTrace_6238784 : CollatzResearch.WordTrace tailWord_6238784 prefixEnd_6238784 3203494891579823962608361 := by
  unfold tailWord_6238784
  simp only [CollatzResearch.WordTrace]
  refine ⟨113773573114979271161781703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151698097486639028215708937 113773573114979271161781703)
  ·
    refine ⟨170660359672468906742672555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113773573114979271161781703 170660359672468906742672555)
    ·
      refine ⟨255990539508703360114008833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170660359672468906742672555 255990539508703360114008833)
      ·
        refine ⟨191992904631527520085506625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 255990539508703360114008833 191992904631527520085506625)
        ·
          refine ⟨143994678473645640064129969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191992904631527520085506625 143994678473645640064129969)
          ·
            refine ⟨107996008855234230048097477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143994678473645640064129969 107996008855234230048097477)
            ·
              refine ⟨20249251660356418134018277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107996008855234230048097477 20249251660356418134018277)
              ·
                refine ⟨3796734686316828400128427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20249251660356418134018277 3796734686316828400128427)
                ·
                  refine ⟨5695102029475242600192641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3796734686316828400128427 5695102029475242600192641)
                  ·
                    refine ⟨4271326522106431950144481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5695102029475242600192641 4271326522106431950144481)
                    ·
                      refine ⟨3203494891579823962608361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4271326522106431950144481 3203494891579823962608361)
                      ·
                        rfl

theorem cell23_6238784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_6238784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238784 prefixEnd_6238784 := by exact prefixLift 6238784
  have htrace : WordTrace (prefixWord ++ tailWord_6238784) baseStart_6238784 baseEnd_6238784 := by
    simpa [prefixWord, tailWord_6238784, baseEnd_6238784] using wordTrace_append hprefix tailTrace_6238784
  have hstable : (prefixWord ++ tailWord_6238784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238784).length < 2 ^ (prefixWord ++ tailWord_6238784).sum := by decide
  have hdescent : baseEnd_6238784 < baseStart_6238784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238797 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_6238797 : Nat := 118140960795 + 6238797 * 2 ^ 59
def prefixEnd_6238797 : Nat := 4983230072969 + 3 ^ 40 * 6238797 * 2
def baseEnd_6238797 : Nat := 3203501566828332411745801

theorem tailTrace_6238797 : CollatzResearch.WordTrace tailWord_6238797 prefixEnd_6238797 3203501566828332411745801 := by
  unfold tailWord_6238797
  simp only [CollatzResearch.WordTrace]
  refine ⟨227547620378911445543786645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151698413585940963695857763 227547620378911445543786645)
  ·
    refine ⟨10666294705261474009864999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 227547620378911445543786645 10666294705261474009864999)
    ·
      refine ⟨15999442057892211014797499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10666294705261474009864999 15999442057892211014797499)
      ·
        refine ⟨23999163086838316522196249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15999442057892211014797499 23999163086838316522196249)
        ·
          refine ⟨17999372315128737391647187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23999163086838316522196249 17999372315128737391647187)
          ·
            refine ⟨26999058472693106087470781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17999372315128737391647187 26999058472693106087470781)
            ·
              refine ⟨10124646927259914782801543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26999058472693106087470781 10124646927259914782801543)
              ·
                refine ⟨15186970390889872174202315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10124646927259914782801543 15186970390889872174202315)
                ·
                  refine ⟨22780455586334808261303473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15186970390889872174202315 22780455586334808261303473)
                  ·
                    refine ⟨17085341689751106195977605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22780455586334808261303473 17085341689751106195977605)
                    ·
                      refine ⟨3203501566828332411745801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17085341689751106195977605 3203501566828332411745801)
                      ·
                        rfl

theorem cell23_6238797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_6238797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238797 prefixEnd_6238797 := by exact prefixLift 6238797
  have htrace : WordTrace (prefixWord ++ tailWord_6238797) baseStart_6238797 baseEnd_6238797 := by
    simpa [prefixWord, tailWord_6238797, baseEnd_6238797] using wordTrace_append hprefix tailTrace_6238797
  have hstable : (prefixWord ++ tailWord_6238797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238797).length < 2 ^ (prefixWord ++ tailWord_6238797).sum := by decide
  have hdescent : baseEnd_6238797 < baseStart_6238797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238823 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_6238823 : Nat := 118140960795 + 6238823 * 2 ^ 59
def prefixEnd_6238823 : Nat := 4983230072969 + 3 ^ 40 * 6238823 * 2
def baseEnd_6238823 : Nat := 3203514917325349310020681

theorem tailTrace_6238823 : CollatzResearch.WordTrace tailWord_6238823 prefixEnd_6238823 3203514917325349310020681 := by
  unfold tailWord_6238823
  simp only [CollatzResearch.WordTrace]
  refine ⟨227548568676817251984233123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151699045784544834656155415 227548568676817251984233123)
  ·
    refine ⟨341322853015225877976349685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227548568676817251984233123 341322853015225877976349685)
    ·
      refine ⟨31999017470177426060282783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 341322853015225877976349685 31999017470177426060282783)
      ·
        refine ⟨47998526205266139090424175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31999017470177426060282783 47998526205266139090424175)
        ·
          refine ⟨71997789307899208635636263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47998526205266139090424175 71997789307899208635636263)
          ·
            refine ⟨107996683961848812953454395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71997789307899208635636263 107996683961848812953454395)
            ·
              refine ⟨161995025942773219430181593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107996683961848812953454395 161995025942773219430181593)
              ·
                refine ⟨121496269457079914572636195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161995025942773219430181593 121496269457079914572636195)
                ·
                  refine ⟨182244404185619871858954293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121496269457079914572636195 182244404185619871858954293)
                  ·
                    refine ⟨17085412892401862986776965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182244404185619871858954293 17085412892401862986776965)
                    ·
                      refine ⟨3203514917325349310020681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17085412892401862986776965 3203514917325349310020681)
                      ·
                        rfl

theorem cell23_6238823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_6238823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238823 prefixEnd_6238823 := by exact prefixLift 6238823
  have htrace : WordTrace (prefixWord ++ tailWord_6238823) baseStart_6238823 baseEnd_6238823 := by
    simpa [prefixWord, tailWord_6238823, baseEnd_6238823] using wordTrace_append hprefix tailTrace_6238823
  have hstable : (prefixWord ++ tailWord_6238823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238823).length < 2 ^ (prefixWord ++ tailWord_6238823).sum := by decide
  have hdescent : baseEnd_6238823 < baseStart_6238823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238840 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 3, 4, 2]
def baseStart_6238840 : Nat := 118140960795 + 6238840 * 2 ^ 59
def prefixEnd_6238840 : Nat := 4983230072969 + 3 ^ 40 * 6238840 * 2
def baseEnd_6238840 : Nat := 3203523646496475743508103

theorem tailTrace_6238840 : CollatzResearch.WordTrace tailWord_6238840 prefixEnd_6238840 3203523646496475743508103 := by
  unfold tailWord_6238840
  simp only [CollatzResearch.WordTrace]
  refine ⟨113774594358877831943800987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151699459145170442591734649 113774594358877831943800987)
  ·
    refine ⟨170661891538316747915701481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113774594358877831943800987 170661891538316747915701481)
    ·
      refine ⟨127996418653737560936776111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170661891538316747915701481 127996418653737560936776111)
      ·
        refine ⟨191994627980606341405164167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127996418653737560936776111 191994627980606341405164167)
        ·
          refine ⟨287991941970909512107746251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191994627980606341405164167 287991941970909512107746251)
          ·
            refine ⟨431987912956364268161619377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287991941970909512107746251 431987912956364268161619377)
            ·
              refine ⟨323990934717273201121214533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431987912956364268161619377 323990934717273201121214533)
              ·
                refine ⟨60748300259488725210227725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323990934717273201121214533 60748300259488725210227725)
                ·
                  refine ⟨22780612597308271953835397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60748300259488725210227725 22780612597308271953835397)
                  ·
                    refine ⟨4271364861995300991344137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22780612597308271953835397 4271364861995300991344137)
                    ·
                      refine ⟨3203523646496475743508103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4271364861995300991344137 3203523646496475743508103)
                      ·
                        rfl

theorem cell23_6238840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_6238840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238840 prefixEnd_6238840 := by exact prefixLift 6238840
  have htrace : WordTrace (prefixWord ++ tailWord_6238840) baseStart_6238840 baseEnd_6238840 := by
    simpa [prefixWord, tailWord_6238840, baseEnd_6238840] using wordTrace_append hprefix tailTrace_6238840
  have hstable : (prefixWord ++ tailWord_6238840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238840).length < 2 ^ (prefixWord ++ tailWord_6238840).sum := by decide
  have hdescent : baseEnd_6238840 < baseStart_6238840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238910 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_6238910 : Nat := 118140960795 + 6238910 * 2 ^ 59
def prefixEnd_6238910 : Nat := 4983230072969 + 3 ^ 40 * 6238910 * 2
def baseEnd_6238910 : Nat := 1067853196714096823210927

theorem tailTrace_6238910 : CollatzResearch.WordTrace tailWord_6238910 prefixEnd_6238910 1067853196714096823210927 := by
  unfold tailWord_6238910
  simp only [CollatzResearch.WordTrace]
  refine ⟨28443967728437758230331273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151701161218334710561766789 28443967728437758230331273)
  ·
    refine ⟨21332975796328318672748455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28443967728437758230331273 21332975796328318672748455)
    ·
      refine ⟨31999463694492478009122683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21332975796328318672748455 31999463694492478009122683)
      ·
        refine ⟨47999195541738717013684025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31999463694492478009122683 47999195541738717013684025)
        ·
          refine ⟨35999396656304037760263019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47999195541738717013684025 35999396656304037760263019)
          ·
            refine ⟨53999094984456056640394529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35999396656304037760263019 53999094984456056640394529)
            ·
              refine ⟨40499321238342042480295897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53999094984456056640394529 40499321238342042480295897)
              ·
                refine ⟨30374490928756531860221923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40499321238342042480295897 30374490928756531860221923)
                ·
                  refine ⟨45561736393134797790332885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30374490928756531860221923 45561736393134797790332885)
                  ·
                    refine ⟨1067853196714096823210927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45561736393134797790332885 1067853196714096823210927)
                    ·
                      rfl

theorem cell23_6238910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_6238910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238910 prefixEnd_6238910 := by exact prefixLift 6238910
  have htrace : WordTrace (prefixWord ++ tailWord_6238910) baseStart_6238910 baseEnd_6238910 := by
    simpa [prefixWord, tailWord_6238910, baseEnd_6238910] using wordTrace_append hprefix tailTrace_6238910
  have hstable : (prefixWord ++ tailWord_6238910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238910).length < 2 ^ (prefixWord ++ tailWord_6238910).sum := by decide
  have hdescent : baseEnd_6238910 < baseStart_6238910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238970 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 6]
def baseStart_6238970 : Nat := 118140960795 + 6238970 * 2 ^ 59
def prefixEnd_6238970 : Nat := 4983230072969 + 3 ^ 40 * 6238970 * 2
def baseEnd_6238970 : Nat := 355954488775728914986945

theorem tailTrace_6238970 : CollatzResearch.WordTrace tailWord_6238970 prefixEnd_6238970 355954488775728914986945 := by
  unfold tailWord_6238970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56888482551821174022458591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151702620138189797393222909 56888482551821174022458591)
  ·
    refine ⟨85332723827731761033687887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56888482551821174022458591 85332723827731761033687887)
    ·
      refine ⟨127999085741597641550531831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85332723827731761033687887 127999085741597641550531831)
      ·
        refine ⟨191998628612396462325797747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127999085741597641550531831 191998628612396462325797747)
        ·
          refine ⟨287997942918594693488696621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191998628612396462325797747 287997942918594693488696621)
          ·
            refine ⟨107999228594473010058261233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 287997942918594693488696621 107999228594473010058261233)
            ·
              refine ⟨80999421445854757543695925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107999228594473010058261233 80999421445854757543695925)
              ·
                refine ⟨7593695760548883519721493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80999421445854757543695925 7593695760548883519721493)
                ·
                  refine ⟨355954488775728914986945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7593695760548883519721493 355954488775728914986945)
                  ·
                    rfl

theorem cell23_6238970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_6238970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238970 prefixEnd_6238970 := by exact prefixLift 6238970
  have htrace : WordTrace (prefixWord ++ tailWord_6238970) baseStart_6238970 baseEnd_6238970 := by
    simpa [prefixWord, tailWord_6238970, baseEnd_6238970] using wordTrace_append hprefix tailTrace_6238970
  have hstable : (prefixWord ++ tailWord_6238970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238970).length < 2 ^ (prefixWord ++ tailWord_6238970).sum := by decide
  have hdescent : baseEnd_6238970 < baseStart_6238970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238974 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_6238974 : Nat := 118140960795 + 6238974 * 2 ^ 59
def prefixEnd_6238974 : Nat := 4983230072969 + 3 ^ 40 * 6238974 * 2
def baseEnd_6238974 : Nat := 1067864150968059406410829

theorem tailTrace_6238974 : CollatzResearch.WordTrace tailWord_6238974 prefixEnd_6238974 1067864150968059406410829 := by
  unfold tailWord_6238974
  simp only [CollatzResearch.WordTrace]
  refine ⟨28444259512408775596622497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151702717399513469848653317 28444259512408775596622497)
  ·
    refine ⟨21333194634306581697466873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28444259512408775596622497 21333194634306581697466873)
    ·
      refine ⟨15999895975729936273100155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21333194634306581697466873 15999895975729936273100155)
      ·
        refine ⟨23999843963594904409650233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15999895975729936273100155 23999843963594904409650233)
        ·
          refine ⟨17999882972696178307237675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23999843963594904409650233 17999882972696178307237675)
          ·
            refine ⟨26999824459044267460856513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17999882972696178307237675 26999824459044267460856513)
            ·
              refine ⟨20249868344283200595642385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26999824459044267460856513 20249868344283200595642385)
              ·
                refine ⟨15187401258212400446731789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20249868344283200595642385 15187401258212400446731789)
                ·
                  refine ⟨5695275471829650167524421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15187401258212400446731789 5695275471829650167524421)
                  ·
                    refine ⟨1067864150968059406410829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5695275471829650167524421 1067864150968059406410829)
                    ·
                      rfl

theorem cell23_6238974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_6238974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6238974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6238974 prefixEnd_6238974 := by exact prefixLift 6238974
  have htrace : WordTrace (prefixWord ++ tailWord_6238974) baseStart_6238974 baseEnd_6238974 := by
    simpa [prefixWord, tailWord_6238974, baseEnd_6238974] using wordTrace_append hprefix tailTrace_6238974
  have hstable : (prefixWord ++ tailWord_6238974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238974).length < 2 ^ (prefixWord ++ tailWord_6238974).sum := by decide
  have hdescent : baseEnd_6238974 < baseStart_6238974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239000 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 5, 5]
def baseStart_6239000 : Nat := 118140960795 + 6239000 * 2 ^ 59
def prefixEnd_6239000 : Nat := 4983230072969 + 3 ^ 40 * 6239000 * 2
def baseEnd_6239000 : Nat := 1067868601133731705835789

theorem tailTrace_6239000 : CollatzResearch.WordTrace tailWord_6239000 prefixEnd_6239000 1067868601133731705835789 := by
  unfold tailWord_6239000
  simp only [CollatzResearch.WordTrace]
  refine ⟨113777512198588005606713227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151703349598117340808950969 113777512198588005606713227)
  ·
    refine ⟨170666268297882008410069841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113777512198588005606713227 170666268297882008410069841)
    ·
      refine ⟨127999701223411506307552381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170666268297882008410069841 127999701223411506307552381)
      ·
        refine ⟨47999887958779314865332143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127999701223411506307552381 47999887958779314865332143)
        ·
          refine ⟨71999831938168972297998215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47999887958779314865332143 71999831938168972297998215)
          ·
            refine ⟨107999747907253458446997323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71999831938168972297998215 107999747907253458446997323)
            ·
              refine ⟨161999621860880187670495985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107999747907253458446997323 161999621860880187670495985)
              ·
                refine ⟨121499716395660140752871989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161999621860880187670495985 121499716395660140752871989)
                ·
                  refine ⟨11390598412093138195581749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 121499716395660140752871989 11390598412093138195581749)
                  ·
                    refine ⟨1067868601133731705835789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11390598412093138195581749 1067868601133731705835789)
                    ·
                      rfl

theorem cell23_6239000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_6239000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239000 prefixEnd_6239000 := by exact prefixLift 6239000
  have htrace : WordTrace (prefixWord ++ tailWord_6239000) baseStart_6239000 baseEnd_6239000 := by
    simpa [prefixWord, tailWord_6239000, baseEnd_6239000] using wordTrace_append hprefix tailTrace_6239000
  have hstable : (prefixWord ++ tailWord_6239000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239000).length < 2 ^ (prefixWord ++ tailWord_6239000).sum := by decide
  have hdescent : baseEnd_6239000 < baseStart_6239000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239021 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 6]
def baseStart_6239021 : Nat := 118140960795 + 6239021 * 2 ^ 59
def prefixEnd_6239021 : Nat := 4983230072969 + 3 ^ 40 * 6239021 * 2
def baseEnd_6239021 : Nat := 355957398499437726149419

theorem tailTrace_6239021 : CollatzResearch.WordTrace tailWord_6239021 prefixEnd_6239021 355957398499437726149419 := by
  unfold tailWord_6239021
  simp only [CollatzResearch.WordTrace]
  refine ⟨227555790330099931799940917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151703860220066621199960611 227555790330099931799940917)
  ·
    refine ⟨21333355343446868606244461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 227555790330099931799940917 21333355343446868606244461)
    ·
      refine ⟨8000008253792575727341673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21333355343446868606244461 8000008253792575727341673)
      ·
        refine ⟨6000006190344431795506255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8000008253792575727341673 6000006190344431795506255)
        ·
          refine ⟨9000009285516647693259383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6000006190344431795506255 9000009285516647693259383)
          ·
            refine ⟨13500013928274971539889075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9000009285516647693259383 13500013928274971539889075)
            ·
              refine ⟨20250020892412457309833613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13500013928274971539889075 20250020892412457309833613)
              ·
                refine ⟨7593757834654671491187605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20250020892412457309833613 7593757834654671491187605)
                ·
                  refine ⟨355957398499437726149419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7593757834654671491187605 355957398499437726149419)
                  ·
                    rfl

theorem cell23_6239021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_6239021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239021 prefixEnd_6239021 := by exact prefixLift 6239021
  have htrace : WordTrace (prefixWord ++ tailWord_6239021) baseStart_6239021 baseEnd_6239021 := by
    simpa [prefixWord, tailWord_6239021, baseEnd_6239021] using wordTrace_append hprefix tailTrace_6239021
  have hstable : (prefixWord ++ tailWord_6239021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239021).length < 2 ^ (prefixWord ++ tailWord_6239021).sum := by decide
  have hdescent : baseEnd_6239021 < baseStart_6239021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239040 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_6239040 : Nat := 118140960795 + 6239040 * 2 ^ 59
def prefixEnd_6239040 : Nat := 4983230072969 + 3 ^ 40 * 6239040 * 2
def baseEnd_6239040 : Nat := 3203626342627374961007183

theorem tailTrace_6239040 : CollatzResearch.WordTrace tailWord_6239040 prefixEnd_6239040 3203626342627374961007183 := by
  unfold tailWord_6239040
  simp only [CollatzResearch.WordTrace]
  refine ⟨113778241658515549022441287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151704322211354065363255049 113778241658515549022441287)
  ·
    refine ⟨170667362487773323533661931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113778241658515549022441287 170667362487773323533661931)
    ·
      refine ⟨256001043731659985300492897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170667362487773323533661931 256001043731659985300492897)
      ·
        refine ⟨192000782798744988975369673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256001043731659985300492897 192000782798744988975369673)
        ·
          refine ⟨144000587099058741731527255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192000782798744988975369673 144000587099058741731527255)
          ·
            refine ⟨216000880648588112597290883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144000587099058741731527255 216000880648588112597290883)
            ·
              refine ⟨324001320972882168895936325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216000880648588112597290883 324001320972882168895936325)
              ·
                refine ⟨60750247682415406667988061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324001320972882168895936325 60750247682415406667988061)
                ·
                  refine ⟨22781342880905777500495523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60750247682415406667988061 22781342880905777500495523)
                  ·
                    refine ⟨34172014321358666250743285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22781342880905777500495523 34172014321358666250743285)
                    ·
                      refine ⟨3203626342627374961007183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34172014321358666250743285 3203626342627374961007183)
                      ·
                        rfl

theorem cell23_6239040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_6239040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239040 prefixEnd_6239040 := by exact prefixLift 6239040
  have htrace : WordTrace (prefixWord ++ tailWord_6239040) baseStart_6239040 baseEnd_6239040 := by
    simpa [prefixWord, tailWord_6239040, baseEnd_6239040] using wordTrace_append hprefix tailTrace_6239040
  have hstable : (prefixWord ++ tailWord_6239040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239040).length < 2 ^ (prefixWord ++ tailWord_6239040).sum := by decide
  have hdescent : baseEnd_6239040 < baseStart_6239040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239050 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_6239050 : Nat := 118140960795 + 6239050 * 2 ^ 59
def prefixEnd_6239050 : Nat := 4983230072969 + 3 ^ 40 * 6239050 * 2
def baseEnd_6239050 : Nat := 3203631477433919921882137

theorem tailTrace_6239050 : CollatzResearch.WordTrace tailWord_6239050 prefixEnd_6239050 3203631477433919921882137 := by
  unfold tailWord_6239050
  simp only [CollatzResearch.WordTrace]
  refine ⟨56889212011748717438186651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151704565364663246501831069 56889212011748717438186651)
  ·
    refine ⟨85333818017623076157279977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56889212011748717438186651 85333818017623076157279977)
    ·
      refine ⟨64000363513217307117959983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85333818017623076157279977 64000363513217307117959983)
      ·
        refine ⟨96000545269825960676939975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64000363513217307117959983 96000545269825960676939975)
        ·
          refine ⟨144000817904738941015409963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96000545269825960676939975 144000817904738941015409963)
          ·
            refine ⟨216001226857108411523114945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144000817904738941015409963 216001226857108411523114945)
            ·
              refine ⟨162000920142831308642336209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216001226857108411523114945 162000920142831308642336209)
              ·
                refine ⟨121500690107123481481752157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162000920142831308642336209 121500690107123481481752157)
                ·
                  refine ⟨45562758790171305555657059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 121500690107123481481752157 45562758790171305555657059)
                  ·
                    refine ⟨68344138185256958333485589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45562758790171305555657059 68344138185256958333485589)
                    ·
                      refine ⟨3203631477433919921882137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68344138185256958333485589 3203631477433919921882137)
                      ·
                        rfl

theorem cell23_6239050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_6239050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239050 prefixEnd_6239050 := by exact prefixLift 6239050
  have htrace : WordTrace (prefixWord ++ tailWord_6239050) baseStart_6239050 baseEnd_6239050 := by
    simpa [prefixWord, tailWord_6239050, baseEnd_6239050] using wordTrace_append hprefix tailTrace_6239050
  have hstable : (prefixWord ++ tailWord_6239050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239050).length < 2 ^ (prefixWord ++ tailWord_6239050).sum := by decide
  have hdescent : baseEnd_6239050 < baseStart_6239050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239060 : List Nat := [2, 4, 1, 1, 15]
def baseStart_6239060 : Nat := 118140960795 + 6239060 * 2 ^ 59
def prefixEnd_6239060 : Nat := 4983230072969 + 3 ^ 40 * 6239060 * 2
def baseEnd_6239060 : Nat := 4394563254102146615579

theorem tailTrace_6239060 : CollatzResearch.WordTrace tailWord_6239060 prefixEnd_6239060 4394563254102146615579 := by
  unfold tailWord_6239060
  simp only [CollatzResearch.WordTrace]
  refine ⟨113778606388479320730305317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151704808517972427640407089 113778606388479320730305317)
  ·
    refine ⟨21333488697839872636932247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113778606388479320730305317 21333488697839872636932247)
    ·
      refine ⟨32000233046759808955398371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21333488697839872636932247 32000233046759808955398371)
      ·
        refine ⟨48000349570139713433097557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32000233046759808955398371 48000349570139713433097557)
        ·
          refine ⟨4394563254102146615579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 48000349570139713433097557 4394563254102146615579)
          ·
            rfl

theorem cell23_6239060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 15].length) (baseStart_6239060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239060 prefixEnd_6239060 := by exact prefixLift 6239060
  have htrace : WordTrace (prefixWord ++ tailWord_6239060) baseStart_6239060 baseEnd_6239060 := by
    simpa [prefixWord, tailWord_6239060, baseEnd_6239060] using wordTrace_append hprefix tailTrace_6239060
  have hstable : (prefixWord ++ tailWord_6239060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239060).length < 2 ^ (prefixWord ++ tailWord_6239060).sum := by decide
  have hdescent : baseEnd_6239060 < baseStart_6239060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239161 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 4, 2, 2]
def baseStart_6239161 : Nat := 118140960795 + 6239161 * 2 ^ 59
def prefixEnd_6239161 : Nat := 4983230072969 + 3 ^ 40 * 6239161 * 2
def baseEnd_6239161 : Nat := 3203688473786568987594127

theorem tailTrace_6239161 : CollatzResearch.WordTrace tailWord_6239161 prefixEnd_6239161 3203688473786568987594127 := by
  unfold tailWord_6239161
  simp only [CollatzResearch.WordTrace]
  refine ⟨227560896549592735710037337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151707264366395157140024891 227560896549592735710037337)
  ·
    refine ⟨170670672412194551782528003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227560896549592735710037337 170670672412194551782528003)
    ·
      refine ⟨256006008618291827673792005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170670672412194551782528003 256006008618291827673792005)
      ·
        refine ⟨48001126615929717688836001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256006008618291827673792005 48001126615929717688836001)
        ·
          refine ⟨36000844961947288266627001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48001126615929717688836001 36000844961947288266627001)
          ·
            refine ⟨27000633721460466199970251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36000844961947288266627001 27000633721460466199970251)
            ·
              refine ⟨40500950582190699299955377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27000633721460466199970251 40500950582190699299955377)
              ·
                refine ⟨30375712936643024474966533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40500950582190699299955377 30375712936643024474966533)
                ·
                  refine ⟨5695446175620567089056225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30375712936643024474966533 5695446175620567089056225)
                  ·
                    refine ⟨4271584631715425316792169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5695446175620567089056225 4271584631715425316792169)
                    ·
                      refine ⟨3203688473786568987594127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4271584631715425316792169 3203688473786568987594127)
                      ·
                        rfl

theorem cell23_6239161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_6239161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239161 prefixEnd_6239161 := by exact prefixLift 6239161
  have htrace : WordTrace (prefixWord ++ tailWord_6239161) baseStart_6239161 baseEnd_6239161 := by
    simpa [prefixWord, tailWord_6239161, baseEnd_6239161] using wordTrace_append hprefix tailTrace_6239161
  have hstable : (prefixWord ++ tailWord_6239161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239161).length < 2 ^ (prefixWord ++ tailWord_6239161).sum := by decide
  have hdescent : baseEnd_6239161 < baseStart_6239161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239204 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_6239204 : Nat := 118140960795 + 6239204 * 2 ^ 59
def prefixEnd_6239204 : Nat := 4983230072969 + 3 ^ 40 * 6239204 * 2
def baseEnd_6239204 : Nat := 3203710553454712319356429

theorem tailTrace_6239204 : CollatzResearch.WordTrace tailWord_6239204 prefixEnd_6239204 3203710553454712319356429 := by
  unfold tailWord_6239204
  simp only [CollatzResearch.WordTrace]
  refine ⟨113781232444218477026926333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151708309925624636035901777 113781232444218477026926333)
  ·
    refine ⟨42667962166581928885097375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113781232444218477026926333 42667962166581928885097375)
    ·
      refine ⟨64001943249872893327646063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42667962166581928885097375 64001943249872893327646063)
      ·
        refine ⟨96002914874809339991469095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64001943249872893327646063 96002914874809339991469095)
        ·
          refine ⟨144004372312214009987203643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96002914874809339991469095 144004372312214009987203643)
          ·
            refine ⟨216006558468321014980805465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144004372312214009987203643 216006558468321014980805465)
            ·
              refine ⟨162004918851240761235604099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216006558468321014980805465 162004918851240761235604099)
              ·
                refine ⟨243007378276861141853406149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162004918851240761235604099 243007378276861141853406149)
                ·
                  refine ⟨45563883426911464097513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 243007378276861141853406149 45563883426911464097513653)
                  ·
                    refine ⟨4271614071272949759141905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45563883426911464097513653 4271614071272949759141905)
                    ·
                      refine ⟨3203710553454712319356429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4271614071272949759141905 3203710553454712319356429)
                      ·
                        rfl

theorem cell23_6239204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_6239204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239204 prefixEnd_6239204 := by exact prefixLift 6239204
  have htrace : WordTrace (prefixWord ++ tailWord_6239204) baseStart_6239204 baseEnd_6239204 := by
    simpa [prefixWord, tailWord_6239204, baseEnd_6239204] using wordTrace_append hprefix tailTrace_6239204
  have hstable : (prefixWord ++ tailWord_6239204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239204).length < 2 ^ (prefixWord ++ tailWord_6239204).sum := by decide
  have hdescent : baseEnd_6239204 < baseStart_6239204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239237 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_6239237 : Nat := 118140960795 + 6239237 * 2 ^ 59
def prefixEnd_6239237 : Nat := 4983230072969 + 3 ^ 40 * 6239237 * 2
def baseEnd_6239237 : Nat := 3203727498316310690243777

theorem tailTrace_6239237 : CollatzResearch.WordTrace tailWord_6239237 prefixEnd_6239237 3203727498316310690243777 := by
  unfold tailWord_6239237
  simp only [CollatzResearch.WordTrace]
  refine ⟨227563668497317400689803965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151709112331544933793202643 227563668497317400689803965)
  ·
    refine ⟨85336375686494025258676487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227563668497317400689803965 85336375686494025258676487)
    ·
      refine ⟨128004563529741037888014731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85336375686494025258676487 128004563529741037888014731)
      ·
        refine ⟨192006845294611556832022097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128004563529741037888014731 192006845294611556832022097)
        ·
          refine ⟨144005133970958667624016573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192006845294611556832022097 144005133970958667624016573)
          ·
            refine ⟨54001925239109500359006215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144005133970958667624016573 54001925239109500359006215)
            ·
              refine ⟨81002887858664250538509323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54001925239109500359006215 81002887858664250538509323)
              ·
                refine ⟨121504331787996375807763985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81002887858664250538509323 121504331787996375807763985)
                ·
                  refine ⟨91128248840997281855822989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 121504331787996375807763985 91128248840997281855822989)
                  ·
                    refine ⟨34173093315373980695933621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91128248840997281855822989 34173093315373980695933621)
                    ·
                      refine ⟨3203727498316310690243777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34173093315373980695933621 3203727498316310690243777)
                      ·
                        rfl

theorem cell23_6239237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_6239237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239237 prefixEnd_6239237 := by exact prefixLift 6239237
  have htrace : WordTrace (prefixWord ++ tailWord_6239237) baseStart_6239237 baseEnd_6239237 := by
    simpa [prefixWord, tailWord_6239237, baseEnd_6239237] using wordTrace_append hprefix tailTrace_6239237
  have hstable : (prefixWord ++ tailWord_6239237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239237).length < 2 ^ (prefixWord ++ tailWord_6239237).sum := by decide
  have hdescent : baseEnd_6239237 < baseStart_6239237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239268 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6239268 : Nat := 118140960795 + 6239268 * 2 ^ 59
def prefixEnd_6239268 : Nat := 4983230072969 + 3 ^ 40 * 6239268 * 2
def baseEnd_6239268 : Nat := 3203743416216600068956135

theorem tailTrace_6239268 : CollatzResearch.WordTrace tailWord_6239268 prefixEnd_6239268 3203743416216600068956135 := by
  unfold tailWord_6239268
  simp only [CollatzResearch.WordTrace]
  refine ⟨113782399580102546492091229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151709866106803395322788305 113782399580102546492091229)
  ·
    refine ⟨42668399842538454934534211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113782399580102546492091229 42668399842538454934534211)
    ·
      refine ⟨64002599763807682401801317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42668399842538454934534211 64002599763807682401801317)
      ·
        refine ⟨12000487455713940450337747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64002599763807682401801317 12000487455713940450337747)
        ·
          refine ⟨18000731183570910675506621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12000487455713940450337747 18000731183570910675506621)
          ·
            refine ⟨6750274193839091503314983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18000731183570910675506621 6750274193839091503314983)
            ·
              refine ⟨10125411290758637254972475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750274193839091503314983 10125411290758637254972475)
              ·
                refine ⟨15188116936137955882458713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10125411290758637254972475 15188116936137955882458713)
                ·
                  refine ⟨11391087702103466911844035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15188116936137955882458713 11391087702103466911844035)
                  ·
                    refine ⟨17086631553155200367766053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11391087702103466911844035 17086631553155200367766053)
                    ·
                      refine ⟨3203743416216600068956135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17086631553155200367766053 3203743416216600068956135)
                      ·
                        rfl

theorem cell23_6239268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6239268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239268 prefixEnd_6239268 := by exact prefixLift 6239268
  have htrace : WordTrace (prefixWord ++ tailWord_6239268) baseStart_6239268 baseEnd_6239268 := by
    simpa [prefixWord, tailWord_6239268, baseEnd_6239268] using wordTrace_append hprefix tailTrace_6239268
  have hstable : (prefixWord ++ tailWord_6239268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239268).length < 2 ^ (prefixWord ++ tailWord_6239268).sum := by decide
  have hdescent : baseEnd_6239268 < baseStart_6239268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239301 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_6239301 : Nat := 118140960795 + 6239301 * 2 ^ 59
def prefixEnd_6239301 : Nat := 4983230072969 + 3 ^ 40 * 6239301 * 2
def baseEnd_6239301 : Nat := 3203760361078198439843483

theorem tailTrace_6239301 : CollatzResearch.WordTrace tailWord_6239301 prefixEnd_6239301 3203760361078198439843483 := by
  unfold tailWord_6239301
  simp only [CollatzResearch.WordTrace]
  refine ⟨227566002769085539620133757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151710668512723693080089171 227566002769085539620133757)
  ·
    refine ⟨85337251038407077357550159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227566002769085539620133757 85337251038407077357550159)
    ·
      refine ⟨128005876557610616036325239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85337251038407077357550159 128005876557610616036325239)
      ·
        refine ⟨192008814836415924054487859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128005876557610616036325239 192008814836415924054487859)
        ·
          refine ⟨288013222254623886081731789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192008814836415924054487859 288013222254623886081731789)
          ·
            refine ⟨108004958345483957280649421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288013222254623886081731789 108004958345483957280649421)
            ·
              refine ⟨40501859379556483980243533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108004958345483957280649421 40501859379556483980243533)
              ·
                refine ⟨15188197267333681492591325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40501859379556483980243533 15188197267333681492591325)
                ·
                  refine ⟨5695573975250130559721747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15188197267333681492591325 5695573975250130559721747)
                  ·
                    refine ⟨8543360962875195839582621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5695573975250130559721747 8543360962875195839582621)
                    ·
                      refine ⟨3203760361078198439843483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8543360962875195839582621 3203760361078198439843483)
                      ·
                        rfl

theorem cell23_6239301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_6239301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239301 prefixEnd_6239301 := by exact prefixLift 6239301
  have htrace : WordTrace (prefixWord ++ tailWord_6239301) baseStart_6239301 baseEnd_6239301 := by
    simpa [prefixWord, tailWord_6239301, baseEnd_6239301] using wordTrace_append hprefix tailTrace_6239301
  have hstable : (prefixWord ++ tailWord_6239301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239301).length < 2 ^ (prefixWord ++ tailWord_6239301).sum := by decide
  have hdescent : baseEnd_6239301 < baseStart_6239301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239335 : List Nat := [1, 1, 5, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_6239335 : Nat := 118140960795 + 6239335 * 2 ^ 59
def prefixEnd_6239335 : Nat := 4983230072969 + 3 ^ 40 * 6239335 * 2
def baseEnd_6239335 : Nat := 3203777819420451306818327

theorem tailTrace_6239335 : CollatzResearch.WordTrace tailWord_6239335 prefixEnd_6239335 3203777819420451306818327 := by
  unfold tailWord_6239335
  simp only [CollatzResearch.WordTrace]
  refine ⟨227567242850962363426871459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151711495233974908951247639 227567242850962363426871459)
  ·
    refine ⟨341350864276443545140307189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227567242850962363426871459 341350864276443545140307189)
    ·
      refine ⟨32001643525916582356903799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 341350864276443545140307189 32001643525916582356903799)
      ·
        refine ⟨48002465288874873535355699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32001643525916582356903799 48002465288874873535355699)
        ·
          refine ⟨72003697933312310303033549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48002465288874873535355699 72003697933312310303033549)
          ·
            refine ⟨27001386724992116363637581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72003697933312310303033549 27001386724992116363637581)
            ·
              refine ⟨10125520021872043636364093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27001386724992116363637581 10125520021872043636364093)
              ·
                refine ⟨3797070008202016363636535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10125520021872043636364093 3797070008202016363636535)
                ·
                  refine ⟨5695605012303024545454803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797070008202016363636535 5695605012303024545454803)
                  ·
                    refine ⟨8543407518454536818182205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5695605012303024545454803 8543407518454536818182205)
                    ·
                      refine ⟨3203777819420451306818327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8543407518454536818182205 3203777819420451306818327)
                      ·
                        rfl

theorem cell23_6239335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_6239335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239335 prefixEnd_6239335 := by exact prefixLift 6239335
  have htrace : WordTrace (prefixWord ++ tailWord_6239335) baseStart_6239335 baseEnd_6239335 := by
    simpa [prefixWord, tailWord_6239335, baseEnd_6239335] using wordTrace_append hprefix tailTrace_6239335
  have hstable : (prefixWord ++ tailWord_6239335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239335).length < 2 ^ (prefixWord ++ tailWord_6239335).sum := by decide
  have hdescent : baseEnd_6239335 < baseStart_6239335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239351 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 2, 4]
def baseStart_6239351 : Nat := 118140960795 + 6239351 * 2 ^ 59
def prefixEnd_6239351 : Nat := 4983230072969 + 3 ^ 40 * 6239351 * 2
def baseEnd_6239351 : Nat := 1067928678370307748072751

theorem tailTrace_6239351 : CollatzResearch.WordTrace tailWord_6239351 prefixEnd_6239351 1067928678370307748072751 := by
  unfold tailWord_6239351
  simp only [CollatzResearch.WordTrace]
  refine ⟨227567826418904398159453907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151711884279269598772969271 227567826418904398159453907)
  ·
    refine ⟨341351739628356597239180861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227567826418904398159453907 341351739628356597239180861)
    ·
      refine ⟨128006902360633723964692823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341351739628356597239180861 128006902360633723964692823)
      ·
        refine ⟨192010353540950585947039235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128006902360633723964692823 192010353540950585947039235)
        ·
          refine ⟨288015530311425878920558853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192010353540950585947039235 288015530311425878920558853)
          ·
            refine ⟨54002911933392352297604785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288015530311425878920558853 54002911933392352297604785)
            ·
              refine ⟨40502183950044264223203589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54002911933392352297604785 40502183950044264223203589)
              ·
                refine ⟨7594159490633299541850673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40502183950044264223203589 7594159490633299541850673)
                ·
                  refine ⟨5695619617974974656388005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7594159490633299541850673 5695619617974974656388005)
                  ·
                    refine ⟨1067928678370307748072751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5695619617974974656388005 1067928678370307748072751)
                    ·
                      rfl

theorem cell23_6239351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_6239351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239351 prefixEnd_6239351 := by exact prefixLift 6239351
  have htrace : WordTrace (prefixWord ++ tailWord_6239351) baseStart_6239351 baseEnd_6239351 := by
    simpa [prefixWord, tailWord_6239351, baseEnd_6239351] using wordTrace_append hprefix tailTrace_6239351
  have hstable : (prefixWord ++ tailWord_6239351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239351).length < 2 ^ (prefixWord ++ tailWord_6239351).sum := by decide
  have hdescent : baseEnd_6239351 < baseStart_6239351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239361 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_6239361 : Nat := 118140960795 + 6239361 * 2 ^ 59
def prefixEnd_6239361 : Nat := 4983230072969 + 3 ^ 40 * 6239361 * 2
def baseEnd_6239361 : Nat := 3203791169917468205093207

theorem tailTrace_6239361 : CollatzResearch.WordTrace tailWord_6239361 prefixEnd_6239361 3203791169917468205093207 := by
  unfold tailWord_6239361
  simp only [CollatzResearch.WordTrace]
  refine ⟨227568191148868169867317937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151712127432578779911545291 227568191148868169867317937)
  ·
    refine ⟨170676143361651127400488453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227568191148868169867317937 170676143361651127400488453)
    ·
      refine ⟨32001776880309586387591585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170676143361651127400488453 32001776880309586387591585)
      ·
        refine ⟨24001332660232189790693689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32001776880309586387591585 24001332660232189790693689)
        ·
          refine ⟨18000999495174142343020267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24001332660232189790693689 18000999495174142343020267)
          ·
            refine ⟨27001499242761213514530401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18000999495174142343020267 27001499242761213514530401)
            ·
              refine ⟨20251124432070910135897801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27001499242761213514530401 20251124432070910135897801)
              ·
                refine ⟨15188343324053182601923351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20251124432070910135897801 15188343324053182601923351)
                ·
                  refine ⟨22782514986079773902885027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15188343324053182601923351 22782514986079773902885027)
                  ·
                    refine ⟨34173772479119660854327541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22782514986079773902885027 34173772479119660854327541)
                    ·
                      refine ⟨3203791169917468205093207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34173772479119660854327541 3203791169917468205093207)
                      ·
                        rfl

theorem cell23_6239361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_6239361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239361 prefixEnd_6239361 := by exact prefixLift 6239361
  have htrace : WordTrace (prefixWord ++ tailWord_6239361) baseStart_6239361 baseEnd_6239361 := by
    simpa [prefixWord, tailWord_6239361, baseEnd_6239361] using wordTrace_append hprefix tailTrace_6239361
  have hstable : (prefixWord ++ tailWord_6239361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239361).length < 2 ^ (prefixWord ++ tailWord_6239361).sum := by decide
  have hdescent : baseEnd_6239361 < baseStart_6239361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239364 : List Nat := [2, 3, 2, 1, 2, 2, 1, 10]
def baseStart_6239364 : Nat := 118140960795 + 6239364 * 2 ^ 59
def prefixEnd_6239364 : Nat := 4983230072969 + 3 ^ 40 * 6239364 * 2
def baseEnd_6239364 : Nat := 118658989272571544198359

theorem tailTrace_6239364 : CollatzResearch.WordTrace tailWord_6239364 prefixEnd_6239364 118658989272571544198359 := by
  unfold tailWord_6239364
  simp only [CollatzResearch.WordTrace]
  refine ⟨113784150283928650689838573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151712200378571534253118097 113784150283928650689838573)
  ·
    refine ⟨42669056356473244008689465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113784150283928650689838573 42669056356473244008689465)
    ·
      refine ⟨32001792267354933006517099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42669056356473244008689465 32001792267354933006517099)
      ·
        refine ⟨48002688401032399509775649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32001792267354933006517099 48002688401032399509775649)
        ·
          refine ⟨36002016300774299632331737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48002688401032399509775649 36002016300774299632331737)
          ·
            refine ⟨27001512225580724724248803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36002016300774299632331737 27001512225580724724248803)
            ·
              refine ⟨40502268338371087086373205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27001512225580724724248803 40502268338371087086373205)
              ·
                refine ⟨118658989272571544198359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40502268338371087086373205 118658989272571544198359)
                ·
                  rfl

theorem cell23_6239364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 10].length) (baseStart_6239364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239364 prefixEnd_6239364 := by exact prefixLift 6239364
  have htrace : WordTrace (prefixWord ++ tailWord_6239364) baseStart_6239364 baseEnd_6239364 := by
    simpa [prefixWord, tailWord_6239364, baseEnd_6239364] using wordTrace_append hprefix tailTrace_6239364
  have hstable : (prefixWord ++ tailWord_6239364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239364).length < 2 ^ (prefixWord ++ tailWord_6239364).sum := by decide
  have hdescent : baseEnd_6239364 < baseStart_6239364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239378 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_6239378 : Nat := 118140960795 + 6239378 * 2 ^ 59
def prefixEnd_6239378 : Nat := 4983230072969 + 3 ^ 40 * 6239378 * 2
def baseEnd_6239378 : Nat := 3203799899088594638580629

theorem tailTrace_6239378 : CollatzResearch.WordTrace tailWord_6239378 prefixEnd_6239378 3203799899088594638580629 := by
  unfold tailWord_6239378
  simp only [CollatzResearch.WordTrace]
  refine ⟨56892202797451645442671697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151712540793204387847124525 56892202797451645442671697)
  ·
    refine ⟨42669152098088734082003773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56892202797451645442671697 42669152098088734082003773)
    ·
      refine ⟨16000932036783275280751415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42669152098088734082003773 16000932036783275280751415)
      ·
        refine ⟨24001398055174912921127123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16000932036783275280751415 24001398055174912921127123)
        ·
          refine ⟨36002097082762369381690685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24001398055174912921127123 36002097082762369381690685)
          ·
            refine ⟨13500786406035888518134007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36002097082762369381690685 13500786406035888518134007)
            ·
              refine ⟨20251179609053832777201011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13500786406035888518134007 20251179609053832777201011)
              ·
                refine ⟨30376769413580749165801517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20251179609053832777201011 30376769413580749165801517)
                ·
                  refine ⟨11391288530092780937175569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30376769413580749165801517 11391288530092780937175569)
                  ·
                    refine ⟨8543466397569585702881677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11391288530092780937175569 8543466397569585702881677)
                    ·
                      refine ⟨3203799899088594638580629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8543466397569585702881677 3203799899088594638580629)
                      ·
                        rfl

theorem cell23_6239378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_6239378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239378 prefixEnd_6239378 := by exact prefixLift 6239378
  have htrace : WordTrace (prefixWord ++ tailWord_6239378) baseStart_6239378 baseEnd_6239378 := by
    simpa [prefixWord, tailWord_6239378, baseEnd_6239378] using wordTrace_append hprefix tailTrace_6239378
  have hstable : (prefixWord ++ tailWord_6239378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239378).length < 2 ^ (prefixWord ++ tailWord_6239378).sum := by decide
  have hdescent : baseEnd_6239378 < baseStart_6239378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239409 : List Nat := [1, 2, 2, 5, 1, 1, 4, 2, 1, 2, 2]
def baseStart_6239409 : Nat := 118140960795 + 6239409 * 2 ^ 59
def prefixEnd_6239409 : Nat := 4983230072969 + 3 ^ 40 * 6239409 * 2
def baseEnd_6239409 : Nat := 3203815816988884017292987

theorem tailTrace_6239409 : CollatzResearch.WordTrace tailWord_6239409 prefixEnd_6239409 3203815816988884017292987 := by
  unfold tailWord_6239409
  simp only [CollatzResearch.WordTrace]
  refine ⟨227569941852694274065065281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151713294568462849376710187 227569941852694274065065281)
  ·
    refine ⟨170677456389520705548798961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227569941852694274065065281 170677456389520705548798961)
    ·
      refine ⟨128008092292140529161599221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170677456389520705548798961 128008092292140529161599221)
      ·
        refine ⟨12000758652388174608899927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128008092292140529161599221 12000758652388174608899927)
        ·
          refine ⟨18001137978582261913349891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12000758652388174608899927 18001137978582261913349891)
          ·
            refine ⟨27001706967873392870024837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18001137978582261913349891 27001706967873392870024837)
            ·
              refine ⟨5062820056476261163129657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27001706967873392870024837 5062820056476261163129657)
              ·
                refine ⟨3797115042357195872347243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5062820056476261163129657 3797115042357195872347243)
                ·
                  refine ⟨5695672563535793808520865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3797115042357195872347243 5695672563535793808520865)
                  ·
                    refine ⟨4271754422651845356390649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5695672563535793808520865 4271754422651845356390649)
                    ·
                      refine ⟨3203815816988884017292987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4271754422651845356390649 3203815816988884017292987)
                      ·
                        rfl

theorem cell23_6239409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_6239409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239409 prefixEnd_6239409 := by exact prefixLift 6239409
  have htrace : WordTrace (prefixWord ++ tailWord_6239409) baseStart_6239409 baseEnd_6239409 := by
    simpa [prefixWord, tailWord_6239409, baseEnd_6239409] using wordTrace_append hprefix tailTrace_6239409
  have hstable : (prefixWord ++ tailWord_6239409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239409).length < 2 ^ (prefixWord ++ tailWord_6239409).sum := by decide
  have hdescent : baseEnd_6239409 < baseStart_6239409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239425 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6239425 : Nat := 118140960795 + 6239425 * 2 ^ 59
def prefixEnd_6239425 : Nat := 4983230072969 + 3 ^ 40 * 6239425 * 2
def baseEnd_6239425 : Nat := 3203824032679355954692913

theorem tailTrace_6239425 : CollatzResearch.WordTrace tailWord_6239425 prefixEnd_6239425 3203824032679355954692913 := by
  unfold tailWord_6239425
  simp only [CollatzResearch.WordTrace]
  refine ⟨227570525420636308797647729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151713683613757539198431819 227570525420636308797647729)
  ·
    refine ⟨170677894065477231598235797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227570525420636308797647729 170677894065477231598235797)
    ·
      refine ⟨8000526284319245231167303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 170677894065477231598235797 8000526284319245231167303)
      ·
        refine ⟨12000789426478867846750955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8000526284319245231167303 12000789426478867846750955)
        ·
          refine ⟨18001184139718301770126433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12000789426478867846750955 18001184139718301770126433)
          ·
            refine ⟨13500888104788726327594825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18001184139718301770126433 13500888104788726327594825)
            ·
              refine ⟨10125666078591544745696119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13500888104788726327594825 10125666078591544745696119)
              ·
                refine ⟨15188499117887317118544179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10125666078591544745696119 15188499117887317118544179)
                ·
                  refine ⟨22782748676830975677816269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15188499117887317118544179 22782748676830975677816269)
                  ·
                    refine ⟨8543530753811615879181101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22782748676830975677816269 8543530753811615879181101)
                    ·
                      refine ⟨3203824032679355954692913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8543530753811615879181101 3203824032679355954692913)
                      ·
                        rfl

theorem cell23_6239425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6239425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239425 prefixEnd_6239425 := by exact prefixLift 6239425
  have htrace : WordTrace (prefixWord ++ tailWord_6239425) baseStart_6239425 baseEnd_6239425 := by
    simpa [prefixWord, tailWord_6239425, baseEnd_6239425] using wordTrace_append hprefix tailTrace_6239425
  have hstable : (prefixWord ++ tailWord_6239425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239425).length < 2 ^ (prefixWord ++ tailWord_6239425).sum := by decide
  have hdescent : baseEnd_6239425 < baseStart_6239425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239446 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_6239446 : Nat := 118140960795 + 6239446 * 2 ^ 59
def prefixEnd_6239446 : Nat := 4983230072969 + 3 ^ 40 * 6239446 * 2
def baseEnd_6239446 : Nat := 3203834815773100372530317

theorem tailTrace_6239446 : CollatzResearch.WordTrace tailWord_6239446 prefixEnd_6239446 3203834815773100372530317 := by
  unfold tailWord_6239446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223205709597514336510137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151714194235706819589441461 14223205709597514336510137)
  ·
    refine ⟨10667404282198135752382603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14223205709597514336510137 10667404282198135752382603)
    ·
      refine ⟨16001106423297203628573905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10667404282198135752382603 16001106423297203628573905)
      ·
        refine ⟨12000829817472902721430429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16001106423297203628573905 12000829817472902721430429)
        ·
          refine ⟨4500311181552338520536411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12000829817472902721430429 4500311181552338520536411)
          ·
            refine ⟨6750466772328507780804617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500311181552338520536411 6750466772328507780804617)
            ·
              refine ⟨5062850079246380835603463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6750466772328507780804617 5062850079246380835603463)
              ·
                refine ⟨7594275118869571253405195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5062850079246380835603463 7594275118869571253405195)
                ·
                  refine ⟨11391412678304356880107793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7594275118869571253405195 11391412678304356880107793)
                  ·
                    refine ⟨8543559508728267660080845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11391412678304356880107793 8543559508728267660080845)
                    ·
                      refine ⟨3203834815773100372530317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8543559508728267660080845 3203834815773100372530317)
                      ·
                        rfl

theorem cell23_6239446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_6239446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239446 prefixEnd_6239446 := by exact prefixLift 6239446
  have htrace : WordTrace (prefixWord ++ tailWord_6239446) baseStart_6239446 baseEnd_6239446 := by
    simpa [prefixWord, tailWord_6239446, baseEnd_6239446] using wordTrace_append hprefix tailTrace_6239446
  have hstable : (prefixWord ++ tailWord_6239446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239446).length < 2 ^ (prefixWord ++ tailWord_6239446).sum := by decide
  have hdescent : baseEnd_6239446 < baseStart_6239446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239476 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6239476 : Nat := 118140960795 + 6239476 * 2 ^ 59
def prefixEnd_6239476 : Nat := 4983230072969 + 3 ^ 40 * 6239476 * 2
def baseEnd_6239476 : Nat := 3203850220192735255155179

theorem tailTrace_6239476 : CollatzResearch.WordTrace tailWord_6239476 prefixEnd_6239476 3203850220192735255155179 := by
  unfold tailWord_6239476
  simp only [CollatzResearch.WordTrace]
  refine ⟨113786192771725772253877141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151714923695634363005169521 113786192771725772253877141)
  ·
    refine ⟨5333727786174645574400491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113786192771725772253877141 5333727786174645574400491)
    ·
      refine ⟨8000591679261968361600737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5333727786174645574400491 8000591679261968361600737)
      ·
        refine ⟨6000443759446476271200553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8000591679261968361600737 6000443759446476271200553)
        ·
          refine ⟨4500332819584857203400415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6000443759446476271200553 4500332819584857203400415)
          ·
            refine ⟨6750499229377285805100623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4500332819584857203400415 6750499229377285805100623)
            ·
              refine ⟨10125748844065928707650935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750499229377285805100623 10125748844065928707650935)
              ·
                refine ⟨15188623266098893061476403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10125748844065928707650935 15188623266098893061476403)
                ·
                  refine ⟨22782934899148339592214605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15188623266098893061476403 22782934899148339592214605)
                  ·
                    refine ⟨8543600587180627347080477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22782934899148339592214605 8543600587180627347080477)
                    ·
                      refine ⟨3203850220192735255155179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8543600587180627347080477 3203850220192735255155179)
                      ·
                        rfl

theorem cell23_6239476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6239476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239476 prefixEnd_6239476 := by exact prefixLift 6239476
  have htrace : WordTrace (prefixWord ++ tailWord_6239476) baseStart_6239476 baseEnd_6239476 := by
    simpa [prefixWord, tailWord_6239476, baseEnd_6239476] using wordTrace_append hprefix tailTrace_6239476
  have hstable : (prefixWord ++ tailWord_6239476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239476).length < 2 ^ (prefixWord ++ tailWord_6239476).sum := by decide
  have hdescent : baseEnd_6239476 < baseStart_6239476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239481 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 3]
def baseStart_6239481 : Nat := 118140960795 + 6239481 * 2 ^ 59
def prefixEnd_6239481 : Nat := 4983230072969 + 3 ^ 40 * 6239481 * 2
def baseEnd_6239481 : Nat := 3203852787596007735592655

theorem tailTrace_6239481 : CollatzResearch.WordTrace tailWord_6239481 prefixEnd_6239481 3203852787596007735592655 := by
  unfold tailWord_6239481
  simp only [CollatzResearch.WordTrace]
  refine ⟨227572567908433430361686297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151715045272288953574457531 227572567908433430361686297)
  ·
    refine ⟨170679425931325072771264723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227572567908433430361686297 170679425931325072771264723)
    ·
      refine ⟨256019138896987609156897085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170679425931325072771264723 256019138896987609156897085)
      ·
        refine ⟨96007177086370353433836407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256019138896987609156897085 96007177086370353433836407)
        ·
          refine ⟨144010765629555530150754611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96007177086370353433836407 144010765629555530150754611)
          ·
            refine ⟨216016148444333295226131917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144010765629555530150754611 216016148444333295226131917)
            ·
              refine ⟨81006055666624985709799469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216016148444333295226131917 81006055666624985709799469)
              ·
                refine ⟨30377270874984369641174801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81006055666624985709799469 30377270874984369641174801)
                ·
                  refine ⟨22782953156238277230881101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30377270874984369641174801 22782953156238277230881101)
                  ·
                    refine ⟨8543607433589353961580413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22782953156238277230881101 8543607433589353961580413)
                    ·
                      refine ⟨3203852787596007735592655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8543607433589353961580413 3203852787596007735592655)
                      ·
                        rfl

theorem cell23_6239481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_6239481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239481 prefixEnd_6239481 := by exact prefixLift 6239481
  have htrace : WordTrace (prefixWord ++ tailWord_6239481) baseStart_6239481 baseEnd_6239481 := by
    simpa [prefixWord, tailWord_6239481, baseEnd_6239481] using wordTrace_append hprefix tailTrace_6239481
  have hstable : (prefixWord ++ tailWord_6239481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239481).length < 2 ^ (prefixWord ++ tailWord_6239481).sum := by decide
  have hdescent : baseEnd_6239481 < baseStart_6239481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239482 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2]
def baseStart_6239482 : Nat := 118140960795 + 6239482 * 2 ^ 59
def prefixEnd_6239482 : Nat := 4983230072969 + 3 ^ 40 * 6239482 * 2
def baseEnd_6239482 : Nat := 3203853301076662231680151

theorem tailTrace_6239482 : CollatzResearch.WordTrace tailWord_6239482 prefixEnd_6239482 3203853301076662231680151 := by
  unfold tailWord_6239482
  simp only [CollatzResearch.WordTrace]
  refine ⟨56893151095357451883118175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151715069587619871688315133 56893151095357451883118175)
  ·
    refine ⟨85339726643036177824677263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56893151095357451883118175 85339726643036177824677263)
    ·
      refine ⟨128009589964554266737015895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85339726643036177824677263 128009589964554266737015895)
      ·
        refine ⟨192014384946831400105523843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128009589964554266737015895 192014384946831400105523843)
        ·
          refine ⟨288021577420247100158285765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192014384946831400105523843 288021577420247100158285765)
          ·
            refine ⟨54004045766296331279678581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 288021577420247100158285765 54004045766296331279678581)
            ·
              refine ⟨5062879290590281057469867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54004045766296331279678581 5062879290590281057469867)
              ·
                refine ⟨7594318935885421586204801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5062879290590281057469867 7594318935885421586204801)
                ·
                  refine ⟨5695739201914066189653601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7594318935885421586204801 5695739201914066189653601)
                  ·
                    refine ⟨4271804401435549642240201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5695739201914066189653601 4271804401435549642240201)
                    ·
                      refine ⟨3203853301076662231680151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4271804401435549642240201 3203853301076662231680151)
                      ·
                        rfl

theorem cell23_6239482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_6239482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239482 prefixEnd_6239482 := by exact prefixLift 6239482
  have htrace : WordTrace (prefixWord ++ tailWord_6239482) baseStart_6239482 baseEnd_6239482 := by
    simpa [prefixWord, tailWord_6239482, baseEnd_6239482] using wordTrace_append hprefix tailTrace_6239482
  have hstable : (prefixWord ++ tailWord_6239482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239482).length < 2 ^ (prefixWord ++ tailWord_6239482).sum := by decide
  have hdescent : baseEnd_6239482 < baseStart_6239482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239504 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_6239504 : Nat := 118140960795 + 6239504 * 2 ^ 59
def prefixEnd_6239504 : Nat := 4983230072969 + 3 ^ 40 * 6239504 * 2
def baseEnd_6239504 : Nat := 3203864597651061145605049

theorem tailTrace_6239504 : CollatzResearch.WordTrace tailWord_6239504 prefixEnd_6239504 3203864597651061145605049 := by
  unfold tailWord_6239504
  simp only [CollatzResearch.WordTrace]
  refine ⟨113786703393675052644886783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151715604524900070193182377 113786703393675052644886783)
  ·
    refine ⟨170680055090512578967330175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113786703393675052644886783 170680055090512578967330175)
    ·
      refine ⟨256020082635768868450995263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170680055090512578967330175 256020082635768868450995263)
      ·
        refine ⟨384030123953653302676492895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256020082635768868450995263 384030123953653302676492895)
        ·
          refine ⟨576045185930479954014739343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384030123953653302676492895 576045185930479954014739343)
          ·
            refine ⟨864067778895719931022109015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576045185930479954014739343 864067778895719931022109015)
            ·
              refine ⟨1296101668343579896533163523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864067778895719931022109015 1296101668343579896533163523)
              ·
                refine ⟨1944152502515369844799745285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296101668343579896533163523 1944152502515369844799745285)
                ·
                  refine ⟨364528594221631845899952241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944152502515369844799745285 364528594221631845899952241)
                  ·
                    refine ⟨273396445666223884424964181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 364528594221631845899952241 273396445666223884424964181)
                    ·
                      refine ⟨3203864597651061145605049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 273396445666223884424964181 3203864597651061145605049)
                      ·
                        rfl

theorem cell23_6239504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_6239504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239504 prefixEnd_6239504 := by exact prefixLift 6239504
  have htrace : WordTrace (prefixWord ++ tailWord_6239504) baseStart_6239504 baseEnd_6239504 := by
    simpa [prefixWord, tailWord_6239504, baseEnd_6239504] using wordTrace_append hprefix tailTrace_6239504
  have hstable : (prefixWord ++ tailWord_6239504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239504).length < 2 ^ (prefixWord ++ tailWord_6239504).sum := by decide
  have hdescent : baseEnd_6239504 < baseStart_6239504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239511 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6239511 : Nat := 118140960795 + 6239511 * 2 ^ 59
def prefixEnd_6239511 : Nat := 4983230072969 + 3 ^ 40 * 6239511 * 2
def baseEnd_6239511 : Nat := 3203868192015642618217517

theorem tailTrace_6239511 : CollatzResearch.WordTrace tailWord_6239511 prefixEnd_6239511 3203868192015642618217517 := by
  unfold tailWord_6239511
  simp only [CollatzResearch.WordTrace]
  refine ⟨227573662098324745485278387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151715774732216496990185591 227573662098324745485278387)
  ·
    refine ⟨341360493147487118227917581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227573662098324745485278387 341360493147487118227917581)
    ·
      refine ⟨128010184930307669335469093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 341360493147487118227917581 128010184930307669335469093)
      ·
        refine ⟨24001909674432688000400455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128010184930307669335469093 24001909674432688000400455)
        ·
          refine ⟨36002864511649032000600683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24001909674432688000400455 36002864511649032000600683)
          ·
            refine ⟨54004296767473548000901025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36002864511649032000600683 54004296767473548000901025)
            ·
              refine ⟨40503222575605161000675769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54004296767473548000901025 40503222575605161000675769)
              ·
                refine ⟨30377416931703870750506827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40503222575605161000675769 30377416931703870750506827)
                ·
                  refine ⟨45566125397555806125760241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30377416931703870750506827 45566125397555806125760241)
                  ·
                    refine ⟨34174594048166854594320181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45566125397555806125760241 34174594048166854594320181)
                    ·
                      refine ⟨3203868192015642618217517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34174594048166854594320181 3203868192015642618217517)
                      ·
                        rfl

theorem cell23_6239511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6239511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239511 prefixEnd_6239511 := by exact prefixLift 6239511
  have htrace : WordTrace (prefixWord ++ tailWord_6239511) baseStart_6239511 baseEnd_6239511 := by
    simpa [prefixWord, tailWord_6239511, baseEnd_6239511] using wordTrace_append hprefix tailTrace_6239511
  have hstable : (prefixWord ++ tailWord_6239511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239511).length < 2 ^ (prefixWord ++ tailWord_6239511).sum := by decide
  have hdescent : baseEnd_6239511 < baseStart_6239511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239522 : List Nat := [3, 3, 1, 1, 4, 1, 3, 2, 5]
def baseStart_6239522 : Nat := 118140960795 + 6239522 * 2 ^ 59
def prefixEnd_6239522 : Nat := 4983230072969 + 3 ^ 40 * 6239522 * 2
def baseEnd_6239522 : Nat := 355985982255871341686663

theorem tailTrace_6239522 : CollatzResearch.WordTrace tailWord_6239522 prefixEnd_6239522 355985982255871341686663 := by
  unfold tailWord_6239522
  simp only [CollatzResearch.WordTrace]
  refine ⟨56893515825321223590982205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151716042200856596242619213 56893515825321223590982205)
  ·
    refine ⟨21335068434495458846618327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56893515825321223590982205 21335068434495458846618327)
    ·
      refine ⟨32002602651743188269927491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21335068434495458846618327 32002602651743188269927491)
      ·
        refine ⟨48003903977614782404891237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32002602651743188269927491 48003903977614782404891237)
        ·
          refine ⟨9000731995802771700917107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48003903977614782404891237 9000731995802771700917107)
          ·
            refine ⟨13501097993704157551375661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9000731995802771700917107 13501097993704157551375661)
            ·
              refine ⟨5062911747639059081765873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13501097993704157551375661 5062911747639059081765873)
              ·
                refine ⟨3797183810729294311324405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5062911747639059081765873 3797183810729294311324405)
                ·
                  refine ⟨355985982255871341686663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3797183810729294311324405 355985982255871341686663)
                  ·
                    rfl

theorem cell23_6239522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_6239522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239522 prefixEnd_6239522 := by exact prefixLift 6239522
  have htrace : WordTrace (prefixWord ++ tailWord_6239522) baseStart_6239522 baseEnd_6239522 := by
    simpa [prefixWord, tailWord_6239522, baseEnd_6239522] using wordTrace_append hprefix tailTrace_6239522
  have hstable : (prefixWord ++ tailWord_6239522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239522).length < 2 ^ (prefixWord ++ tailWord_6239522).sum := by decide
  have hdescent : baseEnd_6239522 < baseStart_6239522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239528 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6239528 : Nat := 118140960795 + 6239528 * 2 ^ 59
def prefixEnd_6239528 : Nat := 4983230072969 + 3 ^ 40 * 6239528 * 2
def baseEnd_6239528 : Nat := 3203876921186769051704939

theorem tailTrace_6239528 : CollatzResearch.WordTrace tailWord_6239528 prefixEnd_6239528 3203876921186769051704939 := by
  unfold tailWord_6239528
  simp only [CollatzResearch.WordTrace]
  refine ⟨113787141069631578694323619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151716188092842104925764825 113787141069631578694323619)
  ·
    refine ⟨170680711604447368041485429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113787141069631578694323619 170680711604447368041485429)
    ·
      refine ⟨16001316712916940753889259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 170680711604447368041485429 16001316712916940753889259)
      ·
        refine ⟨24001975069375411130833889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16001316712916940753889259 24001975069375411130833889)
        ·
          refine ⟨18001481302031558348125417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24001975069375411130833889 18001481302031558348125417)
          ·
            refine ⟨13501110976523668761094063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18001481302031558348125417 13501110976523668761094063)
            ·
              refine ⟨20251666464785503141641095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13501110976523668761094063 20251666464785503141641095)
              ·
                refine ⟨30377499697178254712461643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20251666464785503141641095 30377499697178254712461643)
                ·
                  refine ⟨45566249545767382068692465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30377499697178254712461643 45566249545767382068692465)
                  ·
                    refine ⟨34174687159325536551519349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45566249545767382068692465 34174687159325536551519349)
                    ·
                      refine ⟨3203876921186769051704939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34174687159325536551519349 3203876921186769051704939)
                      ·
                        rfl

theorem cell23_6239528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6239528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239528 prefixEnd_6239528 := by exact prefixLift 6239528
  have htrace : WordTrace (prefixWord ++ tailWord_6239528) baseStart_6239528 baseEnd_6239528 := by
    simpa [prefixWord, tailWord_6239528, baseEnd_6239528] using wordTrace_append hprefix tailTrace_6239528
  have hstable : (prefixWord ++ tailWord_6239528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239528).length < 2 ^ (prefixWord ++ tailWord_6239528).sum := by decide
  have hdescent : baseEnd_6239528 < baseStart_6239528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239531 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 9, 4]
def baseStart_6239531 : Nat := 118140960795 + 6239531 * 2 ^ 59
def prefixEnd_6239531 : Nat := 4983230072969 + 3 ^ 40 * 6239531 * 2
def baseEnd_6239531 : Nat := 1067959487209577513322475

theorem tailTrace_6239531 : CollatzResearch.WordTrace tailWord_6239531 prefixEnd_6239531 1067959487209577513322475 := by
  unfold tailWord_6239531
  simp only [CollatzResearch.WordTrace]
  refine ⟨227574391558252288901006447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151716261038834859267337631 227574391558252288901006447)
  ·
    refine ⟨341361587337378433351509671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227574391558252288901006447 341361587337378433351509671)
    ·
      refine ⟨512042381006067650027264507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341361587337378433351509671 512042381006067650027264507)
      ·
        refine ⟨768063571509101475040896761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512042381006067650027264507 768063571509101475040896761)
        ·
          refine ⟨576047678631826106280672571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768063571509101475040896761 576047678631826106280672571)
          ·
            refine ⟨864071517947739159421008857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576047678631826106280672571 864071517947739159421008857)
            ·
              refine ⟨648053638460804369565756643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864071517947739159421008857 648053638460804369565756643)
              ·
                refine ⟨972080457691206554348634965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648053638460804369565756643 972080457691206554348634965)
                ·
                  refine ⟨5695783931784413404386533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 972080457691206554348634965 5695783931784413404386533)
                  ·
                    refine ⟨1067959487209577513322475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5695783931784413404386533 1067959487209577513322475)
                    ·
                      rfl

theorem cell23_6239531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 4].length) (baseStart_6239531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239531 prefixEnd_6239531 := by exact prefixLift 6239531
  have htrace : WordTrace (prefixWord ++ tailWord_6239531) baseStart_6239531 baseEnd_6239531 := by
    simpa [prefixWord, tailWord_6239531, baseEnd_6239531] using wordTrace_append hprefix tailTrace_6239531
  have hstable : (prefixWord ++ tailWord_6239531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239531).length < 2 ^ (prefixWord ++ tailWord_6239531).sum := by decide
  have hdescent : baseEnd_6239531 < baseStart_6239531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239625 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 1, 5]
def baseStart_6239625 : Nat := 118140960795 + 6239625 * 2 ^ 59
def prefixEnd_6239625 : Nat := 4983230072969 + 3 ^ 40 * 6239625 * 2
def baseEnd_6239625 : Nat := 1067975576270085057397331

theorem tailTrace_6239625 : CollatzResearch.WordTrace tailWord_6239625 prefixEnd_6239625 1067975576270085057397331 := by
  unfold tailWord_6239625
  simp only [CollatzResearch.WordTrace]
  refine ⟨227577820019911742954928329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151718546679941161969952219 227577820019911742954928329)
  ·
    refine ⟨170683365014933807216196247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227577820019911742954928329 170683365014933807216196247)
    ·
      refine ⟨256025047522400710824294371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170683365014933807216196247 256025047522400710824294371)
      ·
        refine ⟨384037571283601066236441557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256025047522400710824294371 384037571283601066236441557)
        ·
          refine ⟨9000880576959399989916599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 384037571283601066236441557 9000880576959399989916599)
          ·
            refine ⟨13501320865439099984874899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9000880576959399989916599 13501320865439099984874899)
            ·
              refine ⟨20251981298158649977312349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13501320865439099984874899 20251981298158649977312349)
              ·
                refine ⟨7594492986809493741492131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20251981298158649977312349 7594492986809493741492131)
                ·
                  refine ⟨11391739480214240612238197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7594492986809493741492131 11391739480214240612238197)
                  ·
                    refine ⟨1067975576270085057397331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11391739480214240612238197 1067975576270085057397331)
                    ·
                      rfl

theorem cell23_6239625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_6239625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239625 prefixEnd_6239625 := by exact prefixLift 6239625
  have htrace : WordTrace (prefixWord ++ tailWord_6239625) baseStart_6239625 baseEnd_6239625 := by
    simpa [prefixWord, tailWord_6239625, baseEnd_6239625] using wordTrace_append hprefix tailTrace_6239625
  have hstable : (prefixWord ++ tailWord_6239625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239625).length < 2 ^ (prefixWord ++ tailWord_6239625).sum := by decide
  have hdescent : baseEnd_6239625 < baseStart_6239625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239648 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_6239648 : Nat := 118140960795 + 6239648 * 2 ^ 59
def prefixEnd_6239648 : Nat := 4983230072969 + 3 ^ 40 * 6239648 * 2
def baseEnd_6239648 : Nat := 3203938538865308582204387

theorem tailTrace_6239648 : CollatzResearch.WordTrace tailWord_6239648 prefixEnd_6239648 3203938538865308582204387 := by
  unfold tailWord_6239648
  simp only [CollatzResearch.WordTrace]
  refine ⟨113789329449414208941507799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151719105932552278588677065 113789329449414208941507799)
  ·
    refine ⟨170683994174121313412261699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113789329449414208941507799 170683994174121313412261699)
    ·
      refine ⟨256025991261181970118392549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170683994174121313412261699 256025991261181970118392549)
      ·
        refine ⟨48004873361471619397198603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 256025991261181970118392549 48004873361471619397198603)
        ·
          refine ⟨72007310042207429095797905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48004873361471619397198603 72007310042207429095797905)
          ·
            refine ⟨54005482531655571821848429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72007310042207429095797905 54005482531655571821848429)
            ·
              refine ⟨20252055949370839433193161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54005482531655571821848429 20252055949370839433193161)
              ·
                refine ⟨15189041962028129574894871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20252055949370839433193161 15189041962028129574894871)
                ·
                  refine ⟨22783562943042194362342307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15189041962028129574894871 22783562943042194362342307)
                  ·
                    refine ⟨34175344414563291543513461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22783562943042194362342307 34175344414563291543513461)
                    ·
                      refine ⟨3203938538865308582204387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34175344414563291543513461 3203938538865308582204387)
                      ·
                        rfl

theorem cell23_6239648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_6239648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239648 prefixEnd_6239648 := by exact prefixLift 6239648
  have htrace : WordTrace (prefixWord ++ tailWord_6239648) baseStart_6239648 baseEnd_6239648 := by
    simpa [prefixWord, tailWord_6239648, baseEnd_6239648] using wordTrace_append hprefix tailTrace_6239648
  have hstable : (prefixWord ++ tailWord_6239648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239648).length < 2 ^ (prefixWord ++ tailWord_6239648).sum := by decide
  have hdescent : baseEnd_6239648 < baseStart_6239648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239651 : List Nat := [1, 1, 1, 4, 1, 3, 2, 10]
def baseStart_6239651 : Nat := 118140960795 + 6239651 * 2 ^ 59
def prefixEnd_6239651 : Nat := 4983230072969 + 3 ^ 40 * 6239651 * 2
def baseEnd_6239651 : Nat := 118664447381750817424699

theorem tailTrace_6239651 : CollatzResearch.WordTrace tailWord_6239651 prefixEnd_6239651 118664447381750817424699 := by
  unfold tailWord_6239651
  simp only [CollatzResearch.WordTrace]
  refine ⟨227578768317817549395374807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151719178878545032930249871 227578768317817549395374807)
  ·
    refine ⟨341368152476726324093062211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227578768317817549395374807 341368152476726324093062211)
    ·
      refine ⟨512052228715089486139593317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341368152476726324093062211 512052228715089486139593317)
      ·
        refine ⟨96009792884079278651173747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 512052228715089486139593317 96009792884079278651173747)
        ·
          refine ⟨144014689326118917976760621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96009792884079278651173747 144014689326118917976760621)
          ·
            refine ⟨54005508497294594241285233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144014689326118917976760621 54005508497294594241285233)
            ·
              refine ⟨40504131372970945680963925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54005508497294594241285233 40504131372970945680963925)
              ·
                refine ⟨118664447381750817424699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40504131372970945680963925 118664447381750817424699)
                ·
                  rfl

theorem cell23_6239651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 10].length) (baseStart_6239651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239651 prefixEnd_6239651 := by exact prefixLift 6239651
  have htrace : WordTrace (prefixWord ++ tailWord_6239651) baseStart_6239651 baseEnd_6239651 := by
    simpa [prefixWord, tailWord_6239651, baseEnd_6239651] using wordTrace_append hprefix tailTrace_6239651
  have hstable : (prefixWord ++ tailWord_6239651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239651).length < 2 ^ (prefixWord ++ tailWord_6239651).sum := by decide
  have hdescent : baseEnd_6239651 < baseStart_6239651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239695 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 3]
def baseStart_6239695 : Nat := 118140960795 + 6239695 * 2 ^ 59
def prefixEnd_6239695 : Nat := 4983230072969 + 3 ^ 40 * 6239695 * 2
def baseEnd_6239695 : Nat := 3203962672456069898316671

theorem tailTrace_6239695 : CollatzResearch.WordTrace tailWord_6239695 prefixEnd_6239695 3203962672456069898316671 := by
  unfold tailWord_6239695
  simp only [CollatzResearch.WordTrace]
  refine ⟨227580373129658144909976539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151720248753105429939984359 227580373129658144909976539)
  ·
    refine ⟨341370559694487217364964809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227580373129658144909976539 341370559694487217364964809)
    ·
      refine ⟨256027919770865413023723607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341370559694487217364964809 256027919770865413023723607)
      ·
        refine ⟨384041879656298119535585411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256027919770865413023723607 384041879656298119535585411)
        ·
          refine ⟨576062819484447179303378117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384041879656298119535585411 576062819484447179303378117)
          ·
            refine ⟨108011778653333846119383397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 576062819484447179303378117 108011778653333846119383397)
            ·
              refine ⟨20252208497500096147384387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108011778653333846119383397 20252208497500096147384387)
              ·
                refine ⟨30378312746250144221076581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20252208497500096147384387 30378312746250144221076581)
                ·
                  refine ⟨5695933639921902041451859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30378312746250144221076581 5695933639921902041451859)
                  ·
                    refine ⟨8543900459882853062177789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5695933639921902041451859 8543900459882853062177789)
                    ·
                      refine ⟨3203962672456069898316671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8543900459882853062177789 3203962672456069898316671)
                      ·
                        rfl

theorem cell23_6239695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 3].length) (baseStart_6239695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239695 prefixEnd_6239695 := by exact prefixLift 6239695
  have htrace : WordTrace (prefixWord ++ tailWord_6239695) baseStart_6239695 baseEnd_6239695 := by
    simpa [prefixWord, tailWord_6239695, baseEnd_6239695] using wordTrace_append hprefix tailTrace_6239695
  have hstable : (prefixWord ++ tailWord_6239695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239695).length < 2 ^ (prefixWord ++ tailWord_6239695).sum := by decide
  have hdescent : baseEnd_6239695 < baseStart_6239695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239738 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_6239738 : Nat := 118140960795 + 6239738 * 2 ^ 59
def prefixEnd_6239738 : Nat := 4983230072969 + 3 ^ 40 * 6239738 * 2
def baseEnd_6239738 : Nat := 3203984752124213230078973

theorem tailTrace_6239738 : CollatzResearch.WordTrace tailWord_6239738 prefixEnd_6239738 3203984752124213230078973 := by
  unfold tailWord_6239738
  simp only [CollatzResearch.WordTrace]
  refine ⟨56895485367125590813447967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151721294312334908835861245 56895485367125590813447967)
  ·
    refine ⟨85343228050688386220171951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56895485367125590813447967 85343228050688386220171951)
    ·
      refine ⟨128014842076032579330257927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85343228050688386220171951 128014842076032579330257927)
      ·
        refine ⟨192022263114048868995386891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128014842076032579330257927 192022263114048868995386891)
        ·
          refine ⟨288033394671073303493080337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192022263114048868995386891 288033394671073303493080337)
          ·
            refine ⟨216025046003304977619810253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288033394671073303493080337 216025046003304977619810253)
            ·
              refine ⟨81009392251239366607428845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 216025046003304977619810253 81009392251239366607428845)
              ·
                refine ⟨30378522094214762477785817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81009392251239366607428845 30378522094214762477785817)
                ·
                  refine ⟨22783891570661071858339363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30378522094214762477785817 22783891570661071858339363)
                  ·
                    refine ⟨34175837355991607787509045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22783891570661071858339363 34175837355991607787509045)
                    ·
                      refine ⟨3203984752124213230078973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34175837355991607787509045 3203984752124213230078973)
                      ·
                        rfl

theorem cell23_6239738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_6239738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239738 prefixEnd_6239738 := by exact prefixLift 6239738
  have htrace : WordTrace (prefixWord ++ tailWord_6239738) baseStart_6239738 baseEnd_6239738 := by
    simpa [prefixWord, tailWord_6239738, baseEnd_6239738] using wordTrace_append hprefix tailTrace_6239738
  have hstable : (prefixWord ++ tailWord_6239738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239738).length < 2 ^ (prefixWord ++ tailWord_6239738).sum := by decide
  have hdescent : baseEnd_6239738 < baseStart_6239738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239746 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6239746 : Nat := 118140960795 + 6239746 * 2 ^ 59
def prefixEnd_6239746 : Nat := 4983230072969 + 3 ^ 40 * 6239746 * 2
def baseEnd_6239746 : Nat := 3203988859969449198778937

theorem tailTrace_6239746 : CollatzResearch.WordTrace tailWord_6239746 prefixEnd_6239746 3203988859969449198778937 := by
  unfold tailWord_6239746
  simp only [CollatzResearch.WordTrace]
  refine ⟨56895558313118345155020773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151721488834982253746722061 56895558313118345155020773)
  ·
    refine ⟨10667917183709689716566395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56895558313118345155020773 10667917183709689716566395)
    ·
      refine ⟨16001875775564534574849593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10667917183709689716566395 16001875775564534574849593)
      ·
        refine ⟨12001406831673400931137195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16001875775564534574849593 12001406831673400931137195)
        ·
          refine ⟨18002110247510101396705793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12001406831673400931137195 18002110247510101396705793)
          ·
            refine ⟨13501582685632576047529345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18002110247510101396705793 13501582685632576047529345)
            ·
              refine ⟨10126187014224432035647009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13501582685632576047529345 10126187014224432035647009)
              ·
                refine ⟨7594640260668324026735257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10126187014224432035647009 7594640260668324026735257)
                ·
                  refine ⟨5695980195501243020051443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7594640260668324026735257 5695980195501243020051443)
                  ·
                    refine ⟨8543970293251864530077165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5695980195501243020051443 8543970293251864530077165)
                    ·
                      refine ⟨3203988859969449198778937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8543970293251864530077165 3203988859969449198778937)
                      ·
                        rfl

theorem cell23_6239746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6239746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239746 prefixEnd_6239746 := by exact prefixLift 6239746
  have htrace : WordTrace (prefixWord ++ tailWord_6239746) baseStart_6239746 baseEnd_6239746 := by
    simpa [prefixWord, tailWord_6239746, baseEnd_6239746] using wordTrace_append hprefix tailTrace_6239746
  have hstable : (prefixWord ++ tailWord_6239746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239746).length < 2 ^ (prefixWord ++ tailWord_6239746).sum := by decide
  have hdescent : baseEnd_6239746 < baseStart_6239746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239752 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_6239752 : Nat := 118140960795 + 6239752 * 2 ^ 59
def prefixEnd_6239752 : Nat := 4983230072969 + 3 ^ 40 * 6239752 * 2
def baseEnd_6239752 : Nat := 3203991940853376175303909

theorem tailTrace_6239752 : CollatzResearch.WordTrace tailWord_6239752 prefixEnd_6239752 3203991940853376175303909 := by
  unfold tailWord_6239752
  simp only [CollatzResearch.WordTrace]
  refine ⟨113791226045225821822400755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151721634726967762429867673 113791226045225821822400755)
  ·
    refine ⟨170686839067838732733601133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113791226045225821822400755 170686839067838732733601133)
    ·
      refine ⟨64007564650439524775100425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 170686839067838732733601133 64007564650439524775100425)
      ·
        refine ⟨48005673487829643581325319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64007564650439524775100425 48005673487829643581325319)
        ·
          refine ⟨72008510231744465371987979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48005673487829643581325319 72008510231744465371987979)
          ·
            refine ⟨108012765347616698057981969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72008510231744465371987979 108012765347616698057981969)
            ·
              refine ⟨81009574010712523543486477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108012765347616698057981969 81009574010712523543486477)
              ·
                refine ⟨30378590254017196328807429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81009574010712523543486477 30378590254017196328807429)
                ·
                  refine ⟨5695985672628224311651393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30378590254017196328807429 5695985672628224311651393)
                  ·
                    refine ⟨4271989254471168233738545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5695985672628224311651393 4271989254471168233738545)
                    ·
                      refine ⟨3203991940853376175303909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4271989254471168233738545 3203991940853376175303909)
                      ·
                        rfl

theorem cell23_6239752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_6239752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239752 prefixEnd_6239752 := by exact prefixLift 6239752
  have htrace : WordTrace (prefixWord ++ tailWord_6239752) baseStart_6239752 baseEnd_6239752 := by
    simpa [prefixWord, tailWord_6239752, baseEnd_6239752] using wordTrace_append hprefix tailTrace_6239752
  have hstable : (prefixWord ++ tailWord_6239752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239752).length < 2 ^ (prefixWord ++ tailWord_6239752).sum := by decide
  have hdescent : baseEnd_6239752 < baseStart_6239752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239765 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_6239765 : Nat := 118140960795 + 6239765 * 2 ^ 59
def prefixEnd_6239765 : Nat := 4983230072969 + 3 ^ 40 * 6239765 * 2
def baseEnd_6239765 : Nat := 3203998616101884624441349

theorem tailTrace_6239765 : CollatzResearch.WordTrace tailWord_6239765 prefixEnd_6239765 3203998616101884624441349 := by
  unfold tailWord_6239765
  simp only [CollatzResearch.WordTrace]
  refine ⟨227582926239404546865024749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151721950826269697910016499 227582926239404546865024749)
  ·
    refine ⟨85343597339776705074384281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227582926239404546865024749 85343597339776705074384281)
    ·
      refine ⟨64007698004832528805788211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85343597339776705074384281 64007698004832528805788211)
      ·
        refine ⟨96011547007248793208682317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64007698004832528805788211 96011547007248793208682317)
        ·
          refine ⟨36004330127718297453255869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96011547007248793208682317 36004330127718297453255869)
          ·
            refine ⟨13501623797894361544970951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36004330127718297453255869 13501623797894361544970951)
            ·
              refine ⟨20252435696841542317456427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13501623797894361544970951 20252435696841542317456427)
              ·
                refine ⟨30378653545262313476184641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20252435696841542317456427 30378653545262313476184641)
                ·
                  refine ⟨22783990158946735107138481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30378653545262313476184641 22783990158946735107138481)
                  ·
                    refine ⟨17087992619210051330353861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22783990158946735107138481 17087992619210051330353861)
                    ·
                      refine ⟨3203998616101884624441349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17087992619210051330353861 3203998616101884624441349)
                      ·
                        rfl

theorem cell23_6239765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_6239765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239765 prefixEnd_6239765 := by exact prefixLift 6239765
  have htrace : WordTrace (prefixWord ++ tailWord_6239765) baseStart_6239765 baseEnd_6239765 := by
    simpa [prefixWord, tailWord_6239765, baseEnd_6239765] using wordTrace_append hprefix tailTrace_6239765
  have hstable : (prefixWord ++ tailWord_6239765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239765).length < 2 ^ (prefixWord ++ tailWord_6239765).sum := by decide
  have hdescent : baseEnd_6239765 < baseStart_6239765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239865 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 6]
def baseStart_6239865 : Nat := 118140960795 + 6239865 * 2 ^ 59
def prefixEnd_6239865 : Nat := 4983230072969 + 3 ^ 40 * 6239865 * 2
def baseEnd_6239865 : Nat := 356005551574148248132321

theorem tailTrace_6239865 : CollatzResearch.WordTrace tailWord_6239865 prefixEnd_6239865 356005551574148248132321 := by
  unfold tailWord_6239865
  simp only [CollatzResearch.WordTrace]
  refine ⟨227586573539042263943665049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151724382359361509295776699 227586573539042263943665049)
  ·
    refine ⟨170689930154281697957748787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 227586573539042263943665049 170689930154281697957748787)
    ·
      refine ⟨256034895231422546936623181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170689930154281697957748787 256034895231422546936623181)
      ·
        refine ⟨96013085711783455101233693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256034895231422546936623181 96013085711783455101233693)
        ·
          refine ⟨36004907141918795662962635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96013085711783455101233693 36004907141918795662962635)
          ·
            refine ⟨54007360712878193494443953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36004907141918795662962635 54007360712878193494443953)
            ·
              refine ⟨40505520534658645120832965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54007360712878193494443953 40505520534658645120832965)
              ·
                refine ⟨7594785100248495960156181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40505520534658645120832965 7594785100248495960156181)
                ·
                  refine ⟨356005551574148248132321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7594785100248495960156181 356005551574148248132321)
                  ·
                    rfl

theorem cell23_6239865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 6].length) (baseStart_6239865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239865 prefixEnd_6239865 := by exact prefixLift 6239865
  have htrace : WordTrace (prefixWord ++ tailWord_6239865) baseStart_6239865 baseEnd_6239865 := by
    simpa [prefixWord, tailWord_6239865, baseEnd_6239865] using wordTrace_append hprefix tailTrace_6239865
  have hstable : (prefixWord ++ tailWord_6239865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239865).length < 2 ^ (prefixWord ++ tailWord_6239865).sum := by decide
  have hdescent : baseEnd_6239865 < baseStart_6239865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239869 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_6239869 : Nat := 118140960795 + 6239869 * 2 ^ 59
def prefixEnd_6239869 : Nat := 4983230072969 + 3 ^ 40 * 6239869 * 2
def baseEnd_6239869 : Nat := 1068017339363317405846957

theorem tailTrace_6239869 : CollatzResearch.WordTrace tailWord_6239869 prefixEnd_6239869 1068017339363317405846957 := by
  unfold tailWord_6239869
  simp only [CollatzResearch.WordTrace]
  refine ⟨227586719431027772626810661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151724479620685181751207107 227586719431027772626810661)
  ·
    refine ⟨42672509893317707367526999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 227586719431027772626810661 42672509893317707367526999)
    ·
      refine ⟨64008764839976561051290499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42672509893317707367526999 64008764839976561051290499)
      ·
        refine ⟨96013147259964841576935749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64008764839976561051290499 96013147259964841576935749)
        ·
          refine ⟨18002465111243407795675453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96013147259964841576935749 18002465111243407795675453)
          ·
            refine ⟨6750924416716277923378295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18002465111243407795675453 6750924416716277923378295)
            ·
              refine ⟨10126386625074416885067443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6750924416716277923378295 10126386625074416885067443)
              ·
                refine ⟨15189579937611625327601165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10126386625074416885067443 15189579937611625327601165)
                ·
                  refine ⟨5696092476604359497850437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15189579937611625327601165 5696092476604359497850437)
                  ·
                    refine ⟨1068017339363317405846957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696092476604359497850437 1068017339363317405846957)
                    ·
                      rfl

theorem cell23_6239869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_6239869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239869 prefixEnd_6239869 := by exact prefixLift 6239869
  have htrace : WordTrace (prefixWord ++ tailWord_6239869) baseStart_6239869 baseEnd_6239869 := by
    simpa [prefixWord, tailWord_6239869, baseEnd_6239869] using wordTrace_append hprefix tailTrace_6239869
  have hstable : (prefixWord ++ tailWord_6239869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239869).length < 2 ^ (prefixWord ++ tailWord_6239869).sum := by decide
  have hdescent : baseEnd_6239869 < baseStart_6239869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239882 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 6]
def baseStart_6239882 : Nat := 118140960795 + 6239882 * 2 ^ 59
def prefixEnd_6239882 : Nat := 4983230072969 + 3 ^ 40 * 6239882 * 2
def baseEnd_6239882 : Nat := 356006521482051185186479

theorem tailTrace_6239882 : CollatzResearch.WordTrace tailWord_6239882 prefixEnd_6239882 356006521482051185186479 := by
  unfold tailWord_6239882
  simp only [CollatzResearch.WordTrace]
  refine ⟨56896798394995168961758475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151724795719987117231355933 56896798394995168961758475)
  ·
    refine ⟨85345197592492753442637713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56896798394995168961758475 85345197592492753442637713)
    ·
      refine ⟨64008898194369565081978285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85345197592492753442637713 64008898194369565081978285)
      ·
        refine ⟨24003336822888586905741857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64008898194369565081978285 24003336822888586905741857)
        ·
          refine ⟨18002502617166440179306393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24003336822888586905741857 18002502617166440179306393)
          ·
            refine ⟨13501876962874830134479795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18002502617166440179306393 13501876962874830134479795)
            ·
              refine ⟨20252815444312245201719693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13501876962874830134479795 20252815444312245201719693)
              ·
                refine ⟨7594805791617091950644885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20252815444312245201719693 7594805791617091950644885)
                ·
                  refine ⟨356006521482051185186479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7594805791617091950644885 356006521482051185186479)
                  ·
                    rfl

theorem cell23_6239882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_6239882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239882 prefixEnd_6239882 := by exact prefixLift 6239882
  have htrace : WordTrace (prefixWord ++ tailWord_6239882) baseStart_6239882 baseEnd_6239882 := by
    simpa [prefixWord, tailWord_6239882, baseEnd_6239882] using wordTrace_append hprefix tailTrace_6239882
  have hstable : (prefixWord ++ tailWord_6239882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239882).length < 2 ^ (prefixWord ++ tailWord_6239882).sum := by decide
  have hdescent : baseEnd_6239882 < baseStart_6239882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239932 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_6239932 : Nat := 118140960795 + 6239932 * 2 ^ 59
def prefixEnd_6239932 : Nat := 4983230072969 + 3 ^ 40 * 6239932 * 2
def baseEnd_6239932 : Nat := 3204084367371185471053081

theorem tailTrace_6239932 : CollatzResearch.WordTrace tailWord_6239932 prefixEnd_6239932 3204084367371185471053081 := by
  unfold tailWord_6239932
  simp only [CollatzResearch.WordTrace]
  refine ⟨113794508614899767193177025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151726011486533022924236033 113794508614899767193177025)
  ·
    refine ⟨85345881461174825394882769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113794508614899767193177025 85345881461174825394882769)
    ·
      refine ⟨64009411095881119046162077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85345881461174825394882769 64009411095881119046162077)
      ·
        refine ⟨24003529160955419642310779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64009411095881119046162077 24003529160955419642310779)
        ·
          refine ⟨36005293741433129463466169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24003529160955419642310779 36005293741433129463466169)
          ·
            refine ⟨27003970306074847097599627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36005293741433129463466169 27003970306074847097599627)
            ·
              refine ⟨40505955459112270646399441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27003970306074847097599627 40505955459112270646399441)
              ·
                refine ⟨30379466594334202984799581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40505955459112270646399441 30379466594334202984799581)
                ·
                  refine ⟨11392299972875326119299843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30379466594334202984799581 11392299972875326119299843)
                  ·
                    refine ⟨17088449959312989178949765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11392299972875326119299843 17088449959312989178949765)
                    ·
                      refine ⟨3204084367371185471053081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17088449959312989178949765 3204084367371185471053081)
                      ·
                        rfl

theorem cell23_6239932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_6239932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239932 prefixEnd_6239932 := by exact prefixLift 6239932
  have htrace : WordTrace (prefixWord ++ tailWord_6239932) baseStart_6239932 baseEnd_6239932 := by
    simpa [prefixWord, tailWord_6239932, baseEnd_6239932] using wordTrace_append hprefix tailTrace_6239932
  have hstable : (prefixWord ++ tailWord_6239932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239932).length < 2 ^ (prefixWord ++ tailWord_6239932).sum := by decide
  have hdescent : baseEnd_6239932 < baseStart_6239932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239935 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_6239935 : Nat := 118140960795 + 6239935 * 2 ^ 59
def prefixEnd_6239935 : Nat := 4983230072969 + 3 ^ 40 * 6239935 * 2
def baseEnd_6239935 : Nat := 3204085907813148959315567

theorem tailTrace_6239935 : CollatzResearch.WordTrace tailWord_6239935 prefixEnd_6239935 3204085907813148959315567 := by
  unfold tailWord_6239935
  simp only [CollatzResearch.WordTrace]
  refine ⟨227589126648788665898713259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151726084432525777265808839 227589126648788665898713259)
  ·
    refine ⟨341383689973182998848069889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227589126648788665898713259 341383689973182998848069889)
    ·
      refine ⟨256037767479887249136052417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341383689973182998848069889 256037767479887249136052417)
      ·
        refine ⟨192028325609915436852039313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256037767479887249136052417 192028325609915436852039313)
        ·
          refine ⟨144021244207436577639029485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192028325609915436852039313 144021244207436577639029485)
          ·
            refine ⟨54007966577788716614636057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144021244207436577639029485 54007966577788716614636057)
            ·
              refine ⟨40505974933341537460977043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54007966577788716614636057 40505974933341537460977043)
              ·
                refine ⟨60758962400012306191465565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40505974933341537460977043 60758962400012306191465565)
                ·
                  refine ⟨22784610900004614821799587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60758962400012306191465565 22784610900004614821799587)
                  ·
                    refine ⟨34176916350006922232699381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22784610900004614821799587 34176916350006922232699381)
                    ·
                      refine ⟨3204085907813148959315567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34176916350006922232699381 3204085907813148959315567)
                      ·
                        rfl

theorem cell23_6239935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_6239935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239935 prefixEnd_6239935 := by exact prefixLift 6239935
  have htrace : WordTrace (prefixWord ++ tailWord_6239935) baseStart_6239935 baseEnd_6239935 := by
    simpa [prefixWord, tailWord_6239935, baseEnd_6239935] using wordTrace_append hprefix tailTrace_6239935
  have hstable : (prefixWord ++ tailWord_6239935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239935).length < 2 ^ (prefixWord ++ tailWord_6239935).sum := by decide
  have hdescent : baseEnd_6239935 < baseStart_6239935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239962 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_6239962 : Nat := 118140960795 + 6239962 * 2 ^ 59
def prefixEnd_6239962 : Nat := 4983230072969 + 3 ^ 40 * 6239962 * 2
def baseEnd_6239962 : Nat := 3204099771790820353677943

theorem tailTrace_6239962 : CollatzResearch.WordTrace tailWord_6239962 prefixEnd_6239962 3204099771790820353677943 := by
  unfold tailWord_6239962
  simp only [CollatzResearch.WordTrace]
  refine ⟨56897527854922712377486535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151726740946460566339964093 56897527854922712377486535)
  ·
    refine ⟨85346291782384068566229803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56897527854922712377486535 85346291782384068566229803)
    ·
      refine ⟨128019437673576102849344705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85346291782384068566229803 128019437673576102849344705)
      ·
        refine ⟨96014578255182077137008529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128019437673576102849344705 96014578255182077137008529)
        ·
          refine ⟨72010933691386557852756397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96014578255182077137008529 72010933691386557852756397)
          ·
            refine ⟨27004100134269959194783649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72010933691386557852756397 27004100134269959194783649)
            ·
              refine ⟨20253075100702469396087737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27004100134269959194783649 20253075100702469396087737)
              ·
                refine ⟨15189806325526852047065803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20253075100702469396087737 15189806325526852047065803)
                ·
                  refine ⟨22784709488290278070598705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15189806325526852047065803 22784709488290278070598705)
                  ·
                    refine ⟨17088532116217708552949029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22784709488290278070598705 17088532116217708552949029)
                    ·
                      refine ⟨3204099771790820353677943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17088532116217708552949029 3204099771790820353677943)
                      ·
                        rfl

theorem cell23_6239962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_6239962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239962 prefixEnd_6239962 := by exact prefixLift 6239962
  have htrace : WordTrace (prefixWord ++ tailWord_6239962) baseStart_6239962 baseEnd_6239962 := by
    simpa [prefixWord, tailWord_6239962, baseEnd_6239962] using wordTrace_append hprefix tailTrace_6239962
  have hstable : (prefixWord ++ tailWord_6239962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239962).length < 2 ^ (prefixWord ++ tailWord_6239962).sum := by decide
  have hdescent : baseEnd_6239962 < baseStart_6239962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239976 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 2, 4]
def baseStart_6239976 : Nat := 118140960795 + 6239976 * 2 ^ 59
def prefixEnd_6239976 : Nat := 4983230072969 + 3 ^ 40 * 6239976 * 2
def baseEnd_6239976 : Nat := 1068035653506661099634293

theorem tailTrace_6239976 : CollatzResearch.WordTrace tailWord_6239976 prefixEnd_6239976 1068035653506661099634293 := by
  unfold tailWord_6239976
  simp only [CollatzResearch.WordTrace]
  refine ⟨113795311020820064950477891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151727081361093419933970521 113795311020820064950477891)
  ·
    refine ⟨170692966531230097425716837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113795311020820064950477891 170692966531230097425716837)
    ·
      refine ⟨32004931224605643267321907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 170692966531230097425716837 32004931224605643267321907)
      ·
        refine ⟨48007396836908464900982861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32004931224605643267321907 48007396836908464900982861)
        ·
          refine ⟨18002773813840674337868573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48007396836908464900982861 18002773813840674337868573)
          ·
            refine ⟨6751040180190252876700715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18002773813840674337868573 6751040180190252876700715)
            ·
              refine ⟨10126560270285379315051073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6751040180190252876700715 10126560270285379315051073)
              ·
                refine ⟨7594920202714034486288305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10126560270285379315051073 7594920202714034486288305)
                ·
                  refine ⟨5696190152035525864716229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7594920202714034486288305 5696190152035525864716229)
                  ·
                    refine ⟨1068035653506661099634293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5696190152035525864716229 1068035653506661099634293)
                    ·
                      rfl

theorem cell23_6239976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_6239976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239976 prefixEnd_6239976 := by exact prefixLift 6239976
  have htrace : WordTrace (prefixWord ++ tailWord_6239976) baseStart_6239976 baseEnd_6239976 := by
    simpa [prefixWord, tailWord_6239976, baseEnd_6239976] using wordTrace_append hprefix tailTrace_6239976
  have hstable : (prefixWord ++ tailWord_6239976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239976).length < 2 ^ (prefixWord ++ tailWord_6239976).sum := by decide
  have hdescent : baseEnd_6239976 < baseStart_6239976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239992 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 2, 7, 2]
def baseStart_6239992 : Nat := 118140960795 + 6239992 * 2 ^ 59
def prefixEnd_6239992 : Nat := 4983230072969 + 3 ^ 40 * 6239992 * 2
def baseEnd_6239992 : Nat := 3204115176210455236302805

theorem tailTrace_6239992 : CollatzResearch.WordTrace tailWord_6239992 prefixEnd_6239992 3204115176210455236302805 := by
  unfold tailWord_6239992
  simp only [CollatzResearch.WordTrace]
  refine ⟨113795602804791082316769115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151727470406388109755692153 113795602804791082316769115)
  ·
    refine ⟨170693404207186623475153673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113795602804791082316769115 170693404207186623475153673)
    ·
      refine ⟨128020053155389967606365255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 170693404207186623475153673 128020053155389967606365255)
      ·
        refine ⟨192030079733084951409547883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128020053155389967606365255 192030079733084951409547883)
        ·
          refine ⟨288045119599627427114321825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192030079733084951409547883 288045119599627427114321825)
          ·
            refine ⟨216033839699720570335741369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 288045119599627427114321825 216033839699720570335741369)
            ·
              refine ⟨162025379774790427751806027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216033839699720570335741369 162025379774790427751806027)
              ·
                refine ⟨243038069662185641627709041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162025379774790427751806027 243038069662185641627709041)
                ·
                  refine ⟨182278552246639231220781781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243038069662185641627709041 182278552246639231220781781)
                  ·
                    refine ⟨4272153568280606981737073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 182278552246639231220781781 4272153568280606981737073)
                    ·
                      refine ⟨3204115176210455236302805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272153568280606981737073 3204115176210455236302805)
                      ·
                        rfl

theorem cell23_6239992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_6239992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239992 prefixEnd_6239992 := by exact prefixLift 6239992
  have htrace : WordTrace (prefixWord ++ tailWord_6239992) baseStart_6239992 baseEnd_6239992 := by
    simpa [prefixWord, tailWord_6239992, baseEnd_6239992] using wordTrace_append hprefix tailTrace_6239992
  have hstable : (prefixWord ++ tailWord_6239992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239992).length < 2 ^ (prefixWord ++ tailWord_6239992).sum := by decide
  have hdescent : baseEnd_6239992 < baseStart_6239992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6239999 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 3]
def baseStart_6239999 : Nat := 118140960795 + 6239999 * 2 ^ 59
def prefixEnd_6239999 : Nat := 4983230072969 + 3 ^ 40 * 6239999 * 2
def baseEnd_6239999 : Nat := 3204118770575036708915273

theorem tailTrace_6239999 : CollatzResearch.WordTrace tailWord_6239999 prefixEnd_6239999 3204118770575036708915273 := by
  unfold tailWord_6239999
  simp only [CollatzResearch.WordTrace]
  refine ⟨227591460920556804829043051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151727640613704536552695367 227591460920556804829043051)
  ·
    refine ⟨341387191380835207243564577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227591460920556804829043051 341387191380835207243564577)
    ·
      refine ⟨256040393535626405432673433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341387191380835207243564577 256040393535626405432673433)
      ·
        refine ⟨192030295151719804074505075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256040393535626405432673433 192030295151719804074505075)
        ·
          refine ⟨288045442727579706111757613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192030295151719804074505075 288045442727579706111757613)
          ·
            refine ⟨108017041022842389791909105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 288045442727579706111757613 108017041022842389791909105)
            ·
              refine ⟨81012780767131792343931829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108017041022842389791909105 81012780767131792343931829)
              ·
                refine ⟨7594948196918605532243609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81012780767131792343931829 7594948196918605532243609)
                ·
                  refine ⟨5696211147688954149182707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7594948196918605532243609 5696211147688954149182707)
                  ·
                    refine ⟨8544316721533431223774061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5696211147688954149182707 8544316721533431223774061)
                    ·
                      refine ⟨3204118770575036708915273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8544316721533431223774061 3204118770575036708915273)
                      ·
                        rfl

theorem cell23_6239999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_6239999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6239999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6239999 prefixEnd_6239999 := by exact prefixLift 6239999
  have htrace : WordTrace (prefixWord ++ tailWord_6239999) baseStart_6239999 baseEnd_6239999 := by
    simpa [prefixWord, tailWord_6239999, baseEnd_6239999] using wordTrace_append hprefix tailTrace_6239999
  have hstable : (prefixWord ++ tailWord_6239999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6239999).length < 2 ^ (prefixWord ++ tailWord_6239999).sum := by decide
  have hdescent : baseEnd_6239999 < baseStart_6239999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6239999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240015 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 4, 6]
def baseStart_6240015 : Nat := 118140960795 + 6240015 * 2 ^ 59
def prefixEnd_6240015 : Nat := 4983230072969 + 3 ^ 40 * 6240015 * 2
def baseEnd_6240015 : Nat := 1068042328755169548771733

theorem tailTrace_6240015 : CollatzResearch.WordTrace tailWord_6240015 prefixEnd_6240015 1068042328755169548771733 := by
  unfold tailWord_6240015
  simp only [CollatzResearch.WordTrace]
  refine ⟨227592044488498839561625499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151728029658999226374416999 227592044488498839561625499)
  ·
    refine ⟨341388066732748259342438249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 227592044488498839561625499 341388066732748259342438249)
    ·
      refine ⟨256041050049561194506828687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 341388066732748259342438249 256041050049561194506828687)
      ·
        refine ⟨384061575074341791760243031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256041050049561194506828687 384061575074341791760243031)
        ·
          refine ⟨576092362611512687640364547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384061575074341791760243031 576092362611512687640364547)
          ·
            refine ⟨864138543917269031460546821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576092362611512687640364547 864138543917269031460546821)
            ·
              refine ⟨162025976984487943398852529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 864138543917269031460546821 162025976984487943398852529)
              ·
                refine ⟨121519482738365957549139397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162025976984487943398852529 121519482738365957549139397)
                ·
                  refine ⟨22784903013443617040463637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121519482738365957549139397 22784903013443617040463637)
                  ·
                    refine ⟨1068042328755169548771733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22784903013443617040463637 1068042328755169548771733)
                    ·
                      rfl

theorem cell23_6240015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_6240015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240015 prefixEnd_6240015 := by exact prefixLift 6240015
  have htrace : WordTrace (prefixWord ++ tailWord_6240015) baseStart_6240015 baseEnd_6240015 := by
    simpa [prefixWord, tailWord_6240015, baseEnd_6240015] using wordTrace_append hprefix tailTrace_6240015
  have hstable : (prefixWord ++ tailWord_6240015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240015).length < 2 ^ (prefixWord ++ tailWord_6240015).sum := by decide
  have hdescent : baseEnd_6240015 < baseStart_6240015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240026 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2]
def baseStart_6240026 : Nat := 118140960795 + 6240026 * 2 ^ 59
def prefixEnd_6240026 : Nat := 4983230072969 + 3 ^ 40 * 6240026 * 2
def baseEnd_6240026 : Nat := 3204132634552708103277649

theorem tailTrace_6240026 : CollatzResearch.WordTrace tailWord_6240026 prefixEnd_6240026 3204132634552708103277649 := by
  unfold tailWord_6240026
  simp only [CollatzResearch.WordTrace]
  refine ⟨56898111422864747110068983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151728297127639325626850621 56898111422864747110068983)
  ·
    refine ⟨85347167134297120665103475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56898111422864747110068983 85347167134297120665103475)
    ·
      refine ⟨128020750701445680997655213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85347167134297120665103475 128020750701445680997655213)
      ·
        refine ⟨48007781513042130374120705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128020750701445680997655213 48007781513042130374120705)
        ·
          refine ⟨36005836134781597780590529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48007781513042130374120705 36005836134781597780590529)
          ·
            refine ⟨27004377101086198335442897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36005836134781597780590529 27004377101086198335442897)
            ·
              refine ⟨20253282825814648751582173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27004377101086198335442897 20253282825814648751582173)
              ·
                refine ⟨7594981059680493281843315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20253282825814648751582173 7594981059680493281843315)
                ·
                  refine ⟨11392471589520739922764973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7594981059680493281843315 11392471589520739922764973)
                  ·
                    refine ⟨4272176846070277471036865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11392471589520739922764973 4272176846070277471036865)
                    ·
                      refine ⟨3204132634552708103277649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4272176846070277471036865 3204132634552708103277649)
                      ·
                        rfl

theorem cell23_6240026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_6240026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240026 prefixEnd_6240026 := by exact prefixLift 6240026
  have htrace : WordTrace (prefixWord ++ tailWord_6240026) baseStart_6240026 baseEnd_6240026 := by
    simpa [prefixWord, tailWord_6240026, baseEnd_6240026] using wordTrace_append hprefix tailTrace_6240026
  have hstable : (prefixWord ++ tailWord_6240026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240026).length < 2 ^ (prefixWord ++ tailWord_6240026).sum := by decide
  have hdescent : baseEnd_6240026 < baseStart_6240026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240096 : List Nat := [2, 1, 1, 3, 3, 2, 4, 2, 5]
def baseStart_6240096 : Nat := 118140960795 + 6240096 * 2 ^ 59
def prefixEnd_6240096 : Nat := 4983230072969 + 3 ^ 40 * 6240096 * 2
def baseEnd_6240096 : Nat := 356018730910946981044703

theorem tailTrace_6240096 : CollatzResearch.WordTrace tailWord_6240096 prefixEnd_6240096 356018730910946981044703 := by
  unfold tailWord_6240096
  simp only [CollatzResearch.WordTrace]
  refine ⟨113797499400602695197662071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151729999200803593596882761 113797499400602695197662071)
  ·
    refine ⟨170696249100904042796493107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113797499400602695197662071 170696249100904042796493107)
    ·
      refine ⟨256044373651356064194739661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170696249100904042796493107 256044373651356064194739661)
      ·
        refine ⟨96016640119258524073027373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256044373651356064194739661 96016640119258524073027373)
        ·
          refine ⟨36006240044721946527385265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96016640119258524073027373 36006240044721946527385265)
          ·
            refine ⟨27004680033541459895538949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36006240044721946527385265 27004680033541459895538949)
            ·
              refine ⟨5063377506289023730413553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27004680033541459895538949 5063377506289023730413553)
              ·
                refine ⟨3797533129716767797810165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5063377506289023730413553 3797533129716767797810165)
                ·
                  refine ⟨356018730910946981044703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3797533129716767797810165 356018730910946981044703)
                  ·
                    rfl

theorem cell23_6240096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 5].length) (baseStart_6240096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240096 prefixEnd_6240096 := by exact prefixLift 6240096
  have htrace : WordTrace (prefixWord ++ tailWord_6240096) baseStart_6240096 baseEnd_6240096 := by
    simpa [prefixWord, tailWord_6240096, baseEnd_6240096] using wordTrace_append hprefix tailTrace_6240096
  have hstable : (prefixWord ++ tailWord_6240096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240096).length < 2 ^ (prefixWord ++ tailWord_6240096).sum := by decide
  have hdescent : baseEnd_6240096 < baseStart_6240096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240112 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_6240112 : Nat := 118140960795 + 6240112 * 2 ^ 59
def prefixEnd_6240112 : Nat := 4983230072969 + 3 ^ 40 * 6240112 * 2
def baseEnd_6240112 : Nat := 3204176793888994766802253

theorem tailTrace_6240112 : CollatzResearch.WordTrace tailWord_6240112 prefixEnd_6240112 3204176793888994766802253 := by
  unfold tailWord_6240112
  simp only [CollatzResearch.WordTrace]
  refine ⟨113797791184573712563953295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151730388246098283418604393 113797791184573712563953295)
  ·
    refine ⟨170696686776860568845929943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113797791184573712563953295 170696686776860568845929943)
    ·
      refine ⟨256045030165290853268894915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170696686776860568845929943 256045030165290853268894915)
      ·
        refine ⟨384067545247936279903342373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256045030165290853268894915 384067545247936279903342373)
        ·
          refine ⟨72012664733988052481876695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 384067545247936279903342373 72012664733988052481876695)
          ·
            refine ⟨108018997100982078722815043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72012664733988052481876695 108018997100982078722815043)
            ·
              refine ⟨162028495651473118084222565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108018997100982078722815043 162028495651473118084222565)
              ·
                refine ⟨30380342934651209640791731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162028495651473118084222565 30380342934651209640791731)
                ·
                  refine ⟨45570514401976814461187597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30380342934651209640791731 45570514401976814461187597)
                  ·
                    refine ⟨17088942900741305422945349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45570514401976814461187597 17088942900741305422945349)
                    ·
                      refine ⟨3204176793888994766802253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17088942900741305422945349 3204176793888994766802253)
                      ·
                        rfl

theorem cell23_6240112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_6240112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240112 prefixEnd_6240112 := by exact prefixLift 6240112
  have htrace : WordTrace (prefixWord ++ tailWord_6240112) baseStart_6240112 baseEnd_6240112 := by
    simpa [prefixWord, tailWord_6240112, baseEnd_6240112] using wordTrace_append hprefix tailTrace_6240112
  have hstable : (prefixWord ++ tailWord_6240112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240112).length < 2 ^ (prefixWord ++ tailWord_6240112).sum := by decide
  have hdescent : baseEnd_6240112 < baseStart_6240112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240126 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6240126 : Nat := 118140960795 + 6240126 * 2 ^ 59
def prefixEnd_6240126 : Nat := 4983230072969 + 3 ^ 40 * 6240126 * 2
def baseEnd_6240126 : Nat := 1068061327539385904009063

theorem tailTrace_6240126 : CollatzResearch.WordTrace tailWord_6240126 prefixEnd_6240126 1068061327539385904009063 := by
  unfold tailWord_6240126
  simp only [CollatzResearch.WordTrace]
  refine ⟨28449511623887088189864529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151730728660731137012610821 28449511623887088189864529)
  ·
    refine ⟨21337133717915316142398397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28449511623887088189864529 21337133717915316142398397)
    ·
      refine ⟨8001425144218243553399399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21337133717915316142398397 8001425144218243553399399)
      ·
        refine ⟨12002137716327365330099099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8001425144218243553399399 12002137716327365330099099)
        ·
          refine ⟨18003206574491047995148649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12002137716327365330099099 18003206574491047995148649)
          ·
            refine ⟨13502404930868285996361487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18003206574491047995148649 13502404930868285996361487)
            ·
              refine ⟨20253607396302428994542231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13502404930868285996361487 20253607396302428994542231)
              ·
                refine ⟨30380411094453643491813347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20253607396302428994542231 30380411094453643491813347)
                ·
                  refine ⟨45570616641680465237720021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30380411094453643491813347 45570616641680465237720021)
                  ·
                    refine ⟨1068061327539385904009063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45570616641680465237720021 1068061327539385904009063)
                    ·
                      rfl

theorem cell23_6240126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6240126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240126 prefixEnd_6240126 := by exact prefixLift 6240126
  have htrace : WordTrace (prefixWord ++ tailWord_6240126) baseStart_6240126 baseEnd_6240126 := by
    simpa [prefixWord, tailWord_6240126, baseEnd_6240126] using wordTrace_append hprefix tailTrace_6240126
  have hstable : (prefixWord ++ tailWord_6240126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240126).length < 2 ^ (prefixWord ++ tailWord_6240126).sum := by decide
  have hdescent : baseEnd_6240126 < baseStart_6240126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240149 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_6240149 : Nat := 118140960795 + 6240149 * 2 ^ 59
def prefixEnd_6240149 : Nat := 4983230072969 + 3 ^ 40 * 6240149 * 2
def baseEnd_6240149 : Nat := 3204195792673211122039583

theorem tailTrace_6240149 : CollatzResearch.WordTrace tailWord_6240149 prefixEnd_6240149 3204195792673211122039583 := by
  unfold tailWord_6240149
  simp only [CollatzResearch.WordTrace]
  refine ⟨227596931870013380447003501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151731287913342253631335667 227596931870013380447003501)
  ·
    refine ⟨85348849451255017667626313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 227596931870013380447003501 85348849451255017667626313)
    ·
      refine ⟨64011637088441263250719735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85348849451255017667626313 64011637088441263250719735)
      ·
        refine ⟨96017455632661894876079603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64011637088441263250719735 96017455632661894876079603)
        ·
          refine ⟨144026183448992842314119405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96017455632661894876079603 144026183448992842314119405)
          ·
            refine ⟨54009818793372315867794777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144026183448992842314119405 54009818793372315867794777)
            ·
              refine ⟨40507364095029236900846083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54009818793372315867794777 40507364095029236900846083)
              ·
                refine ⟨60761046142543855351269125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40507364095029236900846083 60761046142543855351269125)
                ·
                  refine ⟨11392696151726972878362961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60761046142543855351269125 11392696151726972878362961)
                  ·
                    refine ⟨8544522113795229658772221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11392696151726972878362961 8544522113795229658772221)
                    ·
                      refine ⟨3204195792673211122039583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8544522113795229658772221 3204195792673211122039583)
                      ·
                        rfl

theorem cell23_6240149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_6240149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6240149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6240149 prefixEnd_6240149 := by exact prefixLift 6240149
  have htrace : WordTrace (prefixWord ++ tailWord_6240149) baseStart_6240149 baseEnd_6240149 := by
    simpa [prefixWord, tailWord_6240149, baseEnd_6240149] using wordTrace_append hprefix tailTrace_6240149
  have hstable : (prefixWord ++ tailWord_6240149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240149).length < 2 ^ (prefixWord ++ tailWord_6240149).sum := by decide
  have hdescent : baseEnd_6240149 < baseStart_6240149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
