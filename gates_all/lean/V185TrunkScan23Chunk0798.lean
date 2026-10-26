import V185TrunkScan23Chunk0797

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4719082 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_4719082 : Nat := 118140960795 + 4719082 * 2 ^ 59
def prefixEnd_4719082 : Nat := 4983230072969 + 3 ^ 40 * 4719082 * 2
def baseEnd_4719082 : Nat := 807719104660270267890781

theorem tailTrace_4719082 : CollatzResearch.WordTrace tailWord_4719082 prefixEnd_4719082 807719104660270267890781 := by
  unfold tailWord_4719082
  simp only [CollatzResearch.WordTrace]
  refine ⟨43029765172394835971337875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114746040459719562590234333 43029765172394835971337875)
  ·
    refine ⟨64544647758592253957006813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43029765172394835971337875 64544647758592253957006813)
    ·
      refine ⟨24204242909472095233877555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64544647758592253957006813 24204242909472095233877555)
      ·
        refine ⟨36306364364208142850816333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24204242909472095233877555 36306364364208142850816333)
        ·
          refine ⟨13614886636578053569056125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36306364364208142850816333 13614886636578053569056125)
          ·
            refine ⟨5105582488716770088396047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13614886636578053569056125 5105582488716770088396047)
            ·
              refine ⟨7658373733075155132594071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5105582488716770088396047 7658373733075155132594071)
              ·
                refine ⟨11487560599612732698891107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7658373733075155132594071 11487560599612732698891107)
                ·
                  refine ⟨17231340899419099048336661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11487560599612732698891107 17231340899419099048336661)
                  ·
                    refine ⟨807719104660270267890781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17231340899419099048336661 807719104660270267890781)
                    ·
                      rfl

theorem cell23_4719082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_4719082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719082 prefixEnd_4719082 := by exact prefixLift 4719082
  have htrace : WordTrace (prefixWord ++ tailWord_4719082) baseStart_4719082 baseEnd_4719082 := by
    simpa [prefixWord, tailWord_4719082, baseEnd_4719082] using wordTrace_append hprefix tailTrace_4719082
  have hstable : (prefixWord ++ tailWord_4719082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719082).length < 2 ^ (prefixWord ++ tailWord_4719082).sum := by decide
  have hdescent : baseEnd_4719082 < baseStart_4719082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719139 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 3]
def baseStart_4719139 : Nat := 118140960795 + 4719139 * 2 ^ 59
def prefixEnd_4719139 : Nat := 4983230072969 + 3 ^ 40 * 4719139 * 2
def baseEnd_4719139 : Nat := 2423186582378117080659581

theorem tailTrace_4719139 : CollatzResearch.WordTrace tailWord_4719139 prefixEnd_4719139 2423186582378117080659581 := by
  unfold tailWord_4719139
  simp only [CollatzResearch.WordTrace]
  refine ⟨172121139650372842620176471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114747426433581895080117647 172121139650372842620176471)
  ·
    refine ⟨258181709475559263930264707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172121139650372842620176471 258181709475559263930264707)
    ·
      refine ⟨387272564213338895895397061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258181709475559263930264707 387272564213338895895397061)
      ·
        refine ⟨72613605790001042980386949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387272564213338895895397061 72613605790001042980386949)
        ·
          refine ⟨13615051085625195558822553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72613605790001042980386949 13615051085625195558822553)
          ·
            refine ⟨10211288314218896669116915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13615051085625195558822553 10211288314218896669116915)
            ·
              refine ⟨15316932471328345003675373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10211288314218896669116915 15316932471328345003675373)
              ·
                refine ⟨5743849676748129376378265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15316932471328345003675373 5743849676748129376378265)
                ·
                  refine ⟨4307887257561097032283699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5743849676748129376378265 4307887257561097032283699)
                  ·
                    refine ⟨6461830886341645548425549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4307887257561097032283699 6461830886341645548425549)
                    ·
                      refine ⟨2423186582378117080659581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6461830886341645548425549 2423186582378117080659581)
                      ·
                        rfl

theorem cell23_4719139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_4719139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719139 prefixEnd_4719139 := by exact prefixLift 4719139
  have htrace : WordTrace (prefixWord ++ tailWord_4719139) baseStart_4719139 baseEnd_4719139 := by
    simpa [prefixWord, tailWord_4719139, baseEnd_4719139] using wordTrace_append hprefix tailTrace_4719139
  have hstable : (prefixWord ++ tailWord_4719139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719139).length < 2 ^ (prefixWord ++ tailWord_4719139).sum := by decide
  have hdescent : baseEnd_4719139 < baseStart_4719139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719143 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4719143 : Nat := 118140960795 + 4719143 * 2 ^ 59
def prefixEnd_4719143 : Nat := 4983230072969 + 3 ^ 40 * 4719143 * 2
def baseEnd_4719143 : Nat := 2423188636300735065009563

theorem tailTrace_4719143 : CollatzResearch.WordTrace tailWord_4719143 prefixEnd_4719143 2423188636300735065009563 := by
  unfold tailWord_4719143
  simp only [CollatzResearch.WordTrace]
  refine ⟨172121285542358351303322083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114747523694905567535548055 172121285542358351303322083)
  ·
    refine ⟨258181928313537526954983125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172121285542358351303322083 258181928313537526954983125)
    ·
      refine ⟨6051138944848535788007417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 258181928313537526954983125 6051138944848535788007417)
      ·
        refine ⟨4538354208636401841005563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6051138944848535788007417 4538354208636401841005563)
        ·
          refine ⟨6807531312954602761508345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4538354208636401841005563 6807531312954602761508345)
          ·
            refine ⟨5105648484715952071131259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6807531312954602761508345 5105648484715952071131259)
            ·
              refine ⟨7658472727073928106696889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5105648484715952071131259 7658472727073928106696889)
              ·
                refine ⟨5743854545305446080022667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7658472727073928106696889 5743854545305446080022667)
                ·
                  refine ⟨8615781817958169120034001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5743854545305446080022667 8615781817958169120034001)
                  ·
                    refine ⟨6461836363468626840025501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8615781817958169120034001 6461836363468626840025501)
                    ·
                      refine ⟨2423188636300735065009563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6461836363468626840025501 2423188636300735065009563)
                      ·
                        rfl

theorem cell23_4719143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4719143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719143 prefixEnd_4719143 := by exact prefixLift 4719143
  have htrace : WordTrace (prefixWord ++ tailWord_4719143) baseStart_4719143 baseEnd_4719143 := by
    simpa [prefixWord, tailWord_4719143, baseEnd_4719143] using wordTrace_append hprefix tailTrace_4719143
  have hstable : (prefixWord ++ tailWord_4719143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719143).length < 2 ^ (prefixWord ++ tailWord_4719143).sum := by decide
  have hdescent : baseEnd_4719143 < baseStart_4719143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719156 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4719156 : Nat := 118140960795 + 4719156 * 2 ^ 59
def prefixEnd_4719156 : Nat := 4983230072969 + 3 ^ 40 * 4719156 * 2
def baseEnd_4719156 : Nat := 2423195311549243514147003

theorem tailTrace_4719156 : CollatzResearch.WordTrace tailWord_4719156 prefixEnd_4719156 2423195311549243514147003 := by
  unfold tailWord_4719156
  simp only [CollatzResearch.WordTrace]
  refine ⟨86060879845655627261772661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114747839794207503015696881 86060879845655627261772661)
  ·
    refine ⟨8068207485530215055791187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86060879845655627261772661 8068207485530215055791187)
    ·
      refine ⟨12102311228295322583686781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8068207485530215055791187 12102311228295322583686781)
      ·
        refine ⟨4538366710610745968882543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12102311228295322583686781 4538366710610745968882543)
        ·
          refine ⟨6807550065916118953323815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4538366710610745968882543 6807550065916118953323815)
          ·
            refine ⟨10211325098874178429985723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6807550065916118953323815 10211325098874178429985723)
            ·
              refine ⟨15316987648311267644978585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10211325098874178429985723 15316987648311267644978585)
              ·
                refine ⟨11487740736233450733733939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15316987648311267644978585 11487740736233450733733939)
                ·
                  refine ⟨17231611104350176100600909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11487740736233450733733939 17231611104350176100600909)
                  ·
                    refine ⟨6461854164131316037725341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17231611104350176100600909 6461854164131316037725341)
                    ·
                      refine ⟨2423195311549243514147003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6461854164131316037725341 2423195311549243514147003)
                      ·
                        rfl

theorem cell23_4719156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4719156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719156 prefixEnd_4719156 := by exact prefixLift 4719156
  have htrace : WordTrace (prefixWord ++ tailWord_4719156) baseStart_4719156 baseEnd_4719156 := by
    simpa [prefixWord, tailWord_4719156, baseEnd_4719156] using wordTrace_append hprefix tailTrace_4719156
  have hstable : (prefixWord ++ tailWord_4719156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719156).length < 2 ^ (prefixWord ++ tailWord_4719156).sum := by decide
  have hdescent : baseEnd_4719156 < baseStart_4719156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719162 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2]
def baseStart_4719162 : Nat := 118140960795 + 4719162 * 2 ^ 59
def prefixEnd_4719162 : Nat := 4983230072969 + 3 ^ 40 * 4719162 * 2
def baseEnd_4719162 : Nat := 2423198392433170490671975

theorem tailTrace_4719162 : CollatzResearch.WordTrace tailWord_4719162 prefixEnd_4719162 2423198392433170490671975 := by
  unfold tailWord_4719162
  simp only [CollatzResearch.WordTrace]
  refine ⟨43030494632322379387065935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114747985686193011698842493 43030494632322379387065935)
  ·
    refine ⟨64545741948483569080598903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43030494632322379387065935 64545741948483569080598903)
    ·
      refine ⟨96818612922725353620898355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64545741948483569080598903 96818612922725353620898355)
      ·
        refine ⟨145227919384088030431347533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96818612922725353620898355 145227919384088030431347533)
        ·
          refine ⟨54460469769033011411755325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145227919384088030431347533 54460469769033011411755325)
          ·
            refine ⟨20422676163387379279408247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54460469769033011411755325 20422676163387379279408247)
            ·
              refine ⟨30634014245081068919112371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20422676163387379279408247 30634014245081068919112371)
              ·
                refine ⟨45951021367621603378668557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30634014245081068919112371 45951021367621603378668557)
                ·
                  refine ⟨17231633012858101267000709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45951021367621603378668557 17231633012858101267000709)
                  ·
                    refine ⟨3230931189910893987562633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17231633012858101267000709 3230931189910893987562633)
                    ·
                      refine ⟨2423198392433170490671975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230931189910893987562633 2423198392433170490671975)
                      ·
                        rfl

theorem cell23_4719162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2].length) (baseStart_4719162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719162 prefixEnd_4719162 := by exact prefixLift 4719162
  have htrace : WordTrace (prefixWord ++ tailWord_4719162) baseStart_4719162 baseEnd_4719162 := by
    simpa [prefixWord, tailWord_4719162, baseEnd_4719162] using wordTrace_append hprefix tailTrace_4719162
  have hstable : (prefixWord ++ tailWord_4719162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719162).length < 2 ^ (prefixWord ++ tailWord_4719162).sum := by decide
  have hdescent : baseEnd_4719162 < baseStart_4719162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719179 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 2, 2, 2]
def baseStart_4719179 : Nat := 118140960795 + 4719179 * 2 ^ 59
def prefixEnd_4719179 : Nat := 4983230072969 + 3 ^ 40 * 4719179 * 2
def baseEnd_4719179 : Nat := 2423207121604296924159397

theorem tailTrace_4719179 : CollatzResearch.WordTrace tailWord_4719179 prefixEnd_4719179 2423207121604296924159397 := by
  unfold tailWord_4719179
  simp only [CollatzResearch.WordTrace]
  refine ⟨172122598570227929451632591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114748399046818619634421727 172122598570227929451632591)
  ·
    refine ⟨258183897855341894177448887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172122598570227929451632591 258183897855341894177448887)
    ·
      refine ⟨387275846783012841266173331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258183897855341894177448887 387275846783012841266173331)
      ·
        refine ⟨580913770174519261899259997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387275846783012841266173331 580913770174519261899259997)
        ·
          refine ⟨217842663815444723212222499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 580913770174519261899259997 217842663815444723212222499)
          ·
            refine ⟨326763995723167084818333749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217842663815444723212222499 326763995723167084818333749)
            ·
              refine ⟨30634124599046914201718789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 326763995723167084818333749 30634124599046914201718789)
              ·
                refine ⟨5743898362321296412822273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30634124599046914201718789 5743898362321296412822273)
                ·
                  refine ⟨4307923771740972309616705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5743898362321296412822273 4307923771740972309616705)
                  ·
                    refine ⟨3230942828805729232212529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4307923771740972309616705 3230942828805729232212529)
                    ·
                      refine ⟨2423207121604296924159397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230942828805729232212529 2423207121604296924159397)
                      ·
                        rfl

theorem cell23_4719179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 2, 2].length) (baseStart_4719179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719179 prefixEnd_4719179 := by exact prefixLift 4719179
  have htrace : WordTrace (prefixWord ++ tailWord_4719179) baseStart_4719179 baseEnd_4719179 := by
    simpa [prefixWord, tailWord_4719179, baseEnd_4719179] using wordTrace_append hprefix tailTrace_4719179
  have hstable : (prefixWord ++ tailWord_4719179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719179).length < 2 ^ (prefixWord ++ tailWord_4719179).sum := by decide
  have hdescent : baseEnd_4719179 < baseStart_4719179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719196 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_4719196 : Nat := 118140960795 + 4719196 * 2 ^ 59
def prefixEnd_4719196 : Nat := 4983230072969 + 3 ^ 40 * 4719196 * 2
def baseEnd_4719196 : Nat := 2423215850775423357646819

theorem tailTrace_4719196 : CollatzResearch.WordTrace tailWord_4719196 prefixEnd_4719196 2423215850775423357646819 := by
  unfold tailWord_4719196
  simp only [CollatzResearch.WordTrace]
  refine ⟨86061609305583170677500721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114748812407444227570000961 86061609305583170677500721)
  ·
    refine ⟨64546206979187378008125541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86061609305583170677500721 64546206979187378008125541)
    ·
      refine ⟨12102413808597633376523539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64546206979187378008125541 12102413808597633376523539)
      ·
        refine ⟨18153620712896450064785309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12102413808597633376523539 18153620712896450064785309)
        ·
          refine ⟨6807607767336168774294491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18153620712896450064785309 6807607767336168774294491)
          ·
            refine ⟨10211411651004253161441737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6807607767336168774294491 10211411651004253161441737)
            ·
              refine ⟨7658558738253189871081303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10211411651004253161441737 7658558738253189871081303)
              ·
                refine ⟨11487838107379784806621955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7658558738253189871081303 11487838107379784806621955)
                ·
                  refine ⟨17231757161069677209932933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11487838107379784806621955 17231757161069677209932933)
                  ·
                    refine ⟨3230954467700564476862425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17231757161069677209932933 3230954467700564476862425)
                    ·
                      refine ⟨2423215850775423357646819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3230954467700564476862425 2423215850775423357646819)
                      ·
                        rfl

theorem cell23_4719196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_4719196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719196 prefixEnd_4719196 := by exact prefixLift 4719196
  have htrace : WordTrace (prefixWord ++ tailWord_4719196) baseStart_4719196 baseEnd_4719196 := by
    simpa [prefixWord, tailWord_4719196, baseEnd_4719196] using wordTrace_append hprefix tailTrace_4719196
  have hstable : (prefixWord ++ tailWord_4719196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719196).length < 2 ^ (prefixWord ++ tailWord_4719196).sum := by decide
  have hdescent : baseEnd_4719196 < baseStart_4719196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719262 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4719262 : Nat := 118140960795 + 4719262 * 2 ^ 59
def prefixEnd_4719262 : Nat := 4983230072969 + 3 ^ 40 * 4719262 * 2
def baseEnd_4719262 : Nat := 807749913499540033140505

theorem tailTrace_4719262 : CollatzResearch.WordTrace tailWord_4719262 prefixEnd_4719262 807749913499540033140505 := by
  unfold tailWord_4719262
  simp only [CollatzResearch.WordTrace]
  refine ⟨21515703228615904328363005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114750417219284823084602693 21515703228615904328363005)
  ·
    refine ⟨8068388710730964123136127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21515703228615904328363005 8068388710730964123136127)
    ·
      refine ⟨12102583066096446184704191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8068388710730964123136127 12102583066096446184704191)
      ·
        refine ⟨18153874599144669277056287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12102583066096446184704191 18153874599144669277056287)
        ·
          refine ⟨27230811898717003915584431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18153874599144669277056287 27230811898717003915584431)
          ·
            refine ⟨40846217848075505873376647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27230811898717003915584431 40846217848075505873376647)
            ·
              refine ⟨61269326772113258810064971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40846217848075505873376647 61269326772113258810064971)
              ·
                refine ⟨91903990158169888215097457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61269326772113258810064971 91903990158169888215097457)
                ·
                  refine ⟨68927992618627416161323093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91903990158169888215097457 68927992618627416161323093)
                  ·
                    refine ⟨807749913499540033140505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68927992618627416161323093 807749913499540033140505)
                    ·
                      rfl

theorem cell23_4719262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4719262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719262 prefixEnd_4719262 := by exact prefixLift 4719262
  have htrace : WordTrace (prefixWord ++ tailWord_4719262) baseStart_4719262 baseEnd_4719262 := by
    simpa [prefixWord, tailWord_4719262, baseEnd_4719262] using wordTrace_append hprefix tailTrace_4719262
  have hstable : (prefixWord ++ tailWord_4719262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719262).length < 2 ^ (prefixWord ++ tailWord_4719262).sum := by decide
  have hdescent : baseEnd_4719262 < baseStart_4719262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719292 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 6]
def baseStart_4719292 : Nat := 118140960795 + 4719292 * 2 ^ 59
def prefixEnd_4719292 : Nat := 4983230072969 + 3 ^ 40 * 4719292 * 2
def baseEnd_4719292 : Nat := 269251682768694998005153

theorem tailTrace_4719292 : CollatzResearch.WordTrace tailWord_4719292 prefixEnd_4719292 269251682768694998005153 := by
  unfold tailWord_4719292
  simp only [CollatzResearch.WordTrace]
  refine ⟨86063360009409274875248065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114751146679212366500330753 86063360009409274875248065)
  ·
    refine ⟨64547520007056956156436049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86063360009409274875248065 64547520007056956156436049)
    ·
      refine ⟨48410640005292717117327037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64547520007056956156436049 48410640005292717117327037)
      ·
        refine ⟨18153990001984768918997639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48410640005292717117327037 18153990001984768918997639)
        ·
          refine ⟨27230985002977153378496459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18153990001984768918997639 27230985002977153378496459)
          ·
            refine ⟨40846477504465730067744689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27230985002977153378496459 40846477504465730067744689)
            ·
              refine ⟨30634858128349297550808517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40846477504465730067744689 30634858128349297550808517)
              ·
                refine ⟨5744035899065493290776597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30634858128349297550808517 5744035899065493290776597)
                ·
                  refine ⟨269251682768694998005153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5744035899065493290776597 269251682768694998005153)
                  ·
                    rfl

theorem cell23_4719292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_4719292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719292 prefixEnd_4719292 := by exact prefixLift 4719292
  have htrace : WordTrace (prefixWord ++ tailWord_4719292) baseStart_4719292 baseEnd_4719292 := by
    simpa [prefixWord, tailWord_4719292, baseEnd_4719292] using wordTrace_append hprefix tailTrace_4719292
  have hstable : (prefixWord ++ tailWord_4719292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719292).length < 2 ^ (prefixWord ++ tailWord_4719292).sum := by decide
  have hdescent : baseEnd_4719292 < baseStart_4719292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719322 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_4719322 : Nat := 118140960795 + 4719322 * 2 ^ 59
def prefixEnd_4719322 : Nat := 4983230072969 + 3 ^ 40 * 4719322 * 2
def baseEnd_4719322 : Nat := 807760183112629954890413

theorem tailTrace_4719322 : CollatzResearch.WordTrace tailWord_4719322 prefixEnd_4719322 807760183112629954890413 := by
  unfold tailWord_4719322
  simp only [CollatzResearch.WordTrace]
  refine ⟨43031953552177466218522055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114751876139139909916058813 43031953552177466218522055)
  ·
    refine ⟨64547930328266199327783083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43031953552177466218522055 64547930328266199327783083)
    ·
      refine ⟨96821895492399298991674625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64547930328266199327783083 96821895492399298991674625)
      ·
        refine ⟨72616421619299474243755969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96821895492399298991674625 72616421619299474243755969)
        ·
          refine ⟨54462316214474605682816977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72616421619299474243755969 54462316214474605682816977)
          ·
            refine ⟨40846737160855954262112733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54462316214474605682816977 40846737160855954262112733)
            ·
              refine ⟨15317526435320982848292275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40846737160855954262112733 15317526435320982848292275)
              ·
                refine ⟨22976289652981474272438413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15317526435320982848292275 22976289652981474272438413)
                ·
                  refine ⟨8616108619868052852164405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22976289652981474272438413 8616108619868052852164405)
                  ·
                    refine ⟨807760183112629954890413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8616108619868052852164405 807760183112629954890413)
                    ·
                      rfl

theorem cell23_4719322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_4719322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719322 prefixEnd_4719322 := by exact prefixLift 4719322
  have htrace : WordTrace (prefixWord ++ tailWord_4719322) baseStart_4719322 baseEnd_4719322 := by
    simpa [prefixWord, tailWord_4719322, baseEnd_4719322] using wordTrace_append hprefix tailTrace_4719322
  have hstable : (prefixWord ++ tailWord_4719322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719322).length < 2 ^ (prefixWord ++ tailWord_4719322).sum := by decide
  have hdescent : baseEnd_4719322 < baseStart_4719322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719346 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_4719346 : Nat := 118140960795 + 4719346 * 2 ^ 59
def prefixEnd_4719346 : Nat := 4983230072969 + 3 ^ 40 * 4719346 * 2
def baseEnd_4719346 : Nat := 2423292872873597770771129

theorem tailTrace_4719346 : CollatzResearch.WordTrace tailWord_4719346 prefixEnd_4719346 2423292872873597770771129 := by
  unfold tailWord_4719346
  simp only [CollatzResearch.WordTrace]
  refine ⟨43032172390155729243240473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114752459707081944648641261 43032172390155729243240473)
  ·
    refine ⟨32274129292616796932430355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43032172390155729243240473 32274129292616796932430355)
    ·
      refine ⟨48411193938925195398645533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32274129292616796932430355 48411193938925195398645533)
      ·
        refine ⟨18154197727096948274492075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48411193938925195398645533 18154197727096948274492075)
        ·
          refine ⟨27231296590645422411738113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18154197727096948274492075 27231296590645422411738113)
          ·
            refine ⟨20423472442984066808803585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27231296590645422411738113 20423472442984066808803585)
            ·
              refine ⟨15317604332238050106602689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20423472442984066808803585 15317604332238050106602689)
              ·
                refine ⟨11488203249178537579952017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15317604332238050106602689 11488203249178537579952017)
                ·
                  refine ⟨8616152436883903184964013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11488203249178537579952017 8616152436883903184964013)
                  ·
                    refine ⟨3231057163831463694361505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8616152436883903184964013 3231057163831463694361505)
                    ·
                      refine ⟨2423292872873597770771129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231057163831463694361505 2423292872873597770771129)
                      ·
                        rfl

theorem cell23_4719346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_4719346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719346 prefixEnd_4719346 := by exact prefixLift 4719346
  have htrace : WordTrace (prefixWord ++ tailWord_4719346) baseStart_4719346 baseEnd_4719346 := by
    simpa [prefixWord, tailWord_4719346, baseEnd_4719346] using wordTrace_append hprefix tailTrace_4719346
  have hstable : (prefixWord ++ tailWord_4719346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719346).length < 2 ^ (prefixWord ++ tailWord_4719346).sum := by decide
  have hdescent : baseEnd_4719346 < baseStart_4719346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719369 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 2, 4]
def baseStart_4719369 : Nat := 118140960795 + 4719369 * 2 ^ 59
def prefixEnd_4719369 : Nat := 4983230072969 + 3 ^ 40 * 4719369 * 2
def baseEnd_4719369 : Nat := 807768227642883726927841

theorem tailTrace_4719369 : CollatzResearch.WordTrace tailWord_4719369 prefixEnd_4719369 807768227642883726927841 := by
  unfold tailWord_4719369
  simp only [CollatzResearch.WordTrace]
  refine ⟨172129528439539591901049161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114753018959693061267366107 172129528439539591901049161)
  ·
    refine ⟨129097146329654693925786871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172129528439539591901049161 129097146329654693925786871)
    ·
      refine ⟨193645719494482040888680307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129097146329654693925786871 193645719494482040888680307)
      ·
        refine ⟨290468579241723061333020461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193645719494482040888680307 290468579241723061333020461)
        ·
          refine ⟨108925717215646147999882673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290468579241723061333020461 108925717215646147999882673)
          ·
            refine ⟨81694287911734610999912005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108925717215646147999882673 81694287911734610999912005)
            ·
              refine ⟨15317678983450239562483501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81694287911734610999912005 15317678983450239562483501)
              ·
                refine ⟨5744129618793839835931313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15317678983450239562483501 5744129618793839835931313)
                ·
                  refine ⟨4308097214095379876948485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5744129618793839835931313 4308097214095379876948485)
                  ·
                    refine ⟨807768227642883726927841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4308097214095379876948485 807768227642883726927841)
                    ·
                      rfl

theorem cell23_4719369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 4].length) (baseStart_4719369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719369 prefixEnd_4719369 := by exact prefixLift 4719369
  have htrace : WordTrace (prefixWord ++ tailWord_4719369) baseStart_4719369 baseEnd_4719369 := by
    simpa [prefixWord, tailWord_4719369, baseEnd_4719369] using wordTrace_append hprefix tailTrace_4719369
  have hstable : (prefixWord ++ tailWord_4719369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719369).length < 2 ^ (prefixWord ++ tailWord_4719369).sum := by decide
  have hdescent : baseEnd_4719369 < baseStart_4719369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719379 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 3]
def baseStart_4719379 : Nat := 118140960795 + 4719379 * 2 ^ 59
def prefixEnd_4719379 : Nat := 4983230072969 + 3 ^ 40 * 4719379 * 2
def baseEnd_4719379 : Nat := 2423309817735196141658477

theorem tailTrace_4719379 : CollatzResearch.WordTrace tailWord_4719379 prefixEnd_4719379 2423309817735196141658477 := by
  unfold tailWord_4719379
  simp only [CollatzResearch.WordTrace]
  refine ⟨172129893169503363608913191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114753262113002242405942127 172129893169503363608913191)
  ·
    refine ⟨258194839754255045413369787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172129893169503363608913191 258194839754255045413369787)
    ·
      refine ⟨387292259631382568120054681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258194839754255045413369787 387292259631382568120054681)
      ·
        refine ⟨290469194723536926090041011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387292259631382568120054681 290469194723536926090041011)
        ·
          refine ⟨435703792085305389135061517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290469194723536926090041011 435703792085305389135061517)
          ·
            refine ⟨163388922031989520925648069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 435703792085305389135061517 163388922031989520925648069)
            ·
              refine ⟨30635422880998035173559013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163388922031989520925648069 30635422880998035173559013)
              ·
                refine ⟨5744141790187131595042315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30635422880998035173559013 5744141790187131595042315)
                ·
                  refine ⟨8616212685280697392563473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5744141790187131595042315 8616212685280697392563473)
                  ·
                    refine ⟨6462159513960523044422605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8616212685280697392563473 6462159513960523044422605)
                    ·
                      refine ⟨2423309817735196141658477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6462159513960523044422605 2423309817735196141658477)
                      ·
                        rfl

theorem cell23_4719379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 3].length) (baseStart_4719379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719379 prefixEnd_4719379 := by exact prefixLift 4719379
  have htrace : WordTrace (prefixWord ++ tailWord_4719379) baseStart_4719379 baseEnd_4719379 := by
    simpa [prefixWord, tailWord_4719379, baseEnd_4719379] using wordTrace_append hprefix tailTrace_4719379
  have hstable : (prefixWord ++ tailWord_4719379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719379).length < 2 ^ (prefixWord ++ tailWord_4719379).sum := by decide
  have hdescent : baseEnd_4719379 < baseStart_4719379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719444 : List Nat := [2, 4, 1, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_4719444 : Nat := 118140960795 + 4719444 * 2 ^ 59
def prefixEnd_4719444 : Nat := 4983230072969 + 3 ^ 40 * 4719444 * 2
def baseEnd_4719444 : Nat := 2423343193977738387345679

theorem tailTrace_4719444 : CollatzResearch.WordTrace tailWord_4719444 prefixEnd_4719444 2423343193977738387345679 := by
  unfold tailWord_4719444
  simp only [CollatzResearch.WordTrace]
  refine ⟨86066131957133939855014693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114754842609511919806686257 86066131957133939855014693)
  ·
    refine ⟨16137399741962613722815255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86066131957133939855014693 16137399741962613722815255)
    ·
      refine ⟨24206099612943920584222883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16137399741962613722815255 24206099612943920584222883)
      ·
        refine ⟨36309149419415880876334325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24206099612943920584222883 36309149419415880876334325)
        ·
          refine ⟨3403982758070238832156343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36309149419415880876334325 3403982758070238832156343)
          ·
            refine ⟨5105974137105358248234515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403982758070238832156343 5105974137105358248234515)
            ·
              refine ⟨7658961205658037372351773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5105974137105358248234515 7658961205658037372351773)
              ·
                refine ⟨2872110452121764014631915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7658961205658037372351773 2872110452121764014631915)
                ·
                  refine ⟨4308165678182646021947873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872110452121764014631915 4308165678182646021947873)
                  ·
                    refine ⟨3231124258636984516460905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4308165678182646021947873 3231124258636984516460905)
                    ·
                      refine ⟨2423343193977738387345679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231124258636984516460905 2423343193977738387345679)
                      ·
                        rfl

theorem cell23_4719444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_4719444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719444 prefixEnd_4719444 := by exact prefixLift 4719444
  have htrace : WordTrace (prefixWord ++ tailWord_4719444) baseStart_4719444 baseEnd_4719444 := by
    simpa [prefixWord, tailWord_4719444, baseEnd_4719444] using wordTrace_append hprefix tailTrace_4719444
  have hstable : (prefixWord ++ tailWord_4719444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719444).length < 2 ^ (prefixWord ++ tailWord_4719444).sum := by decide
  have hdescent : baseEnd_4719444 < baseStart_4719444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719469 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_4719469 : Nat := 118140960795 + 4719469 * 2 ^ 59
def prefixEnd_4719469 : Nat := 4983230072969 + 3 ^ 40 * 4719469 * 2
def baseEnd_4719469 : Nat := 2423356030994100789533063

theorem tailTrace_4719469 : CollatzResearch.WordTrace tailWord_4719469 prefixEnd_4719469 2423356030994100789533063 := by
  unfold tailWord_4719469
  simp only [CollatzResearch.WordTrace]
  refine ⟨172133175739177308979689461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114755450492784872653126307 172133175739177308979689461)
  ·
    refine ⟨16137485225547872716845887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172133175739177308979689461 16137485225547872716845887)
    ·
      refine ⟨24206227838321809075268831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16137485225547872716845887 24206227838321809075268831)
      ·
        refine ⟨36309341757482713612903247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24206227838321809075268831 36309341757482713612903247)
        ·
          refine ⟨54464012636224070419354871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36309341757482713612903247 54464012636224070419354871)
          ·
            refine ⟨81696018954336105629032307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54464012636224070419354871 81696018954336105629032307)
            ·
              refine ⟨122544028431504158443548461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81696018954336105629032307 122544028431504158443548461)
              ·
                refine ⟨45954010661814059416330673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122544028431504158443548461 45954010661814059416330673)
                ·
                  refine ⟨34465507996360544562248005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45954010661814059416330673 34465507996360544562248005)
                  ·
                    refine ⟨6462282749317602105421501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34465507996360544562248005 6462282749317602105421501)
                    ·
                      refine ⟨2423356030994100789533063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6462282749317602105421501 2423356030994100789533063)
                      ·
                        rfl

theorem cell23_4719469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_4719469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719469 prefixEnd_4719469 := by exact prefixLift 4719469
  have htrace : WordTrace (prefixWord ++ tailWord_4719469) baseStart_4719469 baseEnd_4719469 := by
    simpa [prefixWord, tailWord_4719469, baseEnd_4719469] using wordTrace_append hprefix tailTrace_4719469
  have hstable : (prefixWord ++ tailWord_4719469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719469).length < 2 ^ (prefixWord ++ tailWord_4719469).sum := by decide
  have hdescent : baseEnd_4719469 < baseStart_4719469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719583 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 3, 4]
def baseStart_4719583 : Nat := 118140960795 + 4719583 * 2 ^ 59
def prefixEnd_4719583 : Nat := 4983230072969 + 3 ^ 40 * 4719583 * 2
def baseEnd_4719583 : Nat := 807804855929571114502513

theorem tailTrace_4719583 : CollatzResearch.WordTrace tailWord_4719583 prefixEnd_4719583 807804855929571114502513 := by
  unfold tailWord_4719583
  simp only [CollatzResearch.WordTrace]
  refine ⟨172137333660764306449339403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114758222440509537632892935 172137333660764306449339403)
  ·
    refine ⟨258206000491146459674009105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172137333660764306449339403 258206000491146459674009105)
    ·
      refine ⟨193654500368359844755506829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258206000491146459674009105 193654500368359844755506829)
      ·
        refine ⟨72620437638134941783315061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193654500368359844755506829 72620437638134941783315061)
        ·
          refine ⟨6808166028575150792185787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72620437638134941783315061 6808166028575150792185787)
          ·
            refine ⟨10212249042862726188278681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808166028575150792185787 10212249042862726188278681)
            ·
              refine ⟨7659186782147044641209011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10212249042862726188278681 7659186782147044641209011)
              ·
                refine ⟨11488780173220566961813517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7659186782147044641209011 11488780173220566961813517)
                ·
                  refine ⟨4308292564957712610680069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11488780173220566961813517 4308292564957712610680069)
                  ·
                    refine ⟨807804855929571114502513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4308292564957712610680069 807804855929571114502513)
                    ·
                      rfl

theorem cell23_4719583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 4].length) (baseStart_4719583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719583 prefixEnd_4719583 := by exact prefixLift 4719583
  have htrace : WordTrace (prefixWord ++ tailWord_4719583) baseStart_4719583 baseEnd_4719583 := by
    simpa [prefixWord, tailWord_4719583, baseEnd_4719583] using wordTrace_append hprefix tailTrace_4719583
  have hstable : (prefixWord ++ tailWord_4719583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719583).length < 2 ^ (prefixWord ++ tailWord_4719583).sum := by decide
  have hdescent : baseEnd_4719583 < baseStart_4719583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719634 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4719634 : Nat := 118140960795 + 4719634 * 2 ^ 59
def prefixEnd_4719634 : Nat := 4983230072969 + 3 ^ 40 * 4719634 * 2
def baseEnd_4719634 : Nat := 807813585100697547989935

theorem tailTrace_4719634 : CollatzResearch.WordTrace tailWord_4719634 prefixEnd_4719634 807813585100697547989935 := by
  unfold tailWord_4719634
  simp only [CollatzResearch.WordTrace]
  refine ⟨43034798445894885539861489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114759462522386361439630637 43034798445894885539861489)
  ·
    refine ⟨32276098834421164154896117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43034798445894885539861489 32276098834421164154896117)
    ·
      refine ⟨3025884265726984139521511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32276098834421164154896117 3025884265726984139521511)
      ·
        refine ⟨4538826398590476209282267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3025884265726984139521511 4538826398590476209282267)
        ·
          refine ⟨6808239597885714313923401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4538826398590476209282267 6808239597885714313923401)
          ·
            refine ⟨5106179698414285735442551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6808239597885714313923401 5106179698414285735442551)
            ·
              refine ⟨7659269547621428603163827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106179698414285735442551 7659269547621428603163827)
              ·
                refine ⟨11488904321432142904745741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7659269547621428603163827 11488904321432142904745741)
                ·
                  refine ⟨4308339120537053589279653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11488904321432142904745741 4308339120537053589279653)
                  ·
                    refine ⟨807813585100697547989935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4308339120537053589279653 807813585100697547989935)
                    ·
                      rfl

theorem cell23_4719634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4719634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719634 prefixEnd_4719634 := by exact prefixLift 4719634
  have htrace : WordTrace (prefixWord ++ tailWord_4719634) baseStart_4719634 baseEnd_4719634 := by
    simpa [prefixWord, tailWord_4719634, baseEnd_4719634] using wordTrace_append hprefix tailTrace_4719634
  have hstable : (prefixWord ++ tailWord_4719634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719634).length < 2 ^ (prefixWord ++ tailWord_4719634).sum := by decide
  have hdescent : baseEnd_4719634 < baseStart_4719634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719640 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_4719640 : Nat := 118140960795 + 4719640 * 2 ^ 59
def prefixEnd_4719640 : Nat := 4983230072969 + 3 ^ 40 * 4719640 * 2
def baseEnd_4719640 : Nat := 2423443836186019620494777

theorem tailTrace_4719640 : CollatzResearch.WordTrace tailWord_4719640 prefixEnd_4719640 2423443836186019620494777 := by
  unfold tailWord_4719640
  simp only [CollatzResearch.WordTrace]
  refine ⟨86069706310778902592082187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114759608414371870122776249 86069706310778902592082187)
  ·
    refine ⟨129104559466168353888123281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86069706310778902592082187 129104559466168353888123281)
    ·
      refine ⟨96828419599626265416092461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129104559466168353888123281 96828419599626265416092461)
      ·
        refine ⟨36310657349859849531034673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96828419599626265416092461 36310657349859849531034673)
        ·
          refine ⟨27232993012394887148276005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36310657349859849531034673 27232993012394887148276005)
          ·
            refine ⟨5106186189824041340301751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27232993012394887148276005 5106186189824041340301751)
            ·
              refine ⟨7659279284736062010452627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106186189824041340301751 7659279284736062010452627)
              ·
                refine ⟨11488918927104093015678941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7659279284736062010452627 11488918927104093015678941)
                ·
                  refine ⟨4308344597664034880879603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11488918927104093015678941 4308344597664034880879603)
                  ·
                    refine ⟨6462516896496052321319405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4308344597664034880879603 6462516896496052321319405)
                    ·
                      refine ⟨2423443836186019620494777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6462516896496052321319405 2423443836186019620494777)
                      ·
                        rfl

theorem cell23_4719640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_4719640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719640 prefixEnd_4719640 := by exact prefixLift 4719640
  have htrace : WordTrace (prefixWord ++ tailWord_4719640) baseStart_4719640 baseEnd_4719640 := by
    simpa [prefixWord, tailWord_4719640, baseEnd_4719640] using wordTrace_append hprefix tailTrace_4719640
  have hstable : (prefixWord ++ tailWord_4719640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719640).length < 2 ^ (prefixWord ++ tailWord_4719640).sum := by decide
  have hdescent : baseEnd_4719640 < baseStart_4719640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719659 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 6]
def baseStart_4719659 : Nat := 118140960795 + 4719659 * 2 ^ 59
def prefixEnd_4719659 : Nat := 4983230072969 + 3 ^ 40 * 4719659 * 2
def baseEnd_4719659 : Nat := 2423453592318455046157189

theorem tailTrace_4719659 : CollatzResearch.WordTrace tailWord_4719659 prefixEnd_4719659 2423453592318455046157189 := by
  unfold tailWord_4719659
  simp only [CollatzResearch.WordTrace]
  refine ⟨172140105608488971429106031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114760070405659314286070687 172140105608488971429106031)
  ·
    refine ⟨258210158412733457143659047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172140105608488971429106031 258210158412733457143659047)
    ·
      refine ⟨387315237619100185715488571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258210158412733457143659047 387315237619100185715488571)
      ·
        refine ⟨580972856428650278573232857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387315237619100185715488571 580972856428650278573232857)
        ·
          refine ⟨435729642321487708929924643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580972856428650278573232857 435729642321487708929924643)
          ·
            refine ⟨653594463482231563394886965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435729642321487708929924643 653594463482231563394886965)
            ·
              refine ⟨61274480951459209068270653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 653594463482231563394886965 61274480951459209068270653)
              ·
                refine ⟨22977930356797203400601495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61274480951459209068270653 22977930356797203400601495)
                ·
                  refine ⟨34466895535195805100902243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22977930356797203400601495 34466895535195805100902243)
                  ·
                    refine ⟨51700343302793707651353365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34466895535195805100902243 51700343302793707651353365)
                    ·
                      refine ⟨2423453592318455046157189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51700343302793707651353365 2423453592318455046157189)
                      ·
                        rfl

theorem cell23_4719659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_4719659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719659 prefixEnd_4719659 := by exact prefixLift 4719659
  have htrace : WordTrace (prefixWord ++ tailWord_4719659) baseStart_4719659 baseEnd_4719659 := by
    simpa [prefixWord, tailWord_4719659, baseEnd_4719659] using wordTrace_append hprefix tailTrace_4719659
  have hstable : (prefixWord ++ tailWord_4719659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719659).length < 2 ^ (prefixWord ++ tailWord_4719659).sum := by decide
  have hdescent : baseEnd_4719659 < baseStart_4719659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719676 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_4719676 : Nat := 118140960795 + 4719676 * 2 ^ 59
def prefixEnd_4719676 : Nat := 4983230072969 + 3 ^ 40 * 4719676 * 2
def baseEnd_4719676 : Nat := 2423462321489581479644611

theorem tailTrace_4719676 : CollatzResearch.WordTrace tailWord_4719676 prefixEnd_4719676 2423462321489581479644611 := by
  unfold tailWord_4719676
  simp only [CollatzResearch.WordTrace]
  refine ⟨86070362824713691666237441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114760483766284922221649921 86070362824713691666237441)
  ·
    refine ⟨64552772118535268749678081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86070362824713691666237441 64552772118535268749678081)
    ·
      refine ⟨48414579088901451562258561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64552772118535268749678081 48414579088901451562258561)
      ·
        refine ⟨36310934316676088671693921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48414579088901451562258561 36310934316676088671693921)
        ·
          refine ⟨27233200737507066503770441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36310934316676088671693921 27233200737507066503770441)
          ·
            refine ⟨20424900553130299877827831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27233200737507066503770441 20424900553130299877827831)
            ·
              refine ⟨30637350829695449816741747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20424900553130299877827831 30637350829695449816741747)
              ·
                refine ⟨45956026244543174725112621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30637350829695449816741747 45956026244543174725112621)
                ·
                  refine ⟨17233509841703690521917233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45956026244543174725112621 17233509841703690521917233)
                  ·
                    refine ⟨12925132381277767891437925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17233509841703690521917233 12925132381277767891437925)
                    ·
                      refine ⟨2423462321489581479644611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12925132381277767891437925 2423462321489581479644611)
                      ·
                        rfl

theorem cell23_4719676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_4719676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719676 prefixEnd_4719676 := by exact prefixLift 4719676
  have htrace : WordTrace (prefixWord ++ tailWord_4719676) baseStart_4719676 baseEnd_4719676 := by
    simpa [prefixWord, tailWord_4719676, baseEnd_4719676] using wordTrace_append hprefix tailTrace_4719676
  have hstable : (prefixWord ++ tailWord_4719676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719676).length < 2 ^ (prefixWord ++ tailWord_4719676).sum := by decide
  have hdescent : baseEnd_4719676 < baseStart_4719676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719689 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_4719689 : Nat := 118140960795 + 4719689 * 2 ^ 59
def prefixEnd_4719689 : Nat := 4983230072969 + 3 ^ 40 * 4719689 * 2
def baseEnd_4719689 : Nat := 2423468996738089928782051

theorem tailTrace_4719689 : CollatzResearch.WordTrace tailWord_4719689 prefixEnd_4719689 2423468996738089928782051 := by
  unfold tailWord_4719689
  simp only [CollatzResearch.WordTrace]
  refine ⟨172141199798380286552698121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114760799865586857701798747 172141199798380286552698121)
  ·
    refine ⟨129105899848785214914523591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172141199798380286552698121 129105899848785214914523591)
    ·
      refine ⟨193658849773177822371785387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129105899848785214914523591 193658849773177822371785387)
      ·
        refine ⟨290488274659766733557678081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193658849773177822371785387 290488274659766733557678081)
        ·
          refine ⟨217866205994825050168258561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290488274659766733557678081 217866205994825050168258561)
          ·
            refine ⟨163399654496118787626193921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217866205994825050168258561 163399654496118787626193921)
            ·
              refine ⟨122549740872089090719645441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163399654496118787626193921 122549740872089090719645441)
              ·
                refine ⟨91912305654066818039734081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122549740872089090719645441 91912305654066818039734081)
                ·
                  refine ⟨68934229240550113529800561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91912305654066818039734081 68934229240550113529800561)
                  ·
                    refine ⟨51700671930412585147350421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68934229240550113529800561 51700671930412585147350421)
                    ·
                      refine ⟨2423468996738089928782051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51700671930412585147350421 2423468996738089928782051)
                      ·
                        rfl

theorem cell23_4719689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_4719689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719689 prefixEnd_4719689 := by exact prefixLift 4719689
  have htrace : WordTrace (prefixWord ++ tailWord_4719689) baseStart_4719689 baseEnd_4719689 := by
    simpa [prefixWord, tailWord_4719689, baseEnd_4719689] using wordTrace_append hprefix tailTrace_4719689
  have hstable : (prefixWord ++ tailWord_4719689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719689).length < 2 ^ (prefixWord ++ tailWord_4719689).sum := by decide
  have hdescent : baseEnd_4719689 < baseStart_4719689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719699 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 2, 7]
def baseStart_4719699 : Nat := 118140960795 + 4719699 * 2 ^ 59
def prefixEnd_4719699 : Nat := 4983230072969 + 3 ^ 40 * 4719699 * 2
def baseEnd_4719699 : Nat := 807824710514878296552335

theorem tailTrace_4719699 : CollatzResearch.WordTrace tailWord_4719699 prefixEnd_4719699 807824710514878296552335 := by
  unfold tailWord_4719699
  simp only [CollatzResearch.WordTrace]
  refine ⟨172141564528344058260562151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114761043018896038840374767 172141564528344058260562151)
  ·
    refine ⟨258212346792516087390843227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172141564528344058260562151 258212346792516087390843227)
    ·
      refine ⟨387318520188774131086264841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258212346792516087390843227 387318520188774131086264841)
      ·
        refine ⟨290488890141580598314698631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387318520188774131086264841 290488890141580598314698631)
        ·
          refine ⟨435733335212370897472047947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290488890141580598314698631 435733335212370897472047947)
          ·
            refine ⟨653600002818556346208071921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435733335212370897472047947 653600002818556346208071921)
            ·
              refine ⟨490200002113917259656053941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653600002818556346208071921 490200002113917259656053941)
              ·
                refine ⟨45956250198179743092755057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 490200002113917259656053941 45956250198179743092755057)
                ·
                  refine ⟨34467187648634807319566293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45956250198179743092755057 34467187648634807319566293)
                  ·
                    refine ⟨807824710514878296552335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34467187648634807319566293 807824710514878296552335)
                    ·
                      rfl

theorem cell23_4719699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 7].length) (baseStart_4719699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719699 prefixEnd_4719699 := by exact prefixLift 4719699
  have htrace : WordTrace (prefixWord ++ tailWord_4719699) baseStart_4719699 baseEnd_4719699 := by
    simpa [prefixWord, tailWord_4719699, baseEnd_4719699] using wordTrace_append hprefix tailTrace_4719699
  have hstable : (prefixWord ++ tailWord_4719699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719699).length < 2 ^ (prefixWord ++ tailWord_4719699).sum := by decide
  have hdescent : baseEnd_4719699 < baseStart_4719699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719720 : List Nat := [2, 1, 4, 4, 1, 1, 3, 7]
def baseStart_4719720 : Nat := 118140960795 + 4719720 * 2 ^ 59
def prefixEnd_4719720 : Nat := 4983230072969 + 3 ^ 40 * 4719720 * 2
def baseEnd_4719720 : Nat := 89758700542162196573867

theorem tailTrace_4719720 : CollatzResearch.WordTrace tailWord_4719720 prefixEnd_4719720 89758700542162196573867 := by
  unfold tailWord_4719720
  simp only [CollatzResearch.WordTrace]
  refine ⟨86071165230633989423538307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114761553640845319231384409 86071165230633989423538307)
  ·
    refine ⟨129106747845950984135307461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86071165230633989423538307 129106747845950984135307461)
    ·
      refine ⟨24207515221115809525370149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129106747845950984135307461 24207515221115809525370149)
      ·
        refine ⟨4538909103959214286006903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24207515221115809525370149 4538909103959214286006903)
        ·
          refine ⟨6808363655938821429010355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4538909103959214286006903 6808363655938821429010355)
          ·
            refine ⟨10212545483908232143515533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808363655938821429010355 10212545483908232143515533)
            ·
              refine ⟨3829704556465587053818325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10212545483908232143515533 3829704556465587053818325)
              ·
                refine ⟨89758700542162196573867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3829704556465587053818325 89758700542162196573867)
                ·
                  rfl

theorem cell23_4719720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 7].length) (baseStart_4719720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719720 prefixEnd_4719720 := by exact prefixLift 4719720
  have htrace : WordTrace (prefixWord ++ tailWord_4719720) baseStart_4719720 baseEnd_4719720 := by
    simpa [prefixWord, tailWord_4719720, baseEnd_4719720] using wordTrace_append hprefix tailTrace_4719720
  have hstable : (prefixWord ++ tailWord_4719720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719720).length < 2 ^ (prefixWord ++ tailWord_4719720).sum := by decide
  have hdescent : baseEnd_4719720 < baseStart_4719720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719740 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_4719740 : Nat := 118140960795 + 4719740 * 2 ^ 59
def prefixEnd_4719740 : Nat := 4983230072969 + 3 ^ 40 * 4719740 * 2
def baseEnd_4719740 : Nat := 2423495184251469229244317

theorem tailTrace_4719740 : CollatzResearch.WordTrace tailWord_4719740 prefixEnd_4719740 2423495184251469229244317 := by
  unfold tailWord_4719740
  simp only [CollatzResearch.WordTrace]
  refine ⟨86071529960597761131402337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114762039947463681508536449 86071529960597761131402337)
  ·
    refine ⟨64553647470448320848551753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86071529960597761131402337 64553647470448320848551753)
    ·
      refine ⟨48415235602836240636413815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64553647470448320848551753 48415235602836240636413815)
      ·
        refine ⟨72622853404254360954620723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48415235602836240636413815 72622853404254360954620723)
        ·
          refine ⟨108934280106381541431931085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72622853404254360954620723 108934280106381541431931085)
          ·
            refine ⟨40850355039893078036974157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108934280106381541431931085 40850355039893078036974157)
            ·
              refine ⟨15318883139959904263865309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40850355039893078036974157 15318883139959904263865309)
              ·
                refine ⟨5744581177484964098949491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15318883139959904263865309 5744581177484964098949491)
                ·
                  refine ⟨8616871766227446148424237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5744581177484964098949491 8616871766227446148424237)
                  ·
                    refine ⟨3231326912335292305659089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8616871766227446148424237 3231326912335292305659089)
                    ·
                      refine ⟨2423495184251469229244317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231326912335292305659089 2423495184251469229244317)
                      ·
                        rfl

theorem cell23_4719740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_4719740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719740 prefixEnd_4719740 := by exact prefixLift 4719740
  have htrace : WordTrace (prefixWord ++ tailWord_4719740) baseStart_4719740 baseEnd_4719740 := by
    simpa [prefixWord, tailWord_4719740, baseEnd_4719740] using wordTrace_append hprefix tailTrace_4719740
  have hstable : (prefixWord ++ tailWord_4719740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719740).length < 2 ^ (prefixWord ++ tailWord_4719740).sum := by decide
  have hdescent : baseEnd_4719740 < baseStart_4719740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719756 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_4719756 : Nat := 118140960795 + 4719756 * 2 ^ 59
def prefixEnd_4719756 : Nat := 4983230072969 + 3 ^ 40 * 4719756 * 2
def baseEnd_4719756 : Nat := 2423503399941941166644243

theorem tailTrace_4719756 : CollatzResearch.WordTrace tailWord_4719756 prefixEnd_4719756 2423503399941941166644243 := by
  unfold tailWord_4719756
  simp only [CollatzResearch.WordTrace]
  refine ⟨86071821744568778497693561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114762428992758371330258081 86071821744568778497693561)
  ·
    refine ⟨64553866308426583873270171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86071821744568778497693561 64553866308426583873270171)
    ·
      refine ⟨96830799462639875809905257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64553866308426583873270171 96830799462639875809905257)
      ·
        refine ⟨72623099596979906857428943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96830799462639875809905257 72623099596979906857428943)
        ·
          refine ⟨108934649395469860286143415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72623099596979906857428943 108934649395469860286143415)
          ·
            refine ⟨163401974093204790429215123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108934649395469860286143415 163401974093204790429215123)
            ·
              refine ⟨245102961139807185643822685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163401974093204790429215123 245102961139807185643822685)
              ·
                refine ⟨91913610427427694616433507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245102961139807185643822685 91913610427427694616433507)
                ·
                  refine ⟨137870415641141541924650261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91913610427427694616433507 137870415641141541924650261)
                  ·
                    refine ⟨6462675733178509777717981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 137870415641141541924650261 6462675733178509777717981)
                    ·
                      refine ⟨2423503399941941166644243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6462675733178509777717981 2423503399941941166644243)
                      ·
                        rfl

theorem cell23_4719756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_4719756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719756 prefixEnd_4719756 := by exact prefixLift 4719756
  have htrace : WordTrace (prefixWord ++ tailWord_4719756) baseStart_4719756 baseEnd_4719756 := by
    simpa [prefixWord, tailWord_4719756, baseEnd_4719756] using wordTrace_append hprefix tailTrace_4719756
  have hstable : (prefixWord ++ tailWord_4719756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719756).length < 2 ^ (prefixWord ++ tailWord_4719756).sum := by decide
  have hdescent : baseEnd_4719756 < baseStart_4719756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719774 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_4719774 : Nat := 118140960795 + 4719774 * 2 ^ 59
def prefixEnd_4719774 : Nat := 4983230072969 + 3 ^ 40 * 4719774 * 2
def baseEnd_4719774 : Nat := 2423512642593722096219161

theorem tailTrace_4719774 : CollatzResearch.WordTrace tailWord_4719774 prefixEnd_4719774 2423512642593722096219161 := by
  unfold tailWord_4719774
  simp only [CollatzResearch.WordTrace]
  refine ⟨21518037500384043258692797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114762866668714897379694917 21518037500384043258692797)
  ·
    refine ⟨8069264062644016222009799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21518037500384043258692797 8069264062644016222009799)
    ·
      refine ⟨12103896093966024333014699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8069264062644016222009799 12103896093966024333014699)
      ·
        refine ⟨18155844140949036499522049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12103896093966024333014699 18155844140949036499522049)
        ·
          refine ⟨13616883105711777374641537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18155844140949036499522049 13616883105711777374641537)
          ·
            refine ⟨10212662329283833030981153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13616883105711777374641537 10212662329283833030981153)
            ·
              refine ⟨7659496746962874773235865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10212662329283833030981153 7659496746962874773235865)
              ·
                refine ⟨5744622560222156079926899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7659496746962874773235865 5744622560222156079926899)
                ·
                  refine ⟨8616933840333234119890349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5744622560222156079926899 8616933840333234119890349)
                  ·
                    refine ⟨3231350190124962794958881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8616933840333234119890349 3231350190124962794958881)
                    ·
                      refine ⟨2423512642593722096219161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231350190124962794958881 2423512642593722096219161)
                      ·
                        rfl

theorem cell23_4719774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_4719774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719774 prefixEnd_4719774 := by exact prefixLift 4719774
  have htrace : WordTrace (prefixWord ++ tailWord_4719774) baseStart_4719774 baseEnd_4719774 := by
    simpa [prefixWord, tailWord_4719774, baseEnd_4719774] using wordTrace_append hprefix tailTrace_4719774
  have hstable : (prefixWord ++ tailWord_4719774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719774).length < 2 ^ (prefixWord ++ tailWord_4719774).sum := by decide
  have hdescent : baseEnd_4719774 < baseStart_4719774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719776 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 7]
def baseStart_4719776 : Nat := 118140960795 + 4719776 * 2 ^ 59
def prefixEnd_4719776 : Nat := 4983230072969 + 3 ^ 40 * 4719776 * 2
def baseEnd_4719776 : Nat := 269279296617225676488239

theorem tailTrace_4719776 : CollatzResearch.WordTrace tailWord_4719776 prefixEnd_4719776 269279296617225676488239 := by
  unfold tailWord_4719776
  simp only [CollatzResearch.WordTrace]
  refine ⟨86072186474532550205557591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114762915299376733607410121 86072186474532550205557591)
  ·
    refine ⟨129108279711798825308336387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86072186474532550205557591 129108279711798825308336387)
    ·
      refine ⟨193662419567698237962504581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129108279711798825308336387 193662419567698237962504581)
      ·
        refine ⟨36311703668943419617969609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193662419567698237962504581 36311703668943419617969609)
        ·
          refine ⟨27233777751707564713477207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36311703668943419617969609 27233777751707564713477207)
          ·
            refine ⟨40850666627561347070215811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27233777751707564713477207 40850666627561347070215811)
            ·
              refine ⟨61275999941342020605323717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40850666627561347070215811 61275999941342020605323717)
              ·
                refine ⟨11489249989001628863498197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61275999941342020605323717 11489249989001628863498197)
                ·
                  refine ⟨269279296617225676488239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11489249989001628863498197 269279296617225676488239)
                  ·
                    rfl

theorem cell23_4719776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 7].length) (baseStart_4719776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719776 prefixEnd_4719776 := by exact prefixLift 4719776
  have htrace : WordTrace (prefixWord ++ tailWord_4719776) baseStart_4719776 baseEnd_4719776 := by
    simpa [prefixWord, tailWord_4719776, baseEnd_4719776] using wordTrace_append hprefix tailTrace_4719776
  have hstable : (prefixWord ++ tailWord_4719776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719776).length < 2 ^ (prefixWord ++ tailWord_4719776).sum := by decide
  have hdescent : baseEnd_4719776 < baseStart_4719776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719813 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 2, 5, 2]
def baseStart_4719813 : Nat := 118140960795 + 4719813 * 2 ^ 59
def prefixEnd_4719813 : Nat := 4983230072969 + 3 ^ 40 * 4719813 * 2
def baseEnd_4719813 : Nat := 2423532668339247443631481

theorem tailTrace_4719813 : CollatzResearch.WordTrace tailWord_4719813 prefixEnd_4719813 2423532668339247443631481 := by
  unfold tailWord_4719813
  simp only [CollatzResearch.WordTrace]
  refine ⟨172145722449931055730212093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114763814966620703820141395 172145722449931055730212093)
  ·
    refine ⟨64554645918724145898829535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172145722449931055730212093 64554645918724145898829535)
    ·
      refine ⟨96831968878086218848244303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64554645918724145898829535 96831968878086218848244303)
      ·
        refine ⟨145247953317129328272366455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96831968878086218848244303 145247953317129328272366455)
        ·
          refine ⟨217871929975693992408549683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145247953317129328272366455 217871929975693992408549683)
          ·
            refine ⟨326807894963540988612824525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217871929975693992408549683 326807894963540988612824525)
            ·
              refine ⟨122552960611327870729809197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326807894963540988612824525 122552960611327870729809197)
              ·
                refine ⟨45957360229247951523678449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122552960611327870729809197 45957360229247951523678449)
                ·
                  refine ⟨34468020171935963642758837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45957360229247951523678449 34468020171935963642758837)
                  ·
                    refine ⟨3231376891118996591508641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34468020171935963642758837 3231376891118996591508641)
                    ·
                      refine ⟨2423532668339247443631481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231376891118996591508641 2423532668339247443631481)
                      ·
                        rfl

theorem cell23_4719813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_4719813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719813 prefixEnd_4719813 := by exact prefixLift 4719813
  have htrace : WordTrace (prefixWord ++ tailWord_4719813) baseStart_4719813 baseEnd_4719813 := by
    simpa [prefixWord, tailWord_4719813, baseEnd_4719813] using wordTrace_append hprefix tailTrace_4719813
  have hstable : (prefixWord ++ tailWord_4719813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719813).length < 2 ^ (prefixWord ++ tailWord_4719813).sum := by decide
  have hdescent : baseEnd_4719813 < baseStart_4719813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719816 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_4719816 : Nat := 118140960795 + 4719816 * 2 ^ 59
def prefixEnd_4719816 : Nat := 4983230072969 + 3 ^ 40 * 4719816 * 2
def baseEnd_4719816 : Nat := 2423534208781210931893967

theorem tailTrace_4719816 : CollatzResearch.WordTrace tailWord_4719816 prefixEnd_4719816 2423534208781210931893967 := by
  unfold tailWord_4719816
  simp only [CollatzResearch.WordTrace]
  refine ⟨86072915934460093621285651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114763887912613458161714201 86072915934460093621285651)
  ·
    refine ⟨129109373901690140431928477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86072915934460093621285651 129109373901690140431928477)
    ·
      refine ⟨48416015213133802661973179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129109373901690140431928477 48416015213133802661973179)
      ·
        refine ⟨72624022819700703992959769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48416015213133802661973179 72624022819700703992959769)
        ·
          refine ⟨54468017114775527994719827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72624022819700703992959769 54468017114775527994719827)
          ·
            refine ⟨81702025672163291992079741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54468017114775527994719827 81702025672163291992079741)
            ·
              refine ⟨30638259627061234497029903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81702025672163291992079741 30638259627061234497029903)
              ·
                refine ⟨45957389440591851745544855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30638259627061234497029903 45957389440591851745544855)
                ·
                  refine ⟨68936084160887777618317283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45957389440591851745544855 68936084160887777618317283)
                  ·
                    refine ⟨103404126241331666427475925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68936084160887777618317283 103404126241331666427475925)
                    ·
                      refine ⟨2423534208781210931893967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103404126241331666427475925 2423534208781210931893967)
                      ·
                        rfl

theorem cell23_4719816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_4719816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719816 prefixEnd_4719816 := by exact prefixLift 4719816
  have htrace : WordTrace (prefixWord ++ tailWord_4719816) baseStart_4719816 baseEnd_4719816 := by
    simpa [prefixWord, tailWord_4719816, baseEnd_4719816] using wordTrace_append hprefix tailTrace_4719816
  have hstable : (prefixWord ++ tailWord_4719816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719816).length < 2 ^ (prefixWord ++ tailWord_4719816).sum := by decide
  have hdescent : baseEnd_4719816 < baseStart_4719816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719883 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 6]
def baseStart_4719883 : Nat := 118140960795 + 4719883 * 2 ^ 59
def prefixEnd_4719883 : Nat := 4983230072969 + 3 ^ 40 * 4719883 * 2
def baseEnd_4719883 : Nat := 269285401331673574417351

theorem tailTrace_4719883 : CollatzResearch.WordTrace tailWord_4719883 prefixEnd_4719883 269285401331673574417351 := by
  unfold tailWord_4719883
  simp only [CollatzResearch.WordTrace]
  refine ⟨172148275559677457685260303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114765517039784971790173535 172148275559677457685260303)
  ·
    refine ⟨258222413339516186527890455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172148275559677457685260303 258222413339516186527890455)
    ·
      refine ⟨387333620009274279791835683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258222413339516186527890455 387333620009274279791835683)
      ·
        refine ⟨581000430013911419687753525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387333620009274279791835683 581000430013911419687753525)
        ·
          refine ⟨54468790313804195595726893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 581000430013911419687753525 54468790313804195595726893)
          ·
            refine ⟨20425796367676573348397585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54468790313804195595726893 20425796367676573348397585)
            ·
              refine ⟨15319347275757430011298189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20425796367676573348397585 15319347275757430011298189)
              ·
                refine ⟨5744755228409036254236821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15319347275757430011298189 5744755228409036254236821)
                ·
                  refine ⟨269285401331673574417351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5744755228409036254236821 269285401331673574417351)
                  ·
                    rfl

theorem cell23_4719883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 6].length) (baseStart_4719883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719883 prefixEnd_4719883 := by exact prefixLift 4719883
  have htrace : WordTrace (prefixWord ++ tailWord_4719883) baseStart_4719883 baseEnd_4719883 := by
    simpa [prefixWord, tailWord_4719883, baseEnd_4719883] using wordTrace_append hprefix tailTrace_4719883
  have hstable : (prefixWord ++ tailWord_4719883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719883).length < 2 ^ (prefixWord ++ tailWord_4719883).sum := by decide
  have hdescent : baseEnd_4719883 < baseStart_4719883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719904 : List Nat := [2, 1, 1, 5, 3, 1, 2, 3, 1, 4]
def baseStart_4719904 : Nat := 118140960795 + 4719904 * 2 ^ 59
def prefixEnd_4719904 : Nat := 4983230072969 + 3 ^ 40 * 4719904 * 2
def baseEnd_4719904 : Nat := 807859798359602195864521

theorem tailTrace_4719904 : CollatzResearch.WordTrace tailWord_4719904 prefixEnd_4719904 807859798359602195864521 := by
  unfold tailWord_4719904
  simp only [CollatzResearch.WordTrace]
  refine ⟨86074520746300689135887383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114766027661734252181183177 86074520746300689135887383)
  ·
    refine ⟨129111781119451033703831075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86074520746300689135887383 129111781119451033703831075)
    ·
      refine ⟨193667671679176550555746613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129111781119451033703831075 193667671679176550555746613)
      ·
        refine ⟨18156344219922801614601245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193667671679176550555746613 18156344219922801614601245)
        ·
          refine ⟨6808629082471050605475467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18156344219922801614601245 6808629082471050605475467)
          ·
            refine ⟨10212943623706575908213201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808629082471050605475467 10212943623706575908213201)
            ·
              refine ⟨7659707717779931931159901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10212943623706575908213201 7659707717779931931159901)
              ·
                refine ⟨2872390394167474474184963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7659707717779931931159901 2872390394167474474184963)
                ·
                  refine ⟨4308585591251211711277445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872390394167474474184963 4308585591251211711277445)
                  ·
                    refine ⟨807859798359602195864521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4308585591251211711277445 807859798359602195864521)
                    ·
                      rfl

theorem cell23_4719904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 1, 4].length) (baseStart_4719904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719904 prefixEnd_4719904 := by exact prefixLift 4719904
  have htrace : WordTrace (prefixWord ++ tailWord_4719904) baseStart_4719904 baseEnd_4719904 := by
    simpa [prefixWord, tailWord_4719904, baseEnd_4719904] using wordTrace_append hprefix tailTrace_4719904
  have hstable : (prefixWord ++ tailWord_4719904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719904).length < 2 ^ (prefixWord ++ tailWord_4719904).sum := by decide
  have hdescent : baseEnd_4719904 < baseStart_4719904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719917 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 6]
def baseStart_4719917 : Nat := 118140960795 + 4719917 * 2 ^ 59
def prefixEnd_4719917 : Nat := 4983230072969 + 3 ^ 40 * 4719917 * 2
def baseEnd_4719917 : Nat := 269287341147479448525667

theorem tailTrace_4719917 : CollatzResearch.WordTrace tailWord_4719917 prefixEnd_4719917 269287341147479448525667 := by
  unfold tailWord_4719917
  simp only [CollatzResearch.WordTrace]
  refine ⟨172149515641554281491998005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114766343761036187661332003 172149515641554281491998005)
  ·
    refine ⟨16139017091395713889874813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172149515641554281491998005 16139017091395713889874813)
    ·
      refine ⟨6052131409273392708703055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16139017091395713889874813 6052131409273392708703055)
      ·
        refine ⟨9078197113910089063054583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052131409273392708703055 9078197113910089063054583)
        ·
          refine ⟨13617295670865133594581875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9078197113910089063054583 13617295670865133594581875)
          ·
            refine ⟨20425943506297700391872813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13617295670865133594581875 20425943506297700391872813)
            ·
              refine ⟨7659728814861637646952305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20425943506297700391872813 7659728814861637646952305)
              ·
                refine ⟨5744796611146228235214229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7659728814861637646952305 5744796611146228235214229)
                ·
                  refine ⟨269287341147479448525667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5744796611146228235214229 269287341147479448525667)
                  ·
                    rfl

theorem cell23_4719917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_4719917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719917 prefixEnd_4719917 := by exact prefixLift 4719917
  have htrace : WordTrace (prefixWord ++ tailWord_4719917) baseStart_4719917 baseEnd_4719917 := by
    simpa [prefixWord, tailWord_4719917, baseEnd_4719917] using wordTrace_append hprefix tailTrace_4719917
  have hstable : (prefixWord ++ tailWord_4719917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719917).length < 2 ^ (prefixWord ++ tailWord_4719917).sum := by decide
  have hdescent : baseEnd_4719917 < baseStart_4719917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719920 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 4, 3, 2]
def baseStart_4719920 : Nat := 118140960795 + 4719920 * 2 ^ 59
def prefixEnd_4719920 : Nat := 4983230072969 + 3 ^ 40 * 4719920 * 2
def baseEnd_4719920 : Nat := 2423587610769278524993489

theorem tailTrace_4719920 : CollatzResearch.WordTrace tailWord_4719920 prefixEnd_4719920 2423587610769278524993489 := by
  unfold tailWord_4719920
  simp only [CollatzResearch.WordTrace]
  refine ⟨86074812530271706502178607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114766416707028942002904809 86074812530271706502178607)
  ·
    refine ⟨129112218795407559753267911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86074812530271706502178607 129112218795407559753267911)
    ·
      refine ⟨193668328193111339629901867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129112218795407559753267911 193668328193111339629901867)
      ·
        refine ⟨290502492289667009444852801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193668328193111339629901867 290502492289667009444852801)
        ·
          refine ⟨217876869217250257083639601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290502492289667009444852801 217876869217250257083639601)
          ·
            refine ⟨163407651912937692812729701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217876869217250257083639601 163407651912937692812729701)
            ·
              refine ⟨30638934733675817402386819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163407651912937692812729701 30638934733675817402386819)
              ·
                refine ⟨45958402100513726103580229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30638934733675817402386819 45958402100513726103580229)
                ·
                  refine ⟨8617200393846323644421293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45958402100513726103580229 8617200393846323644421293)
                  ·
                    refine ⟨3231450147692371366657985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8617200393846323644421293 3231450147692371366657985)
                    ·
                      refine ⟨2423587610769278524993489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231450147692371366657985 2423587610769278524993489)
                      ·
                        rfl

theorem cell23_4719920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 3, 2].length) (baseStart_4719920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719920 prefixEnd_4719920 := by exact prefixLift 4719920
  have htrace : WordTrace (prefixWord ++ tailWord_4719920) baseStart_4719920 baseEnd_4719920 := by
    simpa [prefixWord, tailWord_4719920, baseEnd_4719920] using wordTrace_append hprefix tailTrace_4719920
  have hstable : (prefixWord ++ tailWord_4719920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719920).length < 2 ^ (prefixWord ++ tailWord_4719920).sum := by decide
  have hdescent : baseEnd_4719920 < baseStart_4719920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719937 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4719937 : Nat := 118140960795 + 4719937 * 2 ^ 59
def prefixEnd_4719937 : Nat := 4983230072969 + 3 ^ 40 * 4719937 * 2
def baseEnd_4719937 : Nat := 2423596339940404958480911

theorem tailTrace_4719937 : CollatzResearch.WordTrace tailWord_4719937 prefixEnd_4719937 2423596339940404958480911 := by
  unfold tailWord_4719937
  simp only [CollatzResearch.WordTrace]
  refine ⟨172150245101481824907726065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114766830067654549938484043 172150245101481824907726065)
  ·
    refine ⟨129112683826111368680794549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172150245101481824907726065 129112683826111368680794549)
    ·
      refine ⟨12104314108697940813824489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129112683826111368680794549 12104314108697940813824489)
      ·
        refine ⟨9078235581523455610368367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12104314108697940813824489 9078235581523455610368367)
        ·
          refine ⟨13617353372285183415552551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9078235581523455610368367 13617353372285183415552551)
          ·
            refine ⟨20426030058427775123328827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13617353372285183415552551 20426030058427775123328827)
            ·
              refine ⟨30639045087641662684993241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20426030058427775123328827 30639045087641662684993241)
              ·
                refine ⟨22979283815731247013744931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30639045087641662684993241 22979283815731247013744931)
                ·
                  refine ⟨34468925723596870520617397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22979283815731247013744931 34468925723596870520617397)
                  ·
                    refine ⟨3231461786587206611307881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34468925723596870520617397 3231461786587206611307881)
                    ·
                      refine ⟨2423596339940404958480911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231461786587206611307881 2423596339940404958480911)
                      ·
                        rfl

theorem cell23_4719937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4719937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719937 prefixEnd_4719937 := by exact prefixLift 4719937
  have htrace : WordTrace (prefixWord ++ tailWord_4719937) baseStart_4719937 baseEnd_4719937 := by
    simpa [prefixWord, tailWord_4719937, baseEnd_4719937] using wordTrace_append hprefix tailTrace_4719937
  have hstable : (prefixWord ++ tailWord_4719937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719937).length < 2 ^ (prefixWord ++ tailWord_4719937).sum := by decide
  have hdescent : baseEnd_4719937 < baseStart_4719937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719950 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_4719950 : Nat := 118140960795 + 4719950 * 2 ^ 59
def prefixEnd_4719950 : Nat := 4983230072969 + 3 ^ 40 * 4719950 * 2
def baseEnd_4719950 : Nat := 2423603015188913407618351

theorem tailTrace_4719950 : CollatzResearch.WordTrace tailWord_4719950 prefixEnd_4719950 2423603015188913407618351 := by
  unfold tailWord_4719950
  simp only [CollatzResearch.WordTrace]
  refine ⟨21518839906304341015993663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114767146166956485418632869 21518839906304341015993663)
  ·
    refine ⟨32278259859456511523990495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21518839906304341015993663 32278259859456511523990495)
    ·
      refine ⟨48417389789184767285985743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32278259859456511523990495 48417389789184767285985743)
      ·
        refine ⟨72626084683777150928978615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48417389789184767285985743 72626084683777150928978615)
        ·
          refine ⟨108939127025665726393467923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72626084683777150928978615 108939127025665726393467923)
          ·
            refine ⟨163408690538498589590201885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108939127025665726393467923 163408690538498589590201885)
            ·
              refine ⟨61278258951936971096325707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163408690538498589590201885 61278258951936971096325707)
              ·
                refine ⟨91917388427905456644488561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61278258951936971096325707 91917388427905456644488561)
                ·
                  refine ⟨68938041320929092483366421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91917388427905456644488561 68938041320929092483366421)
                  ·
                    refine ⟨3231470686918551210157801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68938041320929092483366421 3231470686918551210157801)
                    ·
                      refine ⟨2423603015188913407618351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231470686918551210157801 2423603015188913407618351)
                      ·
                        rfl

theorem cell23_4719950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_4719950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719950 prefixEnd_4719950 := by exact prefixLift 4719950
  have htrace : WordTrace (prefixWord ++ tailWord_4719950) baseStart_4719950 baseEnd_4719950 := by
    simpa [prefixWord, tailWord_4719950, baseEnd_4719950] using wordTrace_append hprefix tailTrace_4719950
  have hstable : (prefixWord ++ tailWord_4719950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719950).length < 2 ^ (prefixWord ++ tailWord_4719950).sum := by decide
  have hdescent : baseEnd_4719950 < baseStart_4719950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719953 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_4719953 : Nat := 118140960795 + 4719953 * 2 ^ 59
def prefixEnd_4719953 : Nat := 4983230072969 + 3 ^ 40 * 4719953 * 2
def baseEnd_4719953 : Nat := 2423604555630876895880837

theorem tailTrace_4719953 : CollatzResearch.WordTrace tailWord_4719953 prefixEnd_4719953 2423604555630876895880837 := by
  unfold tailWord_4719953
  simp only [CollatzResearch.WordTrace]
  refine ⟨172150828669423859640308513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114767219112949239760205675 172150828669423859640308513)
  ·
    refine ⟨129113121502067894730231385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172150828669423859640308513 129113121502067894730231385)
    ·
      refine ⟨96834841126550921047673539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129113121502067894730231385 96834841126550921047673539)
      ·
        refine ⟨145252261689826381571510309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96834841126550921047673539 145252261689826381571510309)
        ·
          refine ⟨27234799066842446544658183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145252261689826381571510309 27234799066842446544658183)
          ·
            refine ⟨40852198600263669816987275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27234799066842446544658183 40852198600263669816987275)
            ·
              refine ⟨61278297900395504725480913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40852198600263669816987275 61278297900395504725480913)
              ·
                refine ⟨45958723425296628544110685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61278297900395504725480913 45958723425296628544110685)
                ·
                  refine ⟨17234521284486235704041507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45958723425296628544110685 17234521284486235704041507)
                  ·
                    refine ⟨25851781926729353556062261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17234521284486235704041507 25851781926729353556062261)
                    ·
                      refine ⟨2423604555630876895880837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25851781926729353556062261 2423604555630876895880837)
                      ·
                        rfl

theorem cell23_4719953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_4719953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719953 prefixEnd_4719953 := by exact prefixLift 4719953
  have htrace : WordTrace (prefixWord ++ tailWord_4719953) baseStart_4719953 baseEnd_4719953 := by
    simpa [prefixWord, tailWord_4719953, baseEnd_4719953] using wordTrace_append hprefix tailTrace_4719953
  have hstable : (prefixWord ++ tailWord_4719953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719953).length < 2 ^ (prefixWord ++ tailWord_4719953).sum := by decide
  have hdescent : baseEnd_4719953 < baseStart_4719953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719978 : List Nat := [3, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_4719978 : Nat := 118140960795 + 4719978 * 2 ^ 59
def prefixEnd_4719978 : Nat := 4983230072969 + 3 ^ 40 * 4719978 * 2
def baseEnd_4719978 : Nat := 2423617392647239298068223

theorem tailTrace_4719978 : CollatzResearch.WordTrace tailWord_4719978 prefixEnd_4719978 2423617392647239298068223 := by
  unfold tailWord_4719978
  simp only [CollatzResearch.WordTrace]
  refine ⟨43037935123583322227492147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114767826996222192606645725 43037935123583322227492147)
  ·
    refine ⟨64556902685374983341238221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43037935123583322227492147 64556902685374983341238221)
    ·
      refine ⟨24208838507015618752964333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64556902685374983341238221 24208838507015618752964333)
      ·
        refine ⟨9078314440130857032361625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24208838507015618752964333 9078314440130857032361625)
        ·
          refine ⟨6808735830098142774271219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9078314440130857032361625 6808735830098142774271219)
          ·
            refine ⟨10213103745147214161406829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808735830098142774271219 10213103745147214161406829)
            ·
              refine ⟨3829913904430205310527561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10213103745147214161406829 3829913904430205310527561)
              ·
                refine ⟨2872435428322653982895671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3829913904430205310527561 2872435428322653982895671)
                ·
                  refine ⟨4308653142483980974343507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872435428322653982895671 4308653142483980974343507)
                  ·
                    refine ⟨6462979713725971461515261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4308653142483980974343507 6462979713725971461515261)
                    ·
                      refine ⟨2423617392647239298068223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6462979713725971461515261 2423617392647239298068223)
                      ·
                        rfl

theorem cell23_4719978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_4719978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719978 prefixEnd_4719978 := by exact prefixLift 4719978
  have htrace : WordTrace (prefixWord ++ tailWord_4719978) baseStart_4719978 baseEnd_4719978 := by
    simpa [prefixWord, tailWord_4719978, baseEnd_4719978] using wordTrace_append hprefix tailTrace_4719978
  have hstable : (prefixWord ++ tailWord_4719978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719978).length < 2 ^ (prefixWord ++ tailWord_4719978).sum := by decide
  have hdescent : baseEnd_4719978 < baseStart_4719978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4719998 : List Nat := [4, 2, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4719998 : Nat := 118140960795 + 4719998 * 2 ^ 59
def prefixEnd_4719998 : Nat := 4983230072969 + 3 ^ 40 * 4719998 * 2
def baseEnd_4719998 : Nat := 807875887420109739939377

theorem tailTrace_4719998 : CollatzResearch.WordTrace tailWord_4719998 prefixEnd_4719998 807875887420109739939377 := by
  unfold tailWord_4719998
  simp only [CollatzResearch.WordTrace]
  refine ⟨21519058744282604040712081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114768313302840554883797765 21519058744282604040712081)
  ·
    refine ⟨16139294058211953030534061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21519058744282604040712081 16139294058211953030534061)
    ·
      refine ⟨6052235271829482386450273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16139294058211953030534061 6052235271829482386450273)
      ·
        refine ⟨4539176453872111789837705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6052235271829482386450273 4539176453872111789837705)
        ·
          refine ⟨3404382340404083842378279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4539176453872111789837705 3404382340404083842378279)
          ·
            refine ⟨5106573510606125763567419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404382340404083842378279 5106573510606125763567419)
            ·
              refine ⟨7659860265909188645351129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106573510606125763567419 7659860265909188645351129)
              ·
                refine ⟨5744895199431891484013347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7659860265909188645351129 5744895199431891484013347)
                ·
                  refine ⟨8617342799147837226020021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5744895199431891484013347 8617342799147837226020021)
                  ·
                    refine ⟨807875887420109739939377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8617342799147837226020021 807875887420109739939377)
                    ·
                      rfl

theorem cell23_4719998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4719998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4719998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4719998 prefixEnd_4719998 := by exact prefixLift 4719998
  have htrace : WordTrace (prefixWord ++ tailWord_4719998) baseStart_4719998 baseEnd_4719998 := by
    simpa [prefixWord, tailWord_4719998, baseEnd_4719998] using wordTrace_append hprefix tailTrace_4719998
  have hstable : (prefixWord ++ tailWord_4719998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4719998).length < 2 ^ (prefixWord ++ tailWord_4719998).sum := by decide
  have hdescent : baseEnd_4719998 < baseStart_4719998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4719998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720001 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_4720001 : Nat := 118140960795 + 4720001 * 2 ^ 59
def prefixEnd_4720001 : Nat := 4983230072969 + 3 ^ 40 * 4720001 * 2
def baseEnd_4720001 : Nat := 2423629202702292708080617

theorem tailTrace_4720001 : CollatzResearch.WordTrace tailWord_4720001 prefixEnd_4720001 2423629202702292708080617 := by
  unfold tailWord_4720001
  simp only [CollatzResearch.WordTrace]
  refine ⟨172152579373249963838055857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114768386248833309225370571 172152579373249963838055857)
  ·
    refine ⟨129114434529937472878541893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172152579373249963838055857 129114434529937472878541893)
    ·
      refine ⟨24208956474363276164726605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129114434529937472878541893 24208956474363276164726605)
      ·
        refine ⟨9078358677886228561772477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24208956474363276164726605 9078358677886228561772477)
        ·
          refine ⟨3404384504207335710664679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9078358677886228561772477 3404384504207335710664679)
          ·
            refine ⟨5106576756311003565997019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404384504207335710664679 5106576756311003565997019)
            ·
              refine ⟨7659865134466505348995529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106576756311003565997019 7659865134466505348995529)
              ·
                refine ⟨5744898850849879011746647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7659865134466505348995529 5744898850849879011746647)
                ·
                  refine ⟨8617348276274818517619971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5744898850849879011746647 8617348276274818517619971)
                  ·
                    refine ⟨12926022414412227776429957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8617348276274818517619971 12926022414412227776429957)
                    ·
                      refine ⟨2423629202702292708080617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12926022414412227776429957 2423629202702292708080617)
                      ·
                        rfl

theorem cell23_4720001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_4720001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720001 prefixEnd_4720001 := by exact prefixLift 4720001
  have htrace : WordTrace (prefixWord ++ tailWord_4720001) baseStart_4720001 baseEnd_4720001 := by
    simpa [prefixWord, tailWord_4720001, baseEnd_4720001] using wordTrace_append hprefix tailTrace_4720001
  have hstable : (prefixWord ++ tailWord_4720001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720001).length < 2 ^ (prefixWord ++ tailWord_4720001).sum := by decide
  have hdescent : baseEnd_4720001 < baseStart_4720001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720004 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_4720004 : Nat := 118140960795 + 4720004 * 2 ^ 59
def prefixEnd_4720004 : Nat := 4983230072969 + 3 ^ 40 * 4720004 * 2
def baseEnd_4720004 : Nat := 2423630743144256196343103

theorem tailTrace_4720004 : CollatzResearch.WordTrace tailWord_4720004 prefixEnd_4720004 2423630743144256196343103 := by
  unfold tailWord_4720004
  simp only [CollatzResearch.WordTrace]
  refine ⟨86076344396119547675207533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114768459194826063566943377 86076344396119547675207533)
  ·
    refine ⟨32278629148544830378202825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86076344396119547675207533 32278629148544830378202825)
    ·
      refine ⟨24208971861408622783652119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32278629148544830378202825 24208971861408622783652119)
      ·
        refine ⟨36313457792112934175478179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24208971861408622783652119 36313457792112934175478179)
        ·
          refine ⟨54470186688169401263217269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36313457792112934175478179 54470186688169401263217269)
          ·
            refine ⟨5106580002015881368426619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54470186688169401263217269 5106580002015881368426619)
            ·
              refine ⟨7659870003023822052639929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106580002015881368426619 7659870003023822052639929)
              ·
                refine ⟨5744902502267866539479947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7659870003023822052639929 5744902502267866539479947)
                ·
                  refine ⟨8617353753401799809219921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5744902502267866539479947 8617353753401799809219921)
                  ·
                    refine ⟨6463015315051349856914941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8617353753401799809219921 6463015315051349856914941)
                    ·
                      refine ⟨2423630743144256196343103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463015315051349856914941 2423630743144256196343103)
                      ·
                        rfl

theorem cell23_4720004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_4720004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720004 prefixEnd_4720004 := by exact prefixLift 4720004
  have htrace : WordTrace (prefixWord ++ tailWord_4720004) baseStart_4720004 baseEnd_4720004 := by
    simpa [prefixWord, tailWord_4720004, baseEnd_4720004] using wordTrace_append hprefix tailTrace_4720004
  have hstable : (prefixWord ++ tailWord_4720004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720004).length < 2 ^ (prefixWord ++ tailWord_4720004).sum := by decide
  have hdescent : baseEnd_4720004 < baseStart_4720004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720034 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_4720034 : Nat := 118140960795 + 4720034 * 2 ^ 59
def prefixEnd_4720034 : Nat := 4983230072969 + 3 ^ 40 * 4720034 * 2
def baseEnd_4720034 : Nat := 2423646147563891078967965

theorem tailTrace_4720034 : CollatzResearch.WordTrace tailWord_4720034 prefixEnd_4720034 2423646147563891078967965 := by
  unfold tailWord_4720034
  simp only [CollatzResearch.WordTrace]
  refine ⟨43038445745532602618501789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114769188654753606982671437 43038445745532602618501789)
  ·
    refine ⟨16139417154574725981938171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43038445745532602618501789 16139417154574725981938171)
    ·
      refine ⟨24209125731862088972907257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16139417154574725981938171 24209125731862088972907257)
      ·
        refine ⟨18156844298896566729680443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24209125731862088972907257 18156844298896566729680443)
        ·
          refine ⟨27235266448344850094520665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18156844298896566729680443 27235266448344850094520665)
          ·
            refine ⟨20426449836258637570890499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27235266448344850094520665 20426449836258637570890499)
            ·
              refine ⟨30639674754387956356335749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20426449836258637570890499 30639674754387956356335749)
              ·
                refine ⟨5744939016447741816812953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30639674754387956356335749 5744939016447741816812953)
                ·
                  refine ⟨4308704262335806362609715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5744939016447741816812953 4308704262335806362609715)
                  ·
                    refine ⟨6463056393503709543914573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4308704262335806362609715 6463056393503709543914573)
                    ·
                      refine ⟨2423646147563891078967965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463056393503709543914573 2423646147563891078967965)
                      ·
                        rfl

theorem cell23_4720034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_4720034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720034 prefixEnd_4720034 := by exact prefixLift 4720034
  have htrace : WordTrace (prefixWord ++ tailWord_4720034) baseStart_4720034 baseEnd_4720034 := by
    simpa [prefixWord, tailWord_4720034, baseEnd_4720034] using wordTrace_append hprefix tailTrace_4720034
  have hstable : (prefixWord ++ tailWord_4720034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720034).length < 2 ^ (prefixWord ++ tailWord_4720034).sum := by decide
  have hdescent : baseEnd_4720034 < baseStart_4720034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720073 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_4720073 : Nat := 118140960795 + 4720073 * 2 ^ 59
def prefixEnd_4720073 : Nat := 4983230072969 + 3 ^ 40 * 4720073 * 2
def baseEnd_4720073 : Nat := 2423666173309416426380285

theorem tailTrace_4720073 : CollatzResearch.WordTrace tailWord_4720073 prefixEnd_4720073 2423666173309416426380285 := by
  unfold tailWord_4720073
  simp only [CollatzResearch.WordTrace]
  refine ⟨172155205428989120134676873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114770136952659413423117915 172155205428989120134676873)
  ·
    refine ⟨129116404071741840101007655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172155205428989120134676873 129116404071741840101007655)
    ·
      refine ⟨193674606107612760151511483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129116404071741840101007655 193674606107612760151511483)
      ·
        refine ⟨290511909161419140227267225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193674606107612760151511483 290511909161419140227267225)
        ·
          refine ⟨217883931871064355170450419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290511909161419140227267225 217883931871064355170450419)
          ·
            refine ⟨326825897806596532755675629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217883931871064355170450419 326825897806596532755675629)
            ·
              refine ⟨122559711677473699783378361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326825897806596532755675629 122559711677473699783378361)
              ·
                refine ⟨91919783758105274837533771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122559711677473699783378361 91919783758105274837533771)
                ·
                  refine ⟨137879675637157912256300657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91919783758105274837533771 137879675637157912256300657)
                  ·
                    refine ⟨103409756727868434192225493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137879675637157912256300657 103409756727868434192225493)
                    ·
                      refine ⟨2423666173309416426380285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103409756727868434192225493 2423666173309416426380285)
                      ·
                        rfl

theorem cell23_4720073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_4720073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720073 prefixEnd_4720073 := by exact prefixLift 4720073
  have htrace : WordTrace (prefixWord ++ tailWord_4720073) baseStart_4720073 baseEnd_4720073 := by
    simpa [prefixWord, tailWord_4720073, baseEnd_4720073] using wordTrace_append hprefix tailTrace_4720073
  have hstable : (prefixWord ++ tailWord_4720073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720073).length < 2 ^ (prefixWord ++ tailWord_4720073).sum := by decide
  have hdescent : baseEnd_4720073 < baseStart_4720073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720097 : List Nat := [1, 2, 3, 1, 2, 3, 2, 4, 5]
def baseStart_4720097 : Nat := 118140960795 + 4720097 * 2 ^ 59
def prefixEnd_4720097 : Nat := 4983230072969 + 3 ^ 40 * 4720097 * 2
def baseEnd_4720097 : Nat := 269297610760569370275575

theorem tailTrace_4720097 : CollatzResearch.WordTrace tailWord_4720097 prefixEnd_4720097 269297610760569370275575 := by
  unfold tailWord_4720097
  simp only [CollatzResearch.WordTrace]
  refine ⟨172156080780902172233550545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114770720520601448155700363 172156080780902172233550545)
  ·
    refine ⟨129117060585676629175162909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172156080780902172233550545 129117060585676629175162909)
    ·
      refine ⟨48418897719628735940686091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129117060585676629175162909 48418897719628735940686091)
      ·
        refine ⟨72628346579443103911029137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48418897719628735940686091 72628346579443103911029137)
        ·
          refine ⟨54471259934582327933271853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72628346579443103911029137 54471259934582327933271853)
          ·
            refine ⟨20426722475468372974976945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54471259934582327933271853 20426722475468372974976945)
            ·
              refine ⟨15320041856601279731232709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20426722475468372974976945 15320041856601279731232709)
              ·
                refine ⟨2872507848112739949606133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15320041856601279731232709 2872507848112739949606133)
                ·
                  refine ⟨269297610760569370275575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2872507848112739949606133 269297610760569370275575)
                  ·
                    rfl

theorem cell23_4720097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 5].length) (baseStart_4720097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720097 prefixEnd_4720097 := by exact prefixLift 4720097
  have htrace : WordTrace (prefixWord ++ tailWord_4720097) baseStart_4720097 baseEnd_4720097 := by
    simpa [prefixWord, tailWord_4720097, baseEnd_4720097] using wordTrace_append hprefix tailTrace_4720097
  have hstable : (prefixWord ++ tailWord_4720097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720097).length < 2 ^ (prefixWord ++ tailWord_4720097).sum := by decide
  have hdescent : baseEnd_4720097 < baseStart_4720097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720110 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_4720110 : Nat := 118140960795 + 4720110 * 2 ^ 59
def prefixEnd_4720110 : Nat := 4983230072969 + 3 ^ 40 * 4720110 * 2
def baseEnd_4720110 : Nat := 807895057364544260539205

theorem tailTrace_4720110 : CollatzResearch.WordTrace tailWord_4720110 prefixEnd_4720110 807895057364544260539205 := by
  unfold tailWord_4720110
  simp only [CollatzResearch.WordTrace]
  refine ⟨21519569366231884431721723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114771036619903383635849189 21519569366231884431721723)
  ·
    refine ⟨32279354049347826647582585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21519569366231884431721723 32279354049347826647582585)
    ·
      refine ⟨24209515537010869985686939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32279354049347826647582585 24209515537010869985686939)
      ·
        refine ⟨36314273305516304978530409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24209515537010869985686939 36314273305516304978530409)
        ·
          refine ⟨27235704979137228733897807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36314273305516304978530409 27235704979137228733897807)
          ·
            refine ⟨40853557468705843100846711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27235704979137228733897807 40853557468705843100846711)
            ·
              refine ⟨61280336203058764651270067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40853557468705843100846711 61280336203058764651270067)
              ·
                refine ⟨91920504304588146976905101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61280336203058764651270067 91920504304588146976905101)
                ·
                  refine ⟨34470189114220555116339413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91920504304588146976905101 34470189114220555116339413)
                  ·
                    refine ⟨807895057364544260539205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34470189114220555116339413 807895057364544260539205)
                    ·
                      rfl

theorem cell23_4720110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_4720110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720110 prefixEnd_4720110 := by exact prefixLift 4720110
  have htrace : WordTrace (prefixWord ++ tailWord_4720110) baseStart_4720110 baseEnd_4720110 := by
    simpa [prefixWord, tailWord_4720110, baseEnd_4720110] using wordTrace_append hprefix tailTrace_4720110
  have hstable : (prefixWord ++ tailWord_4720110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720110).length < 2 ^ (prefixWord ++ tailWord_4720110).sum := by decide
  have hdescent : baseEnd_4720110 < baseStart_4720110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720147 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 4]
def baseStart_4720147 : Nat := 118140960795 + 4720147 * 2 ^ 59
def prefixEnd_4720147 : Nat := 4983230072969 + 3 ^ 40 * 4720147 * 2
def baseEnd_4720147 : Nat := 2423704170877849136854945

theorem tailTrace_4720147 : CollatzResearch.WordTrace tailWord_4720147 prefixEnd_4720147 2423704170877849136854945 := by
  unfold tailWord_4720147
  simp only [CollatzResearch.WordTrace]
  refine ⟨172157904430721030772870695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114771936287147353848580463 172157904430721030772870695)
  ·
    refine ⟨258236856646081546159306043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172157904430721030772870695 258236856646081546159306043)
    ·
      refine ⟨387355284969122319238959065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258236856646081546159306043 387355284969122319238959065)
      ·
        refine ⟨290516463726841739429219299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387355284969122319238959065 290516463726841739429219299)
        ·
          refine ⟨435774695590262609143828949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290516463726841739429219299 435774695590262609143828949)
          ·
            refine ⟨10213469427896779901808491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 435774695590262609143828949 10213469427896779901808491)
            ·
              refine ⟨15320204141845169852712737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10213469427896779901808491 15320204141845169852712737)
              ·
                refine ⟨11490153106383877389534553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15320204141845169852712737 11490153106383877389534553)
                ·
                  refine ⟨8617614829787908042150915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11490153106383877389534553 8617614829787908042150915)
                  ·
                    refine ⟨12926422244681862063226373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8617614829787908042150915 12926422244681862063226373)
                    ·
                      refine ⟨2423704170877849136854945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12926422244681862063226373 2423704170877849136854945)
                      ·
                        rfl

theorem cell23_4720147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_4720147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720147 prefixEnd_4720147 := by exact prefixLift 4720147
  have htrace : WordTrace (prefixWord ++ tailWord_4720147) baseStart_4720147 baseEnd_4720147 := by
    simpa [prefixWord, tailWord_4720147, baseEnd_4720147] using wordTrace_append hprefix tailTrace_4720147
  have hstable : (prefixWord ++ tailWord_4720147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720147).length < 2 ^ (prefixWord ++ tailWord_4720147).sum := by decide
  have hdescent : baseEnd_4720147 < baseStart_4720147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720148 : List Nat := [2, 4, 3, 1, 2, 1, 3, 2, 5]
def baseStart_4720148 : Nat := 118140960795 + 4720148 * 2 ^ 59
def prefixEnd_4720148 : Nat := 4983230072969 + 3 ^ 40 * 4720148 * 2
def baseEnd_4720148 : Nat := 269300520484278181438049

theorem tailTrace_4720148 : CollatzResearch.WordTrace tailWord_4720148 prefixEnd_4720148 269300520484278181438049 := by
  unfold tailWord_4720148
  simp only [CollatzResearch.WordTrace]
  refine ⟨86078970451858703971828549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114771960602478271962438065 86078970451858703971828549)
  ·
    refine ⟨16139806959723506994717853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86078970451858703971828549 16139806959723506994717853)
    ·
      refine ⟨6052427609896315123019195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16139806959723506994717853 6052427609896315123019195)
      ·
        refine ⟨9078641414844472684528793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052427609896315123019195 9078641414844472684528793)
        ·
          refine ⟨6808981061133354513396595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9078641414844472684528793 6808981061133354513396595)
          ·
            refine ⟨10213471591700031770094893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808981061133354513396595 10213471591700031770094893)
            ·
              refine ⟨3830051846887511913785585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10213471591700031770094893 3830051846887511913785585)
              ·
                refine ⟨2872538885165633935339189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830051846887511913785585 2872538885165633935339189)
                ·
                  refine ⟨269300520484278181438049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2872538885165633935339189 269300520484278181438049)
                  ·
                    rfl

theorem cell23_4720148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_4720148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720148 prefixEnd_4720148 := by exact prefixLift 4720148
  have htrace : WordTrace (prefixWord ++ tailWord_4720148) baseStart_4720148 baseEnd_4720148 := by
    simpa [prefixWord, tailWord_4720148, baseEnd_4720148] using wordTrace_append hprefix tailTrace_4720148
  have hstable : (prefixWord ++ tailWord_4720148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720148).length < 2 ^ (prefixWord ++ tailWord_4720148).sum := by decide
  have hdescent : baseEnd_4720148 < baseStart_4720148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720184 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_4720184 : Nat := 118140960795 + 4720184 * 2 ^ 59
def prefixEnd_4720184 : Nat := 4983230072969 + 3 ^ 40 * 4720184 * 2
def baseEnd_4720184 : Nat := 2423723169662065492092275

theorem tailTrace_4720184 : CollatzResearch.WordTrace tailWord_4720184 prefixEnd_4720184 2423723169662065492092275 := by
  unfold tailWord_4720184
  simp only [CollatzResearch.WordTrace]
  refine ⟨86079626965793493045983803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114772835954391324061311737 86079626965793493045983803)
  ·
    refine ⟨129119440448690239568975705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86079626965793493045983803 129119440448690239568975705)
    ·
      refine ⟨96839580336517679676731779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129119440448690239568975705 96839580336517679676731779)
      ·
        refine ⟨145259370504776519515097669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96839580336517679676731779 145259370504776519515097669)
        ·
          refine ⟨27236131969645597409080813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145259370504776519515097669 27236131969645597409080813)
          ·
            refine ⟨10213549488617099028405305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27236131969645597409080813 10213549488617099028405305)
            ·
              refine ⟨7660162116462824271303979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10213549488617099028405305 7660162116462824271303979)
              ·
                refine ⟨11490243174694236406955969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7660162116462824271303979 11490243174694236406955969)
                ·
                  refine ⟨8617682381020677305216977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11490243174694236406955969 8617682381020677305216977)
                  ·
                    refine ⟨6463261785765507978912733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8617682381020677305216977 6463261785765507978912733)
                    ·
                      refine ⟨2423723169662065492092275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463261785765507978912733 2423723169662065492092275)
                      ·
                        rfl

theorem cell23_4720184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_4720184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720184 prefixEnd_4720184 := by exact prefixLift 4720184
  have htrace : WordTrace (prefixWord ++ tailWord_4720184) baseStart_4720184 baseEnd_4720184 := by
    simpa [prefixWord, tailWord_4720184, baseEnd_4720184] using wordTrace_append hprefix tailTrace_4720184
  have hstable : (prefixWord ++ tailWord_4720184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720184).length < 2 ^ (prefixWord ++ tailWord_4720184).sum := by decide
  have hdescent : baseEnd_4720184 < baseStart_4720184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720207 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 3, 5, 2]
def baseStart_4720207 : Nat := 118140960795 + 4720207 * 2 ^ 59
def prefixEnd_4720207 : Nat := 4983230072969 + 3 ^ 40 * 4720207 * 2
def baseEnd_4720207 : Nat := 2423734979717118902104669

theorem tailTrace_4720207 : CollatzResearch.WordTrace tailWord_4720207 prefixEnd_4720207 2423734979717118902104669 := by
  unfold tailWord_4720207
  simp only [CollatzResearch.WordTrace]
  refine ⟨172160092810503661020054875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114773395207002440680036583 172160092810503661020054875)
  ·
    refine ⟨258240139215755491530082313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172160092810503661020054875 258240139215755491530082313)
    ·
      refine ⟨193680104411816618647561735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258240139215755491530082313 193680104411816618647561735)
      ·
        refine ⟨290520156617724927971342603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193680104411816618647561735 290520156617724927971342603)
        ·
          refine ⟨435780234926587391957013905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290520156617724927971342603 435780234926587391957013905)
          ·
            refine ⟨326835176194940543967760429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435780234926587391957013905 326835176194940543967760429)
            ·
              refine ⟨122563191073102703987910161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326835176194940543967760429 122563191073102703987910161)
              ·
                refine ⟨91922393304827027990932621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122563191073102703987910161 91922393304827027990932621)
                ·
                  refine ⟨34470897489310135496599733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91922393304827027990932621 34470897489310135496599733)
                  ·
                    refine ⟨3231646639622825202806225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34470897489310135496599733 3231646639622825202806225)
                    ·
                      refine ⟨2423734979717118902104669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231646639622825202806225 2423734979717118902104669)
                      ·
                        rfl

theorem cell23_4720207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 5, 2].length) (baseStart_4720207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720207 prefixEnd_4720207 := by exact prefixLift 4720207
  have htrace : WordTrace (prefixWord ++ tailWord_4720207) baseStart_4720207 baseEnd_4720207 := by
    simpa [prefixWord, tailWord_4720207, baseEnd_4720207] using wordTrace_append hprefix tailTrace_4720207
  have hstable : (prefixWord ++ tailWord_4720207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720207).length < 2 ^ (prefixWord ++ tailWord_4720207).sum := by decide
  have hdescent : baseEnd_4720207 < baseStart_4720207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720247 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 4, 4]
def baseStart_4720247 : Nat := 118140960795 + 4720247 * 2 ^ 59
def prefixEnd_4720247 : Nat := 4983230072969 + 3 ^ 40 * 4720247 * 2
def baseEnd_4720247 : Nat := 807918506314432915201495

theorem tailTrace_4720247 : CollatzResearch.WordTrace tailWord_4720247 prefixEnd_4720247 807918506314432915201495 := by
  unfold tailWord_4720247
  simp only [CollatzResearch.WordTrace]
  refine ⟨172161551730358747851510995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114774367820239165234340663 172161551730358747851510995)
  ·
    refine ⟨258242327595538121777266493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172161551730358747851510995 258242327595538121777266493)
    ·
      refine ⟨96840872848326795666474935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258242327595538121777266493 96840872848326795666474935)
      ·
        refine ⟨145261309272490193499712403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96840872848326795666474935 145261309272490193499712403)
        ·
          refine ⟨217891963908735290249568605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145261309272490193499712403 217891963908735290249568605)
          ·
            refine ⟨81709486465775733843588227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217891963908735290249568605 81709486465775733843588227)
            ·
              refine ⟨122564229698663600765382341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81709486465775733843588227 122564229698663600765382341)
              ·
                refine ⟨22980793068499425143509189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122564229698663600765382341 22980793068499425143509189)
                ·
                  refine ⟨4308898700343642214407973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22980793068499425143509189 4308898700343642214407973)
                  ·
                    refine ⟨807918506314432915201495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4308898700343642214407973 807918506314432915201495)
                    ·
                      rfl

theorem cell23_4720247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_4720247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720247 prefixEnd_4720247 := by exact prefixLift 4720247
  have htrace : WordTrace (prefixWord ++ tailWord_4720247) baseStart_4720247 baseEnd_4720247 := by
    simpa [prefixWord, tailWord_4720247, baseEnd_4720247] using wordTrace_append hprefix tailTrace_4720247
  have hstable : (prefixWord ++ tailWord_4720247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720247).length < 2 ^ (prefixWord ++ tailWord_4720247).sum := by decide
  have hdescent : baseEnd_4720247 < baseStart_4720247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720284 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4720284 : Nat := 118140960795 + 4720284 * 2 ^ 59
def prefixEnd_4720284 : Nat := 4983230072969 + 3 ^ 40 * 4720284 * 2
def baseEnd_4720284 : Nat := 2423774517727515100841815

theorem tailTrace_4720284 : CollatzResearch.WordTrace tailWord_4720284 prefixEnd_4720284 2423774517727515100841815 := by
  unfold tailWord_4720284
  simp only [CollatzResearch.WordTrace]
  refine ⟨86081450615612351585303953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114775267487483135447071937 86081450615612351585303953)
  ·
    refine ⟨64561087961709263688977965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86081450615612351585303953 64561087961709263688977965)
    ·
      refine ⟨24210407985640973883366737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64561087961709263688977965 24210407985640973883366737)
      ·
        refine ⟨18157805989230730412525053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24210407985640973883366737 18157805989230730412525053)
        ·
          refine ⟨6809177245961523904696895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18157805989230730412525053 6809177245961523904696895)
          ·
            refine ⟨10213765868942285857045343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809177245961523904696895 10213765868942285857045343)
            ·
              refine ⟨15320648803413428785568015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10213765868942285857045343 15320648803413428785568015)
              ·
                refine ⟨22980973205120143178352023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15320648803413428785568015 22980973205120143178352023)
                ·
                  refine ⟨34471459807680214767528035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22980973205120143178352023 34471459807680214767528035)
                  ·
                    refine ⟨51707189711520322151292053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34471459807680214767528035 51707189711520322151292053)
                    ·
                      refine ⟨2423774517727515100841815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51707189711520322151292053 2423774517727515100841815)
                      ·
                        rfl

theorem cell23_4720284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4720284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720284 prefixEnd_4720284 := by exact prefixLift 4720284
  have htrace : WordTrace (prefixWord ++ tailWord_4720284) baseStart_4720284 baseEnd_4720284 := by
    simpa [prefixWord, tailWord_4720284, baseEnd_4720284] using wordTrace_append hprefix tailTrace_4720284
  have hstable : (prefixWord ++ tailWord_4720284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720284).length < 2 ^ (prefixWord ++ tailWord_4720284).sum := by decide
  have hdescent : baseEnd_4720284 < baseStart_4720284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720304 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 4, 1, 3]
def baseStart_4720304 : Nat := 118140960795 + 4720304 * 2 ^ 59
def prefixEnd_4720304 : Nat := 4983230072969 + 3 ^ 40 * 4720304 * 2
def baseEnd_4720304 : Nat := 2423784787340605022591723

theorem tailTrace_4720304 : CollatzResearch.WordTrace tailWord_4720304 prefixEnd_4720304 2423784787340605022591723 := by
  unfold tailWord_4720304
  simp only [CollatzResearch.WordTrace]
  refine ⟨86081815345576123293167983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114775753794101497724223977 86081815345576123293167983)
  ·
    refine ⟨129122723018364184939751975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86081815345576123293167983 129122723018364184939751975)
    ·
      refine ⟨193684084527546277409627963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129122723018364184939751975 193684084527546277409627963)
      ·
        refine ⟨290526126791319416114441945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193684084527546277409627963 290526126791319416114441945)
        ·
          refine ⟨217894595093489562085831459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290526126791319416114441945 217894595093489562085831459)
          ·
            refine ⟨326841892640234343128747189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217894595093489562085831459 326841892640234343128747189)
            ·
              refine ⟨30641427435021969668320049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 326841892640234343128747189 30641427435021969668320049)
              ·
                refine ⟨22981070576266477251240037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30641427435021969668320049 22981070576266477251240037)
                ·
                  refine ⟨4308950733049964484607507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22981070576266477251240037 4308950733049964484607507)
                  ·
                    refine ⟨6463426099574946726911261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4308950733049964484607507 6463426099574946726911261)
                    ·
                      refine ⟨2423784787340605022591723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463426099574946726911261 2423784787340605022591723)
                      ·
                        rfl

theorem cell23_4720304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 4, 1, 3].length) (baseStart_4720304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720304 prefixEnd_4720304 := by exact prefixLift 4720304
  have htrace : WordTrace (prefixWord ++ tailWord_4720304) baseStart_4720304 baseEnd_4720304 := by
    simpa [prefixWord, tailWord_4720304, baseEnd_4720304] using wordTrace_append hprefix tailTrace_4720304
  have hstable : (prefixWord ++ tailWord_4720304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720304).length < 2 ^ (prefixWord ++ tailWord_4720304).sum := by decide
  have hdescent : baseEnd_4720304 < baseStart_4720304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720317 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4720317 : Nat := 118140960795 + 4720317 * 2 ^ 59
def prefixEnd_4720317 : Nat := 4983230072969 + 3 ^ 40 * 4720317 * 2
def baseEnd_4720317 : Nat := 2423791462589113471729163

theorem tailTrace_4720317 : CollatzResearch.WordTrace tailWord_4720317 prefixEnd_4720317 2423791462589113471729163 := by
  unfold tailWord_4720317
  simp only [CollatzResearch.WordTrace]
  refine ⟨172164104840105149806559205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114776069893403433204372803 172164104840105149806559205)
  ·
    refine ⟨32280769657519715588729851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172164104840105149806559205 32280769657519715588729851)
    ·
      refine ⟨48421154486279573383094777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32280769657519715588729851 48421154486279573383094777)
      ·
        refine ⟨36315865864709680037321083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48421154486279573383094777 36315865864709680037321083)
        ·
          refine ⟨54473798797064520055981625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36315865864709680037321083 54473798797064520055981625)
          ·
            refine ⟨40855349097798390041986219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54473798797064520055981625 40855349097798390041986219)
            ·
              refine ⟨61283023646697585062979329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40855349097798390041986219 61283023646697585062979329)
              ·
                refine ⟨45962267735023188797234497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61283023646697585062979329 45962267735023188797234497)
                ·
                  refine ⟨34471700801267391597925873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45962267735023188797234497 34471700801267391597925873)
                  ·
                    refine ⟨25853775600950543698444405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34471700801267391597925873 25853775600950543698444405)
                    ·
                      refine ⟨2423791462589113471729163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25853775600950543698444405 2423791462589113471729163)
                      ·
                        rfl

theorem cell23_4720317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4720317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720317 prefixEnd_4720317 := by exact prefixLift 4720317
  have htrace : WordTrace (prefixWord ++ tailWord_4720317) baseStart_4720317 baseEnd_4720317 := by
    simpa [prefixWord, tailWord_4720317, baseEnd_4720317] using wordTrace_append hprefix tailTrace_4720317
  have hstable : (prefixWord ++ tailWord_4720317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720317).length < 2 ^ (prefixWord ++ tailWord_4720317).sum := by decide
  have hdescent : baseEnd_4720317 < baseStart_4720317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720327 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_4720327 : Nat := 118140960795 + 4720327 * 2 ^ 59
def prefixEnd_4720327 : Nat := 4983230072969 + 3 ^ 40 * 4720327 * 2
def baseEnd_4720327 : Nat := 2423796597395658432604117

theorem tailTrace_4720327 : CollatzResearch.WordTrace tailWord_4720327 prefixEnd_4720327 2423796597395658432604117 := by
  unfold tailWord_4720327
  simp only [CollatzResearch.WordTrace]
  refine ⟨172164469570068921514423235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114776313046712614342948823 172164469570068921514423235)
  ·
    refine ⟨258246704355103382271634853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172164469570068921514423235 258246704355103382271634853)
    ·
      refine ⟨48421257066581884175931535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258246704355103382271634853 48421257066581884175931535)
      ·
        refine ⟨72631885599872826263897303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48421257066581884175931535 72631885599872826263897303)
        ·
          refine ⟨108947828399809239395845955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72631885599872826263897303 108947828399809239395845955)
          ·
            refine ⟨163421742599713859093768933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108947828399809239395845955 163421742599713859093768933)
            ·
              refine ⟨30641576737446348580081675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163421742599713859093768933 30641576737446348580081675)
              ·
                refine ⟨45962365106169522870122513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30641576737446348580081675 45962365106169522870122513)
                ·
                  refine ⟨34471773829627142152591885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45962365106169522870122513 34471773829627142152591885)
                  ·
                    refine ⟨12926915186110178307221957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34471773829627142152591885 12926915186110178307221957)
                    ·
                      refine ⟨2423796597395658432604117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12926915186110178307221957 2423796597395658432604117)
                      ·
                        rfl

theorem cell23_4720327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_4720327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720327 prefixEnd_4720327 := by exact prefixLift 4720327
  have htrace : WordTrace (prefixWord ++ tailWord_4720327) baseStart_4720327 baseEnd_4720327 := by
    simpa [prefixWord, tailWord_4720327, baseEnd_4720327] using wordTrace_append hprefix tailTrace_4720327
  have hstable : (prefixWord ++ tailWord_4720327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720327).length < 2 ^ (prefixWord ++ tailWord_4720327).sum := by decide
  have hdescent : baseEnd_4720327 < baseStart_4720327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720338 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_4720338 : Nat := 118140960795 + 4720338 * 2 ^ 59
def prefixEnd_4720338 : Nat := 4983230072969 + 3 ^ 40 * 4720338 * 2
def baseEnd_4720338 : Nat := 2423802245682857889566567

theorem tailTrace_4720338 : CollatzResearch.WordTrace tailWord_4720338 prefixEnd_4720338 2423802245682857889566567 := by
  unfold tailWord_4720338
  simp only [CollatzResearch.WordTrace]
  refine ⟨43041217693257267598268417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114776580515352713595382445 43041217693257267598268417)
  ·
    refine ⟨32280913269942950698701313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43041217693257267598268417 32280913269942950698701313)
    ·
      refine ⟨24210684952457213024025985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32280913269942950698701313 24210684952457213024025985)
      ·
        refine ⟨18158013714342909768019489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24210684952457213024025985 18158013714342909768019489)
        ·
          refine ⟨13618510285757182326014617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18158013714342909768019489 13618510285757182326014617)
          ·
            refine ⟨10213882714317886744510963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13618510285757182326014617 10213882714317886744510963)
            ·
              refine ⟨15320824071476830116766445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10213882714317886744510963 15320824071476830116766445)
              ·
                refine ⟨5745309026803811293787417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15320824071476830116766445 5745309026803811293787417)
                ·
                  refine ⟨4308981770102858470340563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745309026803811293787417 4308981770102858470340563)
                  ·
                    refine ⟨6463472655154287705510845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4308981770102858470340563 6463472655154287705510845)
                    ·
                      refine ⟨2423802245682857889566567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463472655154287705510845 2423802245682857889566567)
                      ·
                        rfl

theorem cell23_4720338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_4720338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720338 prefixEnd_4720338 := by exact prefixLift 4720338
  have htrace : WordTrace (prefixWord ++ tailWord_4720338) baseStart_4720338 baseEnd_4720338 := by
    simpa [prefixWord, tailWord_4720338, baseEnd_4720338] using wordTrace_append hprefix tailTrace_4720338
  have hstable : (prefixWord ++ tailWord_4720338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720338).length < 2 ^ (prefixWord ++ tailWord_4720338).sum := by decide
  have hdescent : baseEnd_4720338 < baseStart_4720338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720342 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4720342 : Nat := 118140960795 + 4720342 * 2 ^ 59
def prefixEnd_4720342 : Nat := 4983230072969 + 3 ^ 40 * 4720342 * 2
def baseEnd_4720342 : Nat := 2423804299605475873916549

theorem tailTrace_4720342 : CollatzResearch.WordTrace tailWord_4720342 prefixEnd_4720342 2423804299605475873916549 := by
  unfold tailWord_4720342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10760313541563411192263705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114776677776676386050812853 10760313541563411192263705)
  ·
    refine ⟨8070235156172558394197779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10760313541563411192263705 8070235156172558394197779)
    ·
      refine ⟨12105352734258837591296669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8070235156172558394197779 12105352734258837591296669)
      ·
        refine ⟨4539507275347064096736251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12105352734258837591296669 4539507275347064096736251)
        ·
          refine ⟨6809260913020596145104377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539507275347064096736251 6809260913020596145104377)
          ·
            refine ⟨5106945684765447108828283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6809260913020596145104377 5106945684765447108828283)
            ·
              refine ⟨7660418527148170663242425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106945684765447108828283 7660418527148170663242425)
              ·
                refine ⟨5745313895361127997431819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7660418527148170663242425 5745313895361127997431819)
                ·
                  refine ⟨8617970843041691996147729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5745313895361127997431819 8617970843041691996147729)
                  ·
                    refine ⟨6463478132281268997110797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8617970843041691996147729 6463478132281268997110797)
                    ·
                      refine ⟨2423804299605475873916549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463478132281268997110797 2423804299605475873916549)
                      ·
                        rfl

theorem cell23_4720342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4720342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720342 prefixEnd_4720342 := by exact prefixLift 4720342
  have htrace : WordTrace (prefixWord ++ tailWord_4720342) baseStart_4720342 baseEnd_4720342 := by
    simpa [prefixWord, tailWord_4720342, baseEnd_4720342] using wordTrace_append hprefix tailTrace_4720342
  have hstable : (prefixWord ++ tailWord_4720342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720342).length < 2 ^ (prefixWord ++ tailWord_4720342).sum := by decide
  have hdescent : baseEnd_4720342 < baseStart_4720342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720365 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_4720365 : Nat := 118140960795 + 4720365 * 2 ^ 59
def prefixEnd_4720365 : Nat := 4983230072969 + 3 ^ 40 * 4720365 * 2
def baseEnd_4720365 : Nat := 2423816109660529283928943

theorem tailTrace_4720365 : CollatzResearch.WordTrace tailWord_4720365 prefixEnd_4720365 2423816109660529283928943 := by
  unfold tailWord_4720365
  simp only [CollatzResearch.WordTrace]
  refine ⟨172165855543931254004306549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114777237029287502669537699 172165855543931254004306549)
  ·
    refine ⟨16140548957243555062903739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172165855543931254004306549 16140548957243555062903739)
    ·
      refine ⟨24210823435865332594355609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16140548957243555062903739 24210823435865332594355609)
      ·
        refine ⟨18158117576898999445766707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24210823435865332594355609 18158117576898999445766707)
        ·
          refine ⟨27237176365348499168650061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18158117576898999445766707 27237176365348499168650061)
          ·
            refine ⟨10213941137005687188243773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27237176365348499168650061 10213941137005687188243773)
            ·
              refine ⟨3830227926377132695591415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10213941137005687188243773 3830227926377132695591415)
              ·
                refine ⟨5745341889565699043387123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830227926377132695591415 5745341889565699043387123)
                ·
                  refine ⟨8618012834348548565080685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5745341889565699043387123 8618012834348548565080685)
                  ·
                    refine ⟨3231754812880705711905257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8618012834348548565080685 3231754812880705711905257)
                    ·
                      refine ⟨2423816109660529283928943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231754812880705711905257 2423816109660529283928943)
                      ·
                        rfl

theorem cell23_4720365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_4720365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720365 prefixEnd_4720365 := by exact prefixLift 4720365
  have htrace : WordTrace (prefixWord ++ tailWord_4720365) baseStart_4720365 baseEnd_4720365 := by
    simpa [prefixWord, tailWord_4720365, baseEnd_4720365] using wordTrace_append hprefix tailTrace_4720365
  have hstable : (prefixWord ++ tailWord_4720365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720365).length < 2 ^ (prefixWord ++ tailWord_4720365).sum := by decide
  have hdescent : baseEnd_4720365 < baseStart_4720365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720372 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4720372 : Nat := 118140960795 + 4720372 * 2 ^ 59
def prefixEnd_4720372 : Nat := 4983230072969 + 3 ^ 40 * 4720372 * 2
def baseEnd_4720372 : Nat := 2423819704025110756541411

theorem tailTrace_4720372 : CollatzResearch.WordTrace tailWord_4720372 prefixEnd_4720372 2423819704025110756541411 := by
  unfold tailWord_4720372
  simp only [CollatzResearch.WordTrace]
  refine ⟨86083055427452947099905685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114777407236603929466540913 86083055427452947099905685)
  ·
    refine ⟨4035143223161856895308079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86083055427452947099905685 4035143223161856895308079)
    ·
      refine ⟨6052714834742785342962119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4035143223161856895308079 6052714834742785342962119)
      ·
        refine ⟨9079072252114178014443179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052714834742785342962119 9079072252114178014443179)
        ·
          refine ⟨13618608378171267021664769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9079072252114178014443179 13618608378171267021664769)
          ·
            refine ⟨10213956283628450266248577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13618608378171267021664769 10213956283628450266248577)
            ·
              refine ⟨7660467212721337699686433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10213956283628450266248577 7660467212721337699686433)
              ·
                refine ⟨5745350409541003274764825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7660467212721337699686433 5745350409541003274764825)
                ·
                  refine ⟨4309012807155752456073619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745350409541003274764825 4309012807155752456073619)
                  ·
                    refine ⟨6463519210733628684110429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4309012807155752456073619 6463519210733628684110429)
                    ·
                      refine ⟨2423819704025110756541411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463519210733628684110429 2423819704025110756541411)
                      ·
                        rfl

theorem cell23_4720372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4720372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720372 prefixEnd_4720372 := by exact prefixLift 4720372
  have htrace : WordTrace (prefixWord ++ tailWord_4720372) baseStart_4720372 baseEnd_4720372 := by
    simpa [prefixWord, tailWord_4720372, baseEnd_4720372] using wordTrace_append hprefix tailTrace_4720372
  have hstable : (prefixWord ++ tailWord_4720372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720372).length < 2 ^ (prefixWord ++ tailWord_4720372).sum := by decide
  have hdescent : baseEnd_4720372 < baseStart_4720372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720384 : List Nat := [2, 1, 1, 2, 1, 1, 2, 8, 5]
def baseStart_4720384 : Nat := 118140960795 + 4720384 * 2 ^ 59
def prefixEnd_4720384 : Nat := 4983230072969 + 3 ^ 40 * 4720384 * 2
def baseEnd_4720384 : Nat := 269313985088107189954595

theorem tailTrace_4720384 : CollatzResearch.WordTrace tailWord_4720384 prefixEnd_4720384 269313985088107189954595 := by
  unfold tailWord_4720384
  simp only [CollatzResearch.WordTrace]
  refine ⟨86083274265431210124624103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114777699020574946832832137 86083274265431210124624103)
  ·
    refine ⟨129124911398146815186936155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86083274265431210124624103 129124911398146815186936155)
    ·
      refine ⟨193687367097220222780404233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129124911398146815186936155 193687367097220222780404233)
      ·
        refine ⟨145265525322915167085303175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193687367097220222780404233 145265525322915167085303175)
        ·
          refine ⟨217898287984372750627954763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145265525322915167085303175 217898287984372750627954763)
          ·
            refine ⟨326847431976559125941932145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217898287984372750627954763 326847431976559125941932145)
            ·
              refine ⟨245135573982419344456449109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326847431976559125941932145 245135573982419344456449109)
              ·
                refine ⟨2872682507606476692849013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 245135573982419344456449109 2872682507606476692849013)
                ·
                  refine ⟨269313985088107189954595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2872682507606476692849013 269313985088107189954595)
                  ·
                    rfl

theorem cell23_4720384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 5].length) (baseStart_4720384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720384 prefixEnd_4720384 := by exact prefixLift 4720384
  have htrace : WordTrace (prefixWord ++ tailWord_4720384) baseStart_4720384 baseEnd_4720384 := by
    simpa [prefixWord, tailWord_4720384, baseEnd_4720384] using wordTrace_append hprefix tailTrace_4720384
  have hstable : (prefixWord ++ tailWord_4720384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720384).length < 2 ^ (prefixWord ++ tailWord_4720384).sum := by decide
  have hdescent : baseEnd_4720384 < baseStart_4720384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720391 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4720391 : Nat := 118140960795 + 4720391 * 2 ^ 59
def prefixEnd_4720391 : Nat := 4983230072969 + 3 ^ 40 * 4720391 * 2
def baseEnd_4720391 : Nat := 2423829460157546182203823

theorem tailTrace_4720391 : CollatzResearch.WordTrace tailWord_4720391 prefixEnd_4720391 2423829460157546182203823 := by
  unfold tailWord_4720391
  simp only [CollatzResearch.WordTrace]
  refine ⟨172166803841837060444753027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114777869227891373629835351 172166803841837060444753027)
  ·
    refine ⟨258250205762755590667129541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172166803841837060444753027 258250205762755590667129541)
    ·
      refine ⟨48421913580516673250086789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258250205762755590667129541 48421913580516673250086789)
      ·
        refine ⟨9079108796346876234391273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48421913580516673250086789 9079108796346876234391273)
        ·
          refine ⟨6809331597260157175793455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9079108796346876234391273 6809331597260157175793455)
          ·
            refine ⟨10213997395890235763690183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809331597260157175793455 10213997395890235763690183)
            ·
              refine ⟨15320996093835353645535275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10213997395890235763690183 15320996093835353645535275)
              ·
                refine ⟨22981494140753030468302913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15320996093835353645535275 22981494140753030468302913)
                ·
                  refine ⟨17236120605564772851227185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22981494140753030468302913 17236120605564772851227185)
                  ·
                    refine ⟨12927090454173579638420389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17236120605564772851227185 12927090454173579638420389)
                    ·
                      refine ⟨2423829460157546182203823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12927090454173579638420389 2423829460157546182203823)
                      ·
                        rfl

theorem cell23_4720391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4720391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720391 prefixEnd_4720391 := by exact prefixLift 4720391
  have htrace : WordTrace (prefixWord ++ tailWord_4720391) baseStart_4720391 baseEnd_4720391 := by
    simpa [prefixWord, tailWord_4720391, baseEnd_4720391] using wordTrace_append hprefix tailTrace_4720391
  have hstable : (prefixWord ++ tailWord_4720391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720391).length < 2 ^ (prefixWord ++ tailWord_4720391).sum := by decide
  have hdescent : baseEnd_4720391 < baseStart_4720391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720394 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_4720394 : Nat := 118140960795 + 4720394 * 2 ^ 59
def prefixEnd_4720394 : Nat := 4983230072969 + 3 ^ 40 * 4720394 * 2
def baseEnd_4720394 : Nat := 2423831000599509670466309

theorem tailTrace_4720394 : CollatzResearch.WordTrace tailWord_4720394 prefixEnd_4720394 2423831000599509670466309 := by
  unfold tailWord_4720394
  simp only [CollatzResearch.WordTrace]
  refine ⟨43041728315206547989278059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114777942173884127971408157 43041728315206547989278059)
  ·
    refine ⟨64562592472809821983917089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43041728315206547989278059 64562592472809821983917089)
    ·
      refine ⟨48421944354607366487937817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64562592472809821983917089 48421944354607366487937817)
      ·
        refine ⟨36316458265955524865953363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48421944354607366487937817 36316458265955524865953363)
        ·
          refine ⟨54474687398933287298930045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36316458265955524865953363 54474687398933287298930045)
          ·
            refine ⟨20428007774599982737098767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54474687398933287298930045 20428007774599982737098767)
            ·
              refine ⟨30642011661899974105648151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20428007774599982737098767 30642011661899974105648151)
              ·
                refine ⟨45963017492849961158472227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30642011661899974105648151 45963017492849961158472227)
                ·
                  refine ⟨68944526239274941737708341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45963017492849961158472227 68944526239274941737708341)
                  ·
                    refine ⟨6463549334932025787910157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68944526239274941737708341 6463549334932025787910157)
                    ·
                      refine ⟨2423831000599509670466309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463549334932025787910157 2423831000599509670466309)
                      ·
                        rfl

theorem cell23_4720394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_4720394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720394 prefixEnd_4720394 := by exact prefixLift 4720394
  have htrace : WordTrace (prefixWord ++ tailWord_4720394) baseStart_4720394 baseEnd_4720394 := by
    simpa [prefixWord, tailWord_4720394, baseEnd_4720394] using wordTrace_append hprefix tailTrace_4720394
  have hstable : (prefixWord ++ tailWord_4720394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720394).length < 2 ^ (prefixWord ++ tailWord_4720394).sum := by decide
  have hdescent : baseEnd_4720394 < baseStart_4720394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720451 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 2, 4, 2]
def baseStart_4720451 : Nat := 118140960795 + 4720451 * 2 ^ 59
def prefixEnd_4720451 : Nat := 4983230072969 + 3 ^ 40 * 4720451 * 2
def baseEnd_4720451 : Nat := 2423860268996815947453547

theorem tailTrace_4720451 : CollatzResearch.WordTrace tailWord_4720451 prefixEnd_4720451 2423860268996815947453547 := by
  unfold tailWord_4720451
  simp only [CollatzResearch.WordTrace]
  refine ⟨172168992221619690691937207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114779328147746460461291471 172168992221619690691937207)
  ·
    refine ⟨258253488332429536037905811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172168992221619690691937207 258253488332429536037905811)
    ·
      refine ⟨387380232498644304056858717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258253488332429536037905811 387380232498644304056858717)
      ·
        refine ⟨145267587186991614021322019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 387380232498644304056858717 145267587186991614021322019)
        ·
          refine ⟨217901380780487421031983029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145267587186991614021322019 217901380780487421031983029)
          ·
            refine ⟨20428254448170695721748409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217901380780487421031983029 20428254448170695721748409)
            ·
              refine ⟨15321190836128021791311307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20428254448170695721748409 15321190836128021791311307)
              ·
                refine ⟨22981786254192032686966961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15321190836128021791311307 22981786254192032686966961)
                ·
                  refine ⟨17236339690644024515225221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22981786254192032686966961 17236339690644024515225221)
                  ·
                    refine ⟨3231813691995754596604729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17236339690644024515225221 3231813691995754596604729)
                    ·
                      refine ⟨2423860268996815947453547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231813691995754596604729 2423860268996815947453547)
                      ·
                        rfl

theorem cell23_4720451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_4720451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720451 prefixEnd_4720451 := by exact prefixLift 4720451
  have htrace : WordTrace (prefixWord ++ tailWord_4720451) baseStart_4720451 baseEnd_4720451 := by
    simpa [prefixWord, tailWord_4720451, baseEnd_4720451] using wordTrace_append hprefix tailTrace_4720451
  have hstable : (prefixWord ++ tailWord_4720451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720451).length < 2 ^ (prefixWord ++ tailWord_4720451).sum := by decide
  have hdescent : baseEnd_4720451 < baseStart_4720451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720467 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 9]
def baseStart_4720467 : Nat := 118140960795 + 4720467 * 2 ^ 59
def prefixEnd_4720467 : Nat := 4983230072969 + 3 ^ 40 * 4720467 * 2
def baseEnd_4720467 : Nat := 2423868484687287884853473

theorem tailTrace_4720467 : CollatzResearch.WordTrace tailWord_4720467 prefixEnd_4720467 2423868484687287884853473 := by
  unfold tailWord_4720467
  simp only [CollatzResearch.WordTrace]
  refine ⟨172169575789561725424519655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114779717193041150283013103 172169575789561725424519655)
  ·
    refine ⟨258254363684342588136779483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172169575789561725424519655 258254363684342588136779483)
    ·
      refine ⟨387381545526513882205169225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258254363684342588136779483 387381545526513882205169225)
      ·
        refine ⟨290536159144885411653876919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387381545526513882205169225 290536159144885411653876919)
        ·
          refine ⟨435804238717328117480815379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290536159144885411653876919 435804238717328117480815379)
          ·
            refine ⟨653706358075992176221223069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435804238717328117480815379 653706358075992176221223069)
            ·
              refine ⟨245139884278497066082958651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 653706358075992176221223069 245139884278497066082958651)
              ·
                refine ⟨367709826417745599124437977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245139884278497066082958651 367709826417745599124437977)
                ·
                  refine ⟨275782369813309199343328483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367709826417745599124437977 275782369813309199343328483)
                  ·
                    refine ⟨413673554719963799014992725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 275782369813309199343328483 413673554719963799014992725)
                    ·
                      refine ⟨2423868484687287884853473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 413673554719963799014992725 2423868484687287884853473)
                      ·
                        rfl

theorem cell23_4720467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_4720467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720467 prefixEnd_4720467 := by exact prefixLift 4720467
  have htrace : WordTrace (prefixWord ++ tailWord_4720467) baseStart_4720467 baseEnd_4720467 := by
    simpa [prefixWord, tailWord_4720467, baseEnd_4720467] using wordTrace_append hprefix tailTrace_4720467
  have hstable : (prefixWord ++ tailWord_4720467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720467).length < 2 ^ (prefixWord ++ tailWord_4720467).sum := by decide
  have hdescent : baseEnd_4720467 < baseStart_4720467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720511 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 6, 3, 2]
def baseStart_4720511 : Nat := 118140960795 + 4720511 * 2 ^ 59
def prefixEnd_4720511 : Nat := 4983230072969 + 3 ^ 40 * 4720511 * 2
def baseEnd_4720511 : Nat := 2423891077836085712703271

theorem tailTrace_4720511 : CollatzResearch.WordTrace tailWord_4720511 prefixEnd_4720511 2423891077836085712703271 := by
  unfold tailWord_4720511
  simp only [CollatzResearch.WordTrace]
  refine ⟨172171180601402320939121387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114780787067601547292747591 172171180601402320939121387)
  ·
    refine ⟨258256770902103481408682081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172171180601402320939121387 258256770902103481408682081)
    ·
      refine ⟨193692578176577611056511561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258256770902103481408682081 193692578176577611056511561)
      ·
        refine ⟨145269433632433208292383671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193692578176577611056511561 145269433632433208292383671)
        ·
          refine ⟨217904150448649812438575507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145269433632433208292383671 217904150448649812438575507)
          ·
            refine ⟨326856225672974718657863261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217904150448649812438575507 326856225672974718657863261)
            ·
              refine ⟨122571084627365519496698723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326856225672974718657863261 122571084627365519496698723)
              ·
                refine ⟨183856626941048279245048085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122571084627365519496698723 183856626941048279245048085)
                ·
                  refine ⟨8618279387861638089611629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 183856626941048279245048085 8618279387861638089611629)
                  ·
                    refine ⟨3231854770448114283604361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8618279387861638089611629 3231854770448114283604361)
                    ·
                      refine ⟨2423891077836085712703271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231854770448114283604361 2423891077836085712703271)
                      ·
                        rfl

theorem cell23_4720511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_4720511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720511 prefixEnd_4720511 := by exact prefixLift 4720511
  have htrace : WordTrace (prefixWord ++ tailWord_4720511) baseStart_4720511 baseEnd_4720511 := by
    simpa [prefixWord, tailWord_4720511, baseEnd_4720511] using wordTrace_append hprefix tailTrace_4720511
  have hstable : (prefixWord ++ tailWord_4720511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720511).length < 2 ^ (prefixWord ++ tailWord_4720511).sum := by decide
  have hdescent : baseEnd_4720511 < baseStart_4720511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720591 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 3]
def baseStart_4720591 : Nat := 118140960795 + 4720591 * 2 ^ 59
def prefixEnd_4720591 : Nat := 4983230072969 + 3 ^ 40 * 4720591 * 2
def baseEnd_4720591 : Nat := 2423932156288445399702903

theorem tailTrace_4720591 : CollatzResearch.WordTrace tailWord_4720591 prefixEnd_4720591 2423932156288445399702903 := by
  unfold tailWord_4720591
  simp only [CollatzResearch.WordTrace]
  refine ⟨172174098441112494602033627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114782732294074996401355751 172174098441112494602033627)
  ·
    refine ⟨258261147661668741903050441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172174098441112494602033627 258261147661668741903050441)
    ·
      refine ⟨193695860746251556427287831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258261147661668741903050441 193695860746251556427287831)
      ·
        refine ⟨290543791119377334640931747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193695860746251556427287831 290543791119377334640931747)
        ·
          refine ⟨435815686679066001961397621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290543791119377334640931747 435815686679066001961397621)
          ·
            refine ⟨40857720626162437683881027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 435815686679066001961397621 40857720626162437683881027)
            ·
              refine ⟨61286580939243656525821541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40857720626162437683881027 61286580939243656525821541)
              ·
                refine ⟨11491233926108185598591539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61286580939243656525821541 11491233926108185598591539)
                ·
                  refine ⟨17236850889162278397887309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11491233926108185598591539 17236850889162278397887309)
                  ·
                    refine ⟨6463819083435854399207741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17236850889162278397887309 6463819083435854399207741)
                    ·
                      refine ⟨2423932156288445399702903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463819083435854399207741 2423932156288445399702903)
                      ·
                        rfl

theorem cell23_4720591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_4720591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720591 prefixEnd_4720591 := by exact prefixLift 4720591
  have htrace : WordTrace (prefixWord ++ tailWord_4720591) baseStart_4720591 baseEnd_4720591 := by
    simpa [prefixWord, tailWord_4720591, baseEnd_4720591] using wordTrace_append hprefix tailTrace_4720591
  have hstable : (prefixWord ++ tailWord_4720591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720591).length < 2 ^ (prefixWord ++ tailWord_4720591).sum := by decide
  have hdescent : baseEnd_4720591 < baseStart_4720591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720598 : List Nat := [5, 2, 1, 1, 3, 1, 10]
def baseStart_4720598 : Nat := 118140960795 + 4720598 * 2 ^ 59
def prefixEnd_4720598 : Nat := 4983230072969 + 3 ^ 40 * 4720598 * 2
def baseEnd_4720598 : Nat := 29925132724111442868091

theorem tailTrace_4720598 : CollatzResearch.WordTrace tailWord_4720598 prefixEnd_4720598 29925132724111442868091 := by
  unfold tailWord_4720598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10760897109505445924846153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114782902501391423198358965 10760897109505445924846153)
  ·
    refine ⟨8070672832129084443634615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10760897109505445924846153 8070672832129084443634615)
    ·
      refine ⟨12106009248193626665451923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8070672832129084443634615 12106009248193626665451923)
      ·
        refine ⟨18159013872290439998177885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12106009248193626665451923 18159013872290439998177885)
        ·
          refine ⟨6809630202108914999316707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18159013872290439998177885 6809630202108914999316707)
          ·
            refine ⟨10214445303163372498975061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809630202108914999316707 10214445303163372498975061)
            ·
              refine ⟨29925132724111442868091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10214445303163372498975061 29925132724111442868091)
              ·
                rfl

theorem cell23_4720598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 10].length) (baseStart_4720598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720598 prefixEnd_4720598 := by exact prefixLift 4720598
  have htrace : WordTrace (prefixWord ++ tailWord_4720598) baseStart_4720598 baseEnd_4720598 := by
    simpa [prefixWord, tailWord_4720598, baseEnd_4720598] using wordTrace_append hprefix tailTrace_4720598
  have hstable : (prefixWord ++ tailWord_4720598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720598).length < 2 ^ (prefixWord ++ tailWord_4720598).sum := by decide
  have hdescent : baseEnd_4720598 < baseStart_4720598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720602 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_4720602 : Nat := 118140960795 + 4720602 * 2 ^ 59
def prefixEnd_4720602 : Nat := 4983230072969 + 3 ^ 40 * 4720602 * 2
def baseEnd_4720602 : Nat := 807979268191881618888451

theorem tailTrace_4720602 : CollatzResearch.WordTrace tailWord_4720602 prefixEnd_4720602 807979268191881618888451 := by
  unfold tailWord_4720602
  simp only [CollatzResearch.WordTrace]
  refine ⟨43043624911018160870171015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114782999762715095653789373 43043624911018160870171015)
  ·
    refine ⟨64565437366527241305256523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43043624911018160870171015 64565437366527241305256523)
    ·
      refine ⟨96848156049790861957884785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64565437366527241305256523 96848156049790861957884785)
      ·
        refine ⟨72636117037343146468413589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96848156049790861957884785 72636117037343146468413589)
        ·
          refine ⟨3404817986125459990706887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72636117037343146468413589 3404817986125459990706887)
          ·
            refine ⟨5107226979188189986060331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404817986125459990706887 5107226979188189986060331)
            ·
              refine ⟨7660840468782284979090497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107226979188189986060331 7660840468782284979090497)
              ·
                refine ⟨5745630351586713734317873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7660840468782284979090497 5745630351586713734317873)
                ·
                  refine ⟨4309222763690035300738405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745630351586713734317873 4309222763690035300738405)
                  ·
                    refine ⟨807979268191881618888451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4309222763690035300738405 807979268191881618888451)
                    ·
                      rfl

theorem cell23_4720602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_4720602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720602 prefixEnd_4720602 := by exact prefixLift 4720602
  have htrace : WordTrace (prefixWord ++ tailWord_4720602) baseStart_4720602 baseEnd_4720602 := by
    simpa [prefixWord, tailWord_4720602, baseEnd_4720602] using wordTrace_append hprefix tailTrace_4720602
  have hstable : (prefixWord ++ tailWord_4720602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720602).length < 2 ^ (prefixWord ++ tailWord_4720602).sum := by decide
  have hdescent : baseEnd_4720602 < baseStart_4720602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720625 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_4720625 : Nat := 118140960795 + 4720625 * 2 ^ 59
def prefixEnd_4720625 : Nat := 4983230072969 + 3 ^ 40 * 4720625 * 2
def baseEnd_4720625 : Nat := 2423949614630698266677747

theorem tailTrace_4720625 : CollatzResearch.WordTrace tailWord_4720625 prefixEnd_4720625 2423949614630698266677747 := by
  unfold tailWord_4720625
  simp only [CollatzResearch.WordTrace]
  refine ⟨172175338522989318408771329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114783559015326212272514219 172175338522989318408771329)
  ·
    refine ⟨129131503892241988806578497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172175338522989318408771329 129131503892241988806578497)
    ·
      refine ⟨96848627919181491604933873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129131503892241988806578497 96848627919181491604933873)
      ·
        refine ⟨72636470939386118703700405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96848627919181491604933873 72636470939386118703700405)
        ·
          refine ⟨6809669150567448628471913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72636470939386118703700405 6809669150567448628471913)
          ·
            refine ⟨5107251862925586471353935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6809669150567448628471913 5107251862925586471353935)
            ·
              refine ⟨7660877794388379707030903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107251862925586471353935 7660877794388379707030903)
              ·
                refine ⟨11491316691582569560546355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7660877794388379707030903 11491316691582569560546355)
                ·
                  refine ⟨17236975037373854340819533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11491316691582569560546355 17236975037373854340819533)
                  ·
                    refine ⟨6463865639015195377807325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17236975037373854340819533 6463865639015195377807325)
                    ·
                      refine ⟨2423949614630698266677747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463865639015195377807325 2423949614630698266677747)
                      ·
                        rfl

theorem cell23_4720625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_4720625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720625 prefixEnd_4720625 := by exact prefixLift 4720625
  have htrace : WordTrace (prefixWord ++ tailWord_4720625) baseStart_4720625 baseEnd_4720625 := by
    simpa [prefixWord, tailWord_4720625, baseEnd_4720625] using wordTrace_append hprefix tailTrace_4720625
  have hstable : (prefixWord ++ tailWord_4720625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720625).length < 2 ^ (prefixWord ++ tailWord_4720625).sum := by decide
  have hdescent : baseEnd_4720625 < baseStart_4720625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720638 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4720638 : Nat := 118140960795 + 4720638 * 2 ^ 59
def prefixEnd_4720638 : Nat := 4983230072969 + 3 ^ 40 * 4720638 * 2
def baseEnd_4720638 : Nat := 2423956289879206715815187

theorem tailTrace_4720638 : CollatzResearch.WordTrace tailWord_4720638 prefixEnd_4720638 2423956289879206715815187 := by
  unfold tailWord_4720638
  simp only [CollatzResearch.WordTrace]
  refine ⟨21521976583992777703624321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114783875114628147752663045 21521976583992777703624321)
  ·
    refine ⟨16141482437994583277718241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21521976583992777703624321 16141482437994583277718241)
    ·
      refine ⟨12106111828495937458288681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16141482437994583277718241 12106111828495937458288681)
      ·
        refine ⟨9079583871371953093716511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12106111828495937458288681 9079583871371953093716511)
        ·
          refine ⟨13619375807057929640574767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9079583871371953093716511 13619375807057929640574767)
          ·
            refine ⟨20429063710586894460862151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13619375807057929640574767 20429063710586894460862151)
            ·
              refine ⟨30643595565880341691293227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20429063710586894460862151 30643595565880341691293227)
              ·
                refine ⟨45965393348820512536939841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30643595565880341691293227 45965393348820512536939841)
                ·
                  refine ⟨34474045011615384402704881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45965393348820512536939841 34474045011615384402704881)
                  ·
                    refine ⟨25855533758711538302028661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34474045011615384402704881 25855533758711538302028661)
                    ·
                      refine ⟨2423956289879206715815187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25855533758711538302028661 2423956289879206715815187)
                      ·
                        rfl

theorem cell23_4720638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4720638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720638 prefixEnd_4720638 := by exact prefixLift 4720638
  have htrace : WordTrace (prefixWord ++ tailWord_4720638) baseStart_4720638 baseEnd_4720638 := by
    simpa [prefixWord, tailWord_4720638, baseEnd_4720638] using wordTrace_append hprefix tailTrace_4720638
  have hstable : (prefixWord ++ tailWord_4720638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720638).length < 2 ^ (prefixWord ++ tailWord_4720638).sum := by decide
  have hdescent : baseEnd_4720638 < baseStart_4720638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720648 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_4720648 : Nat := 118140960795 + 4720648 * 2 ^ 59
def prefixEnd_4720648 : Nat := 4983230072969 + 3 ^ 40 * 4720648 * 2
def baseEnd_4720648 : Nat := 2423961424685751676690141

theorem tailTrace_4720648 : CollatzResearch.WordTrace tailWord_4720648 prefixEnd_4720648 2423961424685751676690141 := by
  unfold tailWord_4720648
  simp only [CollatzResearch.WordTrace]
  refine ⟨86088088700952996668429299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114784118267937328891239065 86088088700952996668429299)
  ·
    refine ⟨129132133051429495002643949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86088088700952996668429299 129132133051429495002643949)
    ·
      refine ⟨48424549894286060625991481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129132133051429495002643949 48424549894286060625991481)
      ·
        refine ⟨36318412420714545469493611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48424549894286060625991481 36318412420714545469493611)
        ·
          refine ⟨54477618631071818204240417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36318412420714545469493611 54477618631071818204240417)
          ·
            refine ⟨40858213973303863653180313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54477618631071818204240417 40858213973303863653180313)
            ·
              refine ⟨30643660479977897739885235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40858213973303863653180313 30643660479977897739885235)
              ·
                refine ⟨45965490719966846609827853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30643660479977897739885235 45965490719966846609827853)
                ·
                  refine ⟨17237059019987567478685445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45965490719966846609827853 17237059019987567478685445)
                  ·
                    refine ⟨3231948566247668902253521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17237059019987567478685445 3231948566247668902253521)
                    ·
                      refine ⟨2423961424685751676690141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231948566247668902253521 2423961424685751676690141)
                      ·
                        rfl

theorem cell23_4720648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_4720648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720648 prefixEnd_4720648 := by exact prefixLift 4720648
  have htrace : WordTrace (prefixWord ++ tailWord_4720648) baseStart_4720648 baseEnd_4720648 := by
    simpa [prefixWord, tailWord_4720648, baseEnd_4720648] using wordTrace_append hprefix tailTrace_4720648
  have hstable : (prefixWord ++ tailWord_4720648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720648).length < 2 ^ (prefixWord ++ tailWord_4720648).sum := by decide
  have hdescent : baseEnd_4720648 < baseStart_4720648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720651 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 5]
def baseStart_4720651 : Nat := 118140960795 + 4720651 * 2 ^ 59
def prefixEnd_4720651 : Nat := 4983230072969 + 3 ^ 40 * 4720651 * 2
def baseEnd_4720651 : Nat := 2423962965127715164952627

theorem tailTrace_4720651 : CollatzResearch.WordTrace tailWord_4720651 prefixEnd_4720651 2423962965127715164952627 := by
  unfold tailWord_4720651
  simp only [CollatzResearch.WordTrace]
  refine ⟨172176286820895124849217807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114784191213930083232811871 172176286820895124849217807)
  ·
    refine ⟨258264430231342687273826711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172176286820895124849217807 258264430231342687273826711)
    ·
      refine ⟨387396645347014030910740067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258264430231342687273826711 387396645347014030910740067)
      ·
        refine ⟨581094968020521046366110101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387396645347014030910740067 581094968020521046366110101)
        ·
          refine ⟨27238826625961924048411411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 581094968020521046366110101 27238826625961924048411411)
          ·
            refine ⟨40858239938942886072617117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27238826625961924048411411 40858239938942886072617117)
            ·
              refine ⟨15321839977103582277231419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40858239938942886072617117 15321839977103582277231419)
              ·
                refine ⟨22982759965655373415847129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15321839977103582277231419 22982759965655373415847129)
                ·
                  refine ⟨17237069974241530061885347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22982759965655373415847129 17237069974241530061885347)
                  ·
                    refine ⟨25855604961362295092828021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17237069974241530061885347 25855604961362295092828021)
                    ·
                      refine ⟨2423962965127715164952627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25855604961362295092828021 2423962965127715164952627)
                      ·
                        rfl

theorem cell23_4720651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_4720651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720651 prefixEnd_4720651 := by exact prefixLift 4720651
  have htrace : WordTrace (prefixWord ++ tailWord_4720651) baseStart_4720651 baseEnd_4720651 := by
    simpa [prefixWord, tailWord_4720651, baseEnd_4720651] using wordTrace_append hprefix tailTrace_4720651
  have hstable : (prefixWord ++ tailWord_4720651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720651).length < 2 ^ (prefixWord ++ tailWord_4720651).sum := by decide
  have hdescent : baseEnd_4720651 < baseStart_4720651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720665 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 2, 2, 2]
def baseStart_4720665 : Nat := 118140960795 + 4720665 * 2 ^ 59
def prefixEnd_4720665 : Nat := 4983230072969 + 3 ^ 40 * 4720665 * 2
def baseEnd_4720665 : Nat := 2423970153856878110177563

theorem tailTrace_4720665 : CollatzResearch.WordTrace tailWord_4720665 prefixEnd_4720665 2423970153856878110177563 := by
  unfold tailWord_4720665
  simp only [CollatzResearch.WordTrace]
  refine ⟨172176797442844405240227449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114784531628562936826818299 172176797442844405240227449)
  ·
    refine ⟨129132598082133303930170587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172176797442844405240227449 129132598082133303930170587)
    ·
      refine ⟨193698897123199955895255881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129132598082133303930170587 193698897123199955895255881)
      ·
        refine ⟨145274172842399966921441911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193698897123199955895255881 145274172842399966921441911)
        ·
          refine ⟨217911259263599950382162867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145274172842399966921441911 217911259263599950382162867)
          ·
            refine ⟨326866888895399925573244301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217911259263599950382162867 326866888895399925573244301)
            ·
              refine ⟨122575083335774972089966613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326866888895399925573244301 122575083335774972089966613)
              ·
                refine ⟨5745707031364451816717185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122575083335774972089966613 5745707031364451816717185)
                ·
                  refine ⟨4309280273523338862537889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745707031364451816717185 4309280273523338862537889)
                  ·
                    refine ⟨3231960205142504146903417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4309280273523338862537889 3231960205142504146903417)
                    ·
                      refine ⟨2423970153856878110177563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3231960205142504146903417 2423970153856878110177563)
                      ·
                        rfl

theorem cell23_4720665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_4720665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720665 prefixEnd_4720665 := by exact prefixLift 4720665
  have htrace : WordTrace (prefixWord ++ tailWord_4720665) baseStart_4720665 baseEnd_4720665 := by
    simpa [prefixWord, tailWord_4720665, baseEnd_4720665] using wordTrace_append hprefix tailTrace_4720665
  have hstable : (prefixWord ++ tailWord_4720665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720665).length < 2 ^ (prefixWord ++ tailWord_4720665).sum := by decide
  have hdescent : baseEnd_4720665 < baseStart_4720665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720676 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_4720676 : Nat := 118140960795 + 4720676 * 2 ^ 59
def prefixEnd_4720676 : Nat := 4983230072969 + 3 ^ 40 * 4720676 * 2
def baseEnd_4720676 : Nat := 2423975802144077567140013

theorem tailTrace_4720676 : CollatzResearch.WordTrace tailWord_4720676 prefixEnd_4720676 2423975802144077567140013 := by
  unfold tailWord_4720676
  simp only [CollatzResearch.WordTrace]
  refine ⟨86088599322902277059438941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114784799097203036079251921 86088599322902277059438941)
  ·
    refine ⟨32283224746088353897289603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86088599322902277059438941 32283224746088353897289603)
    ·
      refine ⟨48424837119132530845934405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32283224746088353897289603 48424837119132530845934405)
      ·
        refine ⟨9079656959837349533612701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48424837119132530845934405 9079656959837349533612701)
        ·
          refine ⟨3404871359939006075104763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9079656959837349533612701 3404871359939006075104763)
          ·
            refine ⟨5107307039908509112657145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404871359939006075104763 5107307039908509112657145)
            ·
              refine ⟨3830480279931381834492859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5107307039908509112657145 3830480279931381834492859)
              ·
                refine ⟨5745720419897072751739289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830480279931381834492859 5745720419897072751739289)
                ·
                  refine ⟨4309290314922804563804467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745720419897072751739289 4309290314922804563804467)
                  ·
                    refine ⟨6463935472384206845706701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4309290314922804563804467 6463935472384206845706701)
                    ·
                      refine ⟨2423975802144077567140013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463935472384206845706701 2423975802144077567140013)
                      ·
                        rfl

theorem cell23_4720676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_4720676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720676 prefixEnd_4720676 := by exact prefixLift 4720676
  have htrace : WordTrace (prefixWord ++ tailWord_4720676) baseStart_4720676 baseEnd_4720676 := by
    simpa [prefixWord, tailWord_4720676, baseEnd_4720676] using wordTrace_append hprefix tailTrace_4720676
  have hstable : (prefixWord ++ tailWord_4720676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720676).length < 2 ^ (prefixWord ++ tailWord_4720676).sum := by decide
  have hdescent : baseEnd_4720676 < baseStart_4720676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720681 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 3]
def baseStart_4720681 : Nat := 118140960795 + 4720681 * 2 ^ 59
def prefixEnd_4720681 : Nat := 4983230072969 + 3 ^ 40 * 4720681 * 2
def baseEnd_4720681 : Nat := 2423978369547350047577489

theorem tailTrace_4720681 : CollatzResearch.WordTrace tailWord_4720681 prefixEnd_4720681 2423978369547350047577489 := by
  unfold tailWord_4720681
  simp only [CollatzResearch.WordTrace]
  refine ⟨172177381010786439972809897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114784920673857626648539931 172177381010786439972809897)
  ·
    refine ⟨129133035758089829979607423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172177381010786439972809897 129133035758089829979607423)
    ·
      refine ⟨193699553637134744969411135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129133035758089829979607423 193699553637134744969411135)
      ·
        refine ⟨290549330455702117454116703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193699553637134744969411135 290549330455702117454116703)
        ·
          refine ⟨435823995683553176181175055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290549330455702117454116703 435823995683553176181175055)
          ·
            refine ⟨653735993525329764271762583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435823995683553176181175055 653735993525329764271762583)
            ·
              refine ⟨980603990287994646407643875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653735993525329764271762583 980603990287994646407643875)
              ·
                refine ⟨1470905985431991969611465813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 980603990287994646407643875 1470905985431991969611465813)
                ·
                  refine ⟨17237179516781155893884365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1470905985431991969611465813 17237179516781155893884365)
                  ·
                    refine ⟨6463942318792933460206637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17237179516781155893884365 6463942318792933460206637)
                    ·
                      refine ⟨2423978369547350047577489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6463942318792933460206637 2423978369547350047577489)
                      ·
                        rfl

theorem cell23_4720681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_4720681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720681 prefixEnd_4720681 := by exact prefixLift 4720681
  have htrace : WordTrace (prefixWord ++ tailWord_4720681) baseStart_4720681 baseEnd_4720681 := by
    simpa [prefixWord, tailWord_4720681, baseEnd_4720681] using wordTrace_append hprefix tailTrace_4720681
  have hstable : (prefixWord ++ tailWord_4720681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720681).length < 2 ^ (prefixWord ++ tailWord_4720681).sum := by decide
  have hdescent : baseEnd_4720681 < baseStart_4720681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720711 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_4720711 : Nat := 118140960795 + 4720711 * 2 ^ 59
def prefixEnd_4720711 : Nat := 4983230072969 + 3 ^ 40 * 4720711 * 2
def baseEnd_4720711 : Nat := 2423993773966984930202351

theorem tailTrace_4720711 : CollatzResearch.WordTrace tailWord_4720711 prefixEnd_4720711 2423993773966984930202351 := by
  unfold tailWord_4720711
  simp only [CollatzResearch.WordTrace]
  refine ⟨172178475200677755096401987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114785650133785170064267991 172178475200677755096401987)
  ·
    refine ⟨258267712801016632644602981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172178475200677755096401987 258267712801016632644602981)
    ·
      refine ⟨48425196150190618620863059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258267712801016632644602981 48425196150190618620863059)
      ·
        refine ⟨72637794225285927931294589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48425196150190618620863059 72637794225285927931294589)
        ·
          refine ⟨27239172834482222974235471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72637794225285927931294589 27239172834482222974235471)
          ·
            refine ⟨40858759251723334461353207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27239172834482222974235471 40858759251723334461353207)
            ·
              refine ⟨61288138877585001692029811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40858759251723334461353207 61288138877585001692029811)
              ·
                refine ⟨91932208316377502538044717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61288138877585001692029811 91932208316377502538044717)
                ·
                  refine ⟨34474578118641563451766769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91932208316377502538044717 34474578118641563451766769)
                  ·
                    refine ⟨25855933588981172588825077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34474578118641563451766769 25855933588981172588825077)
                    ·
                      refine ⟨2423993773966984930202351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25855933588981172588825077 2423993773966984930202351)
                      ·
                        rfl

theorem cell23_4720711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_4720711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720711 prefixEnd_4720711 := by exact prefixLift 4720711
  have htrace : WordTrace (prefixWord ++ tailWord_4720711) baseStart_4720711 baseEnd_4720711 := by
    simpa [prefixWord, tailWord_4720711, baseEnd_4720711] using wordTrace_append hprefix tailTrace_4720711
  have hstable : (prefixWord ++ tailWord_4720711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720711).length < 2 ^ (prefixWord ++ tailWord_4720711).sum := by decide
  have hdescent : baseEnd_4720711 < baseStart_4720711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720718 : List Nat := [4, 1, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_4720718 : Nat := 118140960795 + 4720718 * 2 ^ 59
def prefixEnd_4720718 : Nat := 4983230072969 + 3 ^ 40 * 4720718 * 2
def baseEnd_4720718 : Nat := 807999122777188800938273

theorem tailTrace_4720718 : CollatzResearch.WordTrace tailWord_4720718 prefixEnd_4720718 807999122777188800938273 := by
  unfold tailWord_4720718
  simp only [CollatzResearch.WordTrace]
  refine ⟨21522341313956549411488351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114785820341101596861271205 21522341313956549411488351)
  ·
    refine ⟨32283511970934824117232527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21522341313956549411488351 32283511970934824117232527)
    ·
      refine ⟨48425267956402236175848791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32283511970934824117232527 48425267956402236175848791)
      ·
        refine ⟨72637901934603354263773187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48425267956402236175848791 72637901934603354263773187)
        ·
          refine ⟨108956852901905031395659781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72637901934603354263773187 108956852901905031395659781)
          ·
            refine ⟨20429409919107193386686209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108956852901905031395659781 20429409919107193386686209)
            ·
              refine ⟨15322057439330395040014657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20429409919107193386686209 15322057439330395040014657)
              ·
                refine ⟨11491543079497796280010993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15322057439330395040014657 11491543079497796280010993)
                ·
                  refine ⟨8618657309623347210008245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11491543079497796280010993 8618657309623347210008245)
                  ·
                    refine ⟨807999122777188800938273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8618657309623347210008245 807999122777188800938273)
                    ·
                      rfl

theorem cell23_4720718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_4720718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720718 prefixEnd_4720718 := by exact prefixLift 4720718
  have htrace : WordTrace (prefixWord ++ tailWord_4720718) baseStart_4720718 baseEnd_4720718 := by
    simpa [prefixWord, tailWord_4720718, baseEnd_4720718] using wordTrace_append hprefix tailTrace_4720718
  have hstable : (prefixWord ++ tailWord_4720718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720718).length < 2 ^ (prefixWord ++ tailWord_4720718).sum := by decide
  have hdescent : baseEnd_4720718 < baseStart_4720718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720721 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_4720721 : Nat := 118140960795 + 4720721 * 2 ^ 59
def prefixEnd_4720721 : Nat := 4983230072969 + 3 ^ 40 * 4720721 * 2
def baseEnd_4720721 : Nat := 2423998908773529891077305

theorem tailTrace_4720721 : CollatzResearch.WordTrace tailWord_4720721 prefixEnd_4720721 2423998908773529891077305 := by
  unfold tailWord_4720721
  simp only [CollatzResearch.WordTrace]
  refine ⟨172178839930641526804266017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114785893287094351202844011 172178839930641526804266017)
  ·
    refine ⟨129134129947981145103199513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172178839930641526804266017 129134129947981145103199513)
    ·
      refine ⟨96850597460985858827399635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129134129947981145103199513 96850597460985858827399635)
      ·
        refine ⟨145275896191478788241099453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96850597460985858827399635 145275896191478788241099453)
        ·
          refine ⟨54478461071804545590412295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145275896191478788241099453 54478461071804545590412295)
          ·
            refine ⟨81717691607706818385618443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54478461071804545590412295 81717691607706818385618443)
            ·
              refine ⟨122576537411560227578427665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81717691607706818385618443 122576537411560227578427665)
              ·
                refine ⟨91932403058670170683820749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122576537411560227578427665 91932403058670170683820749)
                ·
                  refine ⟨34474651147001314006432781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91932403058670170683820749 34474651147001314006432781)
                  ·
                    refine ⟨12927994180125492752412293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34474651147001314006432781 12927994180125492752412293)
                    ·
                      refine ⟨2423998908773529891077305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12927994180125492752412293 2423998908773529891077305)
                      ·
                        rfl

theorem cell23_4720721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_4720721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720721 prefixEnd_4720721 := by exact prefixLift 4720721
  have htrace : WordTrace (prefixWord ++ tailWord_4720721) baseStart_4720721 baseEnd_4720721 := by
    simpa [prefixWord, tailWord_4720721, baseEnd_4720721] using wordTrace_append hprefix tailTrace_4720721
  have hstable : (prefixWord ++ tailWord_4720721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720721).length < 2 ^ (prefixWord ++ tailWord_4720721).sum := by decide
  have hdescent : baseEnd_4720721 < baseStart_4720721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720748 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_4720748 : Nat := 118140960795 + 4720748 * 2 ^ 59
def prefixEnd_4720748 : Nat := 4983230072969 + 3 ^ 40 * 4720748 * 2
def baseEnd_4720748 : Nat := 808004257583733761813227

theorem tailTrace_4720748 : CollatzResearch.WordTrace tailWord_4720748 prefixEnd_4720748 808004257583733761813227 := by
  unfold tailWord_4720748
  simp only [CollatzResearch.WordTrace]
  refine ⟨86089912350771855207749449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114786549801029140276999265 86089912350771855207749449)
  ·
    refine ⟨64567434263078891405812087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86089912350771855207749449 64567434263078891405812087)
    ·
      refine ⟨96851151394618337108718131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64567434263078891405812087 96851151394618337108718131)
      ·
        refine ⟨145276727091927505663077197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96851151394618337108718131 145276727091927505663077197)
        ·
          refine ⟨54478772659472814623653949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145276727091927505663077197 54478772659472814623653949)
          ·
            refine ⟨20429539747302305483870231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54478772659472814623653949 20429539747302305483870231)
            ·
              refine ⟨30644309620953458225805347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20429539747302305483870231 30644309620953458225805347)
              ·
                refine ⟨45966464431430187338708021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30644309620953458225805347 45966464431430187338708021)
                ·
                  refine ⟨4309356040446580063003877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45966464431430187338708021 4309356040446580063003877)
                  ·
                    refine ⟨808004257583733761813227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4309356040446580063003877 808004257583733761813227)
                    ·
                      rfl

theorem cell23_4720748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_4720748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720748 prefixEnd_4720748 := by exact prefixLift 4720748
  have htrace : WordTrace (prefixWord ++ tailWord_4720748) baseStart_4720748 baseEnd_4720748 := by
    simpa [prefixWord, tailWord_4720748, baseEnd_4720748] using wordTrace_append hprefix tailTrace_4720748
  have hstable : (prefixWord ++ tailWord_4720748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720748).length < 2 ^ (prefixWord ++ tailWord_4720748).sum := by decide
  have hdescent : baseEnd_4720748 < baseStart_4720748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720778 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 8]
def baseStart_4720778 : Nat := 118140960795 + 4720778 * 2 ^ 59
def prefixEnd_4720778 : Nat := 4983230072969 + 3 ^ 40 * 4720778 * 2
def baseEnd_4720778 : Nat := 269336464130092907562727

theorem tailTrace_4720778 : CollatzResearch.WordTrace tailWord_4720778 prefixEnd_4720778 269336464130092907562727 := by
  unfold tailWord_4720778
  simp only [CollatzResearch.WordTrace]
  refine ⟨43045229722858756384772747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114787279260956683692727325 43045229722858756384772747)
  ·
    refine ⟨64567844584288134577159121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43045229722858756384772747 64567844584288134577159121)
    ·
      refine ⟨48425883438216100932869341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64567844584288134577159121 48425883438216100932869341)
      ·
        refine ⟨18159706289331037849826003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48425883438216100932869341 18159706289331037849826003)
        ·
          refine ⟨27239559433996556774739005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18159706289331037849826003 27239559433996556774739005)
          ·
            refine ⟨10214834787748708790527127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27239559433996556774739005 10214834787748708790527127)
            ·
              refine ⟨15322252181623063185790691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10214834787748708790527127 15322252181623063185790691)
              ·
                refine ⟨22983378272434594778686037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15322252181623063185790691 22983378272434594778686037)
                ·
                  refine ⟨269336464130092907562727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22983378272434594778686037 269336464130092907562727)
                  ·
                    rfl

theorem cell23_4720778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_4720778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720778 prefixEnd_4720778 := by exact prefixLift 4720778
  have htrace : WordTrace (prefixWord ++ tailWord_4720778) baseStart_4720778 baseEnd_4720778 := by
    simpa [prefixWord, tailWord_4720778, baseEnd_4720778] using wordTrace_append hprefix tailTrace_4720778
  have hstable : (prefixWord ++ tailWord_4720778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720778).length < 2 ^ (prefixWord ++ tailWord_4720778).sum := by decide
  have hdescent : baseEnd_4720778 < baseStart_4720778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720782 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_4720782 : Nat := 118140960795 + 4720782 * 2 ^ 59
def prefixEnd_4720782 : Nat := 4983230072969 + 3 ^ 40 * 4720782 * 2
def baseEnd_4720782 : Nat := 808010077031151384138175

theorem tailTrace_4720782 : CollatzResearch.WordTrace tailWord_4720782 prefixEnd_4720782 808010077031151384138175 := by
  unfold tailWord_4720782
  simp only [CollatzResearch.WordTrace]
  refine ⟨21522633097927566777779575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114787376522280356148157733 21522633097927566777779575)
  ·
    refine ⟨32283949646891350166669363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21522633097927566777779575 32283949646891350166669363)
    ·
      refine ⟨48425924470337025250004045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32283949646891350166669363 48425924470337025250004045)
      ·
        refine ⟨18159721676376384468751517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48425924470337025250004045 18159721676376384468751517)
        ·
          refine ⟨6809895628641144175781819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18159721676376384468751517 6809895628641144175781819)
          ·
            refine ⟨10214843442961716263672729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809895628641144175781819 10214843442961716263672729)
            ·
              refine ⟨7661132582221287197754547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10214843442961716263672729 7661132582221287197754547)
              ·
                refine ⟨11491698873331930796631821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7661132582221287197754547 11491698873331930796631821)
                ·
                  refine ⟨4309387077499474048736933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11491698873331930796631821 4309387077499474048736933)
                  ·
                    refine ⟨808010077031151384138175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4309387077499474048736933 808010077031151384138175)
                    ·
                      rfl

theorem cell23_4720782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_4720782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720782 prefixEnd_4720782 := by exact prefixLift 4720782
  have htrace : WordTrace (prefixWord ++ tailWord_4720782) baseStart_4720782 baseEnd_4720782 := by
    simpa [prefixWord, tailWord_4720782, baseEnd_4720782] using wordTrace_append hprefix tailTrace_4720782
  have hstable : (prefixWord ++ tailWord_4720782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720782).length < 2 ^ (prefixWord ++ tailWord_4720782).sum := by decide
  have hdescent : baseEnd_4720782 < baseStart_4720782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720805 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_4720805 : Nat := 118140960795 + 4720805 * 2 ^ 59
def prefixEnd_4720805 : Nat := 4983230072969 + 3 ^ 40 * 4720805 * 2
def baseEnd_4720805 : Nat := 2424042041148507562426919

theorem tailTrace_4720805 : CollatzResearch.WordTrace tailWord_4720805 prefixEnd_4720805 2424042041148507562426919 := by
  unfold tailWord_4720805
  simp only [CollatzResearch.WordTrace]
  refine ⟨172181903662337209150323869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114787935774891472766882579 172181903662337209150323869)
  ·
    refine ⟨64568213873376453431371451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172181903662337209150323869 64568213873376453431371451)
    ·
      refine ⟨96852320810064680147057177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64568213873376453431371451 96852320810064680147057177)
      ·
        refine ⟨72639240607548510110292883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96852320810064680147057177 72639240607548510110292883)
        ·
          refine ⟨108958860911322765165439325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72639240607548510110292883 108958860911322765165439325)
          ·
            refine ⟨40859572841746036937039747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108958860911322765165439325 40859572841746036937039747)
            ·
              refine ⟨61289359262619055405559621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40859572841746036937039747 61289359262619055405559621)
              ·
                refine ⟨11491754861741072888542429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61289359262619055405559621 11491754861741072888542429)
                ·
                  refine ⟨4309408073152902333203411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11491754861741072888542429 4309408073152902333203411)
                  ·
                    refine ⟨6464112109729353499805117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4309408073152902333203411 6464112109729353499805117)
                    ·
                      refine ⟨2424042041148507562426919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6464112109729353499805117 2424042041148507562426919)
                      ·
                        rfl

theorem cell23_4720805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_4720805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720805 prefixEnd_4720805 := by exact prefixLift 4720805
  have htrace : WordTrace (prefixWord ++ tailWord_4720805) baseStart_4720805 baseEnd_4720805 := by
    simpa [prefixWord, tailWord_4720805, baseEnd_4720805] using wordTrace_append hprefix tailTrace_4720805
  have hstable : (prefixWord ++ tailWord_4720805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720805).length < 2 ^ (prefixWord ++ tailWord_4720805).sum := by decide
  have hdescent : baseEnd_4720805 < baseStart_4720805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720815 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 2, 3, 2]
def baseStart_4720815 : Nat := 118140960795 + 4720815 * 2 ^ 59
def prefixEnd_4720815 : Nat := 4983230072969 + 3 ^ 40 * 4720815 * 2
def baseEnd_4720815 : Nat := 2424047175955052523301873

theorem tailTrace_4720815 : CollatzResearch.WordTrace tailWord_4720815 prefixEnd_4720815 2424047175955052523301873 := by
  unfold tailWord_4720815
  simp only [CollatzResearch.WordTrace]
  refine ⟨172182268392300980858187899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114788178928200653905458599 172182268392300980858187899)
  ·
    refine ⟨258273402588451471287281849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172182268392300980858187899 258273402588451471287281849)
    ·
      refine ⟨193705051941338603465461387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258273402588451471287281849 193705051941338603465461387)
      ·
        refine ⟨290557577912007905198192081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193705051941338603465461387 290557577912007905198192081)
        ·
          refine ⟨217918183434005928898644061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290557577912007905198192081 217918183434005928898644061)
          ·
            refine ⟨81719318787752223336991523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217918183434005928898644061 81719318787752223336991523)
            ·
              refine ⟨122578978181628335005487285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81719318787752223336991523 122578978181628335005487285)
              ·
                refine ⟨11491779204527656406764433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122578978181628335005487285 11491779204527656406764433)
                ·
                  refine ⟨8618834403395742305073325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11491779204527656406764433 8618834403395742305073325)
                  ·
                    refine ⟨3232062901273403364402497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8618834403395742305073325 3232062901273403364402497)
                    ·
                      refine ⟨2424047175955052523301873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232062901273403364402497 2424047175955052523301873)
                      ·
                        rfl

theorem cell23_4720815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 3, 2].length) (baseStart_4720815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720815 prefixEnd_4720815 := by exact prefixLift 4720815
  have htrace : WordTrace (prefixWord ++ tailWord_4720815) baseStart_4720815 baseEnd_4720815 := by
    simpa [prefixWord, tailWord_4720815, baseEnd_4720815] using wordTrace_append hprefix tailTrace_4720815
  have hstable : (prefixWord ++ tailWord_4720815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720815).length < 2 ^ (prefixWord ++ tailWord_4720815).sum := by decide
  have hdescent : baseEnd_4720815 < baseStart_4720815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720832 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 2, 3, 2]
def baseStart_4720832 : Nat := 118140960795 + 4720832 * 2 ^ 59
def prefixEnd_4720832 : Nat := 4983230072969 + 3 ^ 40 * 4720832 * 2
def baseEnd_4720832 : Nat := 2424055905126178956789295

theorem tailTrace_4720832 : CollatzResearch.WordTrace tailWord_4720832 prefixEnd_4720832 2424055905126178956789295 := by
  unfold tailWord_4720832
  simp only [CollatzResearch.WordTrace]
  refine ⟨86091444216619696380778375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114788592288826261841037833 86091444216619696380778375)
  ·
    refine ⟨129137166324929544571167563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86091444216619696380778375 129137166324929544571167563)
    ·
      refine ⟨193705749487394316856751345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129137166324929544571167563 193705749487394316856751345)
      ·
        refine ⟨145279312115545737642563509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193705749487394316856751345 145279312115545737642563509)
        ·
          refine ⟨13619935510832412903990329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145279312115545737642563509 13619935510832412903990329)
          ·
            refine ⟨10214951633124309677992747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13619935510832412903990329 10214951633124309677992747)
            ·
              refine ⟨15322427449686464516989121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10214951633124309677992747 15322427449686464516989121)
              ·
                refine ⟨11491820587264848387741841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15322427449686464516989121 11491820587264848387741841)
                ·
                  refine ⟨8618865440448636290806381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11491820587264848387741841 8618865440448636290806381)
                  ·
                    refine ⟨3232074540168238609052393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8618865440448636290806381 3232074540168238609052393)
                    ·
                      refine ⟨2424055905126178956789295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232074540168238609052393 2424055905126178956789295)
                      ·
                        rfl

theorem cell23_4720832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_4720832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720832 prefixEnd_4720832 := by exact prefixLift 4720832
  have htrace : WordTrace (prefixWord ++ tailWord_4720832) baseStart_4720832 baseEnd_4720832 := by
    simpa [prefixWord, tailWord_4720832, baseEnd_4720832] using wordTrace_append hprefix tailTrace_4720832
  have hstable : (prefixWord ++ tailWord_4720832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720832).length < 2 ^ (prefixWord ++ tailWord_4720832).sum := by decide
  have hdescent : baseEnd_4720832 < baseStart_4720832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720858 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_4720858 : Nat := 118140960795 + 4720858 * 2 ^ 59
def prefixEnd_4720858 : Nat := 4983230072969 + 3 ^ 40 * 4720858 * 2
def baseEnd_4720858 : Nat := 2424069255623195855064175

theorem tailTrace_4720858 : CollatzResearch.WordTrace tailWord_4720858 prefixEnd_4720858 2424069255623195855064175 := by
  unfold tailWord_4720858
  simp only [CollatzResearch.WordTrace]
  refine ⟨43045959182786299800500807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114789224487430132801335485 43045959182786299800500807)
  ·
    refine ⟨64568938774179449700751211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43045959182786299800500807 64568938774179449700751211)
    ·
      refine ⟨96853408161269174551126817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64568938774179449700751211 96853408161269174551126817)
      ·
        refine ⟨72640056120951880913345113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96853408161269174551126817 72640056120951880913345113)
        ·
          refine ⟨54480042090713910685008835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72640056120951880913345113 54480042090713910685008835)
          ·
            refine ⟨81720063136070866027513253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54480042090713910685008835 81720063136070866027513253)
            ·
              refine ⟨15322511838013287380158735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81720063136070866027513253 15322511838013287380158735)
              ·
                refine ⟨22983767757019931070238103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15322511838013287380158735 22983767757019931070238103)
                ·
                  refine ⟨34475651635529896605357155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22983767757019931070238103 34475651635529896605357155)
                  ·
                    refine ⟨51713477453294844908035733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34475651635529896605357155 51713477453294844908035733)
                    ·
                      refine ⟨2424069255623195855064175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51713477453294844908035733 2424069255623195855064175)
                      ·
                        rfl

theorem cell23_4720858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_4720858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720858 prefixEnd_4720858 := by exact prefixLift 4720858
  have htrace : WordTrace (prefixWord ++ tailWord_4720858) baseStart_4720858 baseEnd_4720858 := by
    simpa [prefixWord, tailWord_4720858, baseEnd_4720858] using wordTrace_append hprefix tailTrace_4720858
  have hstable : (prefixWord ++ tailWord_4720858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720858).length < 2 ^ (prefixWord ++ tailWord_4720858).sum := by decide
  have hdescent : baseEnd_4720858 < baseStart_4720858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720865 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_4720865 : Nat := 118140960795 + 4720865 * 2 ^ 59
def prefixEnd_4720865 : Nat := 4983230072969 + 3 ^ 40 * 4720865 * 2
def baseEnd_4720865 : Nat := 2424072849987777327676643

theorem tailTrace_4720865 : CollatzResearch.WordTrace tailWord_4720865 prefixEnd_4720865 2424072849987777327676643 := by
  unfold tailWord_4720865
  simp only [CollatzResearch.WordTrace]
  refine ⟨172184092042119839397508049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114789394694746559598338699 172184092042119839397508049)
  ·
    refine ⟨129138069031589879548131037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172184092042119839397508049 129138069031589879548131037)
    ·
      refine ⟨48426775886846204830549139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129138069031589879548131037 48426775886846204830549139)
      ·
        refine ⟨72640163830269307245823709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48426775886846204830549139 72640163830269307245823709)
        ·
          refine ⟨27240061436350990217183891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72640163830269307245823709 27240061436350990217183891)
          ·
            refine ⟨40860092154526485325775837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27240061436350990217183891 40860092154526485325775837)
            ·
              refine ⟨15322534557947431997165939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40860092154526485325775837 15322534557947431997165939)
              ·
                refine ⟨22983801836921147995748909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15322534557947431997165939 22983801836921147995748909)
                ·
                  refine ⟨8618925688845430498405841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22983801836921147995748909 8618925688845430498405841)
                  ·
                    refine ⟨6464194266634072873804381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8618925688845430498405841 6464194266634072873804381)
                    ·
                      refine ⟨2424072849987777327676643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6464194266634072873804381 2424072849987777327676643)
                      ·
                        rfl

theorem cell23_4720865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_4720865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720865 prefixEnd_4720865 := by exact prefixLift 4720865
  have htrace : WordTrace (prefixWord ++ tailWord_4720865) baseStart_4720865 baseEnd_4720865 := by
    simpa [prefixWord, tailWord_4720865, baseEnd_4720865] using wordTrace_append hprefix tailTrace_4720865
  have hstable : (prefixWord ++ tailWord_4720865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720865).length < 2 ^ (prefixWord ++ tailWord_4720865).sum := by decide
  have hdescent : baseEnd_4720865 < baseStart_4720865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720882 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_4720882 : Nat := 118140960795 + 4720882 * 2 ^ 59
def prefixEnd_4720882 : Nat := 4983230072969 + 3 ^ 40 * 4720882 * 2
def baseEnd_4720882 : Nat := 2424081579158903761164065

theorem tailTrace_4720882 : CollatzResearch.WordTrace tailWord_4720882 prefixEnd_4720882 2424081579158903761164065 := by
  unfold tailWord_4720882
  simp only [CollatzResearch.WordTrace]
  refine ⟨43046178020764562825219225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114789808055372167533917933 43046178020764562825219225)
  ·
    refine ⟨32284633515573422118914419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43046178020764562825219225 32284633515573422118914419)
    ·
      refine ⟨48426950273360133178371629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32284633515573422118914419 48426950273360133178371629)
      ·
        refine ⟨18160106352510049941889361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48426950273360133178371629 18160106352510049941889361)
        ·
          refine ⟨13620079764382537456417021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18160106352510049941889361 13620079764382537456417021)
          ·
            refine ⟨5107529911643451546156383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13620079764382537456417021 5107529911643451546156383)
            ·
              refine ⟨7661294867465177319234575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107529911643451546156383 7661294867465177319234575)
              ·
                refine ⟨11491942301197765978851863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7661294867465177319234575 11491942301197765978851863)
                ·
                  refine ⟨17237913451796648968277795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11491942301197765978851863 17237913451796648968277795)
                  ·
                    refine ⟨25856870177694973452416693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17237913451796648968277795 25856870177694973452416693)
                    ·
                      refine ⟨2424081579158903761164065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25856870177694973452416693 2424081579158903761164065)
                      ·
                        rfl

theorem cell23_4720882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_4720882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720882 prefixEnd_4720882 := by exact prefixLift 4720882
  have htrace : WordTrace (prefixWord ++ tailWord_4720882) baseStart_4720882 baseEnd_4720882 := by
    simpa [prefixWord, tailWord_4720882, baseEnd_4720882] using wordTrace_append hprefix tailTrace_4720882
  have hstable : (prefixWord ++ tailWord_4720882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720882).length < 2 ^ (prefixWord ++ tailWord_4720882).sum := by decide
  have hdescent : baseEnd_4720882 < baseStart_4720882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720896 : List Nat := [2, 1, 1, 2, 1, 1, 8, 2, 1, 2, 2]
def baseStart_4720896 : Nat := 118140960795 + 4720896 * 2 ^ 59
def prefixEnd_4720896 : Nat := 4983230072969 + 3 ^ 40 * 4720896 * 2
def baseEnd_4720896 : Nat := 2424088767888066706389001

theorem tailTrace_4720896 : CollatzResearch.WordTrace tailWord_4720896 prefixEnd_4720896 2424088767888066706389001 := by
  unfold tailWord_4720896
  simp only [CollatzResearch.WordTrace]
  refine ⟨86092611352503765845943271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114790148470005021127924361 86092611352503765845943271)
  ·
    refine ⟨129138917028755648768914907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86092611352503765845943271 129138917028755648768914907)
    ·
      refine ⟨193708375543133473153372361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129138917028755648768914907 193708375543133473153372361)
      ·
        refine ⟨145281281657350104865029271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193708375543133473153372361 145281281657350104865029271)
        ·
          refine ⟨217921922486025157297543907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145281281657350104865029271 217921922486025157297543907)
          ·
            refine ⟨326882883729037735946315861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217921922486025157297543907 326882883729037735946315861)
            ·
              refine ⟨3830658793699660968120889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 326882883729037735946315861 3830658793699660968120889)
              ·
                refine ⟨2872994095274745726090667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830658793699660968120889 2872994095274745726090667)
                ·
                  refine ⟨4309491142912118589136001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872994095274745726090667 4309491142912118589136001)
                  ·
                    refine ⟨3232118357184088941852001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4309491142912118589136001 3232118357184088941852001)
                    ·
                      refine ⟨2424088767888066706389001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232118357184088941852001 2424088767888066706389001)
                      ·
                        rfl

theorem cell23_4720896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_4720896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720896 prefixEnd_4720896 := by exact prefixLift 4720896
  have htrace : WordTrace (prefixWord ++ tailWord_4720896) baseStart_4720896 baseEnd_4720896 := by
    simpa [prefixWord, tailWord_4720896, baseEnd_4720896] using wordTrace_append hprefix tailTrace_4720896
  have hstable : (prefixWord ++ tailWord_4720896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720896).length < 2 ^ (prefixWord ++ tailWord_4720896).sum := by decide
  have hdescent : baseEnd_4720896 < baseStart_4720896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4720946 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_4720946 : Nat := 118140960795 + 4720946 * 2 ^ 59
def prefixEnd_4720946 : Nat := 4983230072969 + 3 ^ 40 * 4720946 * 2
def baseEnd_4720946 : Nat := 2424114441920791510763771

theorem tailTrace_4720946 : CollatzResearch.WordTrace tailWord_4720946 prefixEnd_4720946 2424114441920791510763771 := by
  unfold tailWord_4720946
  simp only [CollatzResearch.WordTrace]
  refine ⟨43046761588706597557801673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114791364236550926820804461 43046761588706597557801673)
  ·
    refine ⟨32285071191529948168351255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43046761588706597557801673 32285071191529948168351255)
    ·
      refine ⟨48427606787294922252526883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32285071191529948168351255 48427606787294922252526883)
      ·
        refine ⟨72641410180942383378790325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48427606787294922252526883 72641410180942383378790325)
        ·
          refine ⟨6810132204463348441761593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72641410180942383378790325 6810132204463348441761593)
          ·
            refine ⟨5107599153347511331321195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6810132204463348441761593 5107599153347511331321195)
            ·
              refine ⟨7661398730021266996981793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107599153347511331321195 7661398730021266996981793)
              ·
                refine ⟨5746049047515950247736345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7661398730021266996981793 5746049047515950247736345)
                ·
                  refine ⟨4309536785636962685802259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5746049047515950247736345 4309536785636962685802259)
                  ·
                    refine ⟨6464305178455444028703389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4309536785636962685802259 6464305178455444028703389)
                    ·
                      refine ⟨2424114441920791510763771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6464305178455444028703389 2424114441920791510763771)
                      ·
                        rfl

theorem cell23_4720946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_4720946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4720946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4720946 prefixEnd_4720946 := by exact prefixLift 4720946
  have htrace : WordTrace (prefixWord ++ tailWord_4720946) baseStart_4720946 baseEnd_4720946 := by
    simpa [prefixWord, tailWord_4720946, baseEnd_4720946] using wordTrace_append hprefix tailTrace_4720946
  have hstable : (prefixWord ++ tailWord_4720946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4720946).length < 2 ^ (prefixWord ++ tailWord_4720946).sum := by decide
  have hdescent : baseEnd_4720946 < baseStart_4720946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4720946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721055 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4721055 : Nat := 118140960795 + 4721055 * 2 ^ 59
def prefixEnd_4721055 : Nat := 4983230072969 + 3 ^ 40 * 4721055 * 2
def baseEnd_4721055 : Nat := 2424170411312131584300769

theorem tailTrace_4721055 : CollatzResearch.WordTrace tailWord_4721055 prefixEnd_4721055 2424170411312131584300769 := by
  unfold tailWord_4721055
  simp only [CollatzResearch.WordTrace]
  refine ⟨172191021911431501846924619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114794014607621001231283079 172191021911431501846924619)
  ·
    refine ⟨258286532867147252770386929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172191021911431501846924619 258286532867147252770386929)
    ·
      refine ⟨193714899650360439577790197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258286532867147252770386929 193714899650360439577790197)
      ·
        refine ⟨18160771842221291210417831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193714899650360439577790197 18160771842221291210417831)
        ·
          refine ⟨27241157763331936815626747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18160771842221291210417831 27241157763331936815626747)
          ·
            refine ⟨40861736644997905223440121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27241157763331936815626747 40861736644997905223440121)
            ·
              refine ⟨30646302483748428917580091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40861736644997905223440121 30646302483748428917580091)
              ·
                refine ⟨45969453725622643376370137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30646302483748428917580091 45969453725622643376370137)
                ·
                  refine ⟨34477090294216982532277603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45969453725622643376370137 34477090294216982532277603)
                  ·
                    refine ⟨51715635441325473798416405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34477090294216982532277603 51715635441325473798416405)
                    ·
                      refine ⟨2424170411312131584300769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51715635441325473798416405 2424170411312131584300769)
                      ·
                        rfl

theorem cell23_4721055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4721055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721055 prefixEnd_4721055 := by exact prefixLift 4721055
  have htrace : WordTrace (prefixWord ++ tailWord_4721055) baseStart_4721055 baseEnd_4721055 := by
    simpa [prefixWord, tailWord_4721055, baseEnd_4721055] using wordTrace_append hprefix tailTrace_4721055
  have hstable : (prefixWord ++ tailWord_4721055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721055).length < 2 ^ (prefixWord ++ tailWord_4721055).sum := by decide
  have hdescent : baseEnd_4721055 < baseStart_4721055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721075 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 3]
def baseStart_4721075 : Nat := 118140960795 + 4721075 * 2 ^ 59
def prefixEnd_4721075 : Nat := 4983230072969 + 3 ^ 40 * 4721075 * 2
def baseEnd_4721075 : Nat := 2424180680925221506050677

theorem tailTrace_4721075 : CollatzResearch.WordTrace tailWord_4721075 prefixEnd_4721075 2424180680925221506050677 := by
  unfold tailWord_4721075
  simp only [CollatzResearch.WordTrace]
  refine ⟨172191751371359045262652679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114794500914239363508435119 172191751371359045262652679)
  ·
    refine ⟨258287627057038567893979019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172191751371359045262652679 258287627057038567893979019)
    ·
      refine ⟨387431440585557851840968529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258287627057038567893979019 387431440585557851840968529)
      ·
        refine ⟨290573580439168388880726397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387431440585557851840968529 290573580439168388880726397)
        ·
          refine ⟨108965092664688145830272399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290573580439168388880726397 108965092664688145830272399)
          ·
            refine ⟨163447638997032218745408599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108965092664688145830272399 163447638997032218745408599)
            ·
              refine ⟨245171458495548328118112899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163447638997032218745408599 245171458495548328118112899)
              ·
                refine ⟨367757187743322492177169349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245171458495548328118112899 367757187743322492177169349)
                ·
                  refine ⟨68954472701872967283219253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367757187743322492177169349 68954472701872967283219253)
                  ·
                    refine ⟨6464481815800590682801805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68954472701872967283219253 6464481815800590682801805)
                    ·
                      refine ⟨2424180680925221506050677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6464481815800590682801805 2424180680925221506050677)
                      ·
                        rfl

theorem cell23_4721075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_4721075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721075 prefixEnd_4721075 := by exact prefixLift 4721075
  have htrace : WordTrace (prefixWord ++ tailWord_4721075) baseStart_4721075 baseEnd_4721075 := by
    simpa [prefixWord, tailWord_4721075, baseEnd_4721075] using wordTrace_append hprefix tailTrace_4721075
  have hstable : (prefixWord ++ tailWord_4721075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721075).length < 2 ^ (prefixWord ++ tailWord_4721075).sum := by decide
  have hdescent : baseEnd_4721075 < baseStart_4721075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721149 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_4721149 : Nat := 118140960795 + 4721149 * 2 ^ 59
def prefixEnd_4721149 : Nat := 4983230072969 + 3 ^ 40 * 4721149 * 2
def baseEnd_4721149 : Nat := 2424218678493654216525337

theorem tailTrace_4721149 : CollatzResearch.WordTrace tailWord_4721149 prefixEnd_4721149 2424218678493654216525337 := by
  unfold tailWord_4721149
  simp only [CollatzResearch.WordTrace]
  refine ⟨172194450373090955900846501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114796300248727303933897667 172194450373090955900846501)
  ·
    refine ⟨32286459444954554231408719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172194450373090955900846501 32286459444954554231408719)
    ·
      refine ⟨48429689167431831347113079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32286459444954554231408719 48429689167431831347113079)
      ·
        refine ⟨72644533751147747020669619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48429689167431831347113079 72644533751147747020669619)
        ·
          refine ⟨108966800626721620531004429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72644533751147747020669619 108966800626721620531004429)
          ·
            refine ⟨40862550235020607699126661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108966800626721620531004429 40862550235020607699126661)
            ·
              refine ⟨7661728169066363943586249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40862550235020607699126661 7661728169066363943586249)
              ·
                refine ⟨5746296126799772957689687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7661728169066363943586249 5746296126799772957689687)
                ·
                  refine ⟨8619444190199659436534531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746296126799772957689687 8619444190199659436534531)
                  ·
                    refine ⟨12929166285299489154801797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8619444190199659436534531 12929166285299489154801797)
                    ·
                      refine ⟨2424218678493654216525337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12929166285299489154801797 2424218678493654216525337)
                      ·
                        rfl

theorem cell23_4721149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_4721149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721149 prefixEnd_4721149 := by exact prefixLift 4721149
  have htrace : WordTrace (prefixWord ++ tailWord_4721149) baseStart_4721149 baseEnd_4721149 := by
    simpa [prefixWord, tailWord_4721149, baseEnd_4721149] using wordTrace_append hprefix tailTrace_4721149
  have hstable : (prefixWord ++ tailWord_4721149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721149).length < 2 ^ (prefixWord ++ tailWord_4721149).sum := by decide
  have hdescent : baseEnd_4721149 < baseStart_4721149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721155 : List Nat := [1, 1, 1, 3, 2, 1, 5, 9]
def baseStart_4721155 : Nat := 118140960795 + 4721155 * 2 ^ 59
def prefixEnd_4721155 : Nat := 4983230072969 + 3 ^ 40 * 4721155 * 2
def baseEnd_4721155 : Nat := 89785991088058562705567

theorem tailTrace_4721155 : CollatzResearch.WordTrace tailWord_4721155 prefixEnd_4721155 89785991088058562705567 := by
  unfold tailWord_4721155
  simp only [CollatzResearch.WordTrace]
  refine ⟨172194669211069218925564919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114796446140712812617043279 172194669211069218925564919)
  ·
    refine ⟨258292003816603828388347379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172194669211069218925564919 258292003816603828388347379)
    ·
      refine ⟨387438005724905742582521069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258292003816603828388347379 387438005724905742582521069)
      ·
        refine ⟨145289252146839653468445401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 387438005724905742582521069 145289252146839653468445401)
        ·
          refine ⟨108966939110129740101334051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145289252146839653468445401 108966939110129740101334051)
          ·
            refine ⟨163450408665194610152001077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108966939110129740101334051 163450408665194610152001077)
            ·
              refine ⟨15323475812361994701750101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163450408665194610152001077 15323475812361994701750101)
              ·
                refine ⟨89785991088058562705567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15323475812361994701750101 89785991088058562705567)
                ·
                  rfl

theorem cell23_4721155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 9].length) (baseStart_4721155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721155 prefixEnd_4721155 := by exact prefixLift 4721155
  have htrace : WordTrace (prefixWord ++ tailWord_4721155) baseStart_4721155 baseEnd_4721155 := by
    simpa [prefixWord, tailWord_4721155, baseEnd_4721155] using wordTrace_append hprefix tailTrace_4721155
  have hstable : (prefixWord ++ tailWord_4721155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721155).length < 2 ^ (prefixWord ++ tailWord_4721155).sum := by decide
  have hdescent : baseEnd_4721155 < baseStart_4721155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721162 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4721162 : Nat := 118140960795 + 4721162 * 2 ^ 59
def prefixEnd_4721162 : Nat := 4983230072969 + 3 ^ 40 * 4721162 * 2
def baseEnd_4721162 : Nat := 2424225353742162665662777

theorem tailTrace_4721162 : CollatzResearch.WordTrace tailWord_4721162 prefixEnd_4721162 2424225353742162665662777 := by
  unfold tailWord_4721162
  simp only [CollatzResearch.WordTrace]
  refine ⟨43048731130510964780267435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114796616348029239414046493 43048731130510964780267435)
  ·
    refine ⟨64573096695766447170401153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43048731130510964780267435 64573096695766447170401153)
    ·
      refine ⟨48429822521824835377800865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64573096695766447170401153 48429822521824835377800865)
      ·
        refine ⟨36322366891368626533350649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48429822521824835377800865 36322366891368626533350649)
        ·
          refine ⟨27241775168526469900012987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36322366891368626533350649 27241775168526469900012987)
          ·
            refine ⟨40862662752789704850019481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27241775168526469900012987 40862662752789704850019481)
            ·
              refine ⟨30646997064592278637514611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40862662752789704850019481 30646997064592278637514611)
              ·
                refine ⟨45970495596888417956271917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30646997064592278637514611 45970495596888417956271917)
                ·
                  refine ⟨17238935848833156733601969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45970495596888417956271917 17238935848833156733601969)
                  ·
                    refine ⟨12929201886624867550201477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17238935848833156733601969 12929201886624867550201477)
                    ·
                      refine ⟨2424225353742162665662777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12929201886624867550201477 2424225353742162665662777)
                      ·
                        rfl

theorem cell23_4721162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4721162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721162 prefixEnd_4721162 := by exact prefixLift 4721162
  have htrace : WordTrace (prefixWord ++ tailWord_4721162) baseStart_4721162 baseEnd_4721162 := by
    simpa [prefixWord, tailWord_4721162, baseEnd_4721162] using wordTrace_append hprefix tailTrace_4721162
  have hstable : (prefixWord ++ tailWord_4721162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721162).length < 2 ^ (prefixWord ++ tailWord_4721162).sum := by decide
  have hdescent : baseEnd_4721162 < baseStart_4721162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721197 : List Nat := [1, 5, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_4721197 : Nat := 118140960795 + 4721197 * 2 ^ 59
def prefixEnd_4721197 : Nat := 4983230072969 + 3 ^ 40 * 4721197 * 2
def baseEnd_4721197 : Nat := 808081108521690009575039

theorem tailTrace_4721197 : CollatzResearch.WordTrace tailWord_4721197 prefixEnd_4721197 808081108521690009575039 := by
  unfold tailWord_4721197
  simp only [CollatzResearch.WordTrace]
  refine ⟨172196201076917060098593845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114797467384611373399062563 172196201076917060098593845)
  ·
    refine ⟨16143393850960974384243173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172196201076917060098593845 16143393850960974384243173)
    ·
      refine ⟨3026886347055182697045595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16143393850960974384243173 3026886347055182697045595)
      ·
        refine ⟨4540329520582774045568393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026886347055182697045595 4540329520582774045568393)
        ·
          refine ⟨3405247140437080534176295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4540329520582774045568393 3405247140437080534176295)
          ·
            refine ⟨5107870710655620801264443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405247140437080534176295 5107870710655620801264443)
            ·
              refine ⟨7661806065983431201896665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107870710655620801264443 7661806065983431201896665)
              ·
                refine ⟨5746354549487573401422499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7661806065983431201896665 5746354549487573401422499)
                ·
                  refine ⟨8619531824231360102133749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746354549487573401422499 8619531824231360102133749)
                  ·
                    refine ⟨808081108521690009575039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8619531824231360102133749 808081108521690009575039)
                    ·
                      rfl

theorem cell23_4721197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_4721197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721197 prefixEnd_4721197 := by exact prefixLift 4721197
  have htrace : WordTrace (prefixWord ++ tailWord_4721197) baseStart_4721197 baseEnd_4721197 := by
    simpa [prefixWord, tailWord_4721197, baseEnd_4721197] using wordTrace_append hprefix tailTrace_4721197
  have hstable : (prefixWord ++ tailWord_4721197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721197).length < 2 ^ (prefixWord ++ tailWord_4721197).sum := by decide
  have hdescent : baseEnd_4721197 < baseStart_4721197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721220 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4721220 : Nat := 118140960795 + 4721220 * 2 ^ 59
def prefixEnd_4721220 : Nat := 4983230072969 + 3 ^ 40 * 4721220 * 2
def baseEnd_4721220 : Nat := 2424255135620123438737511

theorem tailTrace_4721220 : CollatzResearch.WordTrace tailWord_4721220 prefixEnd_4721220 2424255135620123438737511 := by
  unfold tailWord_4721220
  simp only [CollatzResearch.WordTrace]
  refine ⟨86098519977916867513340557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114798026637222490017787409 86098519977916867513340557)
  ·
    refine ⟨32286944991718825317502709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86098519977916867513340557 32286944991718825317502709)
    ·
      refine ⟨3026901092973639873515879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32286944991718825317502709 3026901092973639873515879)
      ·
        refine ⟨4540351639460459810273819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026901092973639873515879 4540351639460459810273819)
        ·
          refine ⟨6810527459190689715410729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540351639460459810273819 6810527459190689715410729)
          ·
            refine ⟨5107895594393017286558047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6810527459190689715410729 5107895594393017286558047)
            ·
              refine ⟨7661843391589525929837071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107895594393017286558047 7661843391589525929837071)
              ·
                refine ⟨11492765087384288894755607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7661843391589525929837071 11492765087384288894755607)
                ·
                  refine ⟨17239147631076433342133411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11492765087384288894755607 17239147631076433342133411)
                  ·
                    refine ⟨25858721446614650013200117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17239147631076433342133411 25858721446614650013200117)
                    ·
                      refine ⟨2424255135620123438737511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25858721446614650013200117 2424255135620123438737511)
                      ·
                        rfl

theorem cell23_4721220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4721220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721220 prefixEnd_4721220 := by exact prefixLift 4721220
  have htrace : WordTrace (prefixWord ++ tailWord_4721220) baseStart_4721220 baseEnd_4721220 := by
    simpa [prefixWord, tailWord_4721220, baseEnd_4721220] using wordTrace_append hprefix tailTrace_4721220
  have hstable : (prefixWord ++ tailWord_4721220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721220).length < 2 ^ (prefixWord ++ tailWord_4721220).sum := by decide
  have hdescent : baseEnd_4721220 < baseStart_4721220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721239 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 3, 4, 2]
def baseStart_4721239 : Nat := 118140960795 + 4721239 * 2 ^ 59
def prefixEnd_4721239 : Nat := 4983230072969 + 3 ^ 40 * 4721239 * 2
def baseEnd_4721239 : Nat := 2424264891752558864399923

theorem tailTrace_4721239 : CollatzResearch.WordTrace tailWord_4721239 prefixEnd_4721239 2424264891752558864399923 := by
  unfold tailWord_4721239
  simp only [CollatzResearch.WordTrace]
  refine ⟨172197732942764901271622771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114798488628509934181081847 172197732942764901271622771)
  ·
    refine ⟨258296599414147351907434157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172197732942764901271622771 258296599414147351907434157)
    ·
      refine ⟨96861224780305256965287809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258296599414147351907434157 96861224780305256965287809)
      ·
        refine ⟨72645918585228942723965857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96861224780305256965287809 72645918585228942723965857)
        ·
          refine ⟨54484438938921707042974393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72645918585228942723965857 54484438938921707042974393)
          ·
            refine ⟨40863329204191280282230795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54484438938921707042974393 40863329204191280282230795)
            ·
              refine ⟨61294993806286920423346193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40863329204191280282230795 61294993806286920423346193)
              ·
                refine ⟨45971245354715190317509645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61294993806286920423346193 45971245354715190317509645)
                ·
                  refine ⟨17239217008018196369066117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45971245354715190317509645 17239217008018196369066117)
                  ·
                    refine ⟨3232353189003411819199897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17239217008018196369066117 3232353189003411819199897)
                    ·
                      refine ⟨2424264891752558864399923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232353189003411819199897 2424264891752558864399923)
                      ·
                        rfl

theorem cell23_4721239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_4721239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721239 prefixEnd_4721239 := by exact prefixLift 4721239
  have htrace : WordTrace (prefixWord ++ tailWord_4721239) baseStart_4721239 baseEnd_4721239 := by
    simpa [prefixWord, tailWord_4721239, baseEnd_4721239] using wordTrace_append hprefix tailTrace_4721239
  have hstable : (prefixWord ++ tailWord_4721239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721239).length < 2 ^ (prefixWord ++ tailWord_4721239).sum := by decide
  have hdescent : baseEnd_4721239 < baseStart_4721239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721277 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_4721277 : Nat := 118140960795 + 4721277 * 2 ^ 59
def prefixEnd_4721277 : Nat := 4983230072969 + 3 ^ 40 * 4721277 * 2
def baseEnd_4721277 : Nat := 2424284404017429715724749

theorem tailTrace_4721277 : CollatzResearch.WordTrace tailWord_4721277 prefixEnd_4721277 2424284404017429715724749 := by
  unfold tailWord_4721277
  simp only [CollatzResearch.WordTrace]
  refine ⟨172199118916627233761506085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114799412611084822507670723 172199118916627233761506085)
  ·
    refine ⟨32287334796867606330282391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172199118916627233761506085 32287334796867606330282391)
    ·
      refine ⟨48431002195301409495423587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32287334796867606330282391 48431002195301409495423587)
      ·
        refine ⟨72646503292952114243135381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48431002195301409495423587 72646503292952114243135381)
        ·
          refine ⟨3405304841857130355146971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72646503292952114243135381 3405304841857130355146971)
          ·
            refine ⟨5107957262785695532720457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405304841857130355146971 5107957262785695532720457)
            ·
              refine ⟨3830967947089271649540343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5107957262785695532720457 3830967947089271649540343)
              ·
                refine ⟨5746451920633907474310515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830967947089271649540343 5746451920633907474310515)
                ·
                  refine ⟨8619677880950861211465773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746451920633907474310515 8619677880950861211465773)
                  ·
                    refine ⟨3232379205356572954299665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8619677880950861211465773 3232379205356572954299665)
                    ·
                      refine ⟨2424284404017429715724749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232379205356572954299665 2424284404017429715724749)
                      ·
                        rfl

theorem cell23_4721277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_4721277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721277 prefixEnd_4721277 := by exact prefixLift 4721277
  have htrace : WordTrace (prefixWord ++ tailWord_4721277) baseStart_4721277 baseEnd_4721277 := by
    simpa [prefixWord, tailWord_4721277, baseEnd_4721277] using wordTrace_append hprefix tailTrace_4721277
  have hstable : (prefixWord ++ tailWord_4721277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721277).length < 2 ^ (prefixWord ++ tailWord_4721277).sum := by decide
  have hdescent : baseEnd_4721277 < baseStart_4721277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721326 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4721326 : Nat := 118140960795 + 4721326 * 2 ^ 59
def prefixEnd_4721326 : Nat := 4983230072969 + 3 ^ 40 * 4721326 * 2
def baseEnd_4721326 : Nat := 808103188189833341337341

theorem tailTrace_4721326 : CollatzResearch.WordTrace tailWord_4721326 prefixEnd_4721326 808103188189833341337341 := by
  unfold tailWord_4721326
  simp only [CollatzResearch.WordTrace]
  refine ⟨21525113261681214391254979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114800604062299810086693221 21525113261681214391254979)
  ·
    refine ⟨32287669892521821586882469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21525113261681214391254979 32287669892521821586882469)
    ·
      refine ⟨6053938104847841547540463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32287669892521821586882469 6053938104847841547540463)
      ·
        refine ⟨9080907157271762321310695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6053938104847841547540463 9080907157271762321310695)
        ·
          refine ⟨13621360735907643481966043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9080907157271762321310695 13621360735907643481966043)
          ·
            refine ⟨20432041103861465222949065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13621360735907643481966043 20432041103861465222949065)
            ·
              refine ⟨15324030827896098917211799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20432041103861465222949065 15324030827896098917211799)
              ·
                refine ⟨22986046241844148375817699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15324030827896098917211799 22986046241844148375817699)
                ·
                  refine ⟨34479069362766222563726549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22986046241844148375817699 34479069362766222563726549)
                  ·
                    refine ⟨808103188189833341337341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34479069362766222563726549 808103188189833341337341)
                    ·
                      rfl

theorem cell23_4721326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4721326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721326 prefixEnd_4721326 := by exact prefixLift 4721326
  have htrace : WordTrace (prefixWord ++ tailWord_4721326) baseStart_4721326 baseEnd_4721326 := by
    simpa [prefixWord, tailWord_4721326, baseEnd_4721326] using wordTrace_append hprefix tailTrace_4721326
  have hstable : (prefixWord ++ tailWord_4721326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721326).length < 2 ^ (prefixWord ++ tailWord_4721326).sum := by decide
  have hdescent : baseEnd_4721326 < baseStart_4721326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721369 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 6]
def baseStart_4721369 : Nat := 118140960795 + 4721369 * 2 ^ 59
def prefixEnd_4721369 : Nat := 4983230072969 + 3 ^ 40 * 4721369 * 2
def baseEnd_4721369 : Nat := 269370182693071483974925

theorem tailTrace_4721369 : CollatzResearch.WordTrace tailWord_4721369 prefixEnd_4721369 269370182693071483974925 := by
  unfold tailWord_4721369
  simp only [CollatzResearch.WordTrace]
  refine ⟨172202474432293933473855161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114801649621529288982570107 172202474432293933473855161)
  ·
    refine ⟨129151855824220450105391371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172202474432293933473855161 129151855824220450105391371)
    ·
      refine ⟨193727783736330675158087057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129151855824220450105391371 193727783736330675158087057)
      ·
        refine ⟨145295837802248006368565293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193727783736330675158087057 145295837802248006368565293)
        ·
          refine ⟨54485939175843002388211985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145295837802248006368565293 54485939175843002388211985)
          ·
            refine ⟨40864454381882251791158989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54485939175843002388211985 40864454381882251791158989)
            ·
              refine ⟨15324170393205844421684621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40864454381882251791158989 15324170393205844421684621)
              ·
                refine ⟨5746563897452191658131733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15324170393205844421684621 5746563897452191658131733)
                ·
                  refine ⟨269370182693071483974925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5746563897452191658131733 269370182693071483974925)
                  ·
                    rfl

theorem cell23_4721369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 6].length) (baseStart_4721369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721369 prefixEnd_4721369 := by exact prefixLift 4721369
  have htrace : WordTrace (prefixWord ++ tailWord_4721369) baseStart_4721369 baseEnd_4721369 := by
    simpa [prefixWord, tailWord_4721369, baseEnd_4721369] using wordTrace_append hprefix tailTrace_4721369
  have hstable : (prefixWord ++ tailWord_4721369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721369).length < 2 ^ (prefixWord ++ tailWord_4721369).sum := by decide
  have hdescent : baseEnd_4721369 < baseStart_4721369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721436 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4721436 : Nat := 118140960795 + 4721436 * 2 ^ 59
def prefixEnd_4721436 : Nat := 4983230072969 + 3 ^ 40 * 4721436 * 2
def baseEnd_4721436 : Nat := 2424366047441494593636517

theorem tailTrace_4721436 : CollatzResearch.WordTrace tailWord_4721436 prefixEnd_4721436 2424366047441494593636517 := by
  unfold tailWord_4721436
  simp only [CollatzResearch.WordTrace]
  refine ⟨86102459061525601958272081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114803278748700802611029441 86102459061525601958272081)
  ·
    refine ⟨64576844296144201468704061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86102459061525601958272081 64576844296144201468704061)
    ·
      refine ⟨24216316611054075550764023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64576844296144201468704061 24216316611054075550764023)
      ·
        refine ⟨36324474916581113326146035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24216316611054075550764023 36324474916581113326146035)
        ·
          refine ⟨54486712374871669989219053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36324474916581113326146035 54486712374871669989219053)
          ·
            refine ⟨20432517140576876245957145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54486712374871669989219053 20432517140576876245957145)
            ·
              refine ⟨15324387855432657184467859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20432517140576876245957145 15324387855432657184467859)
              ·
                refine ⟨22986581783148985776701789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15324387855432657184467859 22986581783148985776701789)
                ·
                  refine ⟨8619968168680869666263171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22986581783148985776701789 8619968168680869666263171)
                  ·
                    refine ⟨12929952253021304499394757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8619968168680869666263171 12929952253021304499394757)
                    ·
                      refine ⟨2424366047441494593636517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12929952253021304499394757 2424366047441494593636517)
                      ·
                        rfl

theorem cell23_4721436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4721436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721436 prefixEnd_4721436 := by exact prefixLift 4721436
  have htrace : WordTrace (prefixWord ++ tailWord_4721436) baseStart_4721436 baseEnd_4721436 := by
    simpa [prefixWord, tailWord_4721436, baseEnd_4721436] using wordTrace_append hprefix tailTrace_4721436
  have hstable : (prefixWord ++ tailWord_4721436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721436).length < 2 ^ (prefixWord ++ tailWord_4721436).sum := by decide
  have hdescent : baseEnd_4721436 < baseStart_4721436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721440 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 2, 3, 2]
def baseStart_4721440 : Nat := 118140960795 + 4721440 * 2 ^ 59
def prefixEnd_4721440 : Nat := 4983230072969 + 3 ^ 40 * 4721440 * 2
def baseEnd_4721440 : Nat := 2424368101364112577986499

theorem tailTrace_4721440 : CollatzResearch.WordTrace tailWord_4721440 prefixEnd_4721440 2424368101364112577986499 := by
  unfold tailWord_4721440
  simp only [CollatzResearch.WordTrace]
  refine ⟨86102532007518356299844887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114803376010024475066459849 86102532007518356299844887)
  ·
    refine ⟨129153798011277534449767331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86102532007518356299844887 129153798011277534449767331)
    ·
      refine ⟨193730697016916301674650997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129153798011277534449767331 193730697016916301674650997)
      ·
        refine ⟨18162252845335903281998531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193730697016916301674650997 18162252845335903281998531)
        ·
          refine ⟨27243379268003854922997797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18162252845335903281998531 27243379268003854922997797)
          ·
            refine ⟨5108133612750722798062087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27243379268003854922997797 5108133612750722798062087)
            ·
              refine ⟨7662200419126084197093131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5108133612750722798062087 7662200419126084197093131)
              ·
                refine ⟨11493300628689126295639697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7662200419126084197093131 11493300628689126295639697)
                ·
                  refine ⟨8619975471516844721729773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11493300628689126295639697 8619975471516844721729773)
                  ·
                    refine ⟨3232490801818816770648665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8619975471516844721729773 3232490801818816770648665)
                    ·
                      refine ⟨2424368101364112577986499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232490801818816770648665 2424368101364112577986499)
                      ·
                        rfl

theorem cell23_4721440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_4721440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721440 prefixEnd_4721440 := by exact prefixLift 4721440
  have htrace : WordTrace (prefixWord ++ tailWord_4721440) baseStart_4721440 baseEnd_4721440 := by
    simpa [prefixWord, tailWord_4721440, baseEnd_4721440] using wordTrace_append hprefix tailTrace_4721440
  have hstable : (prefixWord ++ tailWord_4721440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721440).length < 2 ^ (prefixWord ++ tailWord_4721440).sum := by decide
  have hdescent : baseEnd_4721440 < baseStart_4721440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721450 : List Nat := [3, 1, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_4721450 : Nat := 118140960795 + 4721450 * 2 ^ 59
def prefixEnd_4721450 : Nat := 4983230072969 + 3 ^ 40 * 4721450 * 2
def baseEnd_4721450 : Nat := 808124412056885846287151

theorem tailTrace_4721450 : CollatzResearch.WordTrace tailWord_4721450 prefixEnd_4721450 808124412056885846287151 := by
  unfold tailWord_4721450
  simp only [CollatzResearch.WordTrace]
  refine ⟨43051357186250121076888451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114803619163333656205035869 43051357186250121076888451)
  ·
    refine ⟨64577035779375181615332677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43051357186250121076888451 64577035779375181615332677)
    ·
      refine ⟨12108194208632846552874877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64577035779375181615332677 12108194208632846552874877)
      ·
        refine ⟨4540572828237317457328079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12108194208632846552874877 4540572828237317457328079)
        ·
          refine ⟨6810859242355976185992119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540572828237317457328079 6810859242355976185992119)
          ·
            refine ⟨10216288863533964278988179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6810859242355976185992119 10216288863533964278988179)
            ·
              refine ⟨15324433295300946418482269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10216288863533964278988179 15324433295300946418482269)
              ·
                refine ⟨5746662485737854906930851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15324433295300946418482269 5746662485737854906930851)
                ·
                  refine ⟨8619993728606782360396277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746662485737854906930851 8619993728606782360396277)
                  ·
                    refine ⟨808124412056885846287151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8619993728606782360396277 808124412056885846287151)
                    ·
                      rfl

theorem cell23_4721450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_4721450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721450 prefixEnd_4721450 := by exact prefixLift 4721450
  have htrace : WordTrace (prefixWord ++ tailWord_4721450) baseStart_4721450 baseEnd_4721450 := by
    simpa [prefixWord, tailWord_4721450, baseEnd_4721450] using wordTrace_append hprefix tailTrace_4721450
  have hstable : (prefixWord ++ tailWord_4721450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721450).length < 2 ^ (prefixWord ++ tailWord_4721450).sum := by decide
  have hdescent : baseEnd_4721450 < baseStart_4721450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721459 : List Nat := [1, 1, 1, 2, 6, 2, 10]
def baseStart_4721459 : Nat := 118140960795 + 4721459 * 2 ^ 59
def prefixEnd_4721459 : Nat := 4983230072969 + 3 ^ 40 * 4721459 * 2
def baseEnd_4721459 : Nat := 29930590833290716094431

theorem tailTrace_4721459 : CollatzResearch.WordTrace tailWord_4721459 prefixEnd_4721459 29930590833290716094431 := by
  unfold tailWord_4721459
  simp only [CollatzResearch.WordTrace]
  refine ⟨172205757001967878844631431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114803838001311919229754287 172205757001967878844631431)
  ·
    refine ⟨258308635502951818266947147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172205757001967878844631431 258308635502951818266947147)
    ·
      refine ⟨387462953254427727400420721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258308635502951818266947147 387462953254427727400420721)
      ·
        refine ⟨290597214940820795550315541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387462953254427727400420721 290597214940820795550315541)
        ·
          refine ⟨13621744450350974791421041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 290597214940820795550315541 13621744450350974791421041)
          ·
            refine ⟨10216308337763231093565781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13621744450350974791421041 10216308337763231093565781)
            ·
              refine ⟨29930590833290716094431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10216308337763231093565781 29930590833290716094431)
              ·
                rfl

theorem cell23_4721459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 10].length) (baseStart_4721459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721459 prefixEnd_4721459 := by exact prefixLift 4721459
  have htrace : WordTrace (prefixWord ++ tailWord_4721459) baseStart_4721459 baseEnd_4721459 := by
    simpa [prefixWord, tailWord_4721459, baseEnd_4721459] using wordTrace_append hprefix tailTrace_4721459
  have hstable : (prefixWord ++ tailWord_4721459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721459).length < 2 ^ (prefixWord ++ tailWord_4721459).sum := by decide
  have hdescent : baseEnd_4721459 < baseStart_4721459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721496 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 2, 7, 2]
def baseStart_4721496 : Nat := 118140960795 + 4721496 * 2 ^ 59
def prefixEnd_4721496 : Nat := 4983230072969 + 3 ^ 40 * 4721496 * 2
def baseEnd_4721496 : Nat := 2424396856280764358886241

theorem tailTrace_4721496 : CollatzResearch.WordTrace tailWord_4721496 prefixEnd_4721496 2424396856280764358886241 := by
  unfold tailWord_4721496
  simp only [CollatzResearch.WordTrace]
  refine ⟨86103553251416917081864171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114804737668555889442485561 86103553251416917081864171)
  ·
    refine ⟨129155329877125375622796257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86103553251416917081864171 129155329877125375622796257)
    ·
      refine ⟨96866497407844031717097193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129155329877125375622796257 96866497407844031717097193)
      ·
        refine ⟨72649873055883023787822895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96866497407844031717097193 72649873055883023787822895)
        ·
          refine ⟨108974809583824535681734343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72649873055883023787822895 108974809583824535681734343)
          ·
            refine ⟨163462214375736803522601515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108974809583824535681734343 163462214375736803522601515)
            ·
              refine ⟨245193321563605205283902273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163462214375736803522601515 245193321563605205283902273)
              ·
                refine ⟨183894991172703903962926705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245193321563605205283902273 183894991172703903962926705)
                ·
                  refine ⟨137921243379527927972195029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183894991172703903962926705 137921243379527927972195029)
                  ·
                    refine ⟨3232529141707685811848321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 137921243379527927972195029 3232529141707685811848321)
                    ·
                      refine ⟨2424396856280764358886241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232529141707685811848321 2424396856280764358886241)
                      ·
                        rfl

theorem cell23_4721496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_4721496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721496 prefixEnd_4721496 := by exact prefixLift 4721496
  have htrace : WordTrace (prefixWord ++ tailWord_4721496) baseStart_4721496 baseEnd_4721496 := by
    simpa [prefixWord, tailWord_4721496, baseEnd_4721496] using wordTrace_append hprefix tailTrace_4721496
  have hstable : (prefixWord ++ tailWord_4721496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721496).length < 2 ^ (prefixWord ++ tailWord_4721496).sum := by decide
  have hdescent : baseEnd_4721496 < baseStart_4721496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721519 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 4, 6]
def baseStart_4721519 : Nat := 118140960795 + 4721519 * 2 ^ 59
def prefixEnd_4721519 : Nat := 4983230072969 + 3 ^ 40 * 4721519 * 2
def baseEnd_4721519 : Nat := 808136222111939256299545

theorem tailTrace_4721519 : CollatzResearch.WordTrace tailWord_4721519 prefixEnd_4721519 808136222111939256299545 := by
  unfold tailWord_4721519
  simp only [CollatzResearch.WordTrace]
  refine ⟨172207945381750509091815611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114805296921167006061210407 172207945381750509091815611)
  ·
    refine ⟨258311918072625763637723417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172207945381750509091815611 258311918072625763637723417)
    ·
      refine ⟨193733938554469322728292563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258311918072625763637723417 193733938554469322728292563)
      ·
        refine ⟨290600907831703984092438845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193733938554469322728292563 290600907831703984092438845)
        ·
          refine ⟨108975340436888994034664567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290600907831703984092438845 108975340436888994034664567)
          ·
            refine ⟨163463010655333491051996851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108975340436888994034664567 163463010655333491051996851)
            ·
              refine ⟨245194515983000236577995277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163463010655333491051996851 245194515983000236577995277)
              ·
                refine ⟨91947943493625088716748229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245194515983000236577995277 91947943493625088716748229)
                ·
                  refine ⟨17240239405054704134390293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91947943493625088716748229 17240239405054704134390293)
                  ·
                    refine ⟨808136222111939256299545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17240239405054704134390293 808136222111939256299545)
                    ·
                      rfl

theorem cell23_4721519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_4721519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721519 prefixEnd_4721519 := by exact prefixLift 4721519
  have htrace : WordTrace (prefixWord ++ tailWord_4721519) baseStart_4721519 baseEnd_4721519 := by
    simpa [prefixWord, tailWord_4721519, baseEnd_4721519] using wordTrace_append hprefix tailTrace_4721519
  have hstable : (prefixWord ++ tailWord_4721519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721519).length < 2 ^ (prefixWord ++ tailWord_4721519).sum := by decide
  have hdescent : baseEnd_4721519 < baseStart_4721519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721564 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4721564 : Nat := 118140960795 + 4721564 * 2 ^ 59
def prefixEnd_4721564 : Nat := 4983230072969 + 3 ^ 40 * 4721564 * 2
def baseEnd_4721564 : Nat := 2424431772965270092835929

theorem tailTrace_4721564 : CollatzResearch.WordTrace tailWord_4721564 prefixEnd_4721564 2424431772965270092835929 := by
  unfold tailWord_4721564
  simp only [CollatzResearch.WordTrace]
  refine ⟨86104793333293740888601873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114806391111058321184802497 86104793333293740888601873)
  ·
    refine ⟨64578594999970305666451405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86104793333293740888601873 64578594999970305666451405)
    ·
      refine ⟨24216973124988864624919277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64578594999970305666451405 24216973124988864624919277)
      ·
        refine ⟨9081364921870824234344729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24216973124988864624919277 9081364921870824234344729)
        ·
          refine ⟨6811023691403118175758547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9081364921870824234344729 6811023691403118175758547)
          ·
            refine ⟨10216535537104677263637821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811023691403118175758547 10216535537104677263637821)
            ·
              refine ⟨3831200826414253973864183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10216535537104677263637821 3831200826414253973864183)
              ·
                refine ⟨5746801239621380960796275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3831200826414253973864183 5746801239621380960796275)
                ·
                  refine ⟨8620201859432071441194413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746801239621380960796275 8620201859432071441194413)
                  ·
                    refine ⟨3232575697287026790447905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8620201859432071441194413 3232575697287026790447905)
                    ·
                      refine ⟨2424431772965270092835929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232575697287026790447905 2424431772965270092835929)
                      ·
                        rfl

theorem cell23_4721564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4721564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721564 prefixEnd_4721564 := by exact prefixLift 4721564
  have htrace : WordTrace (prefixWord ++ tailWord_4721564) baseStart_4721564 baseEnd_4721564 := by
    simpa [prefixWord, tailWord_4721564, baseEnd_4721564] using wordTrace_append hprefix tailTrace_4721564
  have hstable : (prefixWord ++ tailWord_4721564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721564).length < 2 ^ (prefixWord ++ tailWord_4721564).sum := by decide
  have hdescent : baseEnd_4721564 < baseStart_4721564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721593 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 3]
def baseStart_4721593 : Nat := 118140960795 + 4721593 * 2 ^ 59
def prefixEnd_4721593 : Nat := 4983230072969 + 3 ^ 40 * 4721593 * 2
def baseEnd_4721593 : Nat := 2424446663904250479373295

theorem tailTrace_4721593 : CollatzResearch.WordTrace tailWord_4721593 prefixEnd_4721593 2424446663904250479373295 := by
  unfold tailWord_4721593
  simp only [CollatzResearch.WordTrace]
  refine ⟨172210644383482419730009433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114807096255654946486672955 172210644383482419730009433)
  ·
    refine ⟨129157983287611814797507075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172210644383482419730009433 129157983287611814797507075)
    ·
      refine ⟨193736974931417722196260613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129157983287611814797507075 193736974931417722196260613)
      ·
        refine ⟨36325682799640822911798865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193736974931417722196260613 36325682799640822911798865)
        ·
          refine ⟨27244262099730617183849149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36325682799640822911798865 27244262099730617183849149)
          ·
            refine ⟨10216598287398981443943431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27244262099730617183849149 10216598287398981443943431)
            ·
              refine ⟨15324897431098472165915147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10216598287398981443943431 15324897431098472165915147)
              ·
                refine ⟨22987346146647708248872721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15324897431098472165915147 22987346146647708248872721)
                ·
                  refine ⟨17240509609985781186654541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22987346146647708248872721 17240509609985781186654541)
                  ·
                    refine ⟨6465191103744667944995453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17240509609985781186654541 6465191103744667944995453)
                    ·
                      refine ⟨2424446663904250479373295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6465191103744667944995453 2424446663904250479373295)
                      ·
                        rfl

theorem cell23_4721593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_4721593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721593 prefixEnd_4721593 := by exact prefixLift 4721593
  have htrace : WordTrace (prefixWord ++ tailWord_4721593) baseStart_4721593 baseEnd_4721593 := by
    simpa [prefixWord, tailWord_4721593, baseEnd_4721593] using wordTrace_append hprefix tailTrace_4721593
  have hstable : (prefixWord ++ tailWord_4721593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721593).length < 2 ^ (prefixWord ++ tailWord_4721593).sum := by decide
  have hdescent : baseEnd_4721593 < baseStart_4721593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721720 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 1, 5]
def baseStart_4721720 : Nat := 118140960795 + 4721720 * 2 ^ 59
def prefixEnd_4721720 : Nat := 4983230072969 + 3 ^ 40 * 4721720 * 2
def baseEnd_4721720 : Nat := 808170625315790494161737

theorem tailTrace_4721720 : CollatzResearch.WordTrace tailWord_4721720 prefixEnd_4721720 808170625315790494161737 := by
  unfold tailWord_4721720
  simp only [CollatzResearch.WordTrace]
  refine ⟨86107638227011160209941307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114810184302681546946588409 86107638227011160209941307)
  ·
    refine ⟨129161457340516740314911961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86107638227011160209941307 129161457340516740314911961)
    ·
      refine ⟨96871093005387555236183971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129161457340516740314911961 96871093005387555236183971)
      ·
        refine ⟨145306639508081332854275957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96871093005387555236183971 145306639508081332854275957)
        ·
          refine ⟨13622497453882624955088371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145306639508081332854275957 13622497453882624955088371)
          ·
            refine ⟨20433746180823937432632557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13622497453882624955088371 20433746180823937432632557)
            ·
              refine ⟨7662654817808976537237209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20433746180823937432632557 7662654817808976537237209)
              ·
                refine ⟨5746991113356732402927907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7662654817808976537237209 5746991113356732402927907)
                ·
                  refine ⟨8620486670035098604391861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746991113356732402927907 8620486670035098604391861)
                  ·
                    refine ⟨808170625315790494161737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8620486670035098604391861 808170625315790494161737)
                    ·
                      rfl

theorem cell23_4721720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_4721720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721720 prefixEnd_4721720 := by exact prefixLift 4721720
  have htrace : WordTrace (prefixWord ++ tailWord_4721720) baseStart_4721720 baseEnd_4721720 := by
    simpa [prefixWord, tailWord_4721720, baseEnd_4721720] using wordTrace_append hprefix tailTrace_4721720
  have hstable : (prefixWord ++ tailWord_4721720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721720).length < 2 ^ (prefixWord ++ tailWord_4721720).sum := by decide
  have hdescent : baseEnd_4721720 < baseStart_4721720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721733 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_4721733 : Nat := 118140960795 + 4721733 * 2 ^ 59
def prefixEnd_4721733 : Nat := 4983230072969 + 3 ^ 40 * 4721733 * 2
def baseEnd_4721733 : Nat := 808172850398626643874217

theorem tailTrace_4721733 : CollatzResearch.WordTrace tailWord_4721733 prefixEnd_4721733 808172850398626643874217 := by
  unfold tailWord_4721733
  simp only [CollatzResearch.WordTrace]
  refine ⟨172215750602975223640105853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114810500401983482426737235 172215750602975223640105853)
  ·
    refine ⟨64580906476115708865039695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172215750602975223640105853 64580906476115708865039695)
    ·
      refine ⟨96871359714173563297559543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64580906476115708865039695 96871359714173563297559543)
      ·
        refine ⟨145307039571260344946339315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96871359714173563297559543 145307039571260344946339315)
        ·
          refine ⟨217960559356890517419508973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145307039571260344946339315 217960559356890517419508973)
          ·
            refine ⟨81735209758833944032315865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217960559356890517419508973 81735209758833944032315865)
            ·
              refine ⟨61301407319125458024236899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81735209758833944032315865 61301407319125458024236899)
              ·
                refine ⟨91952110978688187036355349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61301407319125458024236899 91952110978688187036355349)
                ·
                  refine ⟨4310255202126008767329157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91952110978688187036355349 4310255202126008767329157)
                  ·
                    refine ⟨808172850398626643874217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4310255202126008767329157 808172850398626643874217)
                    ·
                      rfl

theorem cell23_4721733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_4721733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721733 prefixEnd_4721733 := by exact prefixLift 4721733
  have htrace : WordTrace (prefixWord ++ tailWord_4721733) baseStart_4721733 baseEnd_4721733 := by
    simpa [prefixWord, tailWord_4721733, baseEnd_4721733] using wordTrace_append hprefix tailTrace_4721733
  have hstable : (prefixWord ++ tailWord_4721733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721733).length < 2 ^ (prefixWord ++ tailWord_4721733).sum := by decide
  have hdescent : baseEnd_4721733 < baseStart_4721733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721743 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 3]
def baseStart_4721743 : Nat := 118140960795 + 4721743 * 2 ^ 59
def prefixEnd_4721743 : Nat := 4983230072969 + 3 ^ 40 * 4721743 * 2
def baseEnd_4721743 : Nat := 2424523686002424892497605

theorem tailTrace_4721743 : CollatzResearch.WordTrace tailWord_4721743 prefixEnd_4721743 2424523686002424892497605 := by
  unfold tailWord_4721743
  simp only [CollatzResearch.WordTrace]
  refine ⟨172216115332938995347969883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114810743555292663565313255 172216115332938995347969883)
  ·
    refine ⟨258324172999408493021954825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172216115332938995347969883 258324172999408493021954825)
    ·
      refine ⟨193743129749556369766466119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258324172999408493021954825 193743129749556369766466119)
      ·
        refine ⟨290614694624334554649699179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193743129749556369766466119 290614694624334554649699179)
        ·
          refine ⟨435922041936501831974548769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290614694624334554649699179 435922041936501831974548769)
          ·
            refine ⟨326941531452376373980911577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435922041936501831974548769 326941531452376373980911577)
            ·
              refine ⟨245206148589282280485683683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326941531452376373980911577 245206148589282280485683683)
              ·
                refine ⟨367809222883923420728525525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245206148589282280485683683 367809222883923420728525525)
                ·
                  refine ⟨8620528661341955173324817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 367809222883923420728525525 8620528661341955173324817)
                  ·
                    refine ⟨6465396496006466379993613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8620528661341955173324817 6465396496006466379993613)
                    ·
                      refine ⟨2424523686002424892497605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6465396496006466379993613 2424523686002424892497605)
                      ·
                        rfl

theorem cell23_4721743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_4721743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721743 prefixEnd_4721743 := by exact prefixLift 4721743
  have htrace : WordTrace (prefixWord ++ tailWord_4721743) baseStart_4721743 baseEnd_4721743 := by
    simpa [prefixWord, tailWord_4721743, baseEnd_4721743] using wordTrace_append hprefix tailTrace_4721743
  have hstable : (prefixWord ++ tailWord_4721743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721743).length < 2 ^ (prefixWord ++ tailWord_4721743).sum := by decide
  have hdescent : baseEnd_4721743 < baseStart_4721743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721770 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4721770 : Nat := 118140960795 + 4721770 * 2 ^ 59
def prefixEnd_4721770 : Nat := 4983230072969 + 3 ^ 40 * 4721770 * 2
def baseEnd_4721770 : Nat := 2424537549980096286859981

theorem tailTrace_4721770 : CollatzResearch.WordTrace tailWord_4721770 prefixEnd_4721770 2424537549980096286859981 := by
  unfold tailWord_4721770
  simp only [CollatzResearch.WordTrace]
  refine ⟨43054275025960294739800691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114811400069227452639468509 43054275025960294739800691)
  ·
    refine ⟨64581412538940442109701037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43054275025960294739800691 64581412538940442109701037)
    ·
      refine ⟨24218029702102665791137889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64581412538940442109701037 24218029702102665791137889)
      ·
        refine ⟨18163522276576999343353417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24218029702102665791137889 18163522276576999343353417)
        ·
          refine ⟨13622641707432749507515063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18163522276576999343353417 13622641707432749507515063)
          ·
            refine ⟨20433962561149124261272595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13622641707432749507515063 20433962561149124261272595)
            ·
              refine ⟨30650943841723686391908893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20433962561149124261272595 30650943841723686391908893)
              ·
                refine ⟨11494103940646382396965835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30650943841723686391908893 11494103940646382396965835)
                ·
                  refine ⟨17241155910969573595448753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11494103940646382396965835 17241155910969573595448753)
                  ·
                    refine ⟨12930866933227180196586565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17241155910969573595448753 12930866933227180196586565)
                    ·
                      refine ⟨2424537549980096286859981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12930866933227180196586565 2424537549980096286859981)
                      ·
                        rfl

theorem cell23_4721770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4721770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721770 prefixEnd_4721770 := by exact prefixLift 4721770
  have htrace : WordTrace (prefixWord ++ tailWord_4721770) baseStart_4721770 baseEnd_4721770 := by
    simpa [prefixWord, tailWord_4721770, baseEnd_4721770] using wordTrace_append hprefix tailTrace_4721770
  have hstable : (prefixWord ++ tailWord_4721770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721770).length < 2 ^ (prefixWord ++ tailWord_4721770).sum := by decide
  have hdescent : baseEnd_4721770 < baseStart_4721770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721774 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_4721774 : Nat := 118140960795 + 4721774 * 2 ^ 59
def prefixEnd_4721774 : Nat := 4983230072969 + 3 ^ 40 * 4721774 * 2
def baseEnd_4721774 : Nat := 2424539603902714271209963

theorem tailTrace_4721774 : CollatzResearch.WordTrace tailWord_4721774 prefixEnd_4721774 2424539603902714271209963 := by
  unfold tailWord_4721774
  simp only [CollatzResearch.WordTrace]
  refine ⟨21527155749478335955293547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114811497330551125094898917 21527155749478335955293547)
  ·
    refine ⟨32290733624217503932940321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21527155749478335955293547 32290733624217503932940321)
    ·
      refine ⟨24218050218163127949705241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32290733624217503932940321 24218050218163127949705241)
      ·
        refine ⟨18163537663622345962278931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24218050218163127949705241 18163537663622345962278931)
        ·
          refine ⟨27245306495433518943418397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18163537663622345962278931 27245306495433518943418397)
          ·
            refine ⟨10216989935787569603781899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27245306495433518943418397 10216989935787569603781899)
            ·
              refine ⟨15325484903681354405672849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10216989935787569603781899 15325484903681354405672849)
              ·
                refine ⟨11494113677761015804254637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15325484903681354405672849 11494113677761015804254637)
                ·
                  refine ⟨4310292629160380926595489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11494113677761015804254637 4310292629160380926595489)
                  ·
                    refine ⟨3232719471870285694946617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4310292629160380926595489 3232719471870285694946617)
                    ·
                      refine ⟨2424539603902714271209963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232719471870285694946617 2424539603902714271209963)
                      ·
                        rfl

theorem cell23_4721774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_4721774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721774 prefixEnd_4721774 := by exact prefixLift 4721774
  have htrace : WordTrace (prefixWord ++ tailWord_4721774) baseStart_4721774 baseEnd_4721774 := by
    simpa [prefixWord, tailWord_4721774, baseEnd_4721774] using wordTrace_append hprefix tailTrace_4721774
  have hstable : (prefixWord ++ tailWord_4721774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721774).length < 2 ^ (prefixWord ++ tailWord_4721774).sum := by decide
  have hdescent : baseEnd_4721774 < baseStart_4721774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721813 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_4721813 : Nat := 118140960795 + 4721813 * 2 ^ 59
def prefixEnd_4721813 : Nat := 4983230072969 + 3 ^ 40 * 4721813 * 2
def baseEnd_4721813 : Nat := 2424559629648239618622283

theorem tailTrace_4721813 : CollatzResearch.WordTrace tailWord_4721813 prefixEnd_4721813 2424559629648239618622283 := by
  unfold tailWord_4721813
  simp only [CollatzResearch.WordTrace]
  refine ⟨172218668442685397303018093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114812445628456931535345395 172218668442685397303018093)
  ·
    refine ⟨64582000666007023988631785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172218668442685397303018093 64582000666007023988631785)
    ·
      refine ⟨48436500499505267991473839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64582000666007023988631785 48436500499505267991473839)
      ·
        refine ⟨72654750749257901987210759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48436500499505267991473839 72654750749257901987210759)
        ·
          refine ⟨108982126123886852980816139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72654750749257901987210759 108982126123886852980816139)
          ·
            refine ⟨163473189185830279471224209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108982126123886852980816139 163473189185830279471224209)
            ·
              refine ⟨122604891889372709603418157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163473189185830279471224209 122604891889372709603418157)
              ·
                refine ⟨45976834458514766101281809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122604891889372709603418157 45976834458514766101281809)
                ·
                  refine ⟨34482625843886074575961357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45976834458514766101281809 34482625843886074575961357)
                  ·
                    refine ⟨12930984691457277965985509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34482625843886074575961357 12930984691457277965985509)
                    ·
                      refine ⟨2424559629648239618622283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12930984691457277965985509 2424559629648239618622283)
                      ·
                        rfl

theorem cell23_4721813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_4721813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721813 prefixEnd_4721813 := by exact prefixLift 4721813
  have htrace : WordTrace (prefixWord ++ tailWord_4721813) baseStart_4721813 baseEnd_4721813 := by
    simpa [prefixWord, tailWord_4721813, baseEnd_4721813] using wordTrace_append hprefix tailTrace_4721813
  have hstable : (prefixWord ++ tailWord_4721813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721813).length < 2 ^ (prefixWord ++ tailWord_4721813).sum := by decide
  have hdescent : baseEnd_4721813 < baseStart_4721813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721824 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 2, 1, 3]
def baseStart_4721824 : Nat := 118140960795 + 4721824 * 2 ^ 59
def prefixEnd_4721824 : Nat := 4983230072969 + 3 ^ 40 * 4721824 * 2
def baseEnd_4721824 : Nat := 2424565277935439075584733

theorem tailTrace_4721824 : CollatzResearch.WordTrace tailWord_4721824 prefixEnd_4721824 2424565277935439075584733 := by
  unfold tailWord_4721824
  simp only [CollatzResearch.WordTrace]
  refine ⟨86109534822822773090834263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114812713097097030787779017 86109534822822773090834263)
  ·
    refine ⟨129164302234234159636251395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86109534822822773090834263 129164302234234159636251395)
    ·
      refine ⟨193746453351351239454377093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129164302234234159636251395 193746453351351239454377093)
      ·
        refine ⟨36327460003378357397695705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193746453351351239454377093 36327460003378357397695705)
        ·
          refine ⟨27245595002533768048271779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36327460003378357397695705 27245595002533768048271779)
          ·
            refine ⟨40868392503800652072407669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27245595002533768048271779 40868392503800652072407669)
            ·
              refine ⟨3831411797231311131788219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40868392503800652072407669 3831411797231311131788219)
              ·
                refine ⟨5747117695846966697682329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3831411797231311131788219 5747117695846966697682329)
                ·
                  refine ⟨4310338271885225023261747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5747117695846966697682329 4310338271885225023261747)
                  ·
                    refine ⟨6465507407827837534892621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4310338271885225023261747 6465507407827837534892621)
                    ·
                      refine ⟨2424565277935439075584733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6465507407827837534892621 2424565277935439075584733)
                      ·
                        rfl

theorem cell23_4721824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_4721824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721824 prefixEnd_4721824 := by exact prefixLift 4721824
  have htrace : WordTrace (prefixWord ++ tailWord_4721824) baseStart_4721824 baseEnd_4721824 := by
    simpa [prefixWord, tailWord_4721824, baseEnd_4721824] using wordTrace_append hprefix tailTrace_4721824
  have hstable : (prefixWord ++ tailWord_4721824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721824).length < 2 ^ (prefixWord ++ tailWord_4721824).sum := by decide
  have hdescent : baseEnd_4721824 < baseStart_4721824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721843 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 4]
def baseStart_4721843 : Nat := 118140960795 + 4721843 * 2 ^ 59
def prefixEnd_4721843 : Nat := 4983230072969 + 3 ^ 40 * 4721843 * 2
def baseEnd_4721843 : Nat := 2424575034067874501247145

theorem tailTrace_4721843 : CollatzResearch.WordTrace tailWord_4721843 prefixEnd_4721843 2424575034067874501247145 := by
  unfold tailWord_4721843
  simp only [CollatzResearch.WordTrace]
  refine ⟨172219762632576712426610183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114813175088384474951073455 172219762632576712426610183)
  ·
    refine ⟨258329643948865068639915275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172219762632576712426610183 258329643948865068639915275)
    ·
      refine ⟨387494465923297602959872913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258329643948865068639915275 387494465923297602959872913)
      ·
        refine ⟨290620849442473202219904685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387494465923297602959872913 290620849442473202219904685)
        ·
          refine ⟨108982818540927450832464257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290620849442473202219904685 108982818540927450832464257)
          ·
            refine ⟨81737113905695588124348193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108982818540927450832464257 81737113905695588124348193)
            ·
              refine ⟨61302835429271691093261145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81737113905695588124348193 61302835429271691093261145)
              ·
                refine ⟨45977126571953768319945859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61302835429271691093261145 45977126571953768319945859)
                ·
                  refine ⟨68965689857930652479918789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45977126571953768319945859 68965689857930652479918789)
                  ·
                    refine ⟨12931066848361997339984773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68965689857930652479918789 12931066848361997339984773)
                    ·
                      refine ⟨2424575034067874501247145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12931066848361997339984773 2424575034067874501247145)
                      ·
                        rfl

theorem cell23_4721843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_4721843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721843 prefixEnd_4721843 := by exact prefixLift 4721843
  have htrace : WordTrace (prefixWord ++ tailWord_4721843) baseStart_4721843 baseEnd_4721843 := by
    simpa [prefixWord, tailWord_4721843, baseEnd_4721843] using wordTrace_append hprefix tailTrace_4721843
  have hstable : (prefixWord ++ tailWord_4721843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721843).length < 2 ^ (prefixWord ++ tailWord_4721843).sum := by decide
  have hdescent : baseEnd_4721843 < baseStart_4721843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721847 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 6, 2, 2]
def baseStart_4721847 : Nat := 118140960795 + 4721847 * 2 ^ 59
def prefixEnd_4721847 : Nat := 4983230072969 + 3 ^ 40 * 4721847 * 2
def baseEnd_4721847 : Nat := 2424577087990492485597127

theorem tailTrace_4721847 : CollatzResearch.WordTrace tailWord_4721847 prefixEnd_4721847 2424577087990492485597127 := by
  unfold tailWord_4721847
  simp only [CollatzResearch.WordTrace]
  refine ⟨172219908524562221109755795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114813272349708147406503863 172219908524562221109755795)
  ·
    refine ⟨258329862786843331664633693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172219908524562221109755795 258329862786843331664633693)
    ·
      refine ⟨96873698545066249374237635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258329862786843331664633693 96873698545066249374237635)
      ·
        refine ⟨145310547817599374061356453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96873698545066249374237635 145310547817599374061356453)
        ·
          refine ⟨27245727715799882636504335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145310547817599374061356453 27245727715799882636504335)
          ·
            refine ⟨40868591573699823954756503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27245727715799882636504335 40868591573699823954756503)
            ·
              refine ⟨61302887360549735932134755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40868591573699823954756503 61302887360549735932134755)
              ·
                refine ⟨91954331040824603898202133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61302887360549735932134755 91954331040824603898202133)
                ·
                  refine ⟨4310359267538653307728225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91954331040824603898202133 4310359267538653307728225)
                  ·
                    refine ⟨3232769450653989980796169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4310359267538653307728225 3232769450653989980796169)
                    ·
                      refine ⟨2424577087990492485597127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232769450653989980796169 2424577087990492485597127)
                      ·
                        rfl

theorem cell23_4721847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_4721847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721847 prefixEnd_4721847 := by exact prefixLift 4721847
  have htrace : WordTrace (prefixWord ++ tailWord_4721847) baseStart_4721847 baseEnd_4721847 := by
    simpa [prefixWord, tailWord_4721847, baseEnd_4721847] using wordTrace_append hprefix tailTrace_4721847
  have hstable : (prefixWord ++ tailWord_4721847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721847).length < 2 ^ (prefixWord ++ tailWord_4721847).sum := by decide
  have hdescent : baseEnd_4721847 < baseStart_4721847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721853 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 9]
def baseStart_4721853 : Nat := 118140960795 + 4721853 * 2 ^ 59
def prefixEnd_4721853 : Nat := 4983230072969 + 3 ^ 40 * 4721853 * 2
def baseEnd_4721853 : Nat := 269397796541602162458011

theorem tailTrace_4721853 : CollatzResearch.WordTrace tailWord_4721853 prefixEnd_4721853 269397796541602162458011 := by
  unfold tailWord_4721853
  simp only [CollatzResearch.WordTrace]
  refine ⟨172220127362540484134474213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114813418241693656089649475 172220127362540484134474213)
  ·
    refine ⟨32291273880476340775213915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172220127362540484134474213 32291273880476340775213915)
    ·
      refine ⟨48436910820714511162820873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32291273880476340775213915 48436910820714511162820873)
      ·
        refine ⟨36327683115535883372115655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48436910820714511162820873 36327683115535883372115655)
        ·
          refine ⟨54491524673303825058173483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36327683115535883372115655 54491524673303825058173483)
          ·
            refine ⟨81737287009955737587260225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54491524673303825058173483 81737287009955737587260225)
            ·
              refine ⟨61302965257466803190445169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81737287009955737587260225 61302965257466803190445169)
              ·
                refine ⟨45977223943100102392833877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61302965257466803190445169 45977223943100102392833877)
                ·
                  refine ⟨269397796541602162458011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45977223943100102392833877 269397796541602162458011)
                  ·
                    rfl

theorem cell23_4721853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_4721853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721853 prefixEnd_4721853 := by exact prefixLift 4721853
  have htrace : WordTrace (prefixWord ++ tailWord_4721853) baseStart_4721853 baseEnd_4721853 := by
    simpa [prefixWord, tailWord_4721853, baseEnd_4721853] using wordTrace_append hprefix tailTrace_4721853
  have hstable : (prefixWord ++ tailWord_4721853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721853).length < 2 ^ (prefixWord ++ tailWord_4721853).sum := by decide
  have hdescent : baseEnd_4721853 < baseStart_4721853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721900 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_4721900 : Nat := 118140960795 + 4721900 * 2 ^ 59
def prefixEnd_4721900 : Nat := 4983230072969 + 3 ^ 40 * 4721900 * 2
def baseEnd_4721900 : Nat := 808201434155060259411461

theorem tailTrace_4721900 : CollatzResearch.WordTrace tailWord_4721900 prefixEnd_4721900 808201434155060259411461 := by
  unfold tailWord_4721900
  simp only [CollatzResearch.WordTrace]
  refine ⟨86110920796685105580717577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114814561062246807440956769 86110920796685105580717577)
  ·
    refine ⟨64583190597513829185538183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86110920796685105580717577 64583190597513829185538183)
    ·
      refine ⟨96874785896270743778307275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64583190597513829185538183 96874785896270743778307275)
      ·
        refine ⟨145312178844406115667460913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96874785896270743778307275 145312178844406115667460913)
        ·
          refine ⟨108984134133304586750595685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145312178844406115667460913 108984134133304586750595685)
          ·
            refine ⟨20434525149994610015736691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108984134133304586750595685 20434525149994610015736691)
            ·
              refine ⟨30651787724991915023605037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20434525149994610015736691 30651787724991915023605037)
              ·
                refine ⟨11494420396871968133851889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30651787724991915023605037 11494420396871968133851889)
                ·
                  refine ⟨8620815297653976100388917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11494420396871968133851889 8620815297653976100388917)
                  ·
                    refine ⟨808201434155060259411461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8620815297653976100388917 808201434155060259411461)
                    ·
                      rfl

theorem cell23_4721900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_4721900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721900 prefixEnd_4721900 := by exact prefixLift 4721900
  have htrace : WordTrace (prefixWord ++ tailWord_4721900) baseStart_4721900 baseEnd_4721900 := by
    simpa [prefixWord, tailWord_4721900, baseEnd_4721900] using wordTrace_append hprefix tailTrace_4721900
  have hstable : (prefixWord ++ tailWord_4721900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721900).length < 2 ^ (prefixWord ++ tailWord_4721900).sum := by decide
  have hdescent : baseEnd_4721900 < baseStart_4721900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721937 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 2, 4, 2]
def baseStart_4721937 : Nat := 118140960795 + 4721937 * 2 ^ 59
def prefixEnd_4721937 : Nat := 4983230072969 + 3 ^ 40 * 4721937 * 2
def baseEnd_4721937 : Nat := 2424623301249397133471713

theorem tailTrace_4721937 : CollatzResearch.WordTrace tailWord_4721937 prefixEnd_4721937 2424623301249397133471713 := by
  unfold tailWord_4721937
  simp only [CollatzResearch.WordTrace]
  refine ⟨172223191094236166480532065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114815460729490777653688043 172223191094236166480532065)
  ·
    refine ⟨129167393320677124860399049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172223191094236166480532065 129167393320677124860399049)
    ·
      refine ⟨96875544990507843645299287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129167393320677124860399049 96875544990507843645299287)
      ·
        refine ⟨145313317485761765467948931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96875544990507843645299287 145313317485761765467948931)
        ·
          refine ⟨217969976228642648201923397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145313317485761765467948931 217969976228642648201923397)
          ·
            refine ⟨40869370542870496537860637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217969976228642648201923397 40869370542870496537860637)
            ·
              refine ⟨15326013953576436201697739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40869370542870496537860637 15326013953576436201697739)
              ·
                refine ⟨22989020930364654302546609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15326013953576436201697739 22989020930364654302546609)
                ·
                  refine ⟨17241765697773490726909957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22989020930364654302546609 17241765697773490726909957)
                  ·
                    refine ⟨3232831068332529511295617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17241765697773490726909957 3232831068332529511295617)
                    ·
                      refine ⟨2424623301249397133471713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232831068332529511295617 2424623301249397133471713)
                      ·
                        rfl

theorem cell23_4721937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_4721937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721937 prefixEnd_4721937 := by exact prefixLift 4721937
  have htrace : WordTrace (prefixWord ++ tailWord_4721937) baseStart_4721937 baseEnd_4721937 := by
    simpa [prefixWord, tailWord_4721937, baseEnd_4721937] using wordTrace_append hprefix tailTrace_4721937
  have hstable : (prefixWord ++ tailWord_4721937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721937).length < 2 ^ (prefixWord ++ tailWord_4721937).sum := by decide
  have hdescent : baseEnd_4721937 < baseStart_4721937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721957 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_4721957 : Nat := 118140960795 + 4721957 * 2 ^ 59
def prefixEnd_4721957 : Nat := 4983230072969 + 3 ^ 40 * 4721957 * 2
def baseEnd_4721957 : Nat := 2424633570862487055221621

theorem tailTrace_4721957 : CollatzResearch.WordTrace tailWord_4721957 prefixEnd_4721957 2424633570862487055221621 := by
  unfold tailWord_4721957
  simp only [CollatzResearch.WordTrace]
  refine ⟨172223920554163709896260125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114815947036109139930840083 172223920554163709896260125)
  ·
    refine ⟨64583970207811391211097547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172223920554163709896260125 64583970207811391211097547)
    ·
      refine ⟨96875955311717086816646321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64583970207811391211097547 96875955311717086816646321)
      ·
        refine ⟨72656966483787815112484741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96875955311717086816646321 72656966483787815112484741)
        ·
          refine ⟨13623181215710215333590889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72656966483787815112484741 13623181215710215333590889)
          ·
            refine ⟨10217385911782661500193167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13623181215710215333590889 10217385911782661500193167)
            ·
              refine ⟨15326078867673992250289751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10217385911782661500193167 15326078867673992250289751)
              ·
                refine ⟨22989118301510988375434627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15326078867673992250289751 22989118301510988375434627)
                ·
                  refine ⟨34483677452266482563151941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22989118301510988375434627 34483677452266482563151941)
                  ·
                    refine ⟨6465689522299965480590989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34483677452266482563151941 6465689522299965480590989)
                    ·
                      refine ⟨2424633570862487055221621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6465689522299965480590989 2424633570862487055221621)
                      ·
                        rfl

theorem cell23_4721957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_4721957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721957 prefixEnd_4721957 := by exact prefixLift 4721957
  have htrace : WordTrace (prefixWord ++ tailWord_4721957) baseStart_4721957 baseEnd_4721957 := by
    simpa [prefixWord, tailWord_4721957, baseEnd_4721957] using wordTrace_append hprefix tailTrace_4721957
  have hstable : (prefixWord ++ tailWord_4721957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721957).length < 2 ^ (prefixWord ++ tailWord_4721957).sum := by decide
  have hdescent : baseEnd_4721957 < baseStart_4721957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721977 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 8]
def baseStart_4721977 : Nat := 118140960795 + 4721977 * 2 ^ 59
def prefixEnd_4721977 : Nat := 4983230072969 + 3 ^ 40 * 4721977 * 2
def baseEnd_4721977 : Nat := 269404871163952997441281

theorem tailTrace_4721977 : CollatzResearch.WordTrace tailWord_4721977 prefixEnd_4721977 269404871163952997441281 := by
  unfold tailWord_4721977
  simp only [CollatzResearch.WordTrace]
  refine ⟨172224650014091253311988185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114816433342727502207992123 172224650014091253311988185)
  ·
    refine ⟨129168487510568439983991139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172224650014091253311988185 129168487510568439983991139)
    ·
      refine ⟨193752731265852659975986709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129168487510568439983991139 193752731265852659975986709)
      ·
        refine ⟨9082159278086843436374377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193752731265852659975986709 9082159278086843436374377)
        ·
          refine ⟨6811619458565132577280783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9082159278086843436374377 6811619458565132577280783)
          ·
            refine ⟨10217429187847698865921175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811619458565132577280783 10217429187847698865921175)
            ·
              refine ⟨15326143781771548298881763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10217429187847698865921175 15326143781771548298881763)
              ·
                refine ⟨22989215672657322448322645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15326143781771548298881763 22989215672657322448322645)
                ·
                  refine ⟨269404871163952997441281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22989215672657322448322645 269404871163952997441281)
                  ·
                    rfl

theorem cell23_4721977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 8].length) (baseStart_4721977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721977 prefixEnd_4721977 := by exact prefixLift 4721977
  have htrace : WordTrace (prefixWord ++ tailWord_4721977) baseStart_4721977 baseEnd_4721977 := by
    simpa [prefixWord, tailWord_4721977, baseEnd_4721977] using wordTrace_append hprefix tailTrace_4721977
  have hstable : (prefixWord ++ tailWord_4721977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721977).length < 2 ^ (prefixWord ++ tailWord_4721977).sum := by decide
  have hdescent : baseEnd_4721977 < baseStart_4721977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721980 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_4721980 : Nat := 118140960795 + 4721980 * 2 ^ 59
def prefixEnd_4721980 : Nat := 4983230072969 + 3 ^ 40 * 4721980 * 2
def baseEnd_4721980 : Nat := 2424645380917540465234015

theorem tailTrace_4721980 : CollatzResearch.WordTrace tailWord_4721980 prefixEnd_4721980 2424645380917540465234015 := by
  unfold tailWord_4721980
  simp only [CollatzResearch.WordTrace]
  refine ⟨86112379716540192412173697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114816506288720256549564929 86112379716540192412173697)
  ·
    refine ⟨64584284787405144309130273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86112379716540192412173697 64584284787405144309130273)
    ·
      refine ⟨48438213590553858231847705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64584284787405144309130273 48438213590553858231847705)
      ·
        refine ⟨36328660192915393673885779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48438213590553858231847705 36328660192915393673885779)
        ·
          refine ⟨54492990289373090510828669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36328660192915393673885779 54492990289373090510828669)
          ·
            refine ⟨20434871358514908941560751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54492990289373090510828669 20434871358514908941560751)
            ·
              refine ⟨30652307037772363412341127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20434871358514908941560751 30652307037772363412341127)
              ·
                refine ⟨45978460556658545118511691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30652307037772363412341127 45978460556658545118511691)
                ·
                  refine ⟨68967690834987817677767537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45978460556658545118511691 68967690834987817677767537)
                  ·
                    refine ⟨51725768126240863258325653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68967690834987817677767537 51725768126240863258325653)
                    ·
                      refine ⟨2424645380917540465234015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51725768126240863258325653 2424645380917540465234015)
                      ·
                        rfl

theorem cell23_4721980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_4721980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721980 prefixEnd_4721980 := by exact prefixLift 4721980
  have htrace : WordTrace (prefixWord ++ tailWord_4721980) baseStart_4721980 baseEnd_4721980 := by
    simpa [prefixWord, tailWord_4721980, baseEnd_4721980] using wordTrace_append hprefix tailTrace_4721980
  have hstable : (prefixWord ++ tailWord_4721980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721980).length < 2 ^ (prefixWord ++ tailWord_4721980).sum := by decide
  have hdescent : baseEnd_4721980 < baseStart_4721980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4721981 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_4721981 : Nat := 118140960795 + 4721981 * 2 ^ 59
def prefixEnd_4721981 : Nat := 4983230072969 + 3 ^ 40 * 4721981 * 2
def baseEnd_4721981 : Nat := 808215298132731653773837

theorem tailTrace_4721981 : CollatzResearch.WordTrace tailWord_4721981 prefixEnd_4721981 808215298132731653773837 := by
  unfold tailWord_4721981
  simp only [CollatzResearch.WordTrace]
  refine ⟨172224795906076761995133797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114816530604051174663422531 172224795906076761995133797)
  ·
    refine ⟨32292149232389392874087587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172224795906076761995133797 32292149232389392874087587)
    ·
      refine ⟨48438223848584089311131381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32292149232389392874087587 48438223848584089311131381)
      ·
        refine ⟨4541083485804758372918567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48438223848584089311131381 4541083485804758372918567)
        ·
          refine ⟨6811625228707137559377851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4541083485804758372918567 6811625228707137559377851)
          ·
            refine ⟨10217437843060706339066777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811625228707137559377851 10217437843060706339066777)
            ·
              refine ⟨7663078382295529754300083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10217437843060706339066777 7663078382295529754300083)
              ·
                refine ⟨11494617573443294631450125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7663078382295529754300083 11494617573443294631450125)
                ·
                  refine ⟨4310481590041235486793797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11494617573443294631450125 4310481590041235486793797)
                  ·
                    refine ⟨808215298132731653773837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4310481590041235486793797 808215298132731653773837)
                    ·
                      rfl

theorem cell23_4721981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_4721981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4721981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4721981 prefixEnd_4721981 := by exact prefixLift 4721981
  have htrace : WordTrace (prefixWord ++ tailWord_4721981) baseStart_4721981 baseEnd_4721981 := by
    simpa [prefixWord, tailWord_4721981, baseEnd_4721981] using wordTrace_append hprefix tailTrace_4721981
  have hstable : (prefixWord ++ tailWord_4721981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4721981).length < 2 ^ (prefixWord ++ tailWord_4721981).sum := by decide
  have hdescent : baseEnd_4721981 < baseStart_4721981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4721981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722004 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_4722004 : Nat := 118140960795 + 4722004 * 2 ^ 59
def prefixEnd_4722004 : Nat := 4983230072969 + 3 ^ 40 * 4722004 * 2
def baseEnd_4722004 : Nat := 2424657704453248371333905

theorem tailTrace_4722004 : CollatzResearch.WordTrace tailWord_4722004 prefixEnd_4722004 2424657704453248371333905 := by
  unfold tailWord_4722004
  simp only [CollatzResearch.WordTrace]
  refine ⟨86112817392496718461610533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114817089856662291282147377 86112817392496718461610533)
  ·
    refine ⟨16146153261093134711551975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86112817392496718461610533 16146153261093134711551975)
    ·
      refine ⟨24219229891639702067327963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16146153261093134711551975 24219229891639702067327963)
      ·
        refine ⟨36328844837459553100991945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24219229891639702067327963 36328844837459553100991945)
        ·
          refine ⟨27246633628094664825743959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36328844837459553100991945 27246633628094664825743959)
          ·
            refine ⟨40869950442141997238615939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27246633628094664825743959 40869950442141997238615939)
            ·
              refine ⟨61304925663212995857923909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40869950442141997238615939 61304925663212995857923909)
              ·
                refine ⟨11494673561852436723360733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61304925663212995857923909 11494673561852436723360733)
                ·
                  refine ⟨4310502585694663771260275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11494673561852436723360733 4310502585694663771260275)
                  ·
                    refine ⟨6465753878541995656890413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4310502585694663771260275 6465753878541995656890413)
                    ·
                      refine ⟨2424657704453248371333905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6465753878541995656890413 2424657704453248371333905)
                      ·
                        rfl

theorem cell23_4722004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_4722004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722004 prefixEnd_4722004 := by exact prefixLift 4722004
  have htrace : WordTrace (prefixWord ++ tailWord_4722004) baseStart_4722004 baseEnd_4722004 := by
    simpa [prefixWord, tailWord_4722004, baseEnd_4722004] using wordTrace_append hprefix tailTrace_4722004
  have hstable : (prefixWord ++ tailWord_4722004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722004).length < 2 ^ (prefixWord ++ tailWord_4722004).sum := by decide
  have hdescent : baseEnd_4722004 < baseStart_4722004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722007 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 1, 5]
def baseStart_4722007 : Nat := 118140960795 + 4722007 * 2 ^ 59
def prefixEnd_4722007 : Nat := 4983230072969 + 3 ^ 40 * 4722007 * 2
def baseEnd_4722007 : Nat := 808219748298403953198797

theorem tailTrace_4722007 : CollatzResearch.WordTrace tailWord_4722007 prefixEnd_4722007 808219748298403953198797 := by
  unfold tailWord_4722007
  simp only [CollatzResearch.WordTrace]
  refine ⟨172225744203982568435580275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114817162802655045623720183 172225744203982568435580275)
  ·
    refine ⟨258338616305973852653370413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172225744203982568435580275 258338616305973852653370413)
    ·
      refine ⟨96876981114740194745013905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258338616305973852653370413 96876981114740194745013905)
      ·
        refine ⟨72657735836055146058760429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96876981114740194745013905 72657735836055146058760429)
        ·
          refine ⟨27246650938520679772035161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72657735836055146058760429 27246650938520679772035161)
          ·
            refine ⟨20434988203890509829026371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27246650938520679772035161 20434988203890509829026371)
            ·
              refine ⟨30652482305835764743539557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20434988203890509829026371 30652482305835764743539557)
              ·
                refine ⟨5747340432344205889413667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30652482305835764743539557 5747340432344205889413667)
                ·
                  refine ⟨8621010648516308834120501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5747340432344205889413667 8621010648516308834120501)
                  ·
                    refine ⟨808219748298403953198797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8621010648516308834120501 808219748298403953198797)
                    ·
                      rfl

theorem cell23_4722007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_4722007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722007 prefixEnd_4722007 := by exact prefixLift 4722007
  have htrace : WordTrace (prefixWord ++ tailWord_4722007) baseStart_4722007 baseEnd_4722007 := by
    simpa [prefixWord, tailWord_4722007, baseEnd_4722007] using wordTrace_append hprefix tailTrace_4722007
  have hstable : (prefixWord ++ tailWord_4722007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722007).length < 2 ^ (prefixWord ++ tailWord_4722007).sum := by decide
  have hdescent : baseEnd_4722007 < baseStart_4722007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722088 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4722088 : Nat := 118140960795 + 4722088 * 2 ^ 59
def prefixEnd_4722088 : Nat := 4983230072969 + 3 ^ 40 * 4722088 * 2
def baseEnd_4722088 : Nat := 808233612276075347561173

theorem tailTrace_4722088 : CollatzResearch.WordTrace tailWord_4722088 prefixEnd_4722088 808233612276075347561173 := by
  unfold tailWord_4722088
  simp only [CollatzResearch.WordTrace]
  refine ⟨86114349258344559634639459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114819132344459412846185945 86114349258344559634639459)
  ·
    refine ⟨129171523887516839451959189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86114349258344559634639459 129171523887516839451959189)
    ·
      refine ⟨6054915182227351849310587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129171523887516839451959189 6054915182227351849310587)
      ·
        refine ⟨9082372773341027773965881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6054915182227351849310587 9082372773341027773965881)
        ·
          refine ⟨6811779580005770830474411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9082372773341027773965881 6811779580005770830474411)
          ·
            refine ⟨10217669370008656245711617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811779580005770830474411 10217669370008656245711617)
            ·
              refine ⟨7663252027506492184283713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10217669370008656245711617 7663252027506492184283713)
              ·
                refine ⟨5747439020629869138212785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7663252027506492184283713 5747439020629869138212785)
                ·
                  refine ⟨4310579265472401853659589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5747439020629869138212785 4310579265472401853659589)
                  ·
                    refine ⟨808233612276075347561173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4310579265472401853659589 808233612276075347561173)
                    ·
                      rfl

theorem cell23_4722088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4722088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722088 prefixEnd_4722088 := by exact prefixLift 4722088
  have htrace : WordTrace (prefixWord ++ tailWord_4722088) baseStart_4722088 baseEnd_4722088 := by
    simpa [prefixWord, tailWord_4722088, baseEnd_4722088] using wordTrace_append hprefix tailTrace_4722088
  have hstable : (prefixWord ++ tailWord_4722088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722088).length < 2 ^ (prefixWord ++ tailWord_4722088).sum := by decide
  have hdescent : baseEnd_4722088 < baseStart_4722088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722104 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 3, 3, 2]
def baseStart_4722104 : Nat := 118140960795 + 4722104 * 2 ^ 59
def prefixEnd_4722104 : Nat := 4983230072969 + 3 ^ 40 * 4722104 * 2
def baseEnd_4722104 : Nat := 2424709052518697980083445

theorem tailTrace_4722104 : CollatzResearch.WordTrace tailWord_4722104 prefixEnd_4722104 2424709052518697980083445 := by
  unfold tailWord_4722104
  simp only [CollatzResearch.WordTrace]
  refine ⟨86114641042315577000930683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114819521389754102667907577 86114641042315577000930683)
  ·
    refine ⟨129171961563473365501396025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86114641042315577000930683 129171961563473365501396025)
    ·
      refine ⟨96878971172605024126047019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129171961563473365501396025 96878971172605024126047019)
      ·
        refine ⟨145318456758907536189070529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96878971172605024126047019 145318456758907536189070529)
        ·
          refine ⟨108988842569180652141802897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145318456758907536189070529 108988842569180652141802897)
          ·
            refine ⟨81741631926885489106352173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108988842569180652141802897 81741631926885489106352173)
            ·
              refine ⟨30653111972582058414882065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81741631926885489106352173 30653111972582058414882065)
              ·
                refine ⟨22989833979436543811161549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30653111972582058414882065 22989833979436543811161549)
                ·
                  refine ⟨8621187742288703929185581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22989833979436543811161549 8621187742288703929185581)
                  ·
                    refine ⟨3232945403358263973444593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8621187742288703929185581 3232945403358263973444593)
                    ·
                      refine ⟨2424709052518697980083445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232945403358263973444593 2424709052518697980083445)
                      ·
                        rfl

theorem cell23_4722104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_4722104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722104 prefixEnd_4722104 := by exact prefixLift 4722104
  have htrace : WordTrace (prefixWord ++ tailWord_4722104) baseStart_4722104 baseEnd_4722104 := by
    simpa [prefixWord, tailWord_4722104, baseEnd_4722104] using wordTrace_append hprefix tailTrace_4722104
  have hstable : (prefixWord ++ tailWord_4722104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722104).length < 2 ^ (prefixWord ++ tailWord_4722104).sum := by decide
  have hdescent : baseEnd_4722104 < baseStart_4722104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722138 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2]
def baseStart_4722138 : Nat := 118140960795 + 4722138 * 2 ^ 59
def prefixEnd_4722138 : Nat := 4983230072969 + 3 ^ 40 * 4722138 * 2
def baseEnd_4722138 : Nat := 2424726510860950847058289

theorem tailTrace_4722138 : CollatzResearch.WordTrace tailWord_4722138 prefixEnd_4722138 2424726510860950847058289 := by
  unfold tailWord_4722138
  simp only [CollatzResearch.WordTrace]
  refine ⟨43057630541626994452149767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114820348111005318539066045 43057630541626994452149767)
  ·
    refine ⟨64586445812440491678224651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43057630541626994452149767 64586445812440491678224651)
    ·
      refine ⟨96879668718660737517336977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64586445812440491678224651 96879668718660737517336977)
      ·
        refine ⟨72659751538995553138002733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96879668718660737517336977 72659751538995553138002733)
        ·
          refine ⟨27247406827123332426751025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72659751538995553138002733 27247406827123332426751025)
          ·
            refine ⟨20435555120342499320063269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27247406827123332426751025 20435555120342499320063269)
            ·
              refine ⟨3831666585064218622511863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20435555120342499320063269 3831666585064218622511863)
              ·
                refine ⟨5747499877596327933767795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3831666585064218622511863 5747499877596327933767795)
                ·
                  refine ⟨8621249816394491900651693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5747499877596327933767795 8621249816394491900651693)
                  ·
                    refine ⟨3232968681147934462744385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8621249816394491900651693 3232968681147934462744385)
                    ·
                      refine ⟨2424726510860950847058289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3232968681147934462744385 2424726510860950847058289)
                      ·
                        rfl

theorem cell23_4722138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_4722138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722138 prefixEnd_4722138 := by exact prefixLift 4722138
  have htrace : WordTrace (prefixWord ++ tailWord_4722138) baseStart_4722138 baseEnd_4722138 := by
    simpa [prefixWord, tailWord_4722138, baseEnd_4722138] using wordTrace_append hprefix tailTrace_4722138
  have hstable : (prefixWord ++ tailWord_4722138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722138).length < 2 ^ (prefixWord ++ tailWord_4722138).sum := by decide
  have hdescent : baseEnd_4722138 < baseStart_4722138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722167 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_4722167 : Nat := 118140960795 + 4722167 * 2 ^ 59
def prefixEnd_4722167 : Nat := 4983230072969 + 3 ^ 40 * 4722167 * 2
def baseEnd_4722167 : Nat := 2424741401799931233595655

theorem tailTrace_4722167 : CollatzResearch.WordTrace tailWord_4722167 prefixEnd_4722167 2424741401799931233595655 := by
  unfold tailWord_4722167
  simp only [CollatzResearch.WordTrace]
  refine ⟨172231579883402915761404755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114821053255601943840936503 172231579883402915761404755)
  ·
    refine ⟨258347369825104373642107133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172231579883402915761404755 258347369825104373642107133)
    ·
      refine ⟨96880263684414140115790175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258347369825104373642107133 96880263684414140115790175)
      ·
        refine ⟨145320395526621210173685263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96880263684414140115790175 145320395526621210173685263)
        ·
          refine ⟨217980593289931815260527895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145320395526621210173685263 217980593289931815260527895)
          ·
            refine ⟨326970889934897722890791843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217980593289931815260527895 326970889934897722890791843)
            ·
              refine ⟨490456334902346584336187765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326970889934897722890791843 490456334902346584336187765)
              ·
                refine ⟨45980281397094992281517603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 490456334902346584336187765 45980281397094992281517603)
                ·
                  refine ⟨68970422095642488422276405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45980281397094992281517603 68970422095642488422276405)
                  ·
                    refine ⟨6465977071466483289588413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68970422095642488422276405 6465977071466483289588413)
                    ·
                      refine ⟨2424741401799931233595655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6465977071466483289588413 2424741401799931233595655)
                      ·
                        rfl

theorem cell23_4722167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_4722167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722167 prefixEnd_4722167 := by exact prefixLift 4722167
  have htrace : WordTrace (prefixWord ++ tailWord_4722167) baseStart_4722167 baseEnd_4722167 := by
    simpa [prefixWord, tailWord_4722167, baseEnd_4722167] using wordTrace_append hprefix tailTrace_4722167
  have hstable : (prefixWord ++ tailWord_4722167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722167).length < 2 ^ (prefixWord ++ tailWord_4722167).sum := by decide
  have hdescent : baseEnd_4722167 < baseStart_4722167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722204 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_4722204 : Nat := 118140960795 + 4722204 * 2 ^ 59
def prefixEnd_4722204 : Nat := 4983230072969 + 3 ^ 40 * 4722204 * 2
def baseEnd_4722204 : Nat := 808253466861382529610995

theorem tailTrace_4722204 : CollatzResearch.WordTrace tailWord_4722204 prefixEnd_4722204 808253466861382529610995 := by
  unfold tailWord_4722204
  simp only [CollatzResearch.WordTrace]
  refine ⟨86116464692134435540250833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114821952922845914053667777 86116464692134435540250833)
  ·
    refine ⟨64587348519100826655188125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86116464692134435540250833 64587348519100826655188125)
    ·
      refine ⟨24220255694662809995695547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64587348519100826655188125 24220255694662809995695547)
      ·
        refine ⟨36330383541994214993543321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24220255694662809995695547 36330383541994214993543321)
        ·
          refine ⟨27247787656495661245157491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36330383541994214993543321 27247787656495661245157491)
          ·
            refine ⟨40871681484743491867736237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27247787656495661245157491 40871681484743491867736237)
            ·
              refine ⟨15326880556778809450401089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40871681484743491867736237 15326880556778809450401089)
              ·
                refine ⟨11495160417584107087800817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15326880556778809450401089 11495160417584107087800817)
                ·
                  refine ⟨8621370313188080315850613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11495160417584107087800817 8621370313188080315850613)
                  ·
                    refine ⟨808253466861382529610995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8621370313188080315850613 808253466861382529610995)
                    ·
                      rfl

theorem cell23_4722204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_4722204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722204 prefixEnd_4722204 := by exact prefixLift 4722204
  have htrace : WordTrace (prefixWord ++ tailWord_4722204) baseStart_4722204 baseEnd_4722204 := by
    simpa [prefixWord, tailWord_4722204, baseEnd_4722204] using wordTrace_append hprefix tailTrace_4722204
  have hstable : (prefixWord ++ tailWord_4722204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722204).length < 2 ^ (prefixWord ++ tailWord_4722204).sum := by decide
  have hdescent : baseEnd_4722204 < baseStart_4722204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722208 : List Nat := [2, 1, 1, 6, 1, 2, 3, 2, 5]
def baseStart_4722208 : Nat := 118140960795 + 4722208 * 2 ^ 59
def prefixEnd_4722208 : Nat := 4983230072969 + 3 ^ 40 * 4722208 * 2
def baseEnd_4722208 : Nat := 269418050500751730353663

theorem tailTrace_4722208 : CollatzResearch.WordTrace tailWord_4722208 prefixEnd_4722208 269418050500751730353663 := by
  unfold tailWord_4722208
  simp only [CollatzResearch.WordTrace]
  refine ⟨86116537638127189881823639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114822050184169586509098185 86116537638127189881823639)
  ·
    refine ⟨129174806457190784822735459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86116537638127189881823639 129174806457190784822735459)
    ·
      refine ⟨193762209685786177234103189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129174806457190784822735459 193762209685786177234103189)
      ·
        refine ⟨9082603579021227057848587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193762209685786177234103189 9082603579021227057848587)
        ·
          refine ⟨13623905368531840586772881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9082603579021227057848587 13623905368531840586772881)
          ·
            refine ⟨10217929026398880440079661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13623905368531840586772881 10217929026398880440079661)
            ·
              refine ⟨3831723384899580165029873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10217929026398880440079661 3831723384899580165029873)
              ·
                refine ⟨2873792538674685123772405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831723384899580165029873 2873792538674685123772405)
                ·
                  refine ⟨269418050500751730353663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2873792538674685123772405 269418050500751730353663)
                  ·
                    rfl

theorem cell23_4722208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 5].length) (baseStart_4722208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722208 prefixEnd_4722208 := by exact prefixLift 4722208
  have htrace : WordTrace (prefixWord ++ tailWord_4722208) baseStart_4722208 baseEnd_4722208 := by
    simpa [prefixWord, tailWord_4722208, baseEnd_4722208] using wordTrace_append hprefix tailTrace_4722208
  have hstable : (prefixWord ++ tailWord_4722208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722208).length < 2 ^ (prefixWord ++ tailWord_4722208).sum := by decide
  have hdescent : baseEnd_4722208 < baseStart_4722208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722224 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 1, 6, 2]
def baseStart_4722224 : Nat := 118140960795 + 4722224 * 2 ^ 59
def prefixEnd_4722224 : Nat := 4983230072969 + 3 ^ 40 * 4722224 * 2
def baseEnd_4722224 : Nat := 2424770670197237510582893

theorem tailTrace_4722224 : CollatzResearch.WordTrace tailWord_4722224 prefixEnd_4722224 2424770670197237510582893 := by
  unfold tailWord_4722224
  simp only [CollatzResearch.WordTrace]
  refine ⟨86116829422098207248114863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114822439229464276330819817 86116829422098207248114863)
  ·
    refine ⟨129175244133147310872172295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86116829422098207248114863 129175244133147310872172295)
    ·
      refine ⟨193762866199720966308258443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129175244133147310872172295 193762866199720966308258443)
      ·
        refine ⟨290644299299581449462387665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193762866199720966308258443 290644299299581449462387665)
        ·
          refine ⟨217983224474686087096790749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290644299299581449462387665 217983224474686087096790749)
          ·
            refine ⟨81743709178007282661296531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217983224474686087096790749 81743709178007282661296531)
            ·
              refine ⟨122615563767010923991944797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81743709178007282661296531 122615563767010923991944797)
              ·
                refine ⟨45980836412629096496979299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122615563767010923991944797 45980836412629096496979299)
                ·
                  refine ⟨68971254618943644745468949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45980836412629096496979299 68971254618943644745468949)
                  ·
                    refine ⟨3233027560262983347443857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68971254618943644745468949 3233027560262983347443857)
                    ·
                      refine ⟨2424770670197237510582893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3233027560262983347443857 2424770670197237510582893)
                      ·
                        rfl

theorem cell23_4722224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 6, 2].length) (baseStart_4722224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722224 prefixEnd_4722224 := by exact prefixLift 4722224
  have htrace : WordTrace (prefixWord ++ tailWord_4722224) baseStart_4722224 baseEnd_4722224 := by
    simpa [prefixWord, tailWord_4722224, baseEnd_4722224] using wordTrace_append hprefix tailTrace_4722224
  have hstable : (prefixWord ++ tailWord_4722224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722224).length < 2 ^ (prefixWord ++ tailWord_4722224).sum := by decide
  have hdescent : baseEnd_4722224 < baseStart_4722224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722234 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_4722234 : Nat := 118140960795 + 4722234 * 2 ^ 59
def prefixEnd_4722234 : Nat := 4983230072969 + 3 ^ 40 * 4722234 * 2
def baseEnd_4722234 : Nat := 808258601667927490485949

theorem tailTrace_4722234 : CollatzResearch.WordTrace tailWord_4722234 prefixEnd_4722234 808258601667927490485949 := by
  unfold tailWord_4722234
  simp only [CollatzResearch.WordTrace]
  refine ⟨43058505893540046551023439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114822682382773457469395837 43058505893540046551023439)
  ·
    refine ⟨64587758840310069826535159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43058505893540046551023439 64587758840310069826535159)
    ·
      refine ⟨96881638260465104739802739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64587758840310069826535159 96881638260465104739802739)
      ·
        refine ⟨145322457390697657109704109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96881638260465104739802739 145322457390697657109704109)
        ·
          refine ⟨54495921521511621416139041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145322457390697657109704109 54495921521511621416139041)
          ·
            refine ⟨40871941141133716062104281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54495921521511621416139041 40871941141133716062104281)
            ·
              refine ⟨30653955855850287046578211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40871941141133716062104281 30653955855850287046578211)
              ·
                refine ⟨45980933783775430569867317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30653955855850287046578211 45980933783775430569867317)
                ·
                  refine ⟨4310712542228946615925061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45980933783775430569867317 4310712542228946615925061)
                  ·
                    refine ⟨808258601667927490485949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4310712542228946615925061 808258601667927490485949)
                    ·
                      rfl

theorem cell23_4722234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_4722234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722234 prefixEnd_4722234 := by exact prefixLift 4722234
  have htrace : WordTrace (prefixWord ++ tailWord_4722234) baseStart_4722234 baseEnd_4722234 := by
    simpa [prefixWord, tailWord_4722234, baseEnd_4722234] using wordTrace_append hprefix tailTrace_4722234
  have hstable : (prefixWord ++ tailWord_4722234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722234).length < 2 ^ (prefixWord ++ tailWord_4722234).sum := by decide
  have hdescent : baseEnd_4722234 < baseStart_4722234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722241 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_4722241 : Nat := 118140960795 + 4722241 * 2 ^ 59
def prefixEnd_4722241 : Nat := 4983230072969 + 3 ^ 40 * 4722241 * 2
def baseEnd_4722241 : Nat := 2424779399368363944070315

theorem tailTrace_4722241 : CollatzResearch.WordTrace tailWord_4722241 prefixEnd_4722241 2424779399368363944070315 := by
  unfold tailWord_4722241
  simp only [CollatzResearch.WordTrace]
  refine ⟨172234278885134826399598577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114822852590089884266399051 172234278885134826399598577)
  ·
    refine ⟨129175709163851119799698933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172234278885134826399598577 129175709163851119799698933)
    ·
      refine ⟨12110222734111042481221775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129175709163851119799698933 12110222734111042481221775)
      ·
        refine ⟨18165334101166563721832663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12110222734111042481221775 18165334101166563721832663)
        ·
          refine ⟨27248001151749845582748995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18165334101166563721832663 27248001151749845582748995)
          ·
            refine ⟨40872001727624768374123493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27248001151749845582748995 40872001727624768374123493)
            ·
              refine ⟨7663500323929644070148155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40872001727624768374123493 7663500323929644070148155)
              ·
                refine ⟨11495250485894466105222233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7663500323929644070148155 11495250485894466105222233)
                ·
                  refine ⟨8621437864420849578916675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11495250485894466105222233 8621437864420849578916675)
                  ·
                    refine ⟨12932156796631274368375013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8621437864420849578916675 12932156796631274368375013)
                    ·
                      refine ⟨2424779399368363944070315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12932156796631274368375013 2424779399368363944070315)
                      ·
                        rfl

theorem cell23_4722241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_4722241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722241 prefixEnd_4722241 := by exact prefixLift 4722241
  have htrace : WordTrace (prefixWord ++ tailWord_4722241) baseStart_4722241 baseEnd_4722241 := by
    simpa [prefixWord, tailWord_4722241, baseEnd_4722241] using wordTrace_append hprefix tailTrace_4722241
  have hstable : (prefixWord ++ tailWord_4722241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722241).length < 2 ^ (prefixWord ++ tailWord_4722241).sum := by decide
  have hdescent : baseEnd_4722241 < baseStart_4722241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722251 : List Nat := [1, 1, 1, 1, 3, 1, 3, 7, 1, 4]
def baseStart_4722251 : Nat := 118140960795 + 4722251 * 2 ^ 59
def prefixEnd_4722251 : Nat := 4983230072969 + 3 ^ 40 * 4722251 * 2
def baseEnd_4722251 : Nat := 808261511391636301648423

theorem tailTrace_4722251 : CollatzResearch.WordTrace tailWord_4722251 prefixEnd_4722251 808261511391636301648423 := by
  unfold tailWord_4722251
  simp only [CollatzResearch.WordTrace]
  refine ⟨172234643615098598107462607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114823095743399065404975071 172234643615098598107462607)
  ·
    refine ⟨258351965422647897161193911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172234643615098598107462607 258351965422647897161193911)
    ·
      refine ⟨387527948133971845741790867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258351965422647897161193911 387527948133971845741790867)
      ·
        refine ⟨581291922200957768612686301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387527948133971845741790867 581291922200957768612686301)
        ·
          refine ⟨217984470825359163229757363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 581291922200957768612686301 217984470825359163229757363)
          ·
            refine ⟨326976706238038744844636045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217984470825359163229757363 326976706238038744844636045)
            ·
              refine ⟨122616264839264529316738517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326976706238038744844636045 122616264839264529316738517)
              ·
                refine ⟨2873818707170262405861059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 122616264839264529316738517 2873818707170262405861059)
                ·
                  refine ⟨4310728060755393608791589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873818707170262405861059 4310728060755393608791589)
                  ·
                    refine ⟨808261511391636301648423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4310728060755393608791589 808261511391636301648423)
                    ·
                      rfl

theorem cell23_4722251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 1, 4].length) (baseStart_4722251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722251 prefixEnd_4722251 := by exact prefixLift 4722251
  have htrace : WordTrace (prefixWord ++ tailWord_4722251) baseStart_4722251 baseEnd_4722251 := by
    simpa [prefixWord, tailWord_4722251, baseEnd_4722251] using wordTrace_append hprefix tailTrace_4722251
  have hstable : (prefixWord ++ tailWord_4722251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722251).length < 2 ^ (prefixWord ++ tailWord_4722251).sum := by decide
  have hdescent : baseEnd_4722251 < baseStart_4722251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722287 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_4722287 : Nat := 118140960795 + 4722287 * 2 ^ 59
def prefixEnd_4722287 : Nat := 4983230072969 + 3 ^ 40 * 4722287 * 2
def baseEnd_4722287 : Nat := 2424803019478470764095103

theorem tailTrace_4722287 : CollatzResearch.WordTrace tailWord_4722287 prefixEnd_4722287 2424803019478470764095103 := by
  unfold tailWord_4722287
  simp only [CollatzResearch.WordTrace]
  refine ⟨172235956642968176255773115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114823971095312117503848743 172235956642968176255773115)
  ·
    refine ⟨258353934964452264383659673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172235956642968176255773115 258353934964452264383659673)
    ·
      refine ⟨193765451223339198287744755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258353934964452264383659673 193765451223339198287744755)
      ·
        refine ⟨290648176835008797431617133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193765451223339198287744755 290648176835008797431617133)
        ·
          refine ⟨108993066313128299036856425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290648176835008797431617133 108993066313128299036856425)
          ·
            refine ⟨81744799734846224277642319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108993066313128299036856425 81744799734846224277642319)
            ·
              refine ⟨122617199602269336416463479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81744799734846224277642319 122617199602269336416463479)
              ·
                refine ⟨183925799403404004624695219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122617199602269336416463479 183925799403404004624695219)
                ·
                  refine ⟨275888699105106006937042829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183925799403404004624695219 275888699105106006937042829)
                  ·
                    refine ⟨103458262164414752601391061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 275888699105106006937042829 103458262164414752601391061)
                    ·
                      refine ⟨2424803019478470764095103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103458262164414752601391061 2424803019478470764095103)
                      ·
                        rfl

theorem cell23_4722287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_4722287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722287 prefixEnd_4722287 := by exact prefixLift 4722287
  have htrace : WordTrace (prefixWord ++ tailWord_4722287) baseStart_4722287 baseEnd_4722287 := by
    simpa [prefixWord, tailWord_4722287, baseEnd_4722287] using wordTrace_append hprefix tailTrace_4722287
  have hstable : (prefixWord ++ tailWord_4722287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722287).length < 2 ^ (prefixWord ++ tailWord_4722287).sum := by decide
  have hdescent : baseEnd_4722287 < baseStart_4722287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722311 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 1, 5]
def baseStart_4722311 : Nat := 118140960795 + 4722311 * 2 ^ 59
def prefixEnd_4722311 : Nat := 4983230072969 + 3 ^ 40 * 4722311 * 2
def baseEnd_4722311 : Nat := 808271781004726223398331

theorem tailTrace_4722311 : CollatzResearch.WordTrace tailWord_4722311 prefixEnd_4722311 808271781004726223398331 := by
  unfold tailWord_4722311
  simp only [CollatzResearch.WordTrace]
  refine ⟨172236831994881228354646787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114824554663254152236431191 172236831994881228354646787)
  ·
    refine ⟨258355247992321842531970181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172236831994881228354646787 258355247992321842531970181)
    ·
      refine ⟨48441608998560345474744409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258355247992321842531970181 48441608998560345474744409)
      ·
        refine ⟨36331206748920259106058307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48441608998560345474744409 36331206748920259106058307)
        ·
          refine ⟨54496810123380388659087461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36331206748920259106058307 54496810123380388659087461)
          ·
            refine ⟨10218151898133822873578899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54496810123380388659087461 10218151898133822873578899)
            ·
              refine ⟨15327227847200734310368349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10218151898133822873578899 15327227847200734310368349)
              ·
                refine ⟨5747710442700275366388131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15327227847200734310368349 5747710442700275366388131)
                ·
                  refine ⟨8621565664050413049582197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5747710442700275366388131 8621565664050413049582197)
                  ·
                    refine ⟨808271781004726223398331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8621565664050413049582197 808271781004726223398331)
                    ·
                      rfl

theorem cell23_4722311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_4722311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722311 prefixEnd_4722311 := by exact prefixLift 4722311
  have htrace : WordTrace (prefixWord ++ tailWord_4722311) baseStart_4722311 baseEnd_4722311 := by
    simpa [prefixWord, tailWord_4722311, baseEnd_4722311] using wordTrace_append hprefix tailTrace_4722311
  have hstable : (prefixWord ++ tailWord_4722311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722311).length < 2 ^ (prefixWord ++ tailWord_4722311).sum := by decide
  have hdescent : baseEnd_4722311 < baseStart_4722311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722341 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_4722341 : Nat := 118140960795 + 4722341 * 2 ^ 59
def prefixEnd_4722341 : Nat := 4983230072969 + 3 ^ 40 * 4722341 * 2
def baseEnd_4722341 : Nat := 808276915811271184273285

theorem tailTrace_4722341 : CollatzResearch.WordTrace tailWord_4722341 prefixEnd_4722341 808276915811271184273285 := by
  unfold tailWord_4722341
  simp only [CollatzResearch.WordTrace]
  refine ⟨172237926184772543478238877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114825284123181695652159251 172237926184772543478238877)
  ·
    refine ⟨64589222319289703804339579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172237926184772543478238877 64589222319289703804339579)
    ·
      refine ⟨96883833478934555706509369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64589222319289703804339579 96883833478934555706509369)
      ·
        refine ⟨72662875109200916779882027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96883833478934555706509369 72662875109200916779882027)
        ·
          refine ⟨108994312663801375169823041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72662875109200916779882027 108994312663801375169823041)
          ·
            refine ⟨81745734497851031377367281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108994312663801375169823041 81745734497851031377367281)
            ·
              refine ⟨61309300873388273533025461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81745734497851031377367281 61309300873388273533025461)
              ·
                refine ⟨5747746956880150643721137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61309300873388273533025461 5747746956880150643721137)
                ·
                  refine ⟨4310810217660112982790853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5747746956880150643721137 4310810217660112982790853)
                  ·
                    refine ⟨808276915811271184273285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4310810217660112982790853 808276915811271184273285)
                    ·
                      rfl

theorem cell23_4722341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_4722341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722341 prefixEnd_4722341 := by exact prefixLift 4722341
  have htrace : WordTrace (prefixWord ++ tailWord_4722341) baseStart_4722341 baseEnd_4722341 := by
    simpa [prefixWord, tailWord_4722341, baseEnd_4722341] using wordTrace_append hprefix tailTrace_4722341
  have hstable : (prefixWord ++ tailWord_4722341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722341).length < 2 ^ (prefixWord ++ tailWord_4722341).sum := by decide
  have hdescent : baseEnd_4722341 < baseStart_4722341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722424 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_4722424 : Nat := 118140960795 + 4722424 * 2 ^ 59
def prefixEnd_4722424 : Nat := 4983230072969 + 3 ^ 40 * 4722424 * 2
def baseEnd_4722424 : Nat := 2424873366328136728081973

theorem tailTrace_4722424 : CollatzResearch.WordTrace tailWord_4722424 prefixEnd_4722424 2424873366328136728081973 := by
  unfold tailWord_4722424
  simp only [CollatzResearch.WordTrace]
  refine ⟨86120476721735924326755163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114827302295647899102340217 86120476721735924326755163)
  ·
    refine ⟨129180715082603886490132745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86120476721735924326755163 129180715082603886490132745)
    ·
      refine ⟨96885536311952914867599559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129180715082603886490132745 96885536311952914867599559)
      ·
        refine ⟨145328304467929372301399339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96885536311952914867599559 145328304467929372301399339)
        ·
          refine ⟨217992456701894058452099009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145328304467929372301399339 217992456701894058452099009)
          ·
            refine ⟨163494342526420543839074257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217992456701894058452099009 163494342526420543839074257)
            ·
              refine ⟨122620756894815407879305693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163494342526420543839074257 122620756894815407879305693)
              ·
                refine ⟨45982783835555777954739635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122620756894815407879305693 45982783835555777954739635)
                ·
                  refine ⟨68974175753333666932109453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45982783835555777954739635 68974175753333666932109453)
                  ·
                    refine ⟨25865315907500125099541045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68974175753333666932109453 25865315907500125099541045)
                    ·
                      refine ⟨2424873366328136728081973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25865315907500125099541045 2424873366328136728081973)
                      ·
                        rfl

theorem cell23_4722424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_4722424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722424 prefixEnd_4722424 := by exact prefixLift 4722424
  have htrace : WordTrace (prefixWord ++ tailWord_4722424) baseStart_4722424 baseEnd_4722424 := by
    simpa [prefixWord, tailWord_4722424, baseEnd_4722424] using wordTrace_append hprefix tailTrace_4722424
  have hstable : (prefixWord ++ tailWord_4722424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722424).length < 2 ^ (prefixWord ++ tailWord_4722424).sum := by decide
  have hdescent : baseEnd_4722424 < baseStart_4722424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722455 : List Nat := [1, 1, 3, 4, 2, 2, 2, 1, 1, 4, 2]
def baseStart_4722455 : Nat := 118140960795 + 4722455 * 2 ^ 59
def prefixEnd_4722455 : Nat := 4983230072969 + 3 ^ 40 * 4722455 * 2
def baseEnd_4722455 : Nat := 2424889284228426106794331

theorem tailTrace_4722455 : CollatzResearch.WordTrace tailWord_4722455 prefixEnd_4722455 2424889284228426106794331 := by
  unfold tailWord_4722455
  simp only [CollatzResearch.WordTrace]
  refine ⟨172242084106359540947888819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114828056070906360631925879 172242084106359540947888819)
  ·
    refine ⟨258363126159539311421833229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172242084106359540947888819 258363126159539311421833229)
    ·
      refine ⟨96886172309827241783187461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258363126159539311421833229 96886172309827241783187461)
      ·
        refine ⟨18166157308092607834347649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96886172309827241783187461 18166157308092607834347649)
        ·
          refine ⟨13624617981069455875760737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18166157308092607834347649 13624617981069455875760737)
          ·
            refine ⟨10218463485802091906820553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13624617981069455875760737 10218463485802091906820553)
            ·
              refine ⟨7663847614351568930115415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10218463485802091906820553 7663847614351568930115415)
              ·
                refine ⟨11495771421527353395173123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7663847614351568930115415 11495771421527353395173123)
                ·
                  refine ⟨17243657132291030092759685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11495771421527353395173123 17243657132291030092759685)
                  ·
                    refine ⟨3233185712304568142392441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17243657132291030092759685 3233185712304568142392441)
                    ·
                      refine ⟨2424889284228426106794331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3233185712304568142392441 2424889284228426106794331)
                      ·
                        rfl

theorem cell23_4722455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_4722455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722455 prefixEnd_4722455 := by exact prefixLift 4722455
  have htrace : WordTrace (prefixWord ++ tailWord_4722455) baseStart_4722455 baseEnd_4722455 := by
    simpa [prefixWord, tailWord_4722455, baseEnd_4722455] using wordTrace_append hprefix tailTrace_4722455
  have hstable : (prefixWord ++ tailWord_4722455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722455).length < 2 ^ (prefixWord ++ tailWord_4722455).sum := by decide
  have hdescent : baseEnd_4722455 < baseStart_4722455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722541 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4722541 : Nat := 118140960795 + 4722541 * 2 ^ 59
def prefixEnd_4722541 : Nat := 4983230072969 + 3 ^ 40 * 4722541 * 2
def baseEnd_4722541 : Nat := 2424933443564712770318935

theorem tailTrace_4722541 : CollatzResearch.WordTrace tailWord_4722541 prefixEnd_4722541 2424933443564712770318935 := by
  unfold tailWord_4722541
  simp only [CollatzResearch.WordTrace]
  refine ⟨172245220784047977635519477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114830147189365318423679651 172245220784047977635519477)
  ·
    refine ⟨16147989448504497903329951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172245220784047977635519477 16147989448504497903329951)
    ·
      refine ⟨24221984172756746854994927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16147989448504497903329951 24221984172756746854994927)
      ·
        refine ⟨36332976259135120282492391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24221984172756746854994927 36332976259135120282492391)
        ·
          refine ⟨54499464388702680423738587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36332976259135120282492391 54499464388702680423738587)
          ·
            refine ⟨81749196583054020635607881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54499464388702680423738587 81749196583054020635607881)
            ·
              refine ⟨61311897437290515476705911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81749196583054020635607881 61311897437290515476705911)
              ·
                refine ⟨91967846155935773215058867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61311897437290515476705911 91967846155935773215058867)
                ·
                  refine ⟨137951769233903659822588301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91967846155935773215058867 137951769233903659822588301)
                  ·
                    refine ⟨51731913462713872433470613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137951769233903659822588301 51731913462713872433470613)
                    ·
                      refine ⟨2424933443564712770318935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51731913462713872433470613 2424933443564712770318935)
                      ·
                        rfl

theorem cell23_4722541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4722541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722541 prefixEnd_4722541 := by exact prefixLift 4722541
  have htrace : WordTrace (prefixWord ++ tailWord_4722541) baseStart_4722541 baseEnd_4722541 := by
    simpa [prefixWord, tailWord_4722541, baseEnd_4722541] using wordTrace_append hprefix tailTrace_4722541
  have hstable : (prefixWord ++ tailWord_4722541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722541).length < 2 ^ (prefixWord ++ tailWord_4722541).sum := by decide
  have hdescent : baseEnd_4722541 < baseStart_4722541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722611 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 3, 6]
def baseStart_4722611 : Nat := 118140960795 + 4722611 * 2 ^ 59
def prefixEnd_4722611 : Nat := 4983230072969 + 3 ^ 40 * 4722611 * 2
def baseEnd_4722611 : Nat := 808323129070175832147871

theorem tailTrace_4722611 : CollatzResearch.WordTrace tailWord_4722611 prefixEnd_4722611 808323129070175832147871 := by
  unfold tailWord_4722611
  simp only [CollatzResearch.WordTrace]
  refine ⟨172247773893794379590567687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114831849262529586393711791 172247773893794379590567687)
  ·
    refine ⟨258371660840691569385851531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172247773893794379590567687 258371660840691569385851531)
    ·
      refine ⟨387557491261037354078777297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258371660840691569385851531 387557491261037354078777297)
      ·
        refine ⟨290668118445778015559082973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387557491261037354078777297 290668118445778015559082973)
        ·
          refine ⟨109000544417166755834656115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290668118445778015559082973 109000544417166755834656115)
          ·
            refine ⟨163500816625750133751984173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109000544417166755834656115 163500816625750133751984173)
            ·
              refine ⟨61312806234656300156994065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163500816625750133751984173 61312806234656300156994065)
              ·
                refine ⟨45984604675992225117745549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61312806234656300156994065 45984604675992225117745549)
                ·
                  refine ⟨17244226753497084419154581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45984604675992225117745549 17244226753497084419154581)
                  ·
                    refine ⟨808323129070175832147871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17244226753497084419154581 808323129070175832147871)
                    ·
                      rfl

theorem cell23_4722611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 6].length) (baseStart_4722611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722611 prefixEnd_4722611 := by exact prefixLift 4722611
  have htrace : WordTrace (prefixWord ++ tailWord_4722611) baseStart_4722611 baseEnd_4722611 := by
    simpa [prefixWord, tailWord_4722611, baseEnd_4722611] using wordTrace_append hprefix tailTrace_4722611
  have hstable : (prefixWord ++ tailWord_4722611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722611).length < 2 ^ (prefixWord ++ tailWord_4722611).sum := by decide
  have hdescent : baseEnd_4722611 < baseStart_4722611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722648 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_4722648 : Nat := 118140960795 + 4722648 * 2 ^ 59
def prefixEnd_4722648 : Nat := 4983230072969 + 3 ^ 40 * 4722648 * 2
def baseEnd_4722648 : Nat := 2424988385994743851680943

theorem tailTrace_4722648 : CollatzResearch.WordTrace tailWord_4722648 prefixEnd_4722648 2424988385994743851680943 := by
  unfold tailWord_4722648
  simp only [CollatzResearch.WordTrace]
  refine ⟨86124561697330167454832299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114832748929773556606443065 86124561697330167454832299)
  ·
    refine ⟨129186842545995251182248449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86124561697330167454832299 129186842545995251182248449)
    ·
      refine ⟨96890131909496438386686337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129186842545995251182248449 96890131909496438386686337)
      ·
        refine ⟨72667598932122328790014753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96890131909496438386686337 72667598932122328790014753)
        ·
          refine ⟨54500699199091746592511065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72667598932122328790014753 54500699199091746592511065)
          ·
            refine ⟨40875524399318809944383299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54500699199091746592511065 40875524399318809944383299)
            ·
              refine ⟨61313286598978214916574949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40875524399318809944383299 61313286598978214916574949)
              ·
                refine ⟨11496241237308415296857803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61313286598978214916574949 11496241237308415296857803)
                ·
                  refine ⟨17244361855962622945286705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11496241237308415296857803 17244361855962622945286705)
                  ·
                    refine ⟨12933271391971967208965029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17244361855962622945286705 12933271391971967208965029)
                    ·
                      refine ⟨2424988385994743851680943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12933271391971967208965029 2424988385994743851680943)
                      ·
                        rfl

theorem cell23_4722648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_4722648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722648 prefixEnd_4722648 := by exact prefixLift 4722648
  have htrace : WordTrace (prefixWord ++ tailWord_4722648) baseStart_4722648 baseEnd_4722648 := by
    simpa [prefixWord, tailWord_4722648, baseEnd_4722648] using wordTrace_append hprefix tailTrace_4722648
  have hstable : (prefixWord ++ tailWord_4722648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722648).length < 2 ^ (prefixWord ++ tailWord_4722648).sum := by decide
  have hdescent : baseEnd_4722648 < baseStart_4722648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722649 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 1, 5]
def baseStart_4722649 : Nat := 118140960795 + 4722649 * 2 ^ 59
def prefixEnd_4722649 : Nat := 4983230072969 + 3 ^ 40 * 4722649 * 2
def baseEnd_4722649 : Nat := 808329633158466115922813

theorem tailTrace_4722649 : CollatzResearch.WordTrace tailWord_4722649 prefixEnd_4722649 808329633158466115922813 := by
  unfold tailWord_4722649
  simp only [CollatzResearch.WordTrace]
  refine ⟨172249159867656712080451001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114832773245104474720300667 172249159867656712080451001)
  ·
    refine ⟨129186869900742534060338251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172249159867656712080451001 129186869900742534060338251)
    ·
      refine ⟨193780304851113801090507377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129186869900742534060338251 193780304851113801090507377)
      ·
        refine ⟨145335228638335350817880533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193780304851113801090507377 145335228638335350817880533)
        ·
          refine ⟨3406294421210984784794075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 145335228638335350817880533 3406294421210984784794075)
          ·
            refine ⟨5109441631816477177191113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406294421210984784794075 5109441631816477177191113)
            ·
              refine ⟨3832081223862357882893335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5109441631816477177191113 3832081223862357882893335)
              ·
                refine ⟨5748121835793536824340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832081223862357882893335 5748121835793536824340003)
                ·
                  refine ⟨8622182753690305236510005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5748121835793536824340003 8622182753690305236510005)
                  ·
                    refine ⟨808329633158466115922813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8622182753690305236510005 808329633158466115922813)
                    ·
                      rfl

theorem cell23_4722649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 1, 5].length) (baseStart_4722649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722649 prefixEnd_4722649 := by exact prefixLift 4722649
  have htrace : WordTrace (prefixWord ++ tailWord_4722649) baseStart_4722649 baseEnd_4722649 := by
    simpa [prefixWord, tailWord_4722649, baseEnd_4722649] using wordTrace_append hprefix tailTrace_4722649
  have hstable : (prefixWord ++ tailWord_4722649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722649).length < 2 ^ (prefixWord ++ tailWord_4722649).sum := by decide
  have hdescent : baseEnd_4722649 < baseStart_4722649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722668 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_4722668 : Nat := 118140960795 + 4722668 * 2 ^ 59
def prefixEnd_4722668 : Nat := 4983230072969 + 3 ^ 40 * 4722668 * 2
def baseEnd_4722668 : Nat := 2424998655607833773430851

theorem tailTrace_4722668 : CollatzResearch.WordTrace tailWord_4722668 prefixEnd_4722668 2424998655607833773430851 := by
  unfold tailWord_4722668
  simp only [CollatzResearch.WordTrace]
  refine ⟨86124926427293939162696329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114833235236391918883595105 86124926427293939162696329)
  ·
    refine ⟨64593694820470454372022247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86124926427293939162696329 64593694820470454372022247)
    ·
      refine ⟨96890542230705681558033371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64593694820470454372022247 96890542230705681558033371)
      ·
        refine ⟨145335813346058522337050057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96890542230705681558033371 145335813346058522337050057)
        ·
          refine ⟨109001860009543891752787543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145335813346058522337050057 109001860009543891752787543)
          ·
            refine ⟨163502790014315837629181315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109001860009543891752787543 163502790014315837629181315)
            ·
              refine ⟨245254185021473756443771973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163502790014315837629181315 245254185021473756443771973)
              ·
                refine ⟨45985159691526329333207245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245254185021473756443771973 45985159691526329333207245)
                ·
                  refine ⟨17244434884322373499952717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45985159691526329333207245 17244434884322373499952717)
                  ·
                    refine ⟨6466663081620890062482269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17244434884322373499952717 6466663081620890062482269)
                    ·
                      refine ⟨2424998655607833773430851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6466663081620890062482269 2424998655607833773430851)
                      ·
                        rfl

theorem cell23_4722668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_4722668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722668 prefixEnd_4722668 := by exact prefixLift 4722668
  have htrace : WordTrace (prefixWord ++ tailWord_4722668) baseStart_4722668 baseEnd_4722668 := by
    simpa [prefixWord, tailWord_4722668, baseEnd_4722668] using wordTrace_append hprefix tailTrace_4722668
  have hstable : (prefixWord ++ tailWord_4722668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722668).length < 2 ^ (prefixWord ++ tailWord_4722668).sum := by decide
  have hdescent : baseEnd_4722668 < baseStart_4722668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722685 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_4722685 : Nat := 118140960795 + 4722685 * 2 ^ 59
def prefixEnd_4722685 : Nat := 4983230072969 + 3 ^ 40 * 4722685 * 2
def baseEnd_4722685 : Nat := 2425007384778960206918273

theorem tailTrace_4722685 : CollatzResearch.WordTrace tailWord_4722685 prefixEnd_4722685 2425007384778960206918273 := by
  unfold tailWord_4722685
  simp only [CollatzResearch.WordTrace]
  refine ⟨172250472895526290228761509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114833648597017526819174339 172250472895526290228761509)
  ·
    refine ⟨32296963667911179417892783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172250472895526290228761509 32296963667911179417892783)
    ·
      refine ⟨48445445501866769126839175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32296963667911179417892783 48445445501866769126839175)
      ·
        refine ⟨72668168252800153690258763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48445445501866769126839175 72668168252800153690258763)
        ·
          refine ⟨109002252379200230535388145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72668168252800153690258763 109002252379200230535388145)
          ·
            refine ⟨81751689284400172901541109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109002252379200230535388145 81751689284400172901541109)
            ·
              refine ⟨7664220870412516209519479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81751689284400172901541109 7664220870412516209519479)
              ·
                refine ⟨11496331305618774314279219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7664220870412516209519479 11496331305618774314279219)
                ·
                  refine ⟨17244496958428161471418829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11496331305618774314279219 17244496958428161471418829)
                  ·
                    refine ⟨6466686359410560551782061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17244496958428161471418829 6466686359410560551782061)
                    ·
                      refine ⟨2425007384778960206918273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6466686359410560551782061 2425007384778960206918273)
                      ·
                        rfl

theorem cell23_4722685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_4722685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722685 prefixEnd_4722685 := by exact prefixLift 4722685
  have htrace : WordTrace (prefixWord ++ tailWord_4722685) baseStart_4722685 baseEnd_4722685 := by
    simpa [prefixWord, tailWord_4722685, baseEnd_4722685] using wordTrace_append hprefix tailTrace_4722685
  have hstable : (prefixWord ++ tailWord_4722685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722685).length < 2 ^ (prefixWord ++ tailWord_4722685).sum := by decide
  have hdescent : baseEnd_4722685 < baseStart_4722685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722712 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 1, 3, 2]
def baseStart_4722712 : Nat := 118140960795 + 4722712 * 2 ^ 59
def prefixEnd_4722712 : Nat := 4983230072969 + 3 ^ 40 * 4722712 * 2
def baseEnd_4722712 : Nat := 2425021248756631601280649

theorem tailTrace_4722712 : CollatzResearch.WordTrace tailWord_4722712 prefixEnd_4722712 2425021248756631601280649 := by
  unfold tailWord_4722712
  simp only [CollatzResearch.WordTrace]
  refine ⟨86125728833214236919997195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114834305110952315893329593 86125728833214236919997195)
  ·
    refine ⟨129188593249821355379995793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86125728833214236919997195 129188593249821355379995793)
    ·
      refine ⟨96891444937366016534996845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129188593249821355379995793 96891444937366016534996845)
      ·
        refine ⟨36334291851512256200623817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96891444937366016534996845 36334291851512256200623817)
        ·
          refine ⟨27250718888634192150467863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36334291851512256200623817 27250718888634192150467863)
          ·
            refine ⟨40876078332951288225701795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27250718888634192150467863 40876078332951288225701795)
            ·
              refine ⟨61314117499426932338552693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40876078332951288225701795 61314117499426932338552693)
              ·
                refine ⟨5748198515571274906739315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61314117499426932338552693 5748198515571274906739315)
                ·
                  refine ⟨8622297773356912360108973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5748198515571274906739315 8622297773356912360108973)
                  ·
                    refine ⟨3233361665008842135040865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8622297773356912360108973 3233361665008842135040865)
                    ·
                      refine ⟨2425021248756631601280649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3233361665008842135040865 2425021248756631601280649)
                      ·
                        rfl

theorem cell23_4722712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_4722712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722712 prefixEnd_4722712 := by exact prefixLift 4722712
  have htrace : WordTrace (prefixWord ++ tailWord_4722712) baseStart_4722712 baseEnd_4722712 := by
    simpa [prefixWord, tailWord_4722712, baseEnd_4722712] using wordTrace_append hprefix tailTrace_4722712
  have hstable : (prefixWord ++ tailWord_4722712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722712).length < 2 ^ (prefixWord ++ tailWord_4722712).sum := by decide
  have hdescent : baseEnd_4722712 < baseStart_4722712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722748 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 9]
def baseStart_4722748 : Nat := 118140960795 + 4722748 * 2 ^ 59
def prefixEnd_4722748 : Nat := 4983230072969 + 3 ^ 40 * 4722748 * 2
def baseEnd_4722748 : Nat := 269448859340021495603387

theorem tailTrace_4722748 : CollatzResearch.WordTrace tailWord_4722748 prefixEnd_4722748 269448859340021495603387 := by
  unfold tailWord_4722748
  simp only [CollatzResearch.WordTrace]
  refine ⟨86126385347149025994152449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114835180462865367992203265 86126385347149025994152449)
  ·
    refine ⟨64594789010361769495614337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86126385347149025994152449 64594789010361769495614337)
    ·
      refine ⟨48446091757771327121710753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64594789010361769495614337 48446091757771327121710753)
      ·
        refine ⟨36334568818328495341283065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48446091757771327121710753 36334568818328495341283065)
        ·
          refine ⟨27250926613746371505962299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36334568818328495341283065 27250926613746371505962299)
          ·
            refine ⟨40876389920619557258943449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27250926613746371505962299 40876389920619557258943449)
            ·
              refine ⟨30657292440464667944207587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40876389920619557258943449 30657292440464667944207587)
              ·
                refine ⟨45985938660697001916311381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30657292440464667944207587 45985938660697001916311381)
                ·
                  refine ⟨269448859340021495603387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45985938660697001916311381 269448859340021495603387)
                  ·
                    rfl

theorem cell23_4722748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_4722748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722748 prefixEnd_4722748 := by exact prefixLift 4722748
  have htrace : WordTrace (prefixWord ++ tailWord_4722748) baseStart_4722748 baseEnd_4722748 := by
    simpa [prefixWord, tailWord_4722748, baseEnd_4722748] using wordTrace_append hprefix tailTrace_4722748
  have hstable : (prefixWord ++ tailWord_4722748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722748).length < 2 ^ (prefixWord ++ tailWord_4722748).sum := by decide
  have hdescent : baseEnd_4722748 < baseStart_4722748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722812 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_4722812 : Nat := 118140960795 + 4722812 * 2 ^ 59
def prefixEnd_4722812 : Nat := 4983230072969 + 3 ^ 40 * 4722812 * 2
def baseEnd_4722812 : Nat := 808357532274027070010063

theorem tailTrace_4722812 : CollatzResearch.WordTrace tailWord_4722812 prefixEnd_4722812 808357532274027070010063 := by
  unfold tailWord_4722812
  simp only [CollatzResearch.WordTrace]
  refine ⟨86127552483033095459317345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114836736644044127279089793 86127552483033095459317345)
  ·
    refine ⟨64595664362274821594488009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86127552483033095459317345 64595664362274821594488009)
    ·
      refine ⟨48446748271706116195866007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64595664362274821594488009 48446748271706116195866007)
      ·
        refine ⟨72670122407559174293799011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48446748271706116195866007 72670122407559174293799011)
        ·
          refine ⟨109005183611338761440698517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72670122407559174293799011 109005183611338761440698517)
          ·
            refine ⟨5109617981781504442532743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109005183611338761440698517 5109617981781504442532743)
            ·
              refine ⟨7664426972672256663799115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109617981781504442532743 7664426972672256663799115)
              ·
                refine ⟨11496640459008384995698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7664426972672256663799115 11496640459008384995698673)
                ·
                  refine ⟨8622480344256288746774005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11496640459008384995698673 8622480344256288746774005)
                  ·
                    refine ⟨808357532274027070010063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8622480344256288746774005 808357532274027070010063)
                    ·
                      rfl

theorem cell23_4722812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_4722812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722812 prefixEnd_4722812 := by exact prefixLift 4722812
  have htrace : WordTrace (prefixWord ++ tailWord_4722812) baseStart_4722812 baseEnd_4722812 := by
    simpa [prefixWord, tailWord_4722812, baseEnd_4722812] using wordTrace_append hprefix tailTrace_4722812
  have hstable : (prefixWord ++ tailWord_4722812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722812).length < 2 ^ (prefixWord ++ tailWord_4722812).sum := by decide
  have hdescent : baseEnd_4722812 < baseStart_4722812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722825 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 5, 4]
def baseStart_4722825 : Nat := 118140960795 + 4722825 * 2 ^ 59
def prefixEnd_4722825 : Nat := 4983230072969 + 3 ^ 40 * 4722825 * 2
def baseEnd_4722825 : Nat := 808359757356863219722543

theorem tailTrace_4722825 : CollatzResearch.WordTrace tailWord_4722825 prefixEnd_4722825 808359757356863219722543 := by
  unfold tailWord_4722825
  simp only [CollatzResearch.WordTrace]
  refine ⟨172255579115019094138857929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114837052743346062759238619 172255579115019094138857929)
  ·
    refine ⟨129191684336264320604143447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172255579115019094138857929 129191684336264320604143447)
    ·
      refine ⟨193787526504396480906215171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129191684336264320604143447 193787526504396480906215171)
      ·
        refine ⟨290681289756594721359322757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193787526504396480906215171 290681289756594721359322757)
        ·
          refine ⟨54502741829361510254873017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290681289756594721359322757 54502741829361510254873017)
          ·
            refine ⟨40877056372021132691154763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54502741829361510254873017 40877056372021132691154763)
            ·
              refine ⟨61315584558031699036732145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40877056372021132691154763 61315584558031699036732145)
              ·
                refine ⟨45986688418523774277549109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61315584558031699036732145 45986688418523774277549109)
                ·
                  refine ⟨4311252039236603838520229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45986688418523774277549109 4311252039236603838520229)
                  ·
                    refine ⟨808359757356863219722543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4311252039236603838520229 808359757356863219722543)
                    ·
                      rfl

theorem cell23_4722825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 4].length) (baseStart_4722825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722825 prefixEnd_4722825 := by exact prefixLift 4722825
  have htrace : WordTrace (prefixWord ++ tailWord_4722825) baseStart_4722825 baseEnd_4722825 := by
    simpa [prefixWord, tailWord_4722825, baseEnd_4722825] using wordTrace_append hprefix tailTrace_4722825
  have hstable : (prefixWord ++ tailWord_4722825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722825).length < 2 ^ (prefixWord ++ tailWord_4722825).sum := by decide
  have hdescent : baseEnd_4722825 < baseStart_4722825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722835 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 3]
def baseStart_4722835 : Nat := 118140960795 + 4722835 * 2 ^ 59
def prefixEnd_4722835 : Nat := 4983230072969 + 3 ^ 40 * 4722835 * 2
def baseEnd_4722835 : Nat := 2425084406877134620042583

theorem tailTrace_4722835 : CollatzResearch.WordTrace tailWord_4722835 prefixEnd_4722835 2425084406877134620042583 := by
  unfold tailWord_4722835
  simp only [CollatzResearch.WordTrace]
  refine ⟨172255943844982865846721959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114837295896655243897814639 172255943844982865846721959)
  ·
    refine ⟨258383915767474298770082939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172255943844982865846721959 258383915767474298770082939)
    ·
      refine ⟨387575873651211448155124409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258383915767474298770082939 387575873651211448155124409)
      ·
        refine ⟨290681905238408586116343307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387575873651211448155124409 290681905238408586116343307)
        ·
          refine ⟨436022857857612879174514961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290681905238408586116343307 436022857857612879174514961)
          ·
            refine ⟨327017143393209659380886221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436022857857612879174514961 327017143393209659380886221)
            ·
              refine ⟨122631428772453622267832333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327017143393209659380886221 122631428772453622267832333)
              ·
                refine ⟨45986785789670108350437125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122631428772453622267832333 45986785789670108350437125)
                ·
                  refine ⟨8622522335563145315706961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45986785789670108350437125 8622522335563145315706961)
                  ·
                    refine ⟨6466891751672358986780221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8622522335563145315706961 6466891751672358986780221)
                    ·
                      refine ⟨2425084406877134620042583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6466891751672358986780221 2425084406877134620042583)
                      ·
                        rfl

theorem cell23_4722835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_4722835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722835 prefixEnd_4722835 := by exact prefixLift 4722835
  have htrace : WordTrace (prefixWord ++ tailWord_4722835) baseStart_4722835 baseEnd_4722835 := by
    simpa [prefixWord, tailWord_4722835, baseEnd_4722835] using wordTrace_append hprefix tailTrace_4722835
  have hstable : (prefixWord ++ tailWord_4722835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722835).length < 2 ^ (prefixWord ++ tailWord_4722835).sum := by decide
  have hdescent : baseEnd_4722835 < baseStart_4722835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722919 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 1, 5]
def baseStart_4722919 : Nat := 118140960795 + 4722919 * 2 ^ 59
def prefixEnd_4722919 : Nat := 4983230072969 + 3 ^ 40 * 4722919 * 2
def baseEnd_4722919 : Nat := 808375846417370763797399

theorem tailTrace_4722919 : CollatzResearch.WordTrace tailWord_4722919 prefixEnd_4722919 808375846417370763797399 := by
  unfold tailWord_4722919
  simp only [CollatzResearch.WordTrace]
  refine ⟨172259007576678548192779811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114839338384452365461853207 172259007576678548192779811)
  ·
    refine ⟨258388511365017822289169717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172259007576678548192779811 258388511365017822289169717)
    ·
      refine ⟨24223922940470420839609661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 258388511365017822289169717 24223922940470420839609661)
      ·
        refine ⟨9083971102676407814853623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24223922940470420839609661 9083971102676407814853623)
        ·
          refine ⟨13625956654014611722280435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9083971102676407814853623 13625956654014611722280435)
          ·
            refine ⟨20438934981021917583420653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13625956654014611722280435 20438934981021917583420653)
            ·
              refine ⟨7664600617883219093782745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20438934981021917583420653 7664600617883219093782745)
              ·
                refine ⟨5748450463412414320337059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7664600617883219093782745 5748450463412414320337059)
                ·
                  refine ⟨8622675695118621480505589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5748450463412414320337059 8622675695118621480505589)
                  ·
                    refine ⟨808375846417370763797399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8622675695118621480505589 808375846417370763797399)
                    ·
                      rfl

theorem cell23_4722919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_4722919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722919 prefixEnd_4722919 := by exact prefixLift 4722919
  have htrace : WordTrace (prefixWord ++ tailWord_4722919) baseStart_4722919 baseEnd_4722919 := by
    simpa [prefixWord, tailWord_4722919, baseEnd_4722919] using wordTrace_append hprefix tailTrace_4722919
  have hstable : (prefixWord ++ tailWord_4722919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722919).length < 2 ^ (prefixWord ++ tailWord_4722919).sum := by decide
  have hdescent : baseEnd_4722919 < baseStart_4722919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722922 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_4722922 : Nat := 118140960795 + 4722922 * 2 ^ 59
def prefixEnd_4722922 : Nat := 4983230072969 + 3 ^ 40 * 4722922 * 2
def baseEnd_4722922 : Nat := 2425129079694075779654683

theorem tailTrace_4722922 : CollatzResearch.WordTrace tailWord_4722922 prefixEnd_4722922 2425129079694075779654683 := by
  unfold tailWord_4722922
  simp only [CollatzResearch.WordTrace]
  refine ⟨43064779248916919926284755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114839411330445119803426013 43064779248916919926284755)
  ·
    refine ⟨64597168873375379889427133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43064779248916919926284755 64597168873375379889427133)
    ·
      refine ⟨24223938327515767458535175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64597168873375379889427133 24223938327515767458535175)
      ·
        refine ⟨36335907491273651187802763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24223938327515767458535175 36335907491273651187802763)
        ·
          refine ⟨54503861236910476781704145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36335907491273651187802763 54503861236910476781704145)
          ·
            refine ⟨40877895927682857586278109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54503861236910476781704145 40877895927682857586278109)
            ·
              refine ⟨15329210972881071594854291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40877895927682857586278109 15329210972881071594854291)
              ·
                refine ⟨22993816459321607392281437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15329210972881071594854291 22993816459321607392281437)
                ·
                  refine ⟨8622681172245602772105539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22993816459321607392281437 8622681172245602772105539)
                  ·
                    refine ⟨12934021758368404158158309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8622681172245602772105539 12934021758368404158158309)
                    ·
                      refine ⟨2425129079694075779654683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12934021758368404158158309 2425129079694075779654683)
                      ·
                        rfl

theorem cell23_4722922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_4722922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722922 prefixEnd_4722922 := by exact prefixLift 4722922
  have htrace : WordTrace (prefixWord ++ tailWord_4722922) baseStart_4722922 baseEnd_4722922 := by
    simpa [prefixWord, tailWord_4722922, baseEnd_4722922] using wordTrace_append hprefix tailTrace_4722922
  have hstable : (prefixWord ++ tailWord_4722922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722922).length < 2 ^ (prefixWord ++ tailWord_4722922).sum := by decide
  have hdescent : baseEnd_4722922 < baseStart_4722922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722965 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_4722965 : Nat := 118140960795 + 4722965 * 2 ^ 59
def prefixEnd_4722965 : Nat := 4983230072969 + 3 ^ 40 * 4722965 * 2
def baseEnd_4722965 : Nat := 2425151159362219111416985

theorem tailTrace_4722965 : CollatzResearch.WordTrace tailWord_4722965 prefixEnd_4722965 2425151159362219111416985 := by
  unfold tailWord_4722965
  simp only [CollatzResearch.WordTrace]
  refine ⟨172260685334511898048954349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114840456889674598699302899 172260685334511898048954349)
  ·
    refine ⟨64597757000441961768357881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172260685334511898048954349 64597757000441961768357881)
    ·
      refine ⟨48448317750331471326268411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64597757000441961768357881 48448317750331471326268411)
      ·
        refine ⟨72672476625497206989402617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48448317750331471326268411 72672476625497206989402617)
        ·
          refine ⟨54504357469122905242051963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72672476625497206989402617 54504357469122905242051963)
          ·
            refine ⟨81756536203684357863077945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54504357469122905242051963 81756536203684357863077945)
            ·
              refine ⟨61317402152763268397308459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81756536203684357863077945 61317402152763268397308459)
              ·
                refine ⟨91976103229144902595962689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61317402152763268397308459 91976103229144902595962689)
                ·
                  refine ⟨68982077421858676946972017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91976103229144902595962689 68982077421858676946972017)
                  ·
                    refine ⟨51736558066394007710229013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68982077421858676946972017 51736558066394007710229013)
                    ·
                      refine ⟨2425151159362219111416985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51736558066394007710229013 2425151159362219111416985)
                      ·
                        rfl

theorem cell23_4722965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_4722965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722965 prefixEnd_4722965 := by exact prefixLift 4722965
  have htrace : WordTrace (prefixWord ++ tailWord_4722965) baseStart_4722965 baseEnd_4722965 := by
    simpa [prefixWord, tailWord_4722965, baseEnd_4722965] using wordTrace_append hprefix tailTrace_4722965
  have hstable : (prefixWord ++ tailWord_4722965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722965).length < 2 ^ (prefixWord ++ tailWord_4722965).sum := by decide
  have hdescent : baseEnd_4722965 < baseStart_4722965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722973 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_4722973 : Nat := 118140960795 + 4722973 * 2 ^ 59
def prefixEnd_4722973 : Nat := 4983230072969 + 3 ^ 40 * 4722973 * 2
def baseEnd_4722973 : Nat := 2425155267207455080116949

theorem tailTrace_4722973 : CollatzResearch.WordTrace tailWord_4722973 prefixEnd_4722973 2425155267207455080116949 := by
  unfold tailWord_4722973
  simp only [CollatzResearch.WordTrace]
  refine ⟨172260977118482915415245573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114840651412321943610163715 172260977118482915415245573)
  ·
    refine ⟨32298933209715546640358545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172260977118482915415245573 32298933209715546640358545)
    ·
      refine ⟨24224199907286659980268909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32298933209715546640358545 24224199907286659980268909)
      ·
        refine ⟨9084074965232497492600841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24224199907286659980268909 9084074965232497492600841)
        ·
          refine ⟨6813056223924373119450631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9084074965232497492600841 6813056223924373119450631)
          ·
            refine ⟨10219584335886559679175947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6813056223924373119450631 10219584335886559679175947)
            ·
              refine ⟨15329376503829839518763921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10219584335886559679175947 15329376503829839518763921)
              ·
                refine ⟨11497032377872379639072941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15329376503829839518763921 11497032377872379639072941)
                ·
                  refine ⟨4311387141702142364652353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11497032377872379639072941 4311387141702142364652353)
                  ·
                    refine ⟨3233540356276606773489265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4311387141702142364652353 3233540356276606773489265)
                    ·
                      refine ⟨2425155267207455080116949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3233540356276606773489265 2425155267207455080116949)
                      ·
                        rfl

theorem cell23_4722973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_4722973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722973 prefixEnd_4722973 := by exact prefixLift 4722973
  have htrace : WordTrace (prefixWord ++ tailWord_4722973) baseStart_4722973 baseEnd_4722973 := by
    simpa [prefixWord, tailWord_4722973, baseEnd_4722973] using wordTrace_append hprefix tailTrace_4722973
  have hstable : (prefixWord ++ tailWord_4722973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722973).length < 2 ^ (prefixWord ++ tailWord_4722973).sum := by decide
  have hdescent : baseEnd_4722973 < baseStart_4722973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722990 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_4722990 : Nat := 118140960795 + 4722990 * 2 ^ 59
def prefixEnd_4722990 : Nat := 4983230072969 + 3 ^ 40 * 4722990 * 2
def baseEnd_4722990 : Nat := 2425163996378581513604371

theorem tailTrace_4722990 : CollatzResearch.WordTrace tailWord_4722990 prefixEnd_4722990 2425163996378581513604371 := by
  unfold tailWord_4722990
  simp only [CollatzResearch.WordTrace]
  refine ⟨21532699644927665914826803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114841064772947551545742949 21532699644927665914826803)
  ·
    refine ⟨32299049467391498872240205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21532699644927665914826803 32299049467391498872240205)
    ·
      refine ⟨12112143550271812077090077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32299049467391498872240205 12112143550271812077090077)
      ·
        refine ⟨4542053831351929528908779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12112143550271812077090077 4542053831351929528908779)
        ·
          refine ⟨6813080747027894293363169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542053831351929528908779 6813080747027894293363169)
          ·
            refine ⟨5109810560270920720022377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6813080747027894293363169 5109810560270920720022377)
            ·
              refine ⟨3832357920203190540016783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5109810560270920720022377 3832357920203190540016783)
              ·
                refine ⟨5748536880304785810025175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832357920203190540016783 5748536880304785810025175)
                ·
                  refine ⟨8622805320457178715037763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5748536880304785810025175 8622805320457178715037763)
                  ·
                    refine ⟨12934207980685768072556645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8622805320457178715037763 12934207980685768072556645)
                    ·
                      refine ⟨2425163996378581513604371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12934207980685768072556645 2425163996378581513604371)
                      ·
                        rfl

theorem cell23_4722990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_4722990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722990 prefixEnd_4722990 := by exact prefixLift 4722990
  have htrace : WordTrace (prefixWord ++ tailWord_4722990) baseStart_4722990 baseEnd_4722990 := by
    simpa [prefixWord, tailWord_4722990, baseEnd_4722990] using wordTrace_append hprefix tailTrace_4722990
  have hstable : (prefixWord ++ tailWord_4722990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722990).length < 2 ^ (prefixWord ++ tailWord_4722990).sum := by decide
  have hdescent : baseEnd_4722990 < baseStart_4722990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4722993 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 1, 2, 3]
def baseStart_4722993 : Nat := 118140960795 + 4722993 * 2 ^ 59
def prefixEnd_4722993 : Nat := 4983230072969 + 3 ^ 40 * 4722993 * 2
def baseEnd_4722993 : Nat := 2425165536820545001866857

theorem tailTrace_4722993 : CollatzResearch.WordTrace tailWord_4722993 prefixEnd_4722993 2425165536820545001866857 := by
  unfold tailWord_4722993
  simp only [CollatzResearch.WordTrace]
  refine ⟨172261706578410458830973633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114841137718940305887315755 172261706578410458830973633)
  ·
    refine ⟨129196279933807844123230225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172261706578410458830973633 129196279933807844123230225)
    ·
      refine ⟨96897209950355883092422669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129196279933807844123230225 96897209950355883092422669)
      ·
        refine ⟨36336453731383456159658501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96897209950355883092422669 36336453731383456159658501)
        ·
          refine ⟨6813085074634398029935969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36336453731383456159658501 6813085074634398029935969)
          ·
            refine ⟨5109813805975798522451977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6813085074634398029935969 5109813805975798522451977)
            ·
              refine ⟨3832360354481848891838983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5109813805975798522451977 3832360354481848891838983)
              ·
                refine ⟨5748540531722773337758475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832360354481848891838983 5748540531722773337758475)
                ·
                  refine ⟨8622810797584160006637713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5748540531722773337758475 8622810797584160006637713)
                  ·
                    refine ⟨6467108098188120004978285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8622810797584160006637713 6467108098188120004978285)
                    ·
                      refine ⟨2425165536820545001866857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6467108098188120004978285 2425165536820545001866857)
                      ·
                        rfl

theorem cell23_4722993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_4722993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4722993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4722993 prefixEnd_4722993 := by exact prefixLift 4722993
  have htrace : WordTrace (prefixWord ++ tailWord_4722993) baseStart_4722993 baseEnd_4722993 := by
    simpa [prefixWord, tailWord_4722993, baseEnd_4722993] using wordTrace_append hprefix tailTrace_4722993
  have hstable : (prefixWord ++ tailWord_4722993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4722993).length < 2 ^ (prefixWord ++ tailWord_4722993).sum := by decide
  have hdescent : baseEnd_4722993 < baseStart_4722993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4722993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723006 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_4723006 : Nat := 118140960795 + 4723006 * 2 ^ 59
def prefixEnd_4723006 : Nat := 4983230072969 + 3 ^ 40 * 4723006 * 2
def baseEnd_4723006 : Nat := 2425172212069053451004297

theorem tailTrace_4723006 : CollatzResearch.WordTrace tailWord_4723006 prefixEnd_4723006 2425172212069053451004297 := by
  unfold tailWord_4723006
  simp only [CollatzResearch.WordTrace]
  refine ⟨21532772590920420256399609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114841453818242241367464581 21532772590920420256399609)
  ·
    refine ⟨16149579443190315192299707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21532772590920420256399609 16149579443190315192299707)
    ·
      refine ⟨24224369164785472788449561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16149579443190315192299707 24224369164785472788449561)
      ·
        refine ⟨18168276873589104591337171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24224369164785472788449561 18168276873589104591337171)
        ·
          refine ⟨27252415310383656887005757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18168276873589104591337171 27252415310383656887005757)
          ·
            refine ⟨10219655741393871332627159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27252415310383656887005757 10219655741393871332627159)
            ·
              refine ⟨15329483612090806998940739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10219655741393871332627159 15329483612090806998940739)
              ·
                refine ⟨22994225418136210498411109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15329483612090806998940739 22994225418136210498411109)
                ·
                  refine ⟨4311417265900539468452083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22994225418136210498411109 4311417265900539468452083)
                  ·
                    refine ⟨6467125898850809202678125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4311417265900539468452083 6467125898850809202678125)
                    ·
                      refine ⟨2425172212069053451004297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6467125898850809202678125 2425172212069053451004297)
                      ·
                        rfl

theorem cell23_4723006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_4723006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723006 prefixEnd_4723006 := by exact prefixLift 4723006
  have htrace : WordTrace (prefixWord ++ tailWord_4723006) baseStart_4723006 baseEnd_4723006 := by
    simpa [prefixWord, tailWord_4723006, baseEnd_4723006] using wordTrace_append hprefix tailTrace_4723006
  have hstable : (prefixWord ++ tailWord_4723006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723006).length < 2 ^ (prefixWord ++ tailWord_4723006).sum := by decide
  have hdescent : baseEnd_4723006 < baseStart_4723006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723069 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 7]
def baseStart_4723069 : Nat := 118140960795 + 4723069 * 2 ^ 59
def prefixEnd_4723069 : Nat := 4983230072969 + 3 ^ 40 * 4723069 * 2
def baseEnd_4723069 : Nat := 269467173483365189390723

theorem tailTrace_4723069 : CollatzResearch.WordTrace tailWord_4723069 prefixEnd_4723069 269467173483365189390723 := by
  unfold tailWord_4723069
  simp only [CollatzResearch.WordTrace]
  refine ⟨172264478526135123810740261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114842985684090082540493507 172264478526135123810740261)
  ·
    refine ⟨32299589723650335714513799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172264478526135123810740261 32299589723650335714513799)
    ·
      refine ⟨48449384585475503571770699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32299589723650335714513799 48449384585475503571770699)
      ·
        refine ⟨72674076878213255357656049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48449384585475503571770699 72674076878213255357656049)
        ·
          refine ⟨54505557658659941518242037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72674076878213255357656049 54505557658659941518242037)
          ·
            refine ⟨5109896030499369517335191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54505557658659941518242037 5109896030499369517335191)
            ·
              refine ⟨7664844045749054276002787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109896030499369517335191 7664844045749054276002787)
              ·
                refine ⟨11497266068623581414004181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7664844045749054276002787 11497266068623581414004181)
                ·
                  refine ⟨269467173483365189390723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11497266068623581414004181 269467173483365189390723)
                  ·
                    rfl

theorem cell23_4723069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_4723069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723069 prefixEnd_4723069 := by exact prefixLift 4723069
  have htrace : WordTrace (prefixWord ++ tailWord_4723069) baseStart_4723069 baseEnd_4723069 := by
    simpa [prefixWord, tailWord_4723069, baseEnd_4723069] using wordTrace_append hprefix tailTrace_4723069
  have hstable : (prefixWord ++ tailWord_4723069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723069).length < 2 ^ (prefixWord ++ tailWord_4723069).sum := by decide
  have hdescent : baseEnd_4723069 < baseStart_4723069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723074 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_4723074 : Nat := 118140960795 + 4723074 * 2 ^ 59
def prefixEnd_4723074 : Nat := 4983230072969 + 3 ^ 40 * 4723074 * 2
def baseEnd_4723074 : Nat := 2425207128753559184953985

theorem tailTrace_4723074 : CollatzResearch.WordTrace tailWord_4723074 prefixEnd_4723074 2425207128753559184953985 := by
  unfold tailWord_4723074
  simp only [CollatzResearch.WordTrace]
  refine ⟨43066165222779252416168069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114843107260744673109781517 43066165222779252416168069)
  ·
    refine ⟨8074905979271109828031513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43066165222779252416168069 8074905979271109828031513)
    ·
      refine ⟨6056179484453332371023635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8074905979271109828031513 6056179484453332371023635)
      ·
        refine ⟨9084269226679998556535453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6056179484453332371023635 9084269226679998556535453)
        ·
          refine ⟨3406600960004999458700795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9084269226679998556535453 3406600960004999458700795)
          ·
            refine ⟨5109901440007499188051193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406600960004999458700795 5109901440007499188051193)
            ·
              refine ⟨3832426080005624391038395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5109901440007499188051193 3832426080005624391038395)
              ·
                refine ⟨5748639120008436586557593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832426080005624391038395 5748639120008436586557593)
                ·
                  refine ⟨4311479340006327439918195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5748639120008436586557593 4311479340006327439918195)
                  ·
                    refine ⟨6467219010009491159877293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4311479340006327439918195 6467219010009491159877293)
                    ·
                      refine ⟨2425207128753559184953985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6467219010009491159877293 2425207128753559184953985)
                      ·
                        rfl

theorem cell23_4723074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_4723074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723074 prefixEnd_4723074 := by exact prefixLift 4723074
  have htrace : WordTrace (prefixWord ++ tailWord_4723074) baseStart_4723074 baseEnd_4723074 := by
    simpa [prefixWord, tailWord_4723074, baseEnd_4723074] using wordTrace_append hprefix tailTrace_4723074
  have hstable : (prefixWord ++ tailWord_4723074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723074).length < 2 ^ (prefixWord ++ tailWord_4723074).sum := by decide
  have hdescent : baseEnd_4723074 < baseStart_4723074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723114 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4723114 : Nat := 118140960795 + 4723114 * 2 ^ 59
def prefixEnd_4723114 : Nat := 4983230072969 + 3 ^ 40 * 4723114 * 2
def baseEnd_4723114 : Nat := 2425227667979739028453801

theorem tailTrace_4723114 : CollatzResearch.WordTrace tailWord_4723114 prefixEnd_4723114 2425227667979739028453801 := by
  unfold tailWord_4723114
  simp only [CollatzResearch.WordTrace]
  refine ⟨43066529952743024124032099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114844079873981397664085597 43066529952743024124032099)
  ·
    refine ⟨64599794929114536186048149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43066529952743024124032099 64599794929114536186048149)
    ·
      refine ⟨3028115387302243883721007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64599794929114536186048149 3028115387302243883721007)
      ·
        refine ⟨4542173080953365825581511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028115387302243883721007 4542173080953365825581511)
        ·
          refine ⟨6813259621430048738372267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542173080953365825581511 6813259621430048738372267)
          ·
            refine ⟨10219889432145073107558401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6813259621430048738372267 10219889432145073107558401)
            ·
              refine ⟨7664917074108804830668801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10219889432145073107558401 7664917074108804830668801)
              ·
                refine ⟨5748687805581603623001601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7664917074108804830668801 5748687805581603623001601)
                ·
                  refine ⟨4311515854186202717251201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5748687805581603623001601 4311515854186202717251201)
                  ·
                    refine ⟨3233636890639652037938401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4311515854186202717251201 3233636890639652037938401)
                    ·
                      refine ⟨2425227667979739028453801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3233636890639652037938401 2425227667979739028453801)
                      ·
                        rfl

theorem cell23_4723114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4723114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723114 prefixEnd_4723114 := by exact prefixLift 4723114
  have htrace : WordTrace (prefixWord ++ tailWord_4723114) baseStart_4723114 baseEnd_4723114 := by
    simpa [prefixWord, tailWord_4723114, baseEnd_4723114] using wordTrace_append hprefix tailTrace_4723114
  have hstable : (prefixWord ++ tailWord_4723114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723114).length < 2 ^ (prefixWord ++ tailWord_4723114).sum := by decide
  have hdescent : baseEnd_4723114 < baseStart_4723114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723122 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_4723122 : Nat := 118140960795 + 4723122 * 2 ^ 59
def prefixEnd_4723122 : Nat := 4983230072969 + 3 ^ 40 * 4723122 * 2
def baseEnd_4723122 : Nat := 2425231775824974997153763

theorem tailTrace_4723122 : CollatzResearch.WordTrace tailWord_4723122 prefixEnd_4723122 2425231775824974997153763 := by
  unfold tailWord_4723122
  simp only [CollatzResearch.WordTrace]
  refine ⟨43066602898735778465604905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114844274396628742574946413 43066602898735778465604905)
  ·
    refine ⟨32299952174051833849203679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43066602898735778465604905 32299952174051833849203679)
    ·
      refine ⟨48449928261077750773805519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32299952174051833849203679 48449928261077750773805519)
      ·
        refine ⟨72674892391616626160708279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48449928261077750773805519 72674892391616626160708279)
        ·
          refine ⟨109012338587424939241062419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72674892391616626160708279 109012338587424939241062419)
          ·
            refine ⟨163518507881137408861593629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109012338587424939241062419 163518507881137408861593629)
            ·
              refine ⟨61319440455426528323097611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163518507881137408861593629 61319440455426528323097611)
              ·
                refine ⟨91979160683139792484646417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61319440455426528323097611 91979160683139792484646417)
                ·
                  refine ⟨68984370512354844363484813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91979160683139792484646417 68984370512354844363484813)
                  ·
                    refine ⟨25869138942133066636306805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68984370512354844363484813 25869138942133066636306805)
                    ·
                      refine ⟨2425231775824974997153763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25869138942133066636306805 2425231775824974997153763)
                      ·
                        rfl

theorem cell23_4723122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_4723122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723122 prefixEnd_4723122 := by exact prefixLift 4723122
  have htrace : WordTrace (prefixWord ++ tailWord_4723122) baseStart_4723122 baseEnd_4723122 := by
    simpa [prefixWord, tailWord_4723122, baseEnd_4723122] using wordTrace_append hprefix tailTrace_4723122
  have hstable : (prefixWord ++ tailWord_4723122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723122).length < 2 ^ (prefixWord ++ tailWord_4723122).sum := by decide
  have hdescent : baseEnd_4723122 < baseStart_4723122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723156 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_4723156 : Nat := 118140960795 + 4723156 * 2 ^ 59
def prefixEnd_4723156 : Nat := 4983230072969 + 3 ^ 40 * 4723156 * 2
def baseEnd_4723156 : Nat := 2425249234167227864128607

theorem tailTrace_4723156 : CollatzResearch.WordTrace tailWord_4723156 prefixEnd_4723156 2425249234167227864128607 := by
  unfold tailWord_4723156
  simp only [CollatzResearch.WordTrace]
  refine ⟨86133825838409968834578661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114845101117879958446104881 86133825838409968834578661)
  ·
    refine ⟨16150092344701869156483499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86133825838409968834578661 16150092344701869156483499)
    ·
      refine ⟨24225138517052803734725249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16150092344701869156483499 24225138517052803734725249)
      ·
        refine ⟨18168853887789602801043937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24225138517052803734725249 18168853887789602801043937)
        ·
          refine ⟨13626640415842202100782953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18168853887789602801043937 13626640415842202100782953)
          ·
            refine ⟨10219980311881651575587215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13626640415842202100782953 10219980311881651575587215)
            ·
              refine ⟨15329970467822477363380823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10219980311881651575587215 15329970467822477363380823)
              ·
                refine ⟨22994955701733716045071235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15329970467822477363380823 22994955701733716045071235)
                ·
                  refine ⟨34492433552600574067606853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22994955701733716045071235 34492433552600574067606853)
                  ·
                    refine ⟨6467331291112607637676285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34492433552600574067606853 6467331291112607637676285)
                    ·
                      refine ⟨2425249234167227864128607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6467331291112607637676285 2425249234167227864128607)
                      ·
                        rfl

theorem cell23_4723156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_4723156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723156 prefixEnd_4723156 := by exact prefixLift 4723156
  have htrace : WordTrace (prefixWord ++ tailWord_4723156) baseStart_4723156 baseEnd_4723156 := by
    simpa [prefixWord, tailWord_4723156, baseEnd_4723156] using wordTrace_append hprefix tailTrace_4723156
  have hstable : (prefixWord ++ tailWord_4723156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723156).length < 2 ^ (prefixWord ++ tailWord_4723156).sum := by decide
  have hdescent : baseEnd_4723156 < baseStart_4723156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723176 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 6]
def baseStart_4723176 : Nat := 118140960795 + 4723176 * 2 ^ 59
def prefixEnd_4723176 : Nat := 4983230072969 + 3 ^ 40 * 4723176 * 2
def baseEnd_4723176 : Nat := 269473278197813087319835

theorem tailTrace_4723176 : CollatzResearch.WordTrace tailWord_4723176 prefixEnd_4723176 269473278197813087319835 := by
  unfold tailWord_4723176
  simp only [CollatzResearch.WordTrace]
  refine ⟨86134190568373740542442691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114845587424498320723256921 86134190568373740542442691)
  ·
    refine ⟨129201285852560610813664037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86134190568373740542442691 129201285852560610813664037)
    ·
      refine ⟨24225241097355114527562007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129201285852560610813664037 24225241097355114527562007)
      ·
        refine ⟨36337861646032671791343011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24225241097355114527562007 36337861646032671791343011)
        ·
          refine ⟨54506792469049007687014517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36337861646032671791343011 54506792469049007687014517)
          ·
            refine ⟨5110011793973344470657611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54506792469049007687014517 5110011793973344470657611)
            ·
              refine ⟨7665017690960016705986417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5110011793973344470657611 7665017690960016705986417)
              ·
                refine ⟨5748763268220012529489813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7665017690960016705986417 5748763268220012529489813)
                ·
                  refine ⟨269473278197813087319835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5748763268220012529489813 269473278197813087319835)
                  ·
                    rfl

theorem cell23_4723176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 6].length) (baseStart_4723176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723176 prefixEnd_4723176 := by exact prefixLift 4723176
  have htrace : WordTrace (prefixWord ++ tailWord_4723176) baseStart_4723176 baseEnd_4723176 := by
    simpa [prefixWord, tailWord_4723176, baseEnd_4723176] using wordTrace_append hprefix tailTrace_4723176
  have hstable : (prefixWord ++ tailWord_4723176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723176).length < 2 ^ (prefixWord ++ tailWord_4723176).sum := by decide
  have hdescent : baseEnd_4723176 < baseStart_4723176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723219 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 6, 4]
def baseStart_4723219 : Nat := 118140960795 + 4723219 * 2 ^ 59
def prefixEnd_4723219 : Nat := 4983230072969 + 3 ^ 40 * 4723219 * 2
def baseEnd_4723219 : Nat := 808427194482820372546939

theorem tailTrace_4723219 : CollatzResearch.WordTrace tailWord_4723219 prefixEnd_4723219 808427194482820372546939 := by
  unfold tailWord_4723219
  simp only [CollatzResearch.WordTrace]
  refine ⟨172269949475591699428700711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114846632983727799619133807 172269949475591699428700711)
  ·
    refine ⟨258404924213387549143051067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172269949475591699428700711 258404924213387549143051067)
    ·
      refine ⟨387607386320081323714576601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258404924213387549143051067 387607386320081323714576601)
      ·
        refine ⟨290705539740060992785932451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387607386320081323714576601 290705539740060992785932451)
        ·
          refine ⟨436058309610091489178898677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290705539740060992785932451 436058309610091489178898677)
          ·
            refine ⟨40880466525946077110521751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 436058309610091489178898677 40880466525946077110521751)
            ·
              refine ⟨61320699788919115665782627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40880466525946077110521751 61320699788919115665782627)
              ·
                refine ⟨91981049683378673498673941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61320699788919115665782627 91981049683378673498673941)
                ·
                  refine ⟨4311611703908375320250341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91981049683378673498673941 4311611703908375320250341)
                  ·
                    refine ⟨808427194482820372546939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4311611703908375320250341 808427194482820372546939)
                    ·
                      rfl

theorem cell23_4723219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 4].length) (baseStart_4723219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723219 prefixEnd_4723219 := by exact prefixLift 4723219
  have htrace : WordTrace (prefixWord ++ tailWord_4723219) baseStart_4723219 baseEnd_4723219 := by
    simpa [prefixWord, tailWord_4723219, baseEnd_4723219] using wordTrace_append hprefix tailTrace_4723219
  have hstable : (prefixWord ++ tailWord_4723219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723219).length < 2 ^ (prefixWord ++ tailWord_4723219).sum := by decide
  have hdescent : baseEnd_4723219 < baseStart_4723219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723226 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4]
def baseStart_4723226 : Nat := 118140960795 + 4723226 * 2 ^ 59
def prefixEnd_4723226 : Nat := 4983230072969 + 3 ^ 40 * 4723226 * 2
def baseEnd_4723226 : Nat := 2425285177813042590253285

theorem tailTrace_4723226 : CollatzResearch.WordTrace tailWord_4723226 prefixEnd_4723226 2425285177813042590253285 := by
  unfold tailWord_4723226
  simp only [CollatzResearch.WordTrace]
  refine ⟨43067551196641584906051383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114846803191044226416137021 43067551196641584906051383)
  ·
    refine ⟨64601326794962377359077075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43067551196641584906051383 64601326794962377359077075)
    ·
      refine ⟨96901990192443566038615613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64601326794962377359077075 96901990192443566038615613)
      ·
        refine ⟨36338246322166337264480855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96901990192443566038615613 36338246322166337264480855)
        ·
          refine ⟨54507369483249505896721283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36338246322166337264480855 54507369483249505896721283)
          ·
            refine ⟨81761054224874258845081925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54507369483249505896721283 81761054224874258845081925)
            ·
              refine ⟨15330197667163923533452861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81761054224874258845081925 15330197667163923533452861)
              ·
                refine ⟨5748824125186471325044823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15330197667163923533452861 5748824125186471325044823)
                ·
                  refine ⟨8623236187779706987567235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5748824125186471325044823 8623236187779706987567235)
                  ·
                    refine ⟨12934854281669560481350853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8623236187779706987567235 12934854281669560481350853)
                    ·
                      refine ⟨2425285177813042590253285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12934854281669560481350853 2425285177813042590253285)
                      ·
                        rfl

theorem cell23_4723226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_4723226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723226 prefixEnd_4723226 := by exact prefixLift 4723226
  have htrace : WordTrace (prefixWord ++ tailWord_4723226) baseStart_4723226 baseEnd_4723226 := by
    simpa [prefixWord, tailWord_4723226, baseEnd_4723226] using wordTrace_append hprefix tailTrace_4723226
  have hstable : (prefixWord ++ tailWord_4723226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723226).length < 2 ^ (prefixWord ++ tailWord_4723226).sum := by decide
  have hdescent : baseEnd_4723226 < baseStart_4723226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723276 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_4723276 : Nat := 118140960795 + 4723276 * 2 ^ 59
def prefixEnd_4723276 : Nat := 4983230072969 + 3 ^ 40 * 4723276 * 2
def baseEnd_4723276 : Nat := 2425310851845767394628055

theorem tailTrace_4723276 : CollatzResearch.WordTrace tailWord_4723276 prefixEnd_4723276 2425310851845767394628055 := by
  unfold tailWord_4723276
  simp only [CollatzResearch.WordTrace]
  refine ⟨86136014218192599081762841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114848018957590132109017121 86136014218192599081762841)
  ·
    refine ⟨64602010663644449311322131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86136014218192599081762841 64602010663644449311322131)
    ·
      refine ⟨96903015995466673966983197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64602010663644449311322131 96903015995466673966983197)
      ·
        refine ⟨36338630998300002737618699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96903015995466673966983197 36338630998300002737618699)
        ·
          refine ⟨54507946497450004106428049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36338630998300002737618699 54507946497450004106428049)
          ·
            refine ⟨40880959873087503079821037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54507946497450004106428049 40880959873087503079821037)
            ·
              refine ⟨15330359952407813654932889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40880959873087503079821037 15330359952407813654932889)
              ·
                refine ⟨11497769964305860241199667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15330359952407813654932889 11497769964305860241199667)
                ·
                  refine ⟨17246654946458790361799501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11497769964305860241199667 17246654946458790361799501)
                  ·
                    refine ⟨6467495604922046385674813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17246654946458790361799501 6467495604922046385674813)
                    ·
                      refine ⟨2425310851845767394628055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6467495604922046385674813 2425310851845767394628055)
                      ·
                        rfl

theorem cell23_4723276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_4723276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723276 prefixEnd_4723276 := by exact prefixLift 4723276
  have htrace : WordTrace (prefixWord ++ tailWord_4723276) baseStart_4723276 baseEnd_4723276 := by
    simpa [prefixWord, tailWord_4723276, baseEnd_4723276] using wordTrace_append hprefix tailTrace_4723276
  have hstable : (prefixWord ++ tailWord_4723276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723276).length < 2 ^ (prefixWord ++ tailWord_4723276).sum := by decide
  have hdescent : baseEnd_4723276 < baseStart_4723276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723299 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4723299 : Nat := 118140960795 + 4723299 * 2 ^ 59
def prefixEnd_4723299 : Nat := 4983230072969 + 3 ^ 40 * 4723299 * 2
def baseEnd_4723299 : Nat := 2425322661900820804640449

theorem tailTrace_4723299 : CollatzResearch.WordTrace tailWord_4723299 prefixEnd_4723299 2425322661900820804640449 := by
  unfold tailWord_4723299
  simp only [CollatzResearch.WordTrace]
  refine ⟨172272867315301873091612951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114848578210201248727741967 172272867315301873091612951)
  ·
    refine ⟨258409300972952809637419427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172272867315301873091612951 258409300972952809637419427)
    ·
      refine ⟨387613951459429214456129141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258409300972952809637419427 387613951459429214456129141)
      ·
        refine ⟨36338807949321488855262107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 387613951459429214456129141 36338807949321488855262107)
        ·
          refine ⟨54508211923982233282893161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36338807949321488855262107 54508211923982233282893161)
          ·
            refine ⟨40881158942986674962169871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54508211923982233282893161 40881158942986674962169871)
            ·
              refine ⟨61321738414480012443254807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40881158942986674962169871 61321738414480012443254807)
              ·
                refine ⟨91982607621720018664882211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61321738414480012443254807 91982607621720018664882211)
                ·
                  refine ⟨137973911432580027997323317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91982607621720018664882211 137973911432580027997323317)
                  ·
                    refine ⟨12935054196804377624749061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 137973911432580027997323317 12935054196804377624749061)
                    ·
                      refine ⟨2425322661900820804640449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12935054196804377624749061 2425322661900820804640449)
                      ·
                        rfl

theorem cell23_4723299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4723299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723299 prefixEnd_4723299 := by exact prefixLift 4723299
  have htrace : WordTrace (prefixWord ++ tailWord_4723299) baseStart_4723299 baseEnd_4723299 := by
    simpa [prefixWord, tailWord_4723299, baseEnd_4723299] using wordTrace_append hprefix tailTrace_4723299
  have hstable : (prefixWord ++ tailWord_4723299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723299).length < 2 ^ (prefixWord ++ tailWord_4723299).sum := by decide
  have hdescent : baseEnd_4723299 < baseStart_4723299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723310 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_4723310 : Nat := 118140960795 + 4723310 * 2 ^ 59
def prefixEnd_4723310 : Nat := 4983230072969 + 3 ^ 40 * 4723310 * 2
def baseEnd_4723310 : Nat := 2425328310188020261602899

theorem tailTrace_4723310 : CollatzResearch.WordTrace tailWord_4723310 prefixEnd_4723310 2425328310188020261602899 := by
  unfold tailWord_4723310
  simp only [CollatzResearch.WordTrace]
  refine ⟨21534158564782752746282923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114848845678841347980175589 21534158564782752746282923)
  ·
    refine ⟨32301237847174129119424385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21534158564782752746282923 32301237847174129119424385)
    ·
      refine ⟨24225928385380596839568289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32301237847174129119424385 24225928385380596839568289)
      ·
        refine ⟨18169446289035447629676217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24225928385380596839568289 18169446289035447629676217)
        ·
          refine ⟨13627084716776585722257163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18169446289035447629676217 13627084716776585722257163)
          ·
            refine ⟨20440627075164878583385745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13627084716776585722257163 20440627075164878583385745)
            ·
              refine ⟨15330470306373658937539309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20440627075164878583385745 15330470306373658937539309)
              ·
                refine ⟨5748926364890122101577241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15330470306373658937539309 5748926364890122101577241)
                ·
                  refine ⟨4311694773667591576182931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5748926364890122101577241 4311694773667591576182931)
                  ·
                    refine ⟨6467542160501387364274397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4311694773667591576182931 6467542160501387364274397)
                    ·
                      refine ⟨2425328310188020261602899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6467542160501387364274397 2425328310188020261602899)
                      ·
                        rfl

theorem cell23_4723310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_4723310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723310 prefixEnd_4723310 := by exact prefixLift 4723310
  have htrace : WordTrace (prefixWord ++ tailWord_4723310) baseStart_4723310 baseEnd_4723310 := by
    simpa [prefixWord, tailWord_4723310, baseEnd_4723310] using wordTrace_append hprefix tailTrace_4723310
  have hstable : (prefixWord ++ tailWord_4723310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723310).length < 2 ^ (prefixWord ++ tailWord_4723310).sum := by decide
  have hdescent : baseEnd_4723310 < baseStart_4723310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723319 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_4723319 : Nat := 118140960795 + 4723319 * 2 ^ 59
def prefixEnd_4723319 : Nat := 4983230072969 + 3 ^ 40 * 4723319 * 2
def baseEnd_4723319 : Nat := 2425332931513910726390357

theorem tailTrace_4723319 : CollatzResearch.WordTrace tailWord_4723319 prefixEnd_4723319 2425332931513910726390357 := by
  unfold tailWord_4723319
  simp only [CollatzResearch.WordTrace]
  refine ⟨172273596775229416507341011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114849064516819611004894007 172273596775229416507341011)
  ·
    refine ⟨258410395162844124761011517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172273596775229416507341011 258410395162844124761011517)
    ·
      refine ⟨96903898186066546785379319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258410395162844124761011517 96903898186066546785379319)
      ·
        refine ⟨145355847279099820178068979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96903898186066546785379319 145355847279099820178068979)
        ·
          refine ⟨218033770918649730267103469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145355847279099820178068979 218033770918649730267103469)
          ·
            refine ⟨81762664094493648850163801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218033770918649730267103469 81762664094493648850163801)
            ·
              refine ⟨61321998070870236637622851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81762664094493648850163801 61321998070870236637622851)
              ·
                refine ⟨91982997106305354956434277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61321998070870236637622851 91982997106305354956434277)
                ·
                  refine ⟨17246811957432254054331427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91982997106305354956434277 17246811957432254054331427)
                  ·
                    refine ⟨25870217936148381081497141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17246811957432254054331427 25870217936148381081497141)
                    ·
                      refine ⟨2425332931513910726390357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25870217936148381081497141 2425332931513910726390357)
                      ·
                        rfl

theorem cell23_4723319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_4723319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723319 prefixEnd_4723319 := by exact prefixLift 4723319
  have htrace : WordTrace (prefixWord ++ tailWord_4723319) baseStart_4723319 baseEnd_4723319 := by
    simpa [prefixWord, tailWord_4723319, baseEnd_4723319] using wordTrace_append hprefix tailTrace_4723319
  have hstable : (prefixWord ++ tailWord_4723319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723319).length < 2 ^ (prefixWord ++ tailWord_4723319).sum := by decide
  have hdescent : baseEnd_4723319 < baseStart_4723319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723333 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 1, 4, 2]
def baseStart_4723333 : Nat := 118140960795 + 4723333 * 2 ^ 59
def prefixEnd_4723333 : Nat := 4983230072969 + 3 ^ 40 * 4723333 * 2
def baseEnd_4723333 : Nat := 2425340120243073671615293

theorem tailTrace_4723333 : CollatzResearch.WordTrace tailWord_4723333 prefixEnd_4723333 2425340120243073671615293 := by
  unfold tailWord_4723333
  simp only [CollatzResearch.WordTrace]
  refine ⟨172274107397178696898350653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114849404931452464598900435 172274107397178696898350653)
  ·
    refine ⟨64602790273942011336881495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172274107397178696898350653 64602790273942011336881495)
    ·
      refine ⟨96904185410913017005322243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64602790273942011336881495 96904185410913017005322243)
      ·
        refine ⟨145356278116369525507983365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96904185410913017005322243 145356278116369525507983365)
        ·
          refine ⟨27254302146819286032746881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145356278116369525507983365 27254302146819286032746881)
          ·
            refine ⟨20440726610114464524560161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27254302146819286032746881 20440726610114464524560161)
            ·
              refine ⟨15330544957585848393420121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20440726610114464524560161 15330544957585848393420121)
              ·
                refine ⟨11497908718189386295065091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15330544957585848393420121 11497908718189386295065091)
                ·
                  refine ⟨17246863077284079442597637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11497908718189386295065091 17246863077284079442597637)
                  ·
                    refine ⟨3233786826990764895487057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17246863077284079442597637 3233786826990764895487057)
                    ·
                      refine ⟨2425340120243073671615293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3233786826990764895487057 2425340120243073671615293)
                      ·
                        rfl

theorem cell23_4723333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_4723333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723333 prefixEnd_4723333 := by exact prefixLift 4723333
  have htrace : WordTrace (prefixWord ++ tailWord_4723333) baseStart_4723333 baseEnd_4723333 := by
    simpa [prefixWord, tailWord_4723333, baseEnd_4723333] using wordTrace_append hprefix tailTrace_4723333
  have hstable : (prefixWord ++ tailWord_4723333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723333).length < 2 ^ (prefixWord ++ tailWord_4723333).sum := by decide
  have hdescent : baseEnd_4723333 < baseStart_4723333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723356 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 7]
def baseStart_4723356 : Nat := 118140960795 + 4723356 * 2 ^ 59
def prefixEnd_4723356 : Nat := 4983230072969 + 3 ^ 40 * 4723356 * 2
def baseEnd_4723356 : Nat := 269483547810903009069743

theorem tailTrace_4723356 : CollatzResearch.WordTrace tailWord_4723356 prefixEnd_4723356 269483547810903009069743 := by
  unfold tailWord_4723356
  simp only [CollatzResearch.WordTrace]
  refine ⟨86137473138047685913218961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114849964184063581217625281 86137473138047685913218961)
  ·
    refine ⟨64603104853535764434914221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86137473138047685913218961 64603104853535764434914221)
    ·
      refine ⟨24226164320075911663092833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64603104853535764434914221 24226164320075911663092833)
      ·
        refine ⟨18169623240056933747319625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24226164320075911663092833 18169623240056933747319625)
        ·
          refine ⟨13627217430042700310489719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18169623240056933747319625 13627217430042700310489719)
          ·
            refine ⟨20440826145064050465734579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13627217430042700310489719 20440826145064050465734579)
            ·
              refine ⟨30661239217596075698601869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20440826145064050465734579 30661239217596075698601869)
              ·
                refine ⟨11497964706598528386975701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30661239217596075698601869 11497964706598528386975701)
                ·
                  refine ⟨269483547810903009069743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11497964706598528386975701 269483547810903009069743)
                  ·
                    rfl

theorem cell23_4723356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_4723356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723356 prefixEnd_4723356 := by exact prefixLift 4723356
  have htrace : WordTrace (prefixWord ++ tailWord_4723356) baseStart_4723356 baseEnd_4723356 := by
    simpa [prefixWord, tailWord_4723356, baseEnd_4723356] using wordTrace_append hprefix tailTrace_4723356
  have hstable : (prefixWord ++ tailWord_4723356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723356).length < 2 ^ (prefixWord ++ tailWord_4723356).sum := by decide
  have hdescent : baseEnd_4723356 < baseStart_4723356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723369 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 1, 7]
def baseStart_4723369 : Nat := 118140960795 + 4723369 * 2 ^ 59
def prefixEnd_4723369 : Nat := 4983230072969 + 3 ^ 40 * 4723369 * 2
def baseEnd_4723369 : Nat := 808452868515545176921709

theorem tailTrace_4723369 : CollatzResearch.WordTrace tailWord_4723369 prefixEnd_4723369 808452868515545176921709 := by
  unfold tailWord_4723369
  simp only [CollatzResearch.WordTrace]
  refine ⟨172275420425048275046661161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114850280283365516697774107 172275420425048275046661161)
  ·
    refine ⟨129206565318786206284995871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172275420425048275046661161 129206565318786206284995871)
    ·
      refine ⟨193809847978179309427493807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129206565318786206284995871 193809847978179309427493807)
      ·
        refine ⟨290714771967268964141240711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193809847978179309427493807 290714771967268964141240711)
        ·
          refine ⟨436072157950903446211861067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290714771967268964141240711 436072157950903446211861067)
          ·
            refine ⟨654108236926355169317791601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436072157950903446211861067 654108236926355169317791601)
            ·
              refine ⟨490581177694766376988343701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 654108236926355169317791601 490581177694766376988343701)
              ·
                refine ⟨22995992704442173921328611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 490581177694766376988343701 22995992704442173921328611)
                ·
                  refine ⟨34493989056663260881992917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22995992704442173921328611 34493989056663260881992917)
                  ·
                    refine ⟨808452868515545176921709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34493989056663260881992917 808452868515545176921709)
                    ·
                      rfl

theorem cell23_4723369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_4723369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723369 prefixEnd_4723369 := by exact prefixLift 4723369
  have htrace : WordTrace (prefixWord ++ tailWord_4723369) baseStart_4723369 baseEnd_4723369 := by
    simpa [prefixWord, tailWord_4723369, baseEnd_4723369] using wordTrace_append hprefix tailTrace_4723369
  have hstable : (prefixWord ++ tailWord_4723369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723369).length < 2 ^ (prefixWord ++ tailWord_4723369).sum := by decide
  have hdescent : baseEnd_4723369 < baseStart_4723369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723386 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_4723386 : Nat := 118140960795 + 4723386 * 2 ^ 59
def prefixEnd_4723386 : Nat := 4983230072969 + 3 ^ 40 * 4723386 * 2
def baseEnd_4723386 : Nat := 808455778239253988084183

theorem tailTrace_4723386 : CollatzResearch.WordTrace tailWord_4723386 prefixEnd_4723386 808455778239253988084183 := by
  unfold tailWord_4723386
  simp only [CollatzResearch.WordTrace]
  refine ⟨43069010116496671737507503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114850693643991124633353341 43069010116496671737507503)
  ·
    refine ⟨64603515174745007606261255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43069010116496671737507503 64603515174745007606261255)
    ·
      refine ⟨96905272762117511409391883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64603515174745007606261255 96905272762117511409391883)
      ·
        refine ⟨145357909143176267114087825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96905272762117511409391883 145357909143176267114087825)
        ·
          refine ⟨109018431857382200335565869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145357909143176267114087825 109018431857382200335565869)
          ·
            refine ⟨40881911946518325125837201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109018431857382200335565869 40881911946518325125837201)
            ·
              refine ⟨30661433959888743844377901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40881911946518325125837201 30661433959888743844377901)
              ·
                refine ⟨11498037734958278941641713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30661433959888743844377901 11498037734958278941641713)
                ·
                  refine ⟨8623528301218709206231285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11498037734958278941641713 8623528301218709206231285)
                  ·
                    refine ⟨808455778239253988084183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8623528301218709206231285 808455778239253988084183)
                    ·
                      rfl

theorem cell23_4723386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_4723386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723386 prefixEnd_4723386 := by exact prefixLift 4723386
  have htrace : WordTrace (prefixWord ++ tailWord_4723386) baseStart_4723386 baseEnd_4723386 := by
    simpa [prefixWord, tailWord_4723386, baseEnd_4723386] using wordTrace_append hprefix tailTrace_4723386
  have hstable : (prefixWord ++ tailWord_4723386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723386).length < 2 ^ (prefixWord ++ tailWord_4723386).sum := by decide
  have hdescent : baseEnd_4723386 < baseStart_4723386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723463 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 6]
def baseStart_4723463 : Nat := 118140960795 + 4723463 * 2 ^ 59
def prefixEnd_4723463 : Nat := 4983230072969 + 3 ^ 40 * 4723463 * 2
def baseEnd_4723463 : Nat := 269489652525350906998855

theorem tailTrace_4723463 : CollatzResearch.WordTrace tailWord_4723463 prefixEnd_4723463 269489652525350906998855 := by
  unfold tailWord_4723463
  simp only [CollatzResearch.WordTrace]
  refine ⟨172278848886707729100583043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114852565924471819400388695 172278848886707729100583043)
  ·
    refine ⟨258418273330061593650874565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172278848886707729100583043 258418273330061593650874565)
    ·
      refine ⟨48453426249386548809538981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 258418273330061593650874565 48453426249386548809538981)
      ·
        refine ⟨9085017421759977901788559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48453426249386548809538981 9085017421759977901788559)
        ·
          refine ⟨13627526132639966852682839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9085017421759977901788559 13627526132639966852682839)
          ·
            refine ⟨20441289198959950279024259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13627526132639966852682839 20441289198959950279024259)
            ·
              refine ⟨30661933798439925418536389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20441289198959950279024259 30661933798439925418536389)
              ·
                refine ⟨5749112587207486015975573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30661933798439925418536389 5749112587207486015975573)
                ·
                  refine ⟨269489652525350906998855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5749112587207486015975573 269489652525350906998855)
                  ·
                    rfl

theorem cell23_4723463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 6].length) (baseStart_4723463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723463 prefixEnd_4723463 := by exact prefixLift 4723463
  have htrace : WordTrace (prefixWord ++ tailWord_4723463) baseStart_4723463 baseEnd_4723463 := by
    simpa [prefixWord, tailWord_4723463, baseEnd_4723463] using wordTrace_append hprefix tailTrace_4723463
  have hstable : (prefixWord ++ tailWord_4723463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723463).length < 2 ^ (prefixWord ++ tailWord_4723463).sum := by decide
  have hdescent : baseEnd_4723463 < baseStart_4723463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723466 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4723466 : Nat := 118140960795 + 4723466 * 2 ^ 59
def prefixEnd_4723466 : Nat := 4983230072969 + 3 ^ 40 * 4723466 * 2
def baseEnd_4723466 : Nat := 2425408413170121651252181

theorem tailTrace_4723466 : CollatzResearch.WordTrace tailWord_4723466 prefixEnd_4723466 2425408413170121651252181 := by
  unfold tailWord_4723466
  simp only [CollatzResearch.WordTrace]
  refine ⟨43069739576424215153235563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114852638870464573741961501 43069739576424215153235563)
  ·
    refine ⟨64604609364636322729853345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43069739576424215153235563 64604609364636322729853345)
    ·
      refine ⟨48453457023477242047390009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64604609364636322729853345 48453457023477242047390009)
      ·
        refine ⟨36340092767607931535542507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48453457023477242047390009 36340092767607931535542507)
        ·
          refine ⟨54510139151411897303313761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36340092767607931535542507 54510139151411897303313761)
          ·
            refine ⟨40882604363558922977485321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54510139151411897303313761 40882604363558922977485321)
            ·
              refine ⟨30661953272669192233113991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40882604363558922977485321 30661953272669192233113991)
              ·
                refine ⟨45992929909003788349670987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30661953272669192233113991 45992929909003788349670987)
                ·
                  refine ⟨68989394863505682524506481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45992929909003788349670987 68989394863505682524506481)
                  ·
                    refine ⟨51742046147629261893379861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68989394863505682524506481 51742046147629261893379861)
                    ·
                      refine ⟨2425408413170121651252181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51742046147629261893379861 2425408413170121651252181)
                      ·
                        rfl

theorem cell23_4723466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4723466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723466 prefixEnd_4723466 := by exact prefixLift 4723466
  have htrace : WordTrace (prefixWord ++ tailWord_4723466) baseStart_4723466 baseEnd_4723466 := by
    simpa [prefixWord, tailWord_4723466, baseEnd_4723466] using wordTrace_append hprefix tailTrace_4723466
  have hstable : (prefixWord ++ tailWord_4723466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723466).length < 2 ^ (prefixWord ++ tailWord_4723466).sum := by decide
  have hdescent : baseEnd_4723466 < baseStart_4723466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723490 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_4723490 : Nat := 118140960795 + 4723490 * 2 ^ 59
def prefixEnd_4723490 : Nat := 4983230072969 + 3 ^ 40 * 4723490 * 2
def baseEnd_4723490 : Nat := 2425420736705829557352071

theorem tailTrace_4723490 : CollatzResearch.WordTrace tailWord_4723490 prefixEnd_4723490 2425420736705829557352071 := by
  unfold tailWord_4723490
  simp only [CollatzResearch.WordTrace]
  refine ⟨43069958414402478177953981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114853222438406608474543949 43069958414402478177953981)
  ·
    refine ⟨16151234405400929316732743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43069958414402478177953981 16151234405400929316732743)
    ·
      refine ⟨24226851608101393975099115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16151234405400929316732743 24226851608101393975099115)
      ·
        refine ⟨36340277412152090962648673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24226851608101393975099115 36340277412152090962648673)
        ·
          refine ⟨27255208059114068221986505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36340277412152090962648673 27255208059114068221986505)
          ·
            refine ⟨20441406044335551166489879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27255208059114068221986505 20441406044335551166489879)
            ·
              refine ⟨30662109066503326749734819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20441406044335551166489879 30662109066503326749734819)
              ·
                refine ⟨45993163599754990124602229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30662109066503326749734819 45993163599754990124602229)
                ·
                  refine ⟨4311859087477030324181459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45993163599754990124602229 4311859087477030324181459)
                  ·
                    refine ⟨6467788631215545486272189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4311859087477030324181459 6467788631215545486272189)
                    ·
                      refine ⟨2425420736705829557352071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6467788631215545486272189 2425420736705829557352071)
                      ·
                        rfl

theorem cell23_4723490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_4723490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723490 prefixEnd_4723490 := by exact prefixLift 4723490
  have htrace : WordTrace (prefixWord ++ tailWord_4723490) baseStart_4723490 baseEnd_4723490 := by
    simpa [prefixWord, tailWord_4723490, baseEnd_4723490] using wordTrace_append hprefix tailTrace_4723490
  have hstable : (prefixWord ++ tailWord_4723490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723490).length < 2 ^ (prefixWord ++ tailWord_4723490).sum := by decide
  have hdescent : baseEnd_4723490 < baseStart_4723490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723493 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_4723493 : Nat := 118140960795 + 4723493 * 2 ^ 59
def prefixEnd_4723493 : Nat := 4983230072969 + 3 ^ 40 * 4723493 * 2
def baseEnd_4723493 : Nat := 808474092382597681871519

theorem tailTrace_4723493 : CollatzResearch.WordTrace tailWord_4723493 prefixEnd_4723493 808474092382597681871519 := by
  unfold tailWord_4723493
  simp only [CollatzResearch.WordTrace]
  refine ⟨172279943076599044224175133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114853295384399362816116755 172279943076599044224175133)
  ·
    refine ⟨64604978653724641584065675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172279943076599044224175133 64604978653724641584065675)
    ·
      refine ⟨96907467980586962376098513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64604978653724641584065675 96907467980586962376098513)
      ·
        refine ⟨72680600985440221782073885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96907467980586962376098513 72680600985440221782073885)
        ·
          refine ⟨27255225369540083168277707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72680600985440221782073885 27255225369540083168277707)
          ·
            refine ⟨40882838054310124752416561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27255225369540083168277707 40882838054310124752416561)
            ·
              refine ⟨30662128540732593564312421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40882838054310124752416561 30662128540732593564312421)
              ·
                refine ⟨5749149101387361293308579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30662128540732593564312421 5749149101387361293308579)
                ·
                  refine ⟨8623723652081041939962869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5749149101387361293308579 8623723652081041939962869)
                  ·
                    refine ⟨808474092382597681871519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8623723652081041939962869 808474092382597681871519)
                    ·
                      rfl

theorem cell23_4723493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_4723493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723493 prefixEnd_4723493 := by exact prefixLift 4723493
  have htrace : WordTrace (prefixWord ++ tailWord_4723493) baseStart_4723493 baseEnd_4723493 := by
    simpa [prefixWord, tailWord_4723493, baseEnd_4723493] using wordTrace_append hprefix tailTrace_4723493
  have hstable : (prefixWord ++ tailWord_4723493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723493).length < 2 ^ (prefixWord ++ tailWord_4723493).sum := by decide
  have hdescent : baseEnd_4723493 < baseStart_4723493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723501 : List Nat := [1, 5, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_4723501 : Nat := 118140960795 + 4723501 * 2 ^ 59
def prefixEnd_4723501 : Nat := 4983230072969 + 3 ^ 40 * 4723501 * 2
def baseEnd_4723501 : Nat := 808475461664343004771507

theorem tailTrace_4723501 : CollatzResearch.WordTrace tailWord_4723501 prefixEnd_4723501 808475461664343004771507 := by
  unfold tailWord_4723501
  simp only [CollatzResearch.WordTrace]
  refine ⟨172280234860570061590466357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114853489907046707726977571 172280234860570061590466357)
  ·
    refine ⟨16151272018178443274106221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172280234860570061590466357 16151272018178443274106221)
    ·
      refine ⟨6056727006816916227789833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16151272018178443274106221 6056727006816916227789833)
      ·
        refine ⟨4542545255112687170842375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6056727006816916227789833 4542545255112687170842375)
        ·
          refine ⟨6813817882669030756263563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542545255112687170842375 6813817882669030756263563)
          ·
            refine ⟨10220726824003546134395345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6813817882669030756263563 10220726824003546134395345)
            ·
              refine ⟨7665545118002659600796509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10220726824003546134395345 7665545118002659600796509)
              ·
                refine ⟨2874579419250997350298691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7665545118002659600796509 2874579419250997350298691)
                ·
                  refine ⟨4311869128876496025448037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874579419250997350298691 4311869128876496025448037)
                  ·
                    refine ⟨808475461664343004771507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4311869128876496025448037 808475461664343004771507)
                    ·
                      rfl

theorem cell23_4723501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_4723501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723501 prefixEnd_4723501 := by exact prefixLift 4723501
  have htrace : WordTrace (prefixWord ++ tailWord_4723501) baseStart_4723501 baseEnd_4723501 := by
    simpa [prefixWord, tailWord_4723501, baseEnd_4723501] using wordTrace_append hprefix tailTrace_4723501
  have hstable : (prefixWord ++ tailWord_4723501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723501).length < 2 ^ (prefixWord ++ tailWord_4723501).sum := by decide
  have hdescent : baseEnd_4723501 < baseStart_4723501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723507 : List Nat := [1, 1, 1, 2, 6, 1, 1, 5, 1, 1, 3]
def baseStart_4723507 : Nat := 118140960795 + 4723507 * 2 ^ 59
def prefixEnd_4723507 : Nat := 4983230072969 + 3 ^ 40 * 4723507 * 2
def baseEnd_4723507 : Nat := 2425429465876955990839493

theorem tailTrace_4723507 : CollatzResearch.WordTrace tailWord_4723507 prefixEnd_4723507 2425429465876955990839493 := by
  unfold tailWord_4723507
  simp only [CollatzResearch.WordTrace]
  refine ⟨172280453698548324615184775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114853635799032216410123183 172280453698548324615184775)
  ·
    refine ⟨258420680547822486922777163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172280453698548324615184775 258420680547822486922777163)
    ·
      refine ⟨387631020821733730384165745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258420680547822486922777163 387631020821733730384165745)
      ·
        refine ⟨290723265616300297788124309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387631020821733730384165745 290723265616300297788124309)
        ·
          refine ⟨13627653075764076458818327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 290723265616300297788124309 13627653075764076458818327)
          ·
            refine ⟨20441479613646114688227491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13627653075764076458818327 20441479613646114688227491)
            ·
              refine ⟨30662219420469172032341237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20441479613646114688227491 30662219420469172032341237)
              ·
                refine ⟨2874583070668984878031991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30662219420469172032341237 2874583070668984878031991)
                ·
                  refine ⟨4311874606003477317047987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874583070668984878031991 4311874606003477317047987)
                  ·
                    refine ⟨6467811909005215975571981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4311874606003477317047987 6467811909005215975571981)
                    ·
                      refine ⟨2425429465876955990839493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6467811909005215975571981 2425429465876955990839493)
                      ·
                        rfl

theorem cell23_4723507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 1, 1, 3].length) (baseStart_4723507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723507 prefixEnd_4723507 := by exact prefixLift 4723507
  have htrace : WordTrace (prefixWord ++ tailWord_4723507) baseStart_4723507 baseEnd_4723507 := by
    simpa [prefixWord, tailWord_4723507, baseEnd_4723507] using wordTrace_append hprefix tailTrace_4723507
  have hstable : (prefixWord ++ tailWord_4723507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723507).length < 2 ^ (prefixWord ++ tailWord_4723507).sum := by decide
  have hdescent : baseEnd_4723507 < baseStart_4723507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723523 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 4, 4]
def baseStart_4723523 : Nat := 118140960795 + 4723523 * 2 ^ 59
def prefixEnd_4723523 : Nat := 4983230072969 + 3 ^ 40 * 4723523 * 2
def baseEnd_4723523 : Nat := 808479227189142642746473

theorem tailTrace_4723523 : CollatzResearch.WordTrace tailWord_4723523 prefixEnd_4723523 808479227189142642746473 := by
  unfold tailWord_4723523
  simp only [CollatzResearch.WordTrace]
  refine ⟨172281037266490359347767223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114854024844326906231844815 172281037266490359347767223)
  ·
    refine ⟨258421555899735539021650835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172281037266490359347767223 258421555899735539021650835)
    ·
      refine ⟨387632333849603308532476253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258421555899735539021650835 387632333849603308532476253)
      ·
        refine ⟨145362125193601240699678595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 387632333849603308532476253 145362125193601240699678595)
        ·
          refine ⟨218043187790401861049517893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145362125193601240699678595 218043187790401861049517893)
          ·
            refine ⟨40883097710700348946784605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218043187790401861049517893 40883097710700348946784605)
            ·
              refine ⟨15331161641512630855044227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40883097710700348946784605 15331161641512630855044227)
              ·
                refine ⟨22996742462268946282566341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15331161641512630855044227 22996742462268946282566341)
                ·
                  refine ⟨4311889211675427427981189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22996742462268946282566341 4311889211675427427981189)
                  ·
                    refine ⟨808479227189142642746473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4311889211675427427981189 808479227189142642746473)
                    ·
                      rfl

theorem cell23_4723523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 4].length) (baseStart_4723523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723523 prefixEnd_4723523 := by exact prefixLift 4723523
  have htrace : WordTrace (prefixWord ++ tailWord_4723523) baseStart_4723523 baseEnd_4723523 := by
    simpa [prefixWord, tailWord_4723523, baseEnd_4723523] using wordTrace_append hprefix tailTrace_4723523
  have hstable : (prefixWord ++ tailWord_4723523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723523).length < 2 ^ (prefixWord ++ tailWord_4723523).sum := by decide
  have hdescent : baseEnd_4723523 < baseStart_4723523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723543 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_4723543 : Nat := 118140960795 + 4723543 * 2 ^ 59
def prefixEnd_4723543 : Nat := 4983230072969 + 3 ^ 40 * 4723543 * 2
def baseEnd_4723543 : Nat := 2425447951180517849989327

theorem tailTrace_4723543 : CollatzResearch.WordTrace tailWord_4723543 prefixEnd_4723543 2425447951180517849989327 := by
  unfold tailWord_4723543
  simp only [CollatzResearch.WordTrace]
  refine ⟨172281766726417902763495283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114854511150945268508996855 172281766726417902763495283)
  ·
    refine ⟨258422650089626854145242925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172281766726417902763495283 258422650089626854145242925)
    ·
      refine ⟨96908493783610070304466097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258422650089626854145242925 96908493783610070304466097)
      ·
        refine ⟨72681370337707552728349573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96908493783610070304466097 72681370337707552728349573)
        ·
          refine ⟨13627756938320166136565545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72681370337707552728349573 13627756938320166136565545)
          ·
            refine ⟨10220817703740124602424159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13627756938320166136565545 10220817703740124602424159)
            ·
              refine ⟨15331226555610186903636239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10220817703740124602424159 15331226555610186903636239)
              ·
                refine ⟨22996839833415280355454359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15331226555610186903636239 22996839833415280355454359)
                ·
                  refine ⟨34495259750122920533181539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22996839833415280355454359 34495259750122920533181539)
                  ·
                    refine ⟨51742889625184380799772309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34495259750122920533181539 51742889625184380799772309)
                    ·
                      refine ⟨2425447951180517849989327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51742889625184380799772309 2425447951180517849989327)
                      ·
                        rfl

theorem cell23_4723543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_4723543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723543 prefixEnd_4723543 := by exact prefixLift 4723543
  have htrace : WordTrace (prefixWord ++ tailWord_4723543) baseStart_4723543 baseEnd_4723543 := by
    simpa [prefixWord, tailWord_4723543, baseEnd_4723543] using wordTrace_append hprefix tailTrace_4723543
  have hstable : (prefixWord ++ tailWord_4723543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723543).length < 2 ^ (prefixWord ++ tailWord_4723543).sum := by decide
  have hdescent : baseEnd_4723543 < baseStart_4723543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723563 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 3]
def baseStart_4723563 : Nat := 118140960795 + 4723563 * 2 ^ 59
def prefixEnd_4723563 : Nat := 4983230072969 + 3 ^ 40 * 4723563 * 2
def baseEnd_4723563 : Nat := 2425458220793607771739235

theorem tailTrace_4723563 : CollatzResearch.WordTrace tailWord_4723563 prefixEnd_4723563 2425458220793607771739235 := by
  unfold tailWord_4723563
  simp only [CollatzResearch.WordTrace]
  refine ⟨172282496186345446179223343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114854997457563630786148895 172282496186345446179223343)
  ·
    refine ⟨258423744279518169268835015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172282496186345446179223343 258423744279518169268835015)
    ·
      refine ⟨387635616419277253903252523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258423744279518169268835015 387635616419277253903252523)
      ·
        refine ⟨581453424628915880854878785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387635616419277253903252523 581453424628915880854878785)
        ·
          refine ⟨436090068471686910641159089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581453424628915880854878785 436090068471686910641159089)
          ·
            refine ⟨327067551353765182980869317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436090068471686910641159089 327067551353765182980869317)
            ·
              refine ⟨61325165878830971808912997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327067551353765182980869317 61325165878830971808912997)
              ·
                refine ⟨11498468602280807214171187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61325165878830971808912997 11498468602280807214171187)
                ·
                  refine ⟨17247702903421210821256781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11498468602280807214171187 17247702903421210821256781)
                  ·
                    refine ⟨6467888588782954057971293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17247702903421210821256781 6467888588782954057971293)
                    ·
                      refine ⟨2425458220793607771739235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6467888588782954057971293 2425458220793607771739235)
                      ·
                        rfl

theorem cell23_4723563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 3].length) (baseStart_4723563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723563 prefixEnd_4723563 := by exact prefixLift 4723563
  have htrace : WordTrace (prefixWord ++ tailWord_4723563) baseStart_4723563 baseEnd_4723563 := by
    simpa [prefixWord, tailWord_4723563, baseEnd_4723563] using wordTrace_append hprefix tailTrace_4723563
  have hstable : (prefixWord ++ tailWord_4723563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723563).length < 2 ^ (prefixWord ++ tailWord_4723563).sum := by decide
  have hdescent : baseEnd_4723563 < baseStart_4723563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723677 : List Nat := [1, 4, 3, 1, 2, 1, 1, 5, 5]
def baseStart_4723677 : Nat := 118140960795 + 4723677 * 2 ^ 59
def prefixEnd_4723677 : Nat := 4983230072969 + 3 ^ 40 * 4723677 * 2
def baseEnd_4723677 : Nat := 269501861954246702857079

theorem tailTrace_4723677 : CollatzResearch.WordTrace tailWord_4723677 prefixEnd_4723677 269501861954246702857079 := by
  unfold tailWord_4723677
  simp only [CollatzResearch.WordTrace]
  refine ⟨172286654107932443648873285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114857769405288295765915523 172286654107932443648873285)
  ·
    refine ⟨32303747645237333184163741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172286654107932443648873285 32303747645237333184163741)
    ·
      refine ⟨12113905366963999944061403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32303747645237333184163741 12113905366963999944061403)
      ·
        refine ⟨18170858050445999916092105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12113905366963999944061403 18170858050445999916092105)
        ·
          refine ⟨13628143537834499937069079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18170858050445999916092105 13628143537834499937069079)
          ·
            refine ⟨20442215306751749905603619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13628143537834499937069079 20442215306751749905603619)
            ·
              refine ⟨30663322960127624858405429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20442215306751749905603619 30663322960127624858405429)
              ·
                refine ⟨2874686527511964830475509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30663322960127624858405429 2874686527511964830475509)
                ·
                  refine ⟨269501861954246702857079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2874686527511964830475509 269501861954246702857079)
                  ·
                    rfl

theorem cell23_4723677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_4723677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723677 prefixEnd_4723677 := by exact prefixLift 4723677
  have htrace : WordTrace (prefixWord ++ tailWord_4723677) baseStart_4723677 baseEnd_4723677 := by
    simpa [prefixWord, tailWord_4723677, baseEnd_4723677] using wordTrace_append hprefix tailTrace_4723677
  have hstable : (prefixWord ++ tailWord_4723677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723677).length < 2 ^ (prefixWord ++ tailWord_4723677).sum := by decide
  have hdescent : baseEnd_4723677 < baseStart_4723677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723744 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 2, 1, 4]
def baseStart_4723744 : Nat := 118140960795 + 4723744 * 2 ^ 59
def prefixEnd_4723744 : Nat := 4983230072969 + 3 ^ 40 * 4723744 * 2
def baseEnd_4723744 : Nat := 2425551160792071563575903

theorem tailTrace_4723744 : CollatzResearch.WordTrace tailWord_4723744 prefixEnd_4723744 2425551160792071563575903 := by
  unfold tailWord_4723744
  simp only [CollatzResearch.WordTrace]
  refine ⟨86144548899344857045781143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114859398532459809394374857 86144548899344857045781143)
  ·
    refine ⟨129216823349017285568671715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86144548899344857045781143 129216823349017285568671715)
    ·
      refine ⟨193825235023525928353007573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129216823349017285568671715 193825235023525928353007573)
      ·
        refine ⟨4542778945863888945773615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 193825235023525928353007573 4542778945863888945773615)
        ·
          refine ⟨6814168418795833418660423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542778945863888945773615 6814168418795833418660423)
          ·
            refine ⟨10221252628193750127990635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6814168418795833418660423 10221252628193750127990635)
            ·
              refine ⟨15331878942290625191985953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10221252628193750127990635 15331878942290625191985953)
              ·
                refine ⟨11498909206717968893989465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15331878942290625191985953 11498909206717968893989465)
                ·
                  refine ⟨8624181905038476670492099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11498909206717968893989465 8624181905038476670492099)
                  ·
                    refine ⟨12936272857557715005738149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8624181905038476670492099 12936272857557715005738149)
                    ·
                      refine ⟨2425551160792071563575903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12936272857557715005738149 2425551160792071563575903)
                      ·
                        rfl

theorem cell23_4723744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_4723744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723744 prefixEnd_4723744 := by exact prefixLift 4723744
  have htrace : WordTrace (prefixWord ++ tailWord_4723744) baseStart_4723744 baseEnd_4723744 := by
    simpa [prefixWord, tailWord_4723744, baseEnd_4723744] using wordTrace_append hprefix tailTrace_4723744
  have hstable : (prefixWord ++ tailWord_4723744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723744).length < 2 ^ (prefixWord ++ tailWord_4723744).sum := by decide
  have hdescent : baseEnd_4723744 < baseStart_4723744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723747 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 3]
def baseStart_4723747 : Nat := 118140960795 + 4723747 * 2 ^ 59
def prefixEnd_4723747 : Nat := 4983230072969 + 3 ^ 40 * 4723747 * 2
def baseEnd_4723747 : Nat := 2425552701234035051838389

theorem tailTrace_4723747 : CollatzResearch.WordTrace tailWord_4723747 prefixEnd_4723747 2425552701234035051838389 := by
  unfold tailWord_4723747
  simp only [CollatzResearch.WordTrace]
  refine ⟨172289207217678845603921495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114859471478452563735947663 172289207217678845603921495)
  ·
    refine ⟨258433810826518268405882243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172289207217678845603921495 258433810826518268405882243)
    ·
      refine ⟨387650716239777402608823365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258433810826518268405882243 387650716239777402608823365)
      ·
        refine ⟨72684509294958262989154381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387650716239777402608823365 72684509294958262989154381)
        ·
          refine ⟨27256690985609348620932893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72684509294958262989154381 27256690985609348620932893)
          ·
            refine ⟨10221259119603505732849835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27256690985609348620932893 10221259119603505732849835)
            ·
              refine ⟨15331888679405258599274753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10221259119603505732849835 15331888679405258599274753)
              ·
                refine ⟨11498916509553943949456065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15331888679405258599274753 11498916509553943949456065)
                ·
                  refine ⟨8624187382165457962092049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11498916509553943949456065 8624187382165457962092049)
                  ·
                    refine ⟨6468140536624093471569037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8624187382165457962092049 6468140536624093471569037)
                    ·
                      refine ⟨2425552701234035051838389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6468140536624093471569037 2425552701234035051838389)
                      ·
                        rfl

theorem cell23_4723747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_4723747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723747 prefixEnd_4723747 := by exact prefixLift 4723747
  have htrace : WordTrace (prefixWord ++ tailWord_4723747) baseStart_4723747 baseEnd_4723747 := by
    simpa [prefixWord, tailWord_4723747, baseEnd_4723747] using wordTrace_append hprefix tailTrace_4723747
  have hstable : (prefixWord ++ tailWord_4723747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723747).length < 2 ^ (prefixWord ++ tailWord_4723747).sum := by decide
  have hdescent : baseEnd_4723747 < baseStart_4723747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723763 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 2, 9]
def baseStart_4723763 : Nat := 118140960795 + 4723763 * 2 ^ 59
def prefixEnd_4723763 : Nat := 4983230072969 + 3 ^ 40 * 4723763 * 2
def baseEnd_4723763 : Nat := 808520305641502329746105

theorem tailTrace_4723763 : CollatzResearch.WordTrace tailWord_4723763 prefixEnd_4723763 808520305641502329746105 := by
  unfold tailWord_4723763
  simp only [CollatzResearch.WordTrace]
  refine ⟨172289790785620880336503943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114859860523747253557669295 172289790785620880336503943)
  ·
    refine ⟨258434686178431320504755915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172289790785620880336503943 258434686178431320504755915)
    ·
      refine ⟨387652029267646980757133873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258434686178431320504755915 387652029267646980757133873)
      ·
        refine ⟨290739021950735235567850405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387652029267646980757133873 290739021950735235567850405)
        ·
          refine ⟨54513566615762856668971951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290739021950735235567850405 54513566615762856668971951)
          ·
            refine ⟨81770349923644285003457927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54513566615762856668971951 81770349923644285003457927)
            ·
              refine ⟨122655524885466427505186891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81770349923644285003457927 122655524885466427505186891)
              ·
                refine ⟨183983287328199641257780337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122655524885466427505186891 183983287328199641257780337)
                ·
                  refine ⟨137987465496149730943335253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183983287328199641257780337 137987465496149730943335253)
                  ·
                    refine ⟨808520305641502329746105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 137987465496149730943335253 808520305641502329746105)
                    ·
                      rfl

theorem cell23_4723763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 9].length) (baseStart_4723763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723763 prefixEnd_4723763 := by exact prefixLift 4723763
  have htrace : WordTrace (prefixWord ++ tailWord_4723763) baseStart_4723763 baseEnd_4723763 := by
    simpa [prefixWord, tailWord_4723763, baseEnd_4723763] using wordTrace_append hprefix tailTrace_4723763
  have hstable : (prefixWord ++ tailWord_4723763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723763).length < 2 ^ (prefixWord ++ tailWord_4723763).sum := by decide
  have hdescent : baseEnd_4723763 < baseStart_4723763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723804 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_4723804 : Nat := 118140960795 + 4723804 * 2 ^ 59
def prefixEnd_4723804 : Nat := 4983230072969 + 3 ^ 40 * 4723804 * 2
def baseEnd_4723804 : Nat := 2425581969631341328825627

theorem tailTrace_4723804 : CollatzResearch.WordTrace tailWord_4723804 prefixEnd_4723804 2425581969631341328825627 := by
  unfold tailWord_4723804
  simp only [CollatzResearch.WordTrace]
  refine ⟨86145643089236172169373233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114860857452314896225830977 86145643089236172169373233)
  ·
    refine ⟨64609232316927129127029925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86145643089236172169373233 64609232316927129127029925)
    ·
      refine ⟨12114231059423836711318111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64609232316927129127029925 12114231059423836711318111)
      ·
        refine ⟨18171346589135755066977167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12114231059423836711318111 18171346589135755066977167)
        ·
          refine ⟨27257019883703632600465751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18171346589135755066977167 27257019883703632600465751)
          ·
            refine ⟨40885529825555448900698627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27257019883703632600465751 40885529825555448900698627)
            ·
              refine ⟨61328294738333173351047941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40885529825555448900698627 61328294738333173351047941)
              ·
                refine ⟨11499055263437470003321489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61328294738333173351047941 11499055263437470003321489)
                ·
                  refine ⟨8624291447578102502491117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11499055263437470003321489 8624291447578102502491117)
                  ·
                    refine ⟨3234109292841788438434169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8624291447578102502491117 3234109292841788438434169)
                    ·
                      refine ⟨2425581969631341328825627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234109292841788438434169 2425581969631341328825627)
                      ·
                        rfl

theorem cell23_4723804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_4723804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723804 prefixEnd_4723804 := by exact prefixLift 4723804
  have htrace : WordTrace (prefixWord ++ tailWord_4723804) baseStart_4723804 baseEnd_4723804 := by
    simpa [prefixWord, tailWord_4723804, baseEnd_4723804] using wordTrace_append hprefix tailTrace_4723804
  have hstable : (prefixWord ++ tailWord_4723804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723804).length < 2 ^ (prefixWord ++ tailWord_4723804).sum := by decide
  have hdescent : baseEnd_4723804 < baseStart_4723804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723805 : List Nat := [1, 4, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_4723805 : Nat := 118140960795 + 4723805 * 2 ^ 59
def prefixEnd_4723805 : Nat := 4983230072969 + 3 ^ 40 * 4723805 * 2
def baseEnd_4723805 : Nat := 808527494370665274971041

theorem tailTrace_4723805 : CollatzResearch.WordTrace tailWord_4723805 prefixEnd_4723805 808527494370665274971041 := by
  unfold tailWord_4723805
  simp only [CollatzResearch.WordTrace]
  refine ⟨172291322651468721509532869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114860881767645814339688579 172291322651468721509532869)
  ·
    refine ⟨32304622997150385283037413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172291322651468721509532869 32304622997150385283037413)
    ·
      refine ⟨6057116811965697240569515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32304622997150385283037413 6057116811965697240569515)
      ·
        refine ⟨9085675217948545860854273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057116811965697240569515 9085675217948545860854273)
        ·
          refine ⟨6814256413461409395640705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9085675217948545860854273 6814256413461409395640705)
          ·
            refine ⟨5110692310096057046730529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6814256413461409395640705 5110692310096057046730529)
            ·
              refine ⟨3833019232572042785047897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5110692310096057046730529 3833019232572042785047897)
              ·
                refine ⟨2874764424429032088785923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3833019232572042785047897 2874764424429032088785923)
                ·
                  refine ⟨4312146636643548133178885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874764424429032088785923 4312146636643548133178885)
                  ·
                    refine ⟨808527494370665274971041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4312146636643548133178885 808527494370665274971041)
                    ·
                      rfl

theorem cell23_4723805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_4723805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723805 prefixEnd_4723805 := by exact prefixLift 4723805
  have htrace : WordTrace (prefixWord ++ tailWord_4723805) baseStart_4723805 baseEnd_4723805 := by
    simpa [prefixWord, tailWord_4723805, baseEnd_4723805] using wordTrace_append hprefix tailTrace_4723805
  have hstable : (prefixWord ++ tailWord_4723805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723805).length < 2 ^ (prefixWord ++ tailWord_4723805).sum := by decide
  have hdescent : baseEnd_4723805 < baseStart_4723805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723820 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 5]
def baseStart_4723820 : Nat := 118140960795 + 4723820 * 2 ^ 59
def prefixEnd_4723820 : Nat := 4983230072969 + 3 ^ 40 * 4723820 * 2
def baseEnd_4723820 : Nat := 2425590185321813266225553

theorem tailTrace_4723820 : CollatzResearch.WordTrace tailWord_4723820 prefixEnd_4723820 2425590185321813266225553 := by
  unfold tailWord_4723820
  simp only [CollatzResearch.WordTrace]
  refine ⟨86145934873207189535664457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114861246497609586047552609 86145934873207189535664457)
  ·
    refine ⟨64609451154905392151748343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86145934873207189535664457 64609451154905392151748343)
    ·
      refine ⟨96914176732358088227622515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64609451154905392151748343 96914176732358088227622515)
      ·
        refine ⟨145371265098537132341433773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96914176732358088227622515 145371265098537132341433773)
        ·
          refine ⟨54514224411951424628037665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145371265098537132341433773 54514224411951424628037665)
          ·
            refine ⟨40885668308963568471028249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54514224411951424628037665 40885668308963568471028249)
            ·
              refine ⟨30664251231722676353271187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40885668308963568471028249 30664251231722676353271187)
              ·
                refine ⟨45996376847584014529906781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30664251231722676353271187 45996376847584014529906781)
                ·
                  refine ⟨17248641317844005448715043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45996376847584014529906781 17248641317844005448715043)
                  ·
                    refine ⟨25872961976766008173072565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17248641317844005448715043 25872961976766008173072565)
                    ·
                      refine ⟨2425590185321813266225553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25872961976766008173072565 2425590185321813266225553)
                      ·
                        rfl

theorem cell23_4723820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_4723820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723820 prefixEnd_4723820 := by exact prefixLift 4723820
  have htrace : WordTrace (prefixWord ++ tailWord_4723820) baseStart_4723820 baseEnd_4723820 := by
    simpa [prefixWord, tailWord_4723820, baseEnd_4723820] using wordTrace_append hprefix tailTrace_4723820
  have hstable : (prefixWord ++ tailWord_4723820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723820).length < 2 ^ (prefixWord ++ tailWord_4723820).sum := by decide
  have hdescent : baseEnd_4723820 < baseStart_4723820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723837 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_4723837 : Nat := 118140960795 + 4723837 * 2 ^ 59
def prefixEnd_4723837 : Nat := 4983230072969 + 3 ^ 40 * 4723837 * 2
def baseEnd_4723837 : Nat := 2425598914492939699712975

theorem tailTrace_4723837 : CollatzResearch.WordTrace tailWord_4723837 prefixEnd_4723837 2425598914492939699712975 := by
  unfold tailWord_4723837
  simp only [CollatzResearch.WordTrace]
  refine ⟨172292489787352790974697765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114861659858235193983131843 172292489787352790974697765)
  ·
    refine ⟨32304841835128648307755831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172292489787352790974697765 32304841835128648307755831)
    ·
      refine ⟨48457262752692972461633747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32304841835128648307755831 48457262752692972461633747)
      ·
        refine ⟨72685894129039458692450621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48457262752692972461633747 72685894129039458692450621)
        ·
          refine ⟨27257210298389797009668983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72685894129039458692450621 27257210298389797009668983)
          ·
            refine ⟨40885815447584695514503475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27257210298389797009668983 40885815447584695514503475)
            ·
              refine ⟨61328723171377043271755213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40885815447584695514503475 61328723171377043271755213)
              ·
                refine ⟨22998271189266391226908205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61328723171377043271755213 22998271189266391226908205)
                ·
                  refine ⟨8624351695974896710090577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22998271189266391226908205 8624351695974896710090577)
                  ·
                    refine ⟨6468263771981172532567933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8624351695974896710090577 6468263771981172532567933)
                    ·
                      refine ⟨2425598914492939699712975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6468263771981172532567933 2425598914492939699712975)
                      ·
                        rfl

theorem cell23_4723837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_4723837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723837 prefixEnd_4723837 := by exact prefixLift 4723837
  have htrace : WordTrace (prefixWord ++ tailWord_4723837) baseStart_4723837 baseEnd_4723837 := by
    simpa [prefixWord, tailWord_4723837, baseEnd_4723837] using wordTrace_append hprefix tailTrace_4723837
  have hstable : (prefixWord ++ tailWord_4723837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723837).length < 2 ^ (prefixWord ++ tailWord_4723837).sum := by decide
  have hdescent : baseEnd_4723837 < baseStart_4723837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723848 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 1, 5]
def baseStart_4723848 : Nat := 118140960795 + 4723848 * 2 ^ 59
def prefixEnd_4723848 : Nat := 4983230072969 + 3 ^ 40 * 4723848 * 2
def baseEnd_4723848 : Nat := 808534854260046385558475

theorem tailTrace_4723848 : CollatzResearch.WordTrace tailWord_4723848 prefixEnd_4723848 808534854260046385558475 := by
  unfold tailWord_4723848
  simp only [CollatzResearch.WordTrace]
  refine ⟨86146445495156469926674099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114861927326875293235565465 86146445495156469926674099)
  ·
    refine ⟨129219668242734704890011149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86146445495156469926674099 129219668242734704890011149)
    ·
      refine ⟨48457375591025514333754181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129219668242734704890011149 48457375591025514333754181)
      ·
        refine ⟨9085757923317283937578909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48457375591025514333754181 9085757923317283937578909)
        ·
          refine ⟨3407159221243981476592091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9085757923317283937578909 3407159221243981476592091)
          ·
            refine ⟨5110738831865972214888137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407159221243981476592091 5110738831865972214888137)
            ·
              refine ⟨3833054123899479161166103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5110738831865972214888137 3833054123899479161166103)
              ·
                refine ⟨5749581185849218741749155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3833054123899479161166103 5749581185849218741749155)
                ·
                  refine ⟨8624371778773828112623733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5749581185849218741749155 8624371778773828112623733)
                  ·
                    refine ⟨808534854260046385558475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8624371778773828112623733 808534854260046385558475)
                    ·
                      rfl

theorem cell23_4723848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_4723848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723848 prefixEnd_4723848 := by exact prefixLift 4723848
  have htrace : WordTrace (prefixWord ++ tailWord_4723848) baseStart_4723848 baseEnd_4723848 := by
    simpa [prefixWord, tailWord_4723848, baseEnd_4723848] using wordTrace_append hprefix tailTrace_4723848
  have hstable : (prefixWord ++ tailWord_4723848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723848).length < 2 ^ (prefixWord ++ tailWord_4723848).sum := by decide
  have hdescent : baseEnd_4723848 < baseStart_4723848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723868 : List Nat := [2, 2, 3, 2, 1, 2, 2, 4, 1, 2, 2]
def baseStart_4723868 : Nat := 118140960795 + 4723868 * 2 ^ 59
def prefixEnd_4723868 : Nat := 4983230072969 + 3 ^ 40 * 4723868 * 2
def baseEnd_4723868 : Nat := 2425614832393229078425333

theorem tailTrace_4723868 : CollatzResearch.WordTrace tailWord_4723868 prefixEnd_4723868 2425614832393229078425333 := by
  unfold tailWord_4723868
  simp only [CollatzResearch.WordTrace]
  refine ⟨86146810225120241634538129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114862413633493655512717505 86146810225120241634538129)
  ·
    refine ⟨64610107668840181225903597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86146810225120241634538129 64610107668840181225903597)
    ·
      refine ⟨24228790375815067959713849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64610107668840181225903597 24228790375815067959713849)
      ·
        refine ⟨18171592781861300969785387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24228790375815067959713849 18171592781861300969785387)
        ·
          refine ⟨27257389172791951454678081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18171592781861300969785387 27257389172791951454678081)
          ·
            refine ⟨20443041879593963591008561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27257389172791951454678081 20443041879593963591008561)
            ·
              refine ⟨15332281409695472693256421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20443041879593963591008561 15332281409695472693256421)
              ·
                refine ⟨2874802764317901129985579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15332281409695472693256421 2874802764317901129985579)
                ·
                  refine ⟨4312204146476851694978369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874802764317901129985579 4312204146476851694978369)
                  ·
                    refine ⟨3234153109857638771233777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4312204146476851694978369 3234153109857638771233777)
                    ·
                      refine ⟨2425614832393229078425333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234153109857638771233777 2425614832393229078425333)
                      ·
                        rfl

theorem cell23_4723868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_4723868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723868 prefixEnd_4723868 := by exact prefixLift 4723868
  have htrace : WordTrace (prefixWord ++ tailWord_4723868) baseStart_4723868 baseEnd_4723868 := by
    simpa [prefixWord, tailWord_4723868, baseEnd_4723868] using wordTrace_append hprefix tailTrace_4723868
  have hstable : (prefixWord ++ tailWord_4723868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723868).length < 2 ^ (prefixWord ++ tailWord_4723868).sum := by decide
  have hdescent : baseEnd_4723868 < baseStart_4723868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4723977 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 2, 5]
def baseStart_4723977 : Nat := 118140960795 + 4723977 * 2 ^ 59
def prefixEnd_4723977 : Nat := 4983230072969 + 3 ^ 40 * 4723977 * 2
def baseEnd_4723977 : Nat := 808556933928189717320777

theorem tailTrace_4723977 : CollatzResearch.WordTrace tailWord_4723977 prefixEnd_4723977 808556933928189717320777 := by
  unfold tailWord_4723977
  simp only [CollatzResearch.WordTrace]
  refine ⟨172297596006845594884794185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114865064004563729923196123 172297596006845594884794185)
  ·
    refine ⟨129223197005134196163595639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172297596006845594884794185 129223197005134196163595639)
    ·
      refine ⟨193834795507701294245393459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129223197005134196163595639 193834795507701294245393459)
      ·
        refine ⟨290752193261551941368090189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193834795507701294245393459 290752193261551941368090189)
        ·
          refine ⟨109032072473081978013033821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290752193261551941368090189 109032072473081978013033821)
          ·
            refine ⟨40887027177405741754887683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109032072473081978013033821 40887027177405741754887683)
            ·
              refine ⟨61330540766108612632331525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40887027177405741754887683 61330540766108612632331525)
              ·
                refine ⟨11499476393645364868562161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61330540766108612632331525 11499476393645364868562161)
                ·
                  refine ⟨8624607295234023651421621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11499476393645364868562161 8624607295234023651421621)
                  ·
                    refine ⟨808556933928189717320777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8624607295234023651421621 808556933928189717320777)
                    ·
                      rfl

theorem cell23_4723977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_4723977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4723977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4723977 prefixEnd_4723977 := by exact prefixLift 4723977
  have htrace : WordTrace (prefixWord ++ tailWord_4723977) baseStart_4723977 baseEnd_4723977 := by
    simpa [prefixWord, tailWord_4723977, baseEnd_4723977] using wordTrace_append hprefix tailTrace_4723977
  have hstable : (prefixWord ++ tailWord_4723977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4723977).length < 2 ^ (prefixWord ++ tailWord_4723977).sum := by decide
  have hdescent : baseEnd_4723977 < baseStart_4723977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4723977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724041 : List Nat := [1, 2, 1, 1, 2, 3, 4, 4, 1, 4]
def baseStart_4724041 : Nat := 118140960795 + 4724041 * 2 ^ 59
def prefixEnd_4724041 : Nat := 4983230072969 + 3 ^ 40 * 4724041 * 2
def baseEnd_4724041 : Nat := 808567888182152300520679

theorem tailTrace_4724041 : CollatzResearch.WordTrace tailWord_4724041 prefixEnd_4724041 808567888182152300520679 := by
  unfold tailWord_4724041
  simp only [CollatzResearch.WordTrace]
  refine ⟨172299930278613733815123977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114866620185742489210082651 172299930278613733815123977)
  ·
    refine ⟨129224947708960300361342983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172299930278613733815123977 129224947708960300361342983)
    ·
      refine ⟨193837421563440450542014475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129224947708960300361342983 193837421563440450542014475)
      ·
        refine ⟨290756132345160675813021713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193837421563440450542014475 290756132345160675813021713)
        ·
          refine ⟨218067099258870506859766285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290756132345160675813021713 218067099258870506859766285)
          ·
            refine ⟨81775162222076440072412357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218067099258870506859766285 81775162222076440072412357)
            ·
              refine ⟨15332842916639332513577317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81775162222076440072412357 15332842916639332513577317)
              ·
                refine ⟨2874908046869874846295747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15332842916639332513577317 2874908046869874846295747)
                ·
                  refine ⟨4312362070304812269443621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874908046869874846295747 4312362070304812269443621)
                  ·
                    refine ⟨808567888182152300520679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4312362070304812269443621 808567888182152300520679)
                    ·
                      rfl

theorem cell23_4724041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 1, 4].length) (baseStart_4724041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724041 prefixEnd_4724041 := by exact prefixLift 4724041
  have htrace : WordTrace (prefixWord ++ tailWord_4724041) baseStart_4724041 baseEnd_4724041 := by
    simpa [prefixWord, tailWord_4724041, baseEnd_4724041] using wordTrace_append hprefix tailTrace_4724041
  have hstable : (prefixWord ++ tailWord_4724041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724041).length < 2 ^ (prefixWord ++ tailWord_4724041).sum := by decide
  have hdescent : baseEnd_4724041 < baseStart_4724041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724091 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 2, 3, 2]
def baseStart_4724091 : Nat := 118140960795 + 4724091 * 2 ^ 59
def prefixEnd_4724091 : Nat := 4983230072969 + 3 ^ 40 * 4724091 * 2
def baseEnd_4724091 : Nat := 2425729338579181705936807

theorem tailTrace_4724091 : CollatzResearch.WordTrace tailWord_4724091 prefixEnd_4724091 2425729338579181705936807 := by
  unfold tailWord_4724091
  simp only [CollatzResearch.WordTrace]
  refine ⟨172301753928432592354444127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114867835952288394902962751 172301753928432592354444127)
  ·
    refine ⟨258452630892648888531666191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172301753928432592354444127 258452630892648888531666191)
    ·
      refine ⟨387678946338973332797499287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258452630892648888531666191 387678946338973332797499287)
      ·
        refine ⟨581518419508459999196248931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387678946338973332797499287 581518419508459999196248931)
        ·
          refine ⟨872277629262689998794373397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581518419508459999196248931 872277629262689998794373397)
          ·
            refine ⟨40888013871688593693486253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 872277629262689998794373397 40888013871688593693486253)
            ·
              refine ⟨15333005201883222635057345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40888013871688593693486253 15333005201883222635057345)
              ·
                refine ⟨11499753901412416976293009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15333005201883222635057345 11499753901412416976293009)
                ·
                  refine ⟨8624815426059312732219757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11499753901412416976293009 8624815426059312732219757)
                  ·
                    refine ⟨3234305784772242274582409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8624815426059312732219757 3234305784772242274582409)
                    ·
                      refine ⟨2425729338579181705936807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234305784772242274582409 2425729338579181705936807)
                      ·
                        rfl

theorem cell23_4724091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 2, 3, 2].length) (baseStart_4724091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724091 prefixEnd_4724091 := by exact prefixLift 4724091
  have htrace : WordTrace (prefixWord ++ tailWord_4724091) baseStart_4724091 baseEnd_4724091 := by
    simpa [prefixWord, tailWord_4724091, baseEnd_4724091] using wordTrace_append hprefix tailTrace_4724091
  have hstable : (prefixWord ++ tailWord_4724091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724091).length < 2 ^ (prefixWord ++ tailWord_4724091).sum := by decide
  have hdescent : baseEnd_4724091 < baseStart_4724091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724121 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 4]
def baseStart_4724121 : Nat := 118140960795 + 4724121 * 2 ^ 59
def prefixEnd_4724121 : Nat := 4983230072969 + 3 ^ 40 * 4724121 * 2
def baseEnd_4724121 : Nat := 2425744742998816588561669

theorem tailTrace_4724121 : CollatzResearch.WordTrace tailWord_4724121 prefixEnd_4724121 2425744742998816588561669 := by
  unfold tailWord_4724121
  simp only [CollatzResearch.WordTrace]
  refine ⟨172302848118323907478036217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114868565412215938318690811 172302848118323907478036217)
  ·
    refine ⟨129227136088742930608527163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172302848118323907478036217 129227136088742930608527163)
    ·
      refine ⟨193840704133114395912790745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129227136088742930608527163 193840704133114395912790745)
      ·
        refine ⟨145380528099835796934593059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193840704133114395912790745 145380528099835796934593059)
        ·
          refine ⟨218070792149753695401889589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145380528099835796934593059 218070792149753695401889589)
          ·
            refine ⟨20444136764039408943927149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218070792149753695401889589 20444136764039408943927149)
            ·
              refine ⟨7666551286514778353972681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20444136764039408943927149 7666551286514778353972681)
              ·
                refine ⟨5749913464886083765479511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7666551286514778353972681 5749913464886083765479511)
                ·
                  refine ⟨8624870197329125648219267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5749913464886083765479511 8624870197329125648219267)
                  ·
                    refine ⟨12937305295993688472328901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8624870197329125648219267 12937305295993688472328901)
                    ·
                      refine ⟨2425744742998816588561669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12937305295993688472328901 2425744742998816588561669)
                      ·
                        rfl

theorem cell23_4724121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_4724121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724121 prefixEnd_4724121 := by exact prefixLift 4724121
  have htrace : WordTrace (prefixWord ++ tailWord_4724121) baseStart_4724121 baseEnd_4724121 := by
    simpa [prefixWord, tailWord_4724121, baseEnd_4724121] using wordTrace_append hprefix tailTrace_4724121
  have hstable : (prefixWord ++ tailWord_4724121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724121).length < 2 ^ (prefixWord ++ tailWord_4724121).sum := by decide
  have hdescent : baseEnd_4724121 < baseStart_4724121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724205 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4724205 : Nat := 118140960795 + 4724205 * 2 ^ 59
def prefixEnd_4724205 : Nat := 4983230072969 + 3 ^ 40 * 4724205 * 2
def baseEnd_4724205 : Nat := 2425787875373794259911283

theorem tailTrace_4724205 : CollatzResearch.WordTrace tailWord_4724205 prefixEnd_4724205 2425787875373794259911283 := by
  unfold tailWord_4724205
  simp only [CollatzResearch.WordTrace]
  refine ⟨172305911850019589824094069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114870607900013059882729379 172305911850019589824094069)
  ·
    refine ⟨16153679235939336546008819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172305911850019589824094069 16153679235939336546008819)
    ·
      refine ⟨24230518853909004819013229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16153679235939336546008819 24230518853909004819013229)
      ·
        refine ⟨9086444570215876807129961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24230518853909004819013229 9086444570215876807129961)
        ·
          refine ⟨6814833427661907605347471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9086444570215876807129961 6814833427661907605347471)
          ·
            refine ⟨10222250141492861408021207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6814833427661907605347471 10222250141492861408021207)
            ·
              refine ⟨15333375212239292112031811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10222250141492861408021207 15333375212239292112031811)
              ·
                refine ⟨23000062818358938168047717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15333375212239292112031811 23000062818358938168047717)
                ·
                  refine ⟨4312511778442300906508947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23000062818358938168047717 4312511778442300906508947)
                  ·
                    refine ⟨6468767667663451359763421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4312511778442300906508947 6468767667663451359763421)
                    ·
                      refine ⟨2425787875373794259911283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6468767667663451359763421 2425787875373794259911283)
                      ·
                        rfl

theorem cell23_4724205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4724205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724205 prefixEnd_4724205 := by exact prefixLift 4724205
  have htrace : WordTrace (prefixWord ++ tailWord_4724205) baseStart_4724205 baseEnd_4724205 := by
    simpa [prefixWord, tailWord_4724205, baseEnd_4724205] using wordTrace_append hprefix tailTrace_4724205
  have hstable : (prefixWord ++ tailWord_4724205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724205).length < 2 ^ (prefixWord ++ tailWord_4724205).sum := by decide
  have hdescent : baseEnd_4724205 < baseStart_4724205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724222 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4724222 : Nat := 118140960795 + 4724222 * 2 ^ 59
def prefixEnd_4724222 : Nat := 4983230072969 + 3 ^ 40 * 4724222 * 2
def baseEnd_4724222 : Nat := 2425796604544920693398705

theorem tailTrace_4724222 : CollatzResearch.WordTrace tailWord_4724222 prefixEnd_4724222 2425796604544920693398705 := by
  unfold tailWord_4724222
  simp only [CollatzResearch.WordTrace]
  refine ⟨21538316486369750215932865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114871021260638667818308613 21538316486369750215932865)
  ·
    refine ⟨16153737364777312661949649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21538316486369750215932865 16153737364777312661949649)
    ·
      refine ⟨12115303023582984496462237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16153737364777312661949649 12115303023582984496462237)
      ·
        refine ⟨4543238633843619186173339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12115303023582984496462237 4543238633843619186173339)
        ·
          refine ⟨6814857950765428779260009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4543238633843619186173339 6814857950765428779260009)
          ·
            refine ⟨5111143463074071584445007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6814857950765428779260009 5111143463074071584445007)
            ·
              refine ⟨7666715194611107376667511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111143463074071584445007 7666715194611107376667511)
              ·
                refine ⟨11500072791916661065001267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7666715194611107376667511 11500072791916661065001267)
                ·
                  refine ⟨17250109187874991597501901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11500072791916661065001267 17250109187874991597501901)
                  ·
                    refine ⟨6468790945453121849063213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17250109187874991597501901 6468790945453121849063213)
                    ·
                      refine ⟨2425796604544920693398705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6468790945453121849063213 2425796604544920693398705)
                      ·
                        rfl

theorem cell23_4724222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4724222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724222 prefixEnd_4724222 := by exact prefixLift 4724222
  have htrace : WordTrace (prefixWord ++ tailWord_4724222) baseStart_4724222 baseEnd_4724222 := by
    simpa [prefixWord, tailWord_4724222, baseEnd_4724222] using wordTrace_append hprefix tailTrace_4724222
  have hstable : (prefixWord ++ tailWord_4724222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724222).length < 2 ^ (prefixWord ++ tailWord_4724222).sum := by decide
  have hdescent : baseEnd_4724222 < baseStart_4724222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724362 : List Nat := [3, 1, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_4724362 : Nat := 118140960795 + 4724362 * 2 ^ 59
def prefixEnd_4724362 : Nat := 4983230072969 + 3 ^ 40 * 4724362 * 2
def baseEnd_4724362 : Nat := 808622830612183381882687

theorem tailTrace_4724362 : CollatzResearch.WordTrace tailWord_4724362 prefixEnd_4724362 808622830612183381882687 := by
  unfold tailWord_4724362
  simp only [CollatzResearch.WordTrace]
  refine ⟨43077909527612701409389835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114874425406967203758372893 43077909527612701409389835)
  ·
    refine ⟨64616864291419052114084753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43077909527612701409389835 64616864291419052114084753)
    ·
      refine ⟨48462648218564289085563565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64616864291419052114084753 48462648218564289085563565)
      ·
        refine ⟨18173493081961608407086337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48462648218564289085563565 18173493081961608407086337)
        ·
          refine ⟨13630119811471206305314753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18173493081961608407086337 13630119811471206305314753)
          ·
            refine ⟨10222589858603404728986065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13630119811471206305314753 10222589858603404728986065)
            ·
              refine ⟨7666942393952553546739549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10222589858603404728986065 7666942393952553546739549)
              ·
                refine ⟨2875103397732207580027331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7666942393952553546739549 2875103397732207580027331)
                ·
                  refine ⟨4312655096598311370040997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875103397732207580027331 4312655096598311370040997)
                  ·
                    refine ⟨808622830612183381882687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4312655096598311370040997 808622830612183381882687)
                    ·
                      rfl

theorem cell23_4724362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_4724362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724362 prefixEnd_4724362 := by exact prefixLift 4724362
  have htrace : WordTrace (prefixWord ++ tailWord_4724362) baseStart_4724362 baseEnd_4724362 := by
    simpa [prefixWord, tailWord_4724362, baseEnd_4724362] using wordTrace_append hprefix tailTrace_4724362
  have hstable : (prefixWord ++ tailWord_4724362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724362).length < 2 ^ (prefixWord ++ tailWord_4724362).sum := by decide
  have hdescent : baseEnd_4724362 < baseStart_4724362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724385 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_4724385 : Nat := 118140960795 + 4724385 * 2 ^ 59
def prefixEnd_4724385 : Nat := 4983230072969 + 3 ^ 40 * 4724385 * 2
def baseEnd_4724385 : Nat := 2425880301891603555660455

theorem tailTrace_4724385 : CollatzResearch.WordTrace tailWord_4724385 prefixEnd_4724385 2425880301891603555660455 := by
  unfold tailWord_4724385
  simp only [CollatzResearch.WordTrace]
  refine ⟨172312476989367480565646609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114874984659578320377097739 172312476989367480565646609)
  ·
    refine ⟨129234357742025610424234957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172312476989367480565646609 129234357742025610424234957)
    ·
      refine ⟨48462884153259603909088109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129234357742025610424234957 48462884153259603909088109)
      ·
        refine ⟨18173581557472351465908041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48462884153259603909088109 18173581557472351465908041)
        ·
          refine ⟨13630186168104263599431031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18173581557472351465908041 13630186168104263599431031)
          ·
            refine ⟨20445279252156395399146547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13630186168104263599431031 20445279252156395399146547)
            ·
              refine ⟨30667918878234593098719821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20445279252156395399146547 30667918878234593098719821)
              ·
                refine ⟨11500469579337972412019933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30667918878234593098719821 11500469579337972412019933)
                ·
                  refine ⟨4312676092251739654507475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11500469579337972412019933 4312676092251739654507475)
                  ·
                    refine ⟨6469014138377609481761213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4312676092251739654507475 6469014138377609481761213)
                    ·
                      refine ⟨2425880301891603555660455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6469014138377609481761213 2425880301891603555660455)
                      ·
                        rfl

theorem cell23_4724385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_4724385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724385 prefixEnd_4724385 := by exact prefixLift 4724385
  have htrace : WordTrace (prefixWord ++ tailWord_4724385) baseStart_4724385 baseEnd_4724385 := by
    simpa [prefixWord, tailWord_4724385, baseEnd_4724385] using wordTrace_append hprefix tailTrace_4724385
  have hstable : (prefixWord ++ tailWord_4724385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724385).length < 2 ^ (prefixWord ++ tailWord_4724385).sum := by decide
  have hdescent : baseEnd_4724385 < baseStart_4724385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724411 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 3]
def baseStart_4724411 : Nat := 118140960795 + 4724411 * 2 ^ 59
def prefixEnd_4724411 : Nat := 4983230072969 + 3 ^ 40 * 4724411 * 2
def baseEnd_4724411 : Nat := 2425893652388620453935335

theorem tailTrace_4724411 : CollatzResearch.WordTrace tailWord_4724411 prefixEnd_4724411 2425893652388620453935335 := by
  unfold tailWord_4724411
  simp only [CollatzResearch.WordTrace]
  refine ⟨172313425287273287006093087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114875616858182191337395391 172313425287273287006093087)
  ·
    refine ⟨258470137930909930509139631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172313425287273287006093087 258470137930909930509139631)
    ·
      refine ⟨387705206896364895763709447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258470137930909930509139631 387705206896364895763709447)
      ·
        refine ⟨581557810344547343645564171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387705206896364895763709447 581557810344547343645564171)
        ·
          refine ⟨872336715516821015468346257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581557810344547343645564171 872336715516821015468346257)
          ·
            refine ⟨654252536637615761601259693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 872336715516821015468346257 654252536637615761601259693)
            ·
              refine ⟨245344701239105910600472385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 654252536637615761601259693 245344701239105910600472385)
              ·
                refine ⟨184008525929329432950354289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245344701239105910600472385 184008525929329432950354289)
                ·
                  refine ⟨138006394446997074712765717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184008525929329432950354289 138006394446997074712765717)
                  ·
                    refine ⟨6469049739702987877160893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 138006394446997074712765717 6469049739702987877160893)
                    ·
                      refine ⟨2425893652388620453935335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6469049739702987877160893 2425893652388620453935335)
                      ·
                        rfl

theorem cell23_4724411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 3].length) (baseStart_4724411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724411 prefixEnd_4724411 := by exact prefixLift 4724411
  have htrace : WordTrace (prefixWord ++ tailWord_4724411) baseStart_4724411 baseEnd_4724411 := by
    simpa [prefixWord, tailWord_4724411, baseEnd_4724411] using wordTrace_append hprefix tailTrace_4724411
  have hstable : (prefixWord ++ tailWord_4724411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724411).length < 2 ^ (prefixWord ++ tailWord_4724411).sum := by decide
  have hdescent : baseEnd_4724411 < baseStart_4724411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724429 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_4724429 : Nat := 118140960795 + 4724429 * 2 ^ 59
def prefixEnd_4724429 : Nat := 4983230072969 + 3 ^ 40 * 4724429 * 2
def baseEnd_4724429 : Nat := 2425902895040401383510253

theorem tailTrace_4724429 : CollatzResearch.WordTrace tailWord_4724429 prefixEnd_4724429 2425902895040401383510253 := by
  unfold tailWord_4724429
  simp only [CollatzResearch.WordTrace]
  refine ⟨172314081801208076080248341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114876054534138717386832227 172314081801208076080248341)
  ·
    refine ⟨8077222584431628566261641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 172314081801208076080248341 8077222584431628566261641)
    ·
      refine ⟨6057916938323721424696231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8077222584431628566261641 6057916938323721424696231)
      ·
        refine ⟨9086875407485582137044347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057916938323721424696231 9086875407485582137044347)
        ·
          refine ⟨13630313111228373205566521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9086875407485582137044347 13630313111228373205566521)
          ·
            refine ⟨10222734833421279904174891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13630313111228373205566521 10222734833421279904174891)
            ·
              refine ⟨15334102250131919856262337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10222734833421279904174891 15334102250131919856262337)
              ·
                refine ⟨11500576687598939892196753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15334102250131919856262337 11500576687598939892196753)
                ·
                  refine ⟨8625432515699204919147565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11500576687598939892196753 8625432515699204919147565)
                  ·
                    refine ⟨3234537193387201844680337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8625432515699204919147565 3234537193387201844680337)
                    ·
                      refine ⟨2425902895040401383510253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234537193387201844680337 2425902895040401383510253)
                      ·
                        rfl

theorem cell23_4724429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_4724429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724429 prefixEnd_4724429 := by exact prefixLift 4724429
  have htrace : WordTrace (prefixWord ++ tailWord_4724429) baseStart_4724429 baseEnd_4724429 := by
    simpa [prefixWord, tailWord_4724429, baseEnd_4724429] using wordTrace_append hprefix tailTrace_4724429
  have hstable : (prefixWord ++ tailWord_4724429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724429).length < 2 ^ (prefixWord ++ tailWord_4724429).sum := by decide
  have hdescent : baseEnd_4724429 < baseStart_4724429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724436 : List Nat := [2, 4, 1, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4724436 : Nat := 118140960795 + 4724436 * 2 ^ 59
def prefixEnd_4724436 : Nat := 4983230072969 + 3 ^ 40 * 4724436 * 2
def baseEnd_4724436 : Nat := 2425906489404982856122721

theorem tailTrace_4724436 : CollatzResearch.WordTrace tailWord_4724436 prefixEnd_4724436 2425906489404982856122721 := by
  unfold tailWord_4724436
  simp only [CollatzResearch.WordTrace]
  refine ⟨86157168556091358137876581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114876224741455144183835441 86157168556091358137876581)
  ·
    refine ⟨16154469104267129650851859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86157168556091358137876581 16154469104267129650851859)
    ·
      refine ⟨24231703656400694476277789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16154469104267129650851859 24231703656400694476277789)
      ·
        refine ⟨9086888871150260428604171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24231703656400694476277789 9086888871150260428604171)
        ·
          refine ⟨13630333306725390642906257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9086888871150260428604171 13630333306725390642906257)
          ·
            refine ⟨10222749980044042982179693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13630333306725390642906257 10222749980044042982179693)
            ·
              refine ⟨3833531242516516118317385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10222749980044042982179693 3833531242516516118317385)
              ·
                refine ⟨2875148431887387088738039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3833531242516516118317385 2875148431887387088738039)
                ·
                  refine ⟨4312722647831080633107059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875148431887387088738039 4312722647831080633107059)
                  ·
                    refine ⟨6469083971746620949660589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4312722647831080633107059 6469083971746620949660589)
                    ·
                      refine ⟨2425906489404982856122721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6469083971746620949660589 2425906489404982856122721)
                      ·
                        rfl

theorem cell23_4724436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4724436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724436 prefixEnd_4724436 := by exact prefixLift 4724436
  have htrace : WordTrace (prefixWord ++ tailWord_4724436) baseStart_4724436 baseEnd_4724436 := by
    simpa [prefixWord, tailWord_4724436, baseEnd_4724436] using wordTrace_append hprefix tailTrace_4724436
  have hstable : (prefixWord ++ tailWord_4724436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724436).length < 2 ^ (prefixWord ++ tailWord_4724436).sum := by decide
  have hdescent : baseEnd_4724436 < baseStart_4724436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724442 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2]
def baseStart_4724442 : Nat := 118140960795 + 4724442 * 2 ^ 59
def prefixEnd_4724442 : Nat := 4983230072969 + 3 ^ 40 * 4724442 * 2
def baseEnd_4724442 : Nat := 2425909570288909832647693

theorem tailTrace_4724442 : CollatzResearch.WordTrace tailWord_4724442 prefixEnd_4724442 2425909570288909832647693 := by
  unfold tailWord_4724442
  simp only [CollatzResearch.WordTrace]
  refine ⟨43078638987540244825117895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114876370633440652866981053 43078638987540244825117895)
  ·
    refine ⟨64617958481310367237676843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43078638987540244825117895 64617958481310367237676843)
    ·
      refine ⟨96926937721965550856515265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64617958481310367237676843 96926937721965550856515265)
      ·
        refine ⟨72695203291474163142386449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96926937721965550856515265 72695203291474163142386449)
        ·
          refine ⟨54521402468605622356789837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72695203291474163142386449 54521402468605622356789837)
          ·
            refine ⟨20445525925727108383796189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54521402468605622356789837 20445525925727108383796189)
            ·
              refine ⟨7667072222147665643923571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20445525925727108383796189 7667072222147665643923571)
              ·
                refine ⟨11500608333221498465885357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7667072222147665643923571 11500608333221498465885357)
                ·
                  refine ⟨4312728124958061924707009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11500608333221498465885357 4312728124958061924707009)
                  ·
                    refine ⟨3234546093718546443530257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4312728124958061924707009 3234546093718546443530257)
                    ·
                      refine ⟨2425909570288909832647693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234546093718546443530257 2425909570288909832647693)
                      ·
                        rfl

theorem cell23_4724442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_4724442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724442 prefixEnd_4724442 := by exact prefixLift 4724442
  have htrace : WordTrace (prefixWord ++ tailWord_4724442) baseStart_4724442 baseEnd_4724442 := by
    simpa [prefixWord, tailWord_4724442, baseEnd_4724442] using wordTrace_append hprefix tailTrace_4724442
  have hstable : (prefixWord ++ tailWord_4724442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724442).length < 2 ^ (prefixWord ++ tailWord_4724442).sum := by decide
  have hdescent : baseEnd_4724442 < baseStart_4724442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724471 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_4724471 : Nat := 118140960795 + 4724471 * 2 ^ 59
def prefixEnd_4724471 : Nat := 4983230072969 + 3 ^ 40 * 4724471 * 2
def baseEnd_4724471 : Nat := 2425924461227890219185059

theorem tailTrace_4724471 : CollatzResearch.WordTrace tailWord_4724471 prefixEnd_4724471 2425924461227890219185059 := by
  unfold tailWord_4724471
  simp only [CollatzResearch.WordTrace]
  refine ⟨172315613667055917253277267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114877075778037278168851511 172315613667055917253277267)
  ·
    refine ⟨258473420500583875879915901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172315613667055917253277267 258473420500583875879915901)
    ·
      refine ⟨96927532687718953454968463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258473420500583875879915901 96927532687718953454968463)
      ·
        refine ⟨145391299031578430182452695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96927532687718953454968463 145391299031578430182452695)
        ·
          refine ⟨218086948547367645273679043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145391299031578430182452695 218086948547367645273679043)
          ·
            refine ⟨327130422821051467910518565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218086948547367645273679043 327130422821051467910518565)
            ·
              refine ⟨61336954278947150233222231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327130422821051467910518565 61336954278947150233222231)
              ·
                refine ⟨92005431418420725349833347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61336954278947150233222231 92005431418420725349833347)
                ·
                  refine ⟨138008147127631088024750021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92005431418420725349833347 138008147127631088024750021)
                  ·
                    refine ⟨25876527586430829004640629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138008147127631088024750021 25876527586430829004640629)
                    ·
                      refine ⟨2425924461227890219185059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25876527586430829004640629 2425924461227890219185059)
                      ·
                        rfl

theorem cell23_4724471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_4724471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724471 prefixEnd_4724471 := by exact prefixLift 4724471
  have htrace : WordTrace (prefixWord ++ tailWord_4724471) baseStart_4724471 baseEnd_4724471 := by
    simpa [prefixWord, tailWord_4724471, baseEnd_4724471] using wordTrace_append hprefix tailTrace_4724471
  have hstable : (prefixWord ++ tailWord_4724471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724471).length < 2 ^ (prefixWord ++ tailWord_4724471).sum := by decide
  have hdescent : baseEnd_4724471 < baseStart_4724471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724508 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_4724508 : Nat := 118140960795 + 4724508 * 2 ^ 59
def prefixEnd_4724508 : Nat := 4983230072969 + 3 ^ 40 * 4724508 * 2
def baseEnd_4724508 : Nat := 808647820004035524807463

theorem tailTrace_4724508 : CollatzResearch.WordTrace tailWord_4724508 prefixEnd_4724508 808647820004035524807463 := by
  unfold tailWord_4724508
  simp only [CollatzResearch.WordTrace]
  refine ⟨86158481583960936286187089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114877975445281248381582785 86158481583960936286187089)
  ·
    refine ⟨64618861187970702214640317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86158481583960936286187089 64618861187970702214640317)
    ·
      refine ⟨24232072945489013330490119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64618861187970702214640317 24232072945489013330490119)
      ·
        refine ⟨36348109418233519995735179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24232072945489013330490119 36348109418233519995735179)
        ·
          refine ⟨54522164127350279993602769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36348109418233519995735179 54522164127350279993602769)
          ·
            refine ⟨40891623095512709995202077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54522164127350279993602769 40891623095512709995202077)
            ·
              refine ⟨15334358660817266248200779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40891623095512709995202077 15334358660817266248200779)
              ·
                refine ⟨23001537991225899372301169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15334358660817266248200779 23001537991225899372301169)
                ·
                  refine ⟨17251153493419424529225877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23001537991225899372301169 17251153493419424529225877)
                  ·
                    refine ⟨808647820004035524807463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17251153493419424529225877 808647820004035524807463)
                    ·
                      rfl

theorem cell23_4724508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_4724508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724508 prefixEnd_4724508 := by exact prefixLift 4724508
  have htrace : WordTrace (prefixWord ++ tailWord_4724508) baseStart_4724508 baseEnd_4724508 := by
    simpa [prefixWord, tailWord_4724508, baseEnd_4724508] using wordTrace_append hprefix tailTrace_4724508
  have hstable : (prefixWord ++ tailWord_4724508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724508).length < 2 ^ (prefixWord ++ tailWord_4724508).sum := by decide
  have hdescent : baseEnd_4724508 < baseStart_4724508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724515 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 1, 4, 2]
def baseStart_4724515 : Nat := 118140960795 + 4724515 * 2 ^ 59
def prefixEnd_4724515 : Nat := 4983230072969 + 3 ^ 40 * 4724515 * 2
def baseEnd_4724515 : Nat := 2425947054376688047034857

theorem tailTrace_4724515 : CollatzResearch.WordTrace tailWord_4724515 prefixEnd_4724515 2425947054376688047034857 := by
  unfold tailWord_4724515
  simp only [CollatzResearch.WordTrace]
  refine ⟨172317218478896512767878999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114878145652597675178585999 172317218478896512767878999)
  ·
    refine ⟨258475827718344769151818499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172317218478896512767878999 258475827718344769151818499)
    ·
      refine ⟨387713741577517153727727749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258475827718344769151818499 387713741577517153727727749)
      ·
        refine ⟨72696326545784466323948953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387713741577517153727727749 72696326545784466323948953)
        ·
          refine ⟨54522244909338349742961715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72696326545784466323948953 54522244909338349742961715)
          ·
            refine ⟨81783367364007524614442573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54522244909338349742961715 81783367364007524614442573)
            ·
              refine ⟨30668762761502821730415965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81783367364007524614442573 30668762761502821730415965)
              ·
                refine ⟨11500786035563558148905987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30668762761502821730415965 11500786035563558148905987)
                ·
                  refine ⟨17251179053345337223358981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11500786035563558148905987 17251179053345337223358981)
                  ·
                    refine ⟨3234596072502250729379809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17251179053345337223358981 3234596072502250729379809)
                    ·
                      refine ⟨2425947054376688047034857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234596072502250729379809 2425947054376688047034857)
                      ·
                        rfl

theorem cell23_4724515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_4724515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724515 prefixEnd_4724515 := by exact prefixLift 4724515
  have htrace : WordTrace (prefixWord ++ tailWord_4724515) baseStart_4724515 baseEnd_4724515 := by
    simpa [prefixWord, tailWord_4724515, baseEnd_4724515] using wordTrace_append hprefix tailTrace_4724515
  have hstable : (prefixWord ++ tailWord_4724515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724515).length < 2 ^ (prefixWord ++ tailWord_4724515).sum := by decide
  have hdescent : baseEnd_4724515 < baseStart_4724515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724565 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_4724565 : Nat := 118140960795 + 4724565 * 2 ^ 59
def prefixEnd_4724565 : Nat := 4983230072969 + 3 ^ 40 * 4724565 * 2
def baseEnd_4724565 : Nat := 2425972728409412851409627

theorem tailTrace_4724565 : CollatzResearch.WordTrace tailWord_4724565 prefixEnd_4724565 2425972728409412851409627 := by
  unfold tailWord_4724565
  simp only [CollatzResearch.WordTrace]
  refine ⟨172319042128715371307199149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114879361419143580871466099 172319042128715371307199149)
  ·
    refine ⟨64619640798268264240199681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172319042128715371307199149 64619640798268264240199681)
    ·
      refine ⟨48464730598701198180149761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64619640798268264240199681 48464730598701198180149761)
      ·
        refine ⟨36348547949025898635112321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48464730598701198180149761 36348547949025898635112321)
        ·
          refine ⟨27261410961769423976334241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36348547949025898635112321 27261410961769423976334241)
          ·
            refine ⟨20446058221327067982250681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27261410961769423976334241 20446058221327067982250681)
            ·
              refine ⟨15334543665995300986688011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20446058221327067982250681 15334543665995300986688011)
              ·
                refine ⟨23001815498992951480032017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15334543665995300986688011 23001815498992951480032017)
                ·
                  refine ⟨17251361624244713610024013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23001815498992951480032017 17251361624244713610024013)
                  ·
                    refine ⟨6469260609091767603759005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17251361624244713610024013 6469260609091767603759005)
                    ·
                      refine ⟨2425972728409412851409627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6469260609091767603759005 2425972728409412851409627)
                      ·
                        rfl

theorem cell23_4724565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_4724565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724565 prefixEnd_4724565 := by exact prefixLift 4724565
  have htrace : WordTrace (prefixWord ++ tailWord_4724565) baseStart_4724565 baseEnd_4724565 := by
    simpa [prefixWord, tailWord_4724565, baseEnd_4724565] using wordTrace_append hprefix tailTrace_4724565
  have hstable : (prefixWord ++ tailWord_4724565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724565).length < 2 ^ (prefixWord ++ tailWord_4724565).sum := by decide
  have hdescent : baseEnd_4724565 < baseStart_4724565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724606 : List Nat := [4, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_4724606 : Nat := 118140960795 + 4724606 * 2 ^ 59
def prefixEnd_4724606 : Nat := 4983230072969 + 3 ^ 40 * 4724606 * 2
def baseEnd_4724606 : Nat := 269554864568471910110771

theorem tailTrace_4724606 : CollatzResearch.WordTrace tailWord_4724606 prefixEnd_4724606 269554864568471910110771 := by
  unfold tailWord_4724606
  simp only [CollatzResearch.WordTrace]
  refine ⟨21540067190195854413680209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114880358347711223539627781 21540067190195854413680209)
  ·
    refine ⟨16155050392646890810260157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21540067190195854413680209 16155050392646890810260157)
    ·
      refine ⟨6058143897242584053847559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16155050392646890810260157 6058143897242584053847559)
      ·
        refine ⟨9087215845863876080771339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6058143897242584053847559 9087215845863876080771339)
        ·
          refine ⟨13630823768795814121157009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9087215845863876080771339 13630823768795814121157009)
          ·
            refine ⟨10223117826596860590867757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13630823768795814121157009 10223117826596860590867757)
            ·
              refine ⟨3833669184973822721575409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10223117826596860590867757 3833669184973822721575409)
              ·
                refine ⟨2875251888730367041181557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3833669184973822721575409 2875251888730367041181557)
                ·
                  refine ⟨269554864568471910110771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2875251888730367041181557 269554864568471910110771)
                  ·
                    rfl

theorem cell23_4724606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_4724606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724606 prefixEnd_4724606 := by exact prefixLift 4724606
  have htrace : WordTrace (prefixWord ++ tailWord_4724606) baseStart_4724606 baseEnd_4724606 := by
    simpa [prefixWord, tailWord_4724606, baseEnd_4724606] using wordTrace_append hprefix tailTrace_4724606
  have hstable : (prefixWord ++ tailWord_4724606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724606).length < 2 ^ (prefixWord ++ tailWord_4724606).sum := by decide
  have hdescent : baseEnd_4724606 < baseStart_4724606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724672 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 3, 1, 3]
def baseStart_4724672 : Nat := 118140960795 + 4724672 * 2 ^ 59
def prefixEnd_4724672 : Nat := 4983230072969 + 3 ^ 40 * 4724672 * 2
def baseEnd_4724672 : Nat := 2426027670839443932771635

theorem tailTrace_4724672 : CollatzResearch.WordTrace tailWord_4724672 prefixEnd_4724672 2426027670839443932771635 := by
  unfold tailWord_4724672
  simp only [CollatzResearch.WordTrace]
  refine ⟨86161472369663864290672135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114881963159551819054229513 86161472369663864290672135)
  ·
    refine ⟨129242208554495796436008203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86161472369663864290672135 129242208554495796436008203)
    ·
      refine ⟨193863312831743694654012305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129242208554495796436008203 193863312831743694654012305)
      ·
        refine ⟨145397484623807770990509229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193863312831743694654012305 145397484623807770990509229)
        ·
          refine ⟨54524056733927914121440961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145397484623807770990509229 54524056733927914121440961)
          ·
            refine ⟨40893042550445935591080721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54524056733927914121440961 40893042550445935591080721)
            ·
              refine ⟨30669781912834451693310541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40893042550445935591080721 30669781912834451693310541)
              ·
                refine ⟨11501168217312919384991453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30669781912834451693310541 11501168217312919384991453)
                ·
                  refine ⟨4312938081492344769371795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11501168217312919384991453 4312938081492344769371795)
                  ·
                    refine ⟨6469407122238517154057693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4312938081492344769371795 6469407122238517154057693)
                    ·
                      refine ⟨2426027670839443932771635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6469407122238517154057693 2426027670839443932771635)
                      ·
                        rfl

theorem cell23_4724672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_4724672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724672 prefixEnd_4724672 := by exact prefixLift 4724672
  have htrace : WordTrace (prefixWord ++ tailWord_4724672) baseStart_4724672 baseEnd_4724672 := by
    simpa [prefixWord, tailWord_4724672, baseEnd_4724672] using wordTrace_append hprefix tailTrace_4724672
  have hstable : (prefixWord ++ tailWord_4724672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724672).length < 2 ^ (prefixWord ++ tailWord_4724672).sum := by decide
  have hdescent : baseEnd_4724672 < baseStart_4724672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724682 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_4724682 : Nat := 118140960795 + 4724682 * 2 ^ 59
def prefixEnd_4724682 : Nat := 4983230072969 + 3 ^ 40 * 4724682 * 2
def baseEnd_4724682 : Nat := 2426032805645988893646589

theorem tailTrace_4724682 : CollatzResearch.WordTrace tailWord_4724682 prefixEnd_4724682 2426032805645988893646589 := by
  unfold tailWord_4724682
  simp only [CollatzResearch.WordTrace]
  refine ⟨43080827367322875072302075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114882206312861000192805533 43080827367322875072302075)
  ·
    refine ⟨64621241050984312608453113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43080827367322875072302075 64621241050984312608453113)
    ·
      refine ⟨48465930788238234456339835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64621241050984312608453113 48465930788238234456339835)
      ·
        refine ⟨72698896182357351684509753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48465930788238234456339835 72698896182357351684509753)
        ·
          refine ⟨54524172136768013763382315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72698896182357351684509753 54524172136768013763382315)
          ·
            refine ⟨81786258205152020645073473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54524172136768013763382315 81786258205152020645073473)
            ·
              refine ⟨61339693653864015483805105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81786258205152020645073473 61339693653864015483805105)
              ·
                refine ⟨46004770240398011612853829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61339693653864015483805105 46004770240398011612853829)
                ·
                  refine ⟨8625894420074627177410093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46004770240398011612853829 8625894420074627177410093)
                  ·
                    refine ⟨3234710407527985191528785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8625894420074627177410093 3234710407527985191528785)
                    ·
                      refine ⟨2426032805645988893646589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234710407527985191528785 2426032805645988893646589)
                      ·
                        rfl

theorem cell23_4724682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_4724682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724682 prefixEnd_4724682 := by exact prefixLift 4724682
  have htrace : WordTrace (prefixWord ++ tailWord_4724682) baseStart_4724682 baseEnd_4724682 := by
    simpa [prefixWord, tailWord_4724682, baseEnd_4724682] using wordTrace_append hprefix tailTrace_4724682
  have hstable : (prefixWord ++ tailWord_4724682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724682).length < 2 ^ (prefixWord ++ tailWord_4724682).sum := by decide
  have hdescent : baseEnd_4724682 < baseStart_4724682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724692 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_4724692 : Nat := 118140960795 + 4724692 * 2 ^ 59
def prefixEnd_4724692 : Nat := 4983230072969 + 3 ^ 40 * 4724692 * 2
def baseEnd_4724692 : Nat := 808679313484177951507181

theorem tailTrace_4724692 : CollatzResearch.WordTrace tailWord_4724692 prefixEnd_4724692 808679313484177951507181 := by
  unfold tailWord_4724692
  simp only [CollatzResearch.WordTrace]
  refine ⟨86161837099627635998536165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114882449466170181331381553 86161837099627635998536165)
  ·
    refine ⟨16155344456180181749725531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86161837099627635998536165 16155344456180181749725531)
    ·
      refine ⟨24233016684270272624588297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16155344456180181749725531 24233016684270272624588297)
      ·
        refine ⟨18174762513202704468441223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24233016684270272624588297 18174762513202704468441223)
        ·
          refine ⟨27262143769804056702661835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18174762513202704468441223 27262143769804056702661835)
          ·
            refine ⟨40893215654706085053992753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27262143769804056702661835 40893215654706085053992753)
            ·
              refine ⟨30669911741029563790494565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40893215654706085053992753 30669911741029563790494565)
              ·
                refine ⟨5750608451443043210717731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30669911741029563790494565 5750608451443043210717731)
                ·
                  refine ⟨8625912677164564816076597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5750608451443043210717731 8625912677164564816076597)
                  ·
                    refine ⟨808679313484177951507181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8625912677164564816076597 808679313484177951507181)
                    ·
                      rfl

theorem cell23_4724692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_4724692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724692 prefixEnd_4724692 := by exact prefixLift 4724692
  have htrace : WordTrace (prefixWord ++ tailWord_4724692) baseStart_4724692 baseEnd_4724692 := by
    simpa [prefixWord, tailWord_4724692, baseEnd_4724692] using wordTrace_append hprefix tailTrace_4724692
  have hstable : (prefixWord ++ tailWord_4724692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724692).length < 2 ^ (prefixWord ++ tailWord_4724692).sum := by decide
  have hdescent : baseEnd_4724692 < baseStart_4724692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724695 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_4724695 : Nat := 118140960795 + 4724695 * 2 ^ 59
def prefixEnd_4724695 : Nat := 4983230072969 + 3 ^ 40 * 4724695 * 2
def baseEnd_4724695 : Nat := 2426039480894497342784029

theorem tailTrace_4724695 : CollatzResearch.WordTrace tailWord_4724695 prefixEnd_4724695 2426039480894497342784029 := by
  unfold tailWord_4724695
  simp only [CollatzResearch.WordTrace]
  refine ⟨172323783618244403509431539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114882522412162935672954359 172323783618244403509431539)
  ·
    refine ⟨258485675427366605264147309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172323783618244403509431539 258485675427366605264147309)
    ·
      refine ⟨96932128285262476974055241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258485675427366605264147309 96932128285262476974055241)
      ·
        refine ⟨72699096213946857730541431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96932128285262476974055241 72699096213946857730541431)
        ·
          refine ⟨109048644320920286595812147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72699096213946857730541431 109048644320920286595812147)
          ·
            refine ⟨163572966481380429893718221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109048644320920286595812147 163572966481380429893718221)
            ·
              refine ⟨61339862430517661210144333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163572966481380429893718221 61339862430517661210144333)
              ·
                refine ⟨23002448411444122953804125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61339862430517661210144333 23002448411444122953804125)
                ·
                  refine ⟨8625918154291546107676547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23002448411444122953804125 8625918154291546107676547)
                  ·
                    refine ⟨12938877231437319161514821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8625918154291546107676547 12938877231437319161514821)
                    ·
                      refine ⟨2426039480894497342784029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12938877231437319161514821 2426039480894497342784029)
                      ·
                        rfl

theorem cell23_4724695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_4724695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724695 prefixEnd_4724695 := by exact prefixLift 4724695
  have htrace : WordTrace (prefixWord ++ tailWord_4724695) baseStart_4724695 baseEnd_4724695 := by
    simpa [prefixWord, tailWord_4724695, baseEnd_4724695] using wordTrace_append hprefix tailTrace_4724695
  have hstable : (prefixWord ++ tailWord_4724695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724695).length < 2 ^ (prefixWord ++ tailWord_4724695).sum := by decide
  have hdescent : baseEnd_4724695 < baseStart_4724695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724700 : List Nat := [2, 2, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_4724700 : Nat := 118140960795 + 4724700 * 2 ^ 59
def prefixEnd_4724700 : Nat := 4983230072969 + 3 ^ 40 * 4724700 * 2
def baseEnd_4724700 : Nat := 808680682765923274407169

theorem tailTrace_4724700 : CollatzResearch.WordTrace tailWord_4724700 prefixEnd_4724700 808680682765923274407169 := by
  unfold tailWord_4724700
  simp only [CollatzResearch.WordTrace]
  refine ⟨86161982991613144681681777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114882643988817526242242369 86161982991613144681681777)
  ·
    refine ⟨64621487243709858511261333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86161982991613144681681777 64621487243709858511261333)
    ·
      refine ⟨3029132214548899617715375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64621487243709858511261333 3029132214548899617715375)
      ·
        refine ⟨4543698321823349426573063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029132214548899617715375 4543698321823349426573063)
        ·
          refine ⟨6815547482735024139859595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4543698321823349426573063 6815547482735024139859595)
          ·
            refine ⟨10223321224102536209789393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6815547482735024139859595 10223321224102536209789393)
            ·
              refine ⟨7667490918076902157342045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10223321224102536209789393 7667490918076902157342045)
              ·
                refine ⟨2875309094278838309003267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7667490918076902157342045 2875309094278838309003267)
                ·
                  refine ⟨4312963641418257463504901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875309094278838309003267 4312963641418257463504901)
                  ·
                    refine ⟨808680682765923274407169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4312963641418257463504901 808680682765923274407169)
                    ·
                      rfl

theorem cell23_4724700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_4724700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724700 prefixEnd_4724700 := by exact prefixLift 4724700
  have htrace : WordTrace (prefixWord ++ tailWord_4724700) baseStart_4724700 baseEnd_4724700 := by
    simpa [prefixWord, tailWord_4724700, baseEnd_4724700] using wordTrace_append hprefix tailTrace_4724700
  have hstable : (prefixWord ++ tailWord_4724700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724700).length < 2 ^ (prefixWord ++ tailWord_4724700).sum := by decide
  have hdescent : baseEnd_4724700 < baseStart_4724700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724705 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 1, 6]
def baseStart_4724705 : Nat := 118140960795 + 4724705 * 2 ^ 59
def prefixEnd_4724705 : Nat := 4983230072969 + 3 ^ 40 * 4724705 * 2
def baseEnd_4724705 : Nat := 808681538567014101219661

theorem tailTrace_4724705 : CollatzResearch.WordTrace tailWord_4724705 prefixEnd_4724705 808681538567014101219661 := by
  unfold tailWord_4724705
  simp only [CollatzResearch.WordTrace]
  refine ⟨172324148348208175217295569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114882765565472116811530379 172324148348208175217295569)
  ·
    refine ⟨129243111261156131412971677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172324148348208175217295569 129243111261156131412971677)
    ·
      refine ⟨48466166722933549279864379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129243111261156131412971677 48466166722933549279864379)
      ·
        refine ⟨72699250084400323919796569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48466166722933549279864379 72699250084400323919796569)
        ·
          refine ⟨54524437563300242939847427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72699250084400323919796569 54524437563300242939847427)
          ·
            refine ⟨81786656344950364409771141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54524437563300242939847427 81786656344950364409771141)
            ·
              refine ⟨15334998064678193326832089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81786656344950364409771141 15334998064678193326832089)
              ·
                refine ⟨11501248548508644995124067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15334998064678193326832089 11501248548508644995124067)
                ·
                  refine ⟨17251872822762967492686101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11501248548508644995124067 17251872822762967492686101)
                  ·
                    refine ⟨808681538567014101219661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17251872822762967492686101 808681538567014101219661)
                    ·
                      rfl

theorem cell23_4724705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_4724705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724705 prefixEnd_4724705 := by exact prefixLift 4724705
  have htrace : WordTrace (prefixWord ++ tailWord_4724705) baseStart_4724705 baseEnd_4724705 := by
    simpa [prefixWord, tailWord_4724705, baseEnd_4724705] using wordTrace_append hprefix tailTrace_4724705
  have hstable : (prefixWord ++ tailWord_4724705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724705).length < 2 ^ (prefixWord ++ tailWord_4724705).sum := by decide
  have hdescent : baseEnd_4724705 < baseStart_4724705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724729 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 3, 2, 2]
def baseStart_4724729 : Nat := 118140960795 + 4724729 * 2 ^ 59
def prefixEnd_4724729 : Nat := 4983230072969 + 3 ^ 40 * 4724729 * 2
def baseEnd_4724729 : Nat := 2426056939236750209758873

theorem tailTrace_4724729 : CollatzResearch.WordTrace tailWord_4724729 prefixEnd_4724729 2426056939236750209758873 := by
  unfold tailWord_4724729
  simp only [CollatzResearch.WordTrace]
  refine ⟨172325023700121227316169241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114883349133414151544112827 172325023700121227316169241)
  ·
    refine ⟨129243767775090920487126931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172325023700121227316169241 129243767775090920487126931)
    ·
      refine ⟨193865651662636380730690397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129243767775090920487126931 193865651662636380730690397)
      ·
        refine ⟨72699619373488642774008899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193865651662636380730690397 72699619373488642774008899)
        ·
          refine ⟨109049429060232964161013349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72699619373488642774008899 109049429060232964161013349)
          ·
            refine ⟨20446767948793680780190003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109049429060232964161013349 20446767948793680780190003)
            ·
              refine ⟨30670151923190521170285005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20446767948793680780190003 30670151923190521170285005)
              ·
                refine ⟨11501306971196445438856877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30670151923190521170285005 11501306971196445438856877)
                ·
                  refine ⟨4312990114198667039571329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11501306971196445438856877 4312990114198667039571329)
                  ·
                    refine ⟨3234742585649000279678497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4312990114198667039571329 3234742585649000279678497)
                    ·
                      refine ⟨2426056939236750209758873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234742585649000279678497 2426056939236750209758873)
                      ·
                        rfl

theorem cell23_4724729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_4724729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724729 prefixEnd_4724729 := by exact prefixLift 4724729
  have htrace : WordTrace (prefixWord ++ tailWord_4724729) baseStart_4724729 baseEnd_4724729 := by
    simpa [prefixWord, tailWord_4724729, baseEnd_4724729] using wordTrace_append hprefix tailTrace_4724729
  have hstable : (prefixWord ++ tailWord_4724729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724729).length < 2 ^ (prefixWord ++ tailWord_4724729).sum := by decide
  have hdescent : baseEnd_4724729 < baseStart_4724729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724815 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_4724815 : Nat := 118140960795 + 4724815 * 2 ^ 59
def prefixEnd_4724815 : Nat := 4983230072969 + 3 ^ 40 * 4724815 * 2
def baseEnd_4724815 : Nat := 2426101098573036873283477

theorem tailTrace_4724815 : CollatzResearch.WordTrace tailWord_4724815 prefixEnd_4724815 2426101098573036873283477 := by
  unfold tailWord_4724815
  simp only [CollatzResearch.WordTrace]
  refine ⟨172328160377809664003799899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114885440251873109335866599 172328160377809664003799899)
  ·
    refine ⟨258492240566714496005699849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172328160377809664003799899 258492240566714496005699849)
    ·
      refine ⟨193869180425035872004274887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258492240566714496005699849 193869180425035872004274887)
      ·
        refine ⟨290803770637553808006412331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193869180425035872004274887 290803770637553808006412331)
        ·
          refine ⟨436205655956330712009618497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290803770637553808006412331 436205655956330712009618497)
          ·
            refine ⟨327154241967248034007213873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436205655956330712009618497 327154241967248034007213873)
            ·
              refine ⟨245365681475436025505410405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327154241967248034007213873 245365681475436025505410405)
              ·
                refine ⟨46006065276644254782264451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245365681475436025505410405 46006065276644254782264451)
                ·
                  refine ⟨69009097914966382173396677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46006065276644254782264451 69009097914966382173396677)
                  ·
                    refine ⟨12939205859056196657511877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 69009097914966382173396677 12939205859056196657511877)
                    ·
                      refine ⟨2426101098573036873283477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12939205859056196657511877 2426101098573036873283477)
                      ·
                        rfl

theorem cell23_4724815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_4724815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724815 prefixEnd_4724815 := by exact prefixLift 4724815
  have htrace : WordTrace (prefixWord ++ tailWord_4724815) baseStart_4724815 baseEnd_4724815 := by
    simpa [prefixWord, tailWord_4724815, baseEnd_4724815] using wordTrace_append hprefix tailTrace_4724815
  have hstable : (prefixWord ++ tailWord_4724815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724815).length < 2 ^ (prefixWord ++ tailWord_4724815).sum := by decide
  have hdescent : baseEnd_4724815 < baseStart_4724815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724835 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4724835 : Nat := 118140960795 + 4724835 * 2 ^ 59
def prefixEnd_4724835 : Nat := 4983230072969 + 3 ^ 40 * 4724835 * 2
def baseEnd_4724835 : Nat := 2426111368186126795033385

theorem tailTrace_4724835 : CollatzResearch.WordTrace tailWord_4724835 prefixEnd_4724835 2426111368186126795033385 := by
  unfold tailWord_4724835
  simp only [CollatzResearch.WordTrace]
  refine ⟨172328889837737207419527959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114885926558491471613018639 172328889837737207419527959)
  ·
    refine ⟨258493334756605811129291939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172328889837737207419527959 258493334756605811129291939)
    ·
      refine ⟨387740002134908716693937909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258493334756605811129291939 387740002134908716693937909)
      ·
        refine ⟨36350625200147692190056679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 387740002134908716693937909 36350625200147692190056679)
        ·
          refine ⟨54525937800221538285085019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36350625200147692190056679 54525937800221538285085019)
          ·
            refine ⟨81788906700332307427627529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54525937800221538285085019 81788906700332307427627529)
            ·
              refine ⟨61341680025249230570720647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81788906700332307427627529 61341680025249230570720647)
              ·
                refine ⟨92012520037873845856080971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61341680025249230570720647 92012520037873845856080971)
                ·
                  refine ⟨138018780056810768784121457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92012520037873845856080971 138018780056810768784121457)
                  ·
                    refine ⟨103514085042608076588091093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138018780056810768784121457 103514085042608076588091093)
                    ·
                      refine ⟨2426111368186126795033385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103514085042608076588091093 2426111368186126795033385)
                      ·
                        rfl

theorem cell23_4724835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4724835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724835 prefixEnd_4724835 := by exact prefixLift 4724835
  have htrace : WordTrace (prefixWord ++ tailWord_4724835) baseStart_4724835 baseEnd_4724835 := by
    simpa [prefixWord, tailWord_4724835, baseEnd_4724835] using wordTrace_append hprefix tailTrace_4724835
  have hstable : (prefixWord ++ tailWord_4724835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724835).length < 2 ^ (prefixWord ++ tailWord_4724835).sum := by decide
  have hdescent : baseEnd_4724835 < baseStart_4724835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724836 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_4724836 : Nat := 118140960795 + 4724836 * 2 ^ 59
def prefixEnd_4724836 : Nat := 4983230072969 + 3 ^ 40 * 4724836 * 2
def baseEnd_4724836 : Nat := 2426111881666781291120881

theorem tailTrace_4724836 : CollatzResearch.WordTrace tailWord_4724836 prefixEnd_4724836 2426111881666781291120881 := by
  unfold tailWord_4724836
  simp only [CollatzResearch.WordTrace]
  refine ⟨86164463155366792295157181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114885950873822389726876241 86164463155366792295157181)
  ·
    refine ⟨32311673683262547110683943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86164463155366792295157181 32311673683262547110683943)
    ·
      refine ⟨48467510524893820666025915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32311673683262547110683943 48467510524893820666025915)
      ·
        refine ⟨72701265787340730999038873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48467510524893820666025915 72701265787340730999038873)
        ·
          refine ⟨54525949340505548249279155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72701265787340730999038873 54525949340505548249279155)
          ·
            refine ⟨81788924010758322373918733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54525949340505548249279155 81788924010758322373918733)
            ·
              refine ⟨30670846504034370890219525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81788924010758322373918733 30670846504034370890219525)
              ·
                refine ⟨5750783719506444541916161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30670846504034370890219525 5750783719506444541916161)
                ·
                  refine ⟨4313087789629833406437121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5750783719506444541916161 4313087789629833406437121)
                  ·
                    refine ⟨3234815842222375054827841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4313087789629833406437121 3234815842222375054827841)
                    ·
                      refine ⟨2426111881666781291120881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234815842222375054827841 2426111881666781291120881)
                      ·
                        rfl

theorem cell23_4724836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_4724836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724836 prefixEnd_4724836 := by exact prefixLift 4724836
  have htrace : WordTrace (prefixWord ++ tailWord_4724836) baseStart_4724836 baseEnd_4724836 := by
    simpa [prefixWord, tailWord_4724836, baseEnd_4724836] using wordTrace_append hprefix tailTrace_4724836
  have hstable : (prefixWord ++ tailWord_4724836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724836).length < 2 ^ (prefixWord ++ tailWord_4724836).sum := by decide
  have hdescent : baseEnd_4724836 < baseStart_4724836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724909 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_4724909 : Nat := 118140960795 + 4724909 * 2 ^ 59
def prefixEnd_4724909 : Nat := 4983230072969 + 3 ^ 40 * 4724909 * 2
def baseEnd_4724909 : Nat := 2426149365754559505508045

theorem tailTrace_4724909 : CollatzResearch.WordTrace tailWord_4724909 prefixEnd_4724909 2426149365754559505508045 := by
  unfold tailWord_4724909
  simp only [CollatzResearch.WordTrace]
  refine ⟨172331588839469118057721781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114887725892979412038481187 172331588839469118057721781)
  ·
    refine ⟨16156086453700229817911417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172331588839469118057721781 16156086453700229817911417)
    ·
      refine ⟨12117064840275172363433563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16156086453700229817911417 12117064840275172363433563)
      ·
        refine ⟨18175597260412758545150345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12117064840275172363433563 18175597260412758545150345)
        ·
          refine ⟨13631697945309568908862759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18175597260412758545150345 13631697945309568908862759)
          ·
            refine ⟨20447546917964353363294139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13631697945309568908862759 20447546917964353363294139)
            ·
              refine ⟨30671320376946530044941209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20447546917964353363294139 30671320376946530044941209)
              ·
                refine ⟨23003490282709897533705907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30671320376946530044941209 23003490282709897533705907)
                ·
                  refine ⟨34505235424064846300558861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23003490282709897533705907 34505235424064846300558861)
                  ·
                    refine ⟨12939463284024317362709573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34505235424064846300558861 12939463284024317362709573)
                    ·
                      refine ⟨2426149365754559505508045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12939463284024317362709573 2426149365754559505508045)
                      ·
                        rfl

theorem cell23_4724909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_4724909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724909 prefixEnd_4724909 := by exact prefixLift 4724909
  have htrace : WordTrace (prefixWord ++ tailWord_4724909) baseStart_4724909 baseEnd_4724909 := by
    simpa [prefixWord, tailWord_4724909, baseEnd_4724909] using wordTrace_append hprefix tailTrace_4724909
  have hstable : (prefixWord ++ tailWord_4724909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724909).length < 2 ^ (prefixWord ++ tailWord_4724909).sum := by decide
  have hdescent : baseEnd_4724909 < baseStart_4724909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724919 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 3, 4]
def baseStart_4724919 : Nat := 118140960795 + 4724919 * 2 ^ 59
def prefixEnd_4724919 : Nat := 4983230072969 + 3 ^ 40 * 4724919 * 2
def baseEnd_4724919 : Nat := 808718166853701488794333

theorem tailTrace_4724919 : CollatzResearch.WordTrace tailWord_4724919 prefixEnd_4724919 808718166853701488794333 := by
  unfold tailWord_4724919
  simp only [CollatzResearch.WordTrace]
  refine ⟨172331953569432889765585811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114887969046288593177057207 172331953569432889765585811)
  ·
    refine ⟨258497930354149334648378717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172331953569432889765585811 258497930354149334648378717)
    ·
      refine ⟨96936723882806000493142019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258497930354149334648378717 96936723882806000493142019)
      ·
        refine ⟨145405085824209000739713029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96936723882806000493142019 145405085824209000739713029)
        ·
          refine ⟨27263453592039187638696193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145405085824209000739713029 27263453592039187638696193)
          ·
            refine ⟨20447590194029390729022145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27263453592039187638696193 20447590194029390729022145)
            ·
              refine ⟨15335692645522043046766609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20447590194029390729022145 15335692645522043046766609)
              ·
                refine ⟨11501769484141532285074957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15335692645522043046766609 11501769484141532285074957)
                ·
                  refine ⟨4313163556553074606903109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11501769484141532285074957 4313163556553074606903109)
                  ·
                    refine ⟨808718166853701488794333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4313163556553074606903109 808718166853701488794333)
                    ·
                      rfl

theorem cell23_4724919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_4724919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724919 prefixEnd_4724919 := by exact prefixLift 4724919
  have htrace : WordTrace (prefixWord ++ tailWord_4724919) baseStart_4724919 baseEnd_4724919 := by
    simpa [prefixWord, tailWord_4724919, baseEnd_4724919] using wordTrace_append hprefix tailTrace_4724919
  have hstable : (prefixWord ++ tailWord_4724919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724919).length < 2 ^ (prefixWord ++ tailWord_4724919).sum := by decide
  have hdescent : baseEnd_4724919 < baseStart_4724919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724946 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_4724946 : Nat := 118140960795 + 4724946 * 2 ^ 59
def prefixEnd_4724946 : Nat := 4983230072969 + 3 ^ 40 * 4724946 * 2
def baseEnd_4724946 : Nat := 2426168364538775860745375

theorem tailTrace_4724946 : CollatzResearch.WordTrace tailWord_4724946 prefixEnd_4724946 2426168364538775860745375 := by
  unfold tailWord_4724946
  simp only [CollatzResearch.WordTrace]
  refine ⟨43083234585083768344204673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114888625560223382251212461 43083234585083768344204673)
  ·
    refine ⟨32312425938812826258153505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43083234585083768344204673 32312425938812826258153505)
    ·
      refine ⟨24234319454109619693615129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32312425938812826258153505 24234319454109619693615129)
      ·
        refine ⟨18175739590582214770211347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24234319454109619693615129 18175739590582214770211347)
        ·
          refine ⟨27263609385873322155317021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18175739590582214770211347 27263609385873322155317021)
          ·
            refine ⟨10223853519702495808243883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27263609385873322155317021 10223853519702495808243883)
            ·
              refine ⟨15335780279553743712365825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10223853519702495808243883 15335780279553743712365825)
              ·
                refine ⟨11501835209665307784274369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15335780279553743712365825 11501835209665307784274369)
                ·
                  refine ⟨8626376407248980838205777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11501835209665307784274369 8626376407248980838205777)
                  ·
                    refine ⟨6469782305436735628654333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8626376407248980838205777 6469782305436735628654333)
                    ·
                      refine ⟨2426168364538775860745375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6469782305436735628654333 2426168364538775860745375)
                      ·
                        rfl

theorem cell23_4724946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_4724946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724946 prefixEnd_4724946 := by exact prefixLift 4724946
  have htrace : WordTrace (prefixWord ++ tailWord_4724946) baseStart_4724946 baseEnd_4724946 := by
    simpa [prefixWord, tailWord_4724946, baseEnd_4724946] using wordTrace_append hprefix tailTrace_4724946
  have hstable : (prefixWord ++ tailWord_4724946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724946).length < 2 ^ (prefixWord ++ tailWord_4724946).sum := by decide
  have hdescent : baseEnd_4724946 < baseStart_4724946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724986 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2]
def baseStart_4724986 : Nat := 118140960795 + 4724986 * 2 ^ 59
def prefixEnd_4724986 : Nat := 4983230072969 + 3 ^ 40 * 4724986 * 2
def baseEnd_4724986 : Nat := 2426188903764955704245191

theorem tailTrace_4724986 : CollatzResearch.WordTrace tailWord_4724986 prefixEnd_4724986 2426188903764955704245191 := by
  unfold tailWord_4724986
  simp only [CollatzResearch.WordTrace]
  refine ⟨43083599315047540052068703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114889598173460106805516541 43083599315047540052068703)
  ·
    refine ⟨64625398972571310078103055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43083599315047540052068703 64625398972571310078103055)
    ·
      refine ⟨96938098458856965117154583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64625398972571310078103055 96938098458856965117154583)
      ·
        refine ⟨145407147688285447675731875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96938098458856965117154583 145407147688285447675731875)
        ·
          refine ⟨218110721532428171513597813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145407147688285447675731875 218110721532428171513597813)
          ·
            refine ⟨20447880143665141079399795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218110721532428171513597813 20447880143665141079399795)
            ·
              refine ⟨30671820215497711619099693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20447880143665141079399795 30671820215497711619099693)
              ·
                refine ⟨11501932580811641857162385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30671820215497711619099693 11501932580811641857162385)
                ·
                  refine ⟨8626449435608731392871789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11501932580811641857162385 8626449435608731392871789)
                  ·
                    refine ⟨3234918538353274272326921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8626449435608731392871789 3234918538353274272326921)
                    ·
                      refine ⟨2426188903764955704245191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234918538353274272326921 2426188903764955704245191)
                      ·
                        rfl

theorem cell23_4724986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_4724986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724986 prefixEnd_4724986 := by exact prefixLift 4724986
  have htrace : WordTrace (prefixWord ++ tailWord_4724986) baseStart_4724986 baseEnd_4724986 := by
    simpa [prefixWord, tailWord_4724986, baseEnd_4724986] using wordTrace_append hprefix tailTrace_4724986
  have hstable : (prefixWord ++ tailWord_4724986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724986).length < 2 ^ (prefixWord ++ tailWord_4724986).sum := by decide
  have hdescent : baseEnd_4724986 < baseStart_4724986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724992 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 3, 6]
def baseStart_4724992 : Nat := 118140960795 + 4724992 * 2 ^ 59
def prefixEnd_4724992 : Nat := 4983230072969 + 3 ^ 40 * 4724992 * 2
def baseEnd_4724992 : Nat := 808730661549627560256721

theorem tailTrace_4724992 : CollatzResearch.WordTrace tailWord_4724992 prefixEnd_4724992 808730661549627560256721 := by
  unfold tailWord_4724992
  simp only [CollatzResearch.WordTrace]
  refine ⟨86167308049084211616496615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114889744065445615488662153 86167308049084211616496615)
  ·
    refine ⟨129250962073626317424744923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86167308049084211616496615 129250962073626317424744923)
    ·
      refine ⟨193876443110439476137117385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129250962073626317424744923 193876443110439476137117385)
      ·
        refine ⟨145407332332829607102838039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193876443110439476137117385 145407332332829607102838039)
        ·
          refine ⟨218110998499244410654257059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145407332332829607102838039 218110998499244410654257059)
          ·
            refine ⟨327166497748866615981385589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218110998499244410654257059 327166497748866615981385589)
            ·
              refine ⟨30671859163956245248254899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 327166497748866615981385589 30671859163956245248254899)
              ·
                refine ⟨46007788745934367872382349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30671859163956245248254899 46007788745934367872382349)
                ·
                  refine ⟨17252920779725387952143381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46007788745934367872382349 17252920779725387952143381)
                  ·
                    refine ⟨808730661549627560256721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17252920779725387952143381 808730661549627560256721)
                    ·
                      rfl

theorem cell23_4724992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_4724992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724992 prefixEnd_4724992 := by exact prefixLift 4724992
  have htrace : WordTrace (prefixWord ++ tailWord_4724992) baseStart_4724992 baseEnd_4724992 := by
    simpa [prefixWord, tailWord_4724992, baseEnd_4724992] using wordTrace_append hprefix tailTrace_4724992
  have hstable : (prefixWord ++ tailWord_4724992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724992).length < 2 ^ (prefixWord ++ tailWord_4724992).sum := by decide
  have hdescent : baseEnd_4724992 < baseStart_4724992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4724993 : List Nat := [1, 2, 4, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_4724993 : Nat := 118140960795 + 4724993 * 2 ^ 59
def prefixEnd_4724993 : Nat := 4983230072969 + 3 ^ 40 * 4724993 * 2
def baseEnd_4724993 : Nat := 2426192498129537176857659

theorem tailTrace_4724993 : CollatzResearch.WordTrace tailWord_4724993 prefixEnd_4724993 2426192498129537176857659 := by
  unfold tailWord_4724993
  simp only [CollatzResearch.WordTrace]
  refine ⟨172334652571164800403779633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114889768380776533602519755 172334652571164800403779633)
  ·
    refine ⟨129250989428373600302834725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172334652571164800403779633 129250989428373600302834725)
    ·
      refine ⟨24234560517820050056781511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129250989428373600302834725 24234560517820050056781511)
      ·
        refine ⟨36351840776730075085172267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24234560517820050056781511 36351840776730075085172267)
        ·
          refine ⟨54527761165095112627758401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36351840776730075085172267 54527761165095112627758401)
          ·
            refine ⟨40895820873821334470818801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54527761165095112627758401 40895820873821334470818801)
            ·
              refine ⟨30671865655366000853114101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40895820873821334470818801 30671865655366000853114101)
              ·
                refine ⟨2875487405190562579979447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30671865655366000853114101 2875487405190562579979447)
                ·
                  refine ⟨4313231107785843869969171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875487405190562579979447 4313231107785843869969171)
                  ·
                    refine ⟨6469846661678765804953757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4313231107785843869969171 6469846661678765804953757)
                    ·
                      refine ⟨2426192498129537176857659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6469846661678765804953757 2426192498129537176857659)
                      ·
                        rfl

theorem cell23_4724993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_4724993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4724993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4724993 prefixEnd_4724993 := by exact prefixLift 4724993
  have htrace : WordTrace (prefixWord ++ tailWord_4724993) baseStart_4724993 baseEnd_4724993 := by
    simpa [prefixWord, tailWord_4724993, baseEnd_4724993] using wordTrace_append hprefix tailTrace_4724993
  have hstable : (prefixWord ++ tailWord_4724993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4724993).length < 2 ^ (prefixWord ++ tailWord_4724993).sum := by decide
  have hdescent : baseEnd_4724993 < baseStart_4724993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4724993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725019 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 3]
def baseStart_4725019 : Nat := 118140960795 + 4725019 * 2 ^ 59
def prefixEnd_4725019 : Nat := 4983230072969 + 3 ^ 40 * 4725019 * 2
def baseEnd_4725019 : Nat := 2426205848626554075132539

theorem tailTrace_4725019 : CollatzResearch.WordTrace tailWord_4725019 prefixEnd_4725019 2426205848626554075132539 := by
  unfold tailWord_4725019
  simp only [CollatzResearch.WordTrace]
  refine ⟨172335600869070606844226111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114890400579380404562817407 172335600869070606844226111)
  ·
    refine ⟨258503401303605910266339167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172335600869070606844226111 258503401303605910266339167)
    ·
      refine ⟨387755101955408865399508751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258503401303605910266339167 387755101955408865399508751)
      ·
        refine ⟨581632652933113298099263127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387755101955408865399508751 581632652933113298099263127)
        ·
          refine ⟨872448979399669947148894691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581632652933113298099263127 872448979399669947148894691)
          ·
            refine ⟨1308673469099504920723342037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872448979399669947148894691 1308673469099504920723342037)
            ·
              refine ⟨30672034432019646579453329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1308673469099504920723342037 30672034432019646579453329)
              ·
                refine ⟨23004025824014734934589997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30672034432019646579453329 23004025824014734934589997)
                ·
                  refine ⟨8626509684005525600471249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23004025824014734934589997 8626509684005525600471249)
                  ·
                    refine ⟨6469882263004144200353437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8626509684005525600471249 6469882263004144200353437)
                    ·
                      refine ⟨2426205848626554075132539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6469882263004144200353437 2426205848626554075132539)
                      ·
                        rfl

theorem cell23_4725019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 3].length) (baseStart_4725019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725019 prefixEnd_4725019 := by exact prefixLift 4725019
  have htrace : WordTrace (prefixWord ++ tailWord_4725019) baseStart_4725019 baseEnd_4725019 := by
    simpa [prefixWord, tailWord_4725019, baseEnd_4725019] using wordTrace_append hprefix tailTrace_4725019
  have hstable : (prefixWord ++ tailWord_4725019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725019).length < 2 ^ (prefixWord ++ tailWord_4725019).sum := by decide
  have hdescent : baseEnd_4725019 < baseStart_4725019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725026 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_4725026 : Nat := 118140960795 + 4725026 * 2 ^ 59
def prefixEnd_4725026 : Nat := 4983230072969 + 3 ^ 40 * 4725026 * 2
def baseEnd_4725026 : Nat := 808736480997045182581669

theorem tailTrace_4725026 : CollatzResearch.WordTrace tailWord_4725026 prefixEnd_4725026 808736480997045182581669 := by
  unfold tailWord_4725026
  simp only [CollatzResearch.WordTrace]
  refine ⟨43083964045011311759932733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114890570786696831359820621 43083964045011311759932733)
  ·
    refine ⟨16156486516879241909974775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43083964045011311759932733 16156486516879241909974775)
    ·
      refine ⟨24234729775318862864962163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16156486516879241909974775 24234729775318862864962163)
      ·
        refine ⟨36352094662978294297443245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24234729775318862864962163 36352094662978294297443245)
        ·
          refine ⟨13632035498616860361541217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36352094662978294297443245 13632035498616860361541217)
          ·
            refine ⟨10224026623962645271155913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13632035498616860361541217 10224026623962645271155913)
            ·
              refine ⟨7668019967971983953366935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10224026623962645271155913 7668019967971983953366935)
              ·
                refine ⟨11502029951957975930050403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7668019967971983953366935 11502029951957975930050403)
                ·
                  refine ⟨17253044927936963895075605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11502029951957975930050403 17253044927936963895075605)
                  ·
                    refine ⟨808736480997045182581669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17253044927936963895075605 808736480997045182581669)
                    ·
                      rfl

theorem cell23_4725026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_4725026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725026 prefixEnd_4725026 := by exact prefixLift 4725026
  have htrace : WordTrace (prefixWord ++ tailWord_4725026) baseStart_4725026 baseEnd_4725026 := by
    simpa [prefixWord, tailWord_4725026, baseEnd_4725026] using wordTrace_append hprefix tailTrace_4725026
  have hstable : (prefixWord ++ tailWord_4725026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725026).length < 2 ^ (prefixWord ++ tailWord_4725026).sum := by decide
  have hdescent : baseEnd_4725026 < baseStart_4725026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725037 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_4725037 : Nat := 118140960795 + 4725037 * 2 ^ 59
def prefixEnd_4725037 : Nat := 4983230072969 + 3 ^ 40 * 4725037 * 2
def baseEnd_4725037 : Nat := 2426215091278335004707457

theorem tailTrace_4725037 : CollatzResearch.WordTrace tailWord_4725037 prefixEnd_4725037 2426215091278335004707457 := by
  unfold tailWord_4725037
  simp only [CollatzResearch.WordTrace]
  refine ⟨172336257383005395918381365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114890838255336930612254243 172336257383005395918381365)
  ·
    refine ⟨16156524129656755867348253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 172336257383005395918381365 16156524129656755867348253)
    ·
      refine ⟨6058696548621283450255595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16156524129656755867348253 6058696548621283450255595)
      ·
        refine ⟨9088044822931925175383393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6058696548621283450255595 9088044822931925175383393)
        ·
          refine ⟨6816033617198943881537545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9088044822931925175383393 6816033617198943881537545)
          ·
            refine ⟨5112025212899207911153159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6816033617198943881537545 5112025212899207911153159)
            ·
              refine ⟨7668037819348811866729739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112025212899207911153159 7668037819348811866729739)
              ·
                refine ⟨11502056729023217800094609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7668037819348811866729739 11502056729023217800094609)
                ·
                  refine ⟨8626542546767413350070957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11502056729023217800094609 8626542546767413350070957)
                  ·
                    refine ⟨3234953455037780006276609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8626542546767413350070957 3234953455037780006276609)
                    ·
                      refine ⟨2426215091278335004707457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234953455037780006276609 2426215091278335004707457)
                      ·
                        rfl

theorem cell23_4725037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_4725037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725037 prefixEnd_4725037 := by exact prefixLift 4725037
  have htrace : WordTrace (prefixWord ++ tailWord_4725037) baseStart_4725037 baseEnd_4725037 := by
    simpa [prefixWord, tailWord_4725037, baseEnd_4725037] using wordTrace_append hprefix tailTrace_4725037
  have hstable : (prefixWord ++ tailWord_4725037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725037).length < 2 ^ (prefixWord ++ tailWord_4725037).sum := by decide
  have hdescent : baseEnd_4725037 < baseStart_4725037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725050 : List Nat := [3, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2]
def baseStart_4725050 : Nat := 118140960795 + 4725050 * 2 ^ 59
def prefixEnd_4725050 : Nat := 4983230072969 + 3 ^ 40 * 4725050 * 2
def baseEnd_4725050 : Nat := 2426221766526843453844897

theorem tailTrace_4725050 : CollatzResearch.WordTrace tailWord_4725050 prefixEnd_4725050 2426221766526843453844897 := by
  unfold tailWord_4725050
  simp only [CollatzResearch.WordTrace]
  refine ⟨43084182882989574784651151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114891154354638866092403069 43084182882989574784651151)
  ·
    refine ⟨64626274324484362176976727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43084182882989574784651151 64626274324484362176976727)
    ·
      refine ⟨96939411486726543265465091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64626274324484362176976727 96939411486726543265465091)
      ·
        refine ⟨145409117230089814898197637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96939411486726543265465091 145409117230089814898197637)
        ·
          refine ⟨27264209480641840293412057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145409117230089814898197637 27264209480641840293412057)
          ·
            refine ⟨20448157110481380220059043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27264209480641840293412057 20448157110481380220059043)
            ·
              refine ⟨30672235665722070330088565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20448157110481380220059043 30672235665722070330088565)
              ·
                refine ⟨2875522093661444093445803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30672235665722070330088565 2875522093661444093445803)
                ·
                  refine ⟨4313283140492166140168705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875522093661444093445803 4313283140492166140168705)
                  ·
                    refine ⟨3234962355369124605126529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4313283140492166140168705 3234962355369124605126529)
                    ·
                      refine ⟨2426221766526843453844897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234962355369124605126529 2426221766526843453844897)
                      ·
                        rfl

theorem cell23_4725050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2].length) (baseStart_4725050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725050 prefixEnd_4725050 := by exact prefixLift 4725050
  have htrace : WordTrace (prefixWord ++ tailWord_4725050) baseStart_4725050 baseEnd_4725050 := by
    simpa [prefixWord, tailWord_4725050, baseEnd_4725050] using wordTrace_append hprefix tailTrace_4725050
  have hstable : (prefixWord ++ tailWord_4725050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725050).length < 2 ^ (prefixWord ++ tailWord_4725050).sum := by decide
  have hdescent : baseEnd_4725050 < baseStart_4725050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725093 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 1, 3, 2]
def baseStart_4725093 : Nat := 118140960795 + 4725093 * 2 ^ 59
def prefixEnd_4725093 : Nat := 4983230072969 + 3 ^ 40 * 4725093 * 2
def baseEnd_4725093 : Nat := 2426243846194986785607199

theorem tailTrace_4725093 : CollatzResearch.WordTrace tailWord_4725093 prefixEnd_4725093 2426243846194986785607199 := by
  unfold tailWord_4725093
  simp only [CollatzResearch.WordTrace]
  refine ⟨172338299870802517482419933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114892199913868344988279955 172338299870802517482419933)
  ·
    refine ⟨64626862451550944055907475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 172338299870802517482419933 64626862451550944055907475)
    ·
      refine ⟨96940293677326416083861213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64626862451550944055907475 96940293677326416083861213)
      ·
        refine ⟨36352610128997406031447955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96940293677326416083861213 36352610128997406031447955)
        ·
          refine ⟨54528915193496109047171933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36352610128997406031447955 54528915193496109047171933)
          ·
            refine ⟨20448343197561040892689475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54528915193496109047171933 20448343197561040892689475)
            ·
              refine ⟨30672514796341561339034213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20448343197561040892689475 30672514796341561339034213)
              ·
                refine ⟨5751096524314042751068915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30672514796341561339034213 5751096524314042751068915)
                ·
                  refine ⟨8626644786471064126603373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5751096524314042751068915 8626644786471064126603373)
                  ·
                    refine ⟨3234991794926649047476265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8626644786471064126603373 3234991794926649047476265)
                    ·
                      refine ⟨2426243846194986785607199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3234991794926649047476265 2426243846194986785607199)
                      ·
                        rfl

theorem cell23_4725093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_4725093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725093 prefixEnd_4725093 := by exact prefixLift 4725093
  have htrace : WordTrace (prefixWord ++ tailWord_4725093) baseStart_4725093 baseEnd_4725093 := by
    simpa [prefixWord, tailWord_4725093, baseEnd_4725093] using wordTrace_append hprefix tailTrace_4725093
  have hstable : (prefixWord ++ tailWord_4725093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725093).length < 2 ^ (prefixWord ++ tailWord_4725093).sum := by decide
  have hdescent : baseEnd_4725093 < baseStart_4725093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725180 : List Nat := [2, 2, 2, 4, 1, 1, 4, 2, 5]
def baseStart_4725180 : Nat := 118140960795 + 4725180 * 2 ^ 59
def prefixEnd_4725180 : Nat := 4983230072969 + 3 ^ 40 * 4725180 * 2
def baseEnd_4725180 : Nat := 269587613223547549468811

theorem tailTrace_4725180 : CollatzResearch.WordTrace tailWord_4725180 prefixEnd_4725180 269587613223547549468811 := by
  unfold tailWord_4725180
  simp only [CollatzResearch.WordTrace]
  refine ⟨86170736510743665670418497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114894315347658220893891329 86170736510743665670418497)
  ·
    refine ⟨64628052383057749252813873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86170736510743665670418497 64628052383057749252813873)
    ·
      refine ⟨48471039287293311939610405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64628052383057749252813873 48471039287293311939610405)
      ·
        refine ⟨9088319866367495988676951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48471039287293311939610405 9088319866367495988676951)
        ·
          refine ⟨13632479799551243983015427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9088319866367495988676951 13632479799551243983015427)
          ·
            refine ⟨20448719699326865974523141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13632479799551243983015427 20448719699326865974523141)
            ·
              refine ⟨3834134943623787370223089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20448719699326865974523141 3834134943623787370223089)
              ·
                refine ⟨2875601207717840527667317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834134943623787370223089 2875601207717840527667317)
                ·
                  refine ⟨269587613223547549468811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2875601207717840527667317 269587613223547549468811)
                  ·
                    rfl

theorem cell23_4725180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_4725180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725180 prefixEnd_4725180 := by exact prefixLift 4725180
  have htrace : WordTrace (prefixWord ++ tailWord_4725180) baseStart_4725180 baseEnd_4725180 := by
    simpa [prefixWord, tailWord_4725180, baseEnd_4725180] using wordTrace_append hprefix tailTrace_4725180
  have hstable : (prefixWord ++ tailWord_4725180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725180).length < 2 ^ (prefixWord ++ tailWord_4725180).sum := by decide
  have hdescent : baseEnd_4725180 < baseStart_4725180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725213 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_4725213 : Nat := 118140960795 + 4725213 * 2 ^ 59
def prefixEnd_4725213 : Nat := 4983230072969 + 3 ^ 40 * 4725213 * 2
def baseEnd_4725213 : Nat := 2426305463873526316106647

theorem tailTrace_4725213 : CollatzResearch.WordTrace tailWord_4725213 prefixEnd_4725213 2426305463873526316106647 := by
  unfold tailWord_4725213
  simp only [CollatzResearch.WordTrace]
  refine ⟨172342676630367777976788293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114895117753578518651192195 172342676630367777976788293)
  ·
    refine ⟨32314251868193958370647805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 172342676630367777976788293 32314251868193958370647805)
    ·
      refine ⟨12117844450572734388992927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32314251868193958370647805 12117844450572734388992927)
      ·
        refine ⟨18176766675859101583489391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12117844450572734388992927 18176766675859101583489391)
        ·
          refine ⟨27265150013788652375234087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18176766675859101583489391 27265150013788652375234087)
          ·
            refine ⟨40897725020682978562851131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27265150013788652375234087 40897725020682978562851131)
            ·
              refine ⟨61346587531024467844276697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40897725020682978562851131 61346587531024467844276697)
              ·
                refine ⟨46009940648268350883207523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61346587531024467844276697 46009940648268350883207523)
                ·
                  refine ⟨69014910972402526324811285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46009940648268350883207523 69014910972402526324811285)
                  ·
                    refine ⟨3235073951831368421475529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69014910972402526324811285 3235073951831368421475529)
                    ·
                      refine ⟨2426305463873526316106647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235073951831368421475529 2426305463873526316106647)
                      ·
                        rfl

theorem cell23_4725213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_4725213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725213 prefixEnd_4725213 := by exact prefixLift 4725213
  have htrace : WordTrace (prefixWord ++ tailWord_4725213) baseStart_4725213 baseEnd_4725213 := by
    simpa [prefixWord, tailWord_4725213, baseEnd_4725213] using wordTrace_append hprefix tailTrace_4725213
  have hstable : (prefixWord ++ tailWord_4725213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725213).length < 2 ^ (prefixWord ++ tailWord_4725213).sum := by decide
  have hdescent : baseEnd_4725213 < baseStart_4725213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725216 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 3]
def baseStart_4725216 : Nat := 118140960795 + 4725216 * 2 ^ 59
def prefixEnd_4725216 : Nat := 4983230072969 + 3 ^ 40 * 4725216 * 2
def baseEnd_4725216 : Nat := 2426307004315489804369133

theorem tailTrace_4725216 : CollatzResearch.WordTrace tailWord_4725216 prefixEnd_4725216 2426307004315489804369133 := by
  unfold tailWord_4725216
  simp only [CollatzResearch.WordTrace]
  refine ⟨86171393024678454744573751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114895190699571272992765001 86171393024678454744573751)
  ·
    refine ⟨129257089537017682116860627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86171393024678454744573751 129257089537017682116860627)
    ·
      refine ⟨193885634305526523175290941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129257089537017682116860627 193885634305526523175290941)
      ·
        refine ⟨72707112864572446190734103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193885634305526523175290941 72707112864572446190734103)
        ·
          refine ⟨109060669296858669286101155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72707112864572446190734103 109060669296858669286101155)
          ·
            refine ⟨163591003945288003929151733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109060669296858669286101155 163591003945288003929151733)
            ·
              refine ⟨15336656619870750368357975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163591003945288003929151733 15336656619870750368357975)
              ·
                refine ⟨23004984929806125552536963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15336656619870750368357975 23004984929806125552536963)
                ·
                  refine ⟨34507477394709188328805445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23004984929806125552536963 34507477394709188328805445)
                  ·
                    refine ⟨6470152011507972811651021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34507477394709188328805445 6470152011507972811651021)
                    ·
                      refine ⟨2426307004315489804369133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6470152011507972811651021 2426307004315489804369133)
                      ·
                        rfl

theorem cell23_4725216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_4725216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725216 prefixEnd_4725216 := by exact prefixLift 4725216
  have htrace : WordTrace (prefixWord ++ tailWord_4725216) baseStart_4725216 baseEnd_4725216 := by
    simpa [prefixWord, tailWord_4725216, baseEnd_4725216] using wordTrace_append hprefix tailTrace_4725216
  have hstable : (prefixWord ++ tailWord_4725216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725216).length < 2 ^ (prefixWord ++ tailWord_4725216).sum := by decide
  have hdescent : baseEnd_4725216 < baseStart_4725216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725226 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_4725226 : Nat := 118140960795 + 4725226 * 2 ^ 59
def prefixEnd_4725226 : Nat := 4983230072969 + 3 ^ 40 * 4725226 * 2
def baseEnd_4725226 : Nat := 2426312139122034765244087

theorem tailTrace_4725226 : CollatzResearch.WordTrace tailWord_4725226 prefixEnd_4725226 2426312139122034765244087 := by
  unfold tailWord_4725226
  simp only [CollatzResearch.WordTrace]
  refine ⟨43085787694830170299252883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114895433852880454131341021 43085787694830170299252883)
  ·
    refine ⟨64628681542245255448879325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43085787694830170299252883 64628681542245255448879325)
    ·
      refine ⟨24235755578341970793329747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64628681542245255448879325 24235755578341970793329747)
      ·
        refine ⟨36353633367512956189994621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24235755578341970793329747 36353633367512956189994621)
        ·
          refine ⟨13632612512817358571247983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36353633367512956189994621 13632612512817358571247983)
          ·
            refine ⟨20448918769226037856871975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13632612512817358571247983 20448918769226037856871975)
            ·
              refine ⟨30673378153839056785307963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20448918769226037856871975 30673378153839056785307963)
              ·
                refine ⟨46010067230758585177961945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30673378153839056785307963 46010067230758585177961945)
                ·
                  refine ⟨34507550423068938883471459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46010067230758585177961945 34507550423068938883471459)
                  ·
                    refine ⟨51761325634603408325207189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34507550423068938883471459 51761325634603408325207189)
                    ·
                      refine ⟨2426312139122034765244087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51761325634603408325207189 2426312139122034765244087)
                      ·
                        rfl

theorem cell23_4725226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_4725226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725226 prefixEnd_4725226 := by exact prefixLift 4725226
  have htrace : WordTrace (prefixWord ++ tailWord_4725226) baseStart_4725226 baseEnd_4725226 := by
    simpa [prefixWord, tailWord_4725226, baseEnd_4725226] using wordTrace_append hprefix tailTrace_4725226
  have hstable : (prefixWord ++ tailWord_4725226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725226).length < 2 ^ (prefixWord ++ tailWord_4725226).sum := by decide
  have hdescent : baseEnd_4725226 < baseStart_4725226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725283 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 1, 5]
def baseStart_4725283 : Nat := 118140960795 + 4725283 * 2 ^ 59
def prefixEnd_4725283 : Nat := 4983230072969 + 3 ^ 40 * 4725283 * 2
def baseEnd_4725283 : Nat := 808780469173113680743775

theorem tailTrace_4725283 : CollatzResearch.WordTrace tailWord_4725283 prefixEnd_4725283 808780469173113680743775 := by
  unfold tailWord_4725283
  simp only [CollatzResearch.WordTrace]
  refine ⟨172345229740114179931836503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114896819826742786621224335 172345229740114179931836503)
  ·
    refine ⟨258517844610171269897754755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172345229740114179931836503 258517844610171269897754755)
    ·
      refine ⟨387776766915256904846632133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258517844610171269897754755 387776766915256904846632133)
      ·
        refine ⟨72708143796610669658743525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 387776766915256904846632133 72708143796610669658743525)
        ·
          refine ⟨13632776961864500561014411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72708143796610669658743525 13632776961864500561014411)
          ·
            refine ⟨20449165442796750841521617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13632776961864500561014411 20449165442796750841521617)
            ·
              refine ⟨15336874082097563131141213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20449165442796750841521617 15336874082097563131141213)
              ·
                refine ⟨5751327780786586174177955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15336874082097563131141213 5751327780786586174177955)
                ·
                  refine ⟨8626991671179879261266933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5751327780786586174177955 8626991671179879261266933)
                  ·
                    refine ⟨808780469173113680743775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8626991671179879261266933 808780469173113680743775)
                    ·
                      rfl

theorem cell23_4725283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 5].length) (baseStart_4725283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725283 prefixEnd_4725283 := by exact prefixLift 4725283
  have htrace : WordTrace (prefixWord ++ tailWord_4725283) baseStart_4725283 baseEnd_4725283 := by
    simpa [prefixWord, tailWord_4725283, baseEnd_4725283] using wordTrace_append hprefix tailTrace_4725283
  have hstable : (prefixWord ++ tailWord_4725283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725283).length < 2 ^ (prefixWord ++ tailWord_4725283).sum := by decide
  have hdescent : baseEnd_4725283 < baseStart_4725283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725290 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_4725290 : Nat := 118140960795 + 4725290 * 2 ^ 59
def prefixEnd_4725290 : Nat := 4983230072969 + 3 ^ 40 * 4725290 * 2
def baseEnd_4725290 : Nat := 2426345001883922514843793

theorem tailTrace_4725290 : CollatzResearch.WordTrace tailWord_4725290 prefixEnd_4725290 2426345001883922514843793 := by
  unfold tailWord_4725290
  simp only [CollatzResearch.WordTrace]
  refine ⟨43086371262772205031835331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114896990034059213418227549 43086371262772205031835331)
  ·
    refine ⟨64629556894158307547752997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43086371262772205031835331 64629556894158307547752997)
    ·
      refine ⟨12118041917654682665203687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64629556894158307547752997 12118041917654682665203687)
      ·
        refine ⟨18177062876482023997805531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12118041917654682665203687 18177062876482023997805531)
        ·
          refine ⟨27265594314723035996708297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18177062876482023997805531 27265594314723035996708297)
          ·
            refine ⟨20449195736042276997531223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27265594314723035996708297 20449195736042276997531223)
            ·
              refine ⟨30673793604063415496296835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20449195736042276997531223 30673793604063415496296835)
              ·
                refine ⟨46010690406095123244445253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30673793604063415496296835 46010690406095123244445253)
                ·
                  refine ⟨8627004451142835608333485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46010690406095123244445253 8627004451142835608333485)
                  ·
                    refine ⟨3235126669178563353125057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8627004451142835608333485 3235126669178563353125057)
                    ·
                      refine ⟨2426345001883922514843793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235126669178563353125057 2426345001883922514843793)
                      ·
                        rfl

theorem cell23_4725290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_4725290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725290 prefixEnd_4725290 := by exact prefixLift 4725290
  have htrace : WordTrace (prefixWord ++ tailWord_4725290) baseStart_4725290 baseEnd_4725290 := by
    simpa [prefixWord, tailWord_4725290, baseEnd_4725290] using wordTrace_append hprefix tailTrace_4725290
  have hstable : (prefixWord ++ tailWord_4725290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725290).length < 2 ^ (prefixWord ++ tailWord_4725290).sum := by decide
  have hdescent : baseEnd_4725290 < baseStart_4725290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725320 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_4725320 : Nat := 118140960795 + 4725320 * 2 ^ 59
def prefixEnd_4725320 : Nat := 4983230072969 + 3 ^ 40 * 4725320 * 2
def baseEnd_4725320 : Nat := 2426360406303557397468655

theorem tailTrace_4725320 : CollatzResearch.WordTrace tailWord_4725320 prefixEnd_4725320 2426360406303557397468655 := by
  unfold tailWord_4725320
  simp only [CollatzResearch.WordTrace]
  refine ⟨86173289620490067625466707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114897719493986756833955609 86173289620490067625466707)
  ·
    refine ⟨129259934430735101438200061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86173289620490067625466707 129259934430735101438200061)
    ·
      refine ⟨48472475411525663039325023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129259934430735101438200061 48472475411525663039325023)
      ·
        refine ⟨72708713117288494558987535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48472475411525663039325023 72708713117288494558987535)
        ·
          refine ⟨109063069675932741838481303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72708713117288494558987535 109063069675932741838481303)
          ·
            refine ⟨163594604513899112757721955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109063069675932741838481303 163594604513899112757721955)
            ·
              refine ⟨245391906770848669136582933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163594604513899112757721955 245391906770848669136582933)
              ·
                refine ⟨11502745629883531365777325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 245391906770848669136582933 11502745629883531365777325)
                ·
                  refine ⟨4313529611206324262166497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11502745629883531365777325 4313529611206324262166497)
                  ·
                    refine ⟨3235147208404743196624873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4313529611206324262166497 3235147208404743196624873)
                    ·
                      refine ⟨2426360406303557397468655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235147208404743196624873 2426360406303557397468655)
                      ·
                        rfl

theorem cell23_4725320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_4725320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725320 prefixEnd_4725320 := by exact prefixLift 4725320
  have htrace : WordTrace (prefixWord ++ tailWord_4725320) baseStart_4725320 baseEnd_4725320 := by
    simpa [prefixWord, tailWord_4725320, baseEnd_4725320] using wordTrace_append hprefix tailTrace_4725320
  have hstable : (prefixWord ++ tailWord_4725320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725320).length < 2 ^ (prefixWord ++ tailWord_4725320).sum := by decide
  have hdescent : baseEnd_4725320 < baseStart_4725320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725326 : List Nat := [4, 1, 1, 1, 1, 2, 4, 9]
def baseStart_4725326 : Nat := 118140960795 + 4725326 * 2 ^ 59
def prefixEnd_4725326 : Nat := 4983230072969 + 3 ^ 40 * 4725326 * 2
def baseEnd_4725326 : Nat := 89865314340277199036801

theorem tailTrace_4725326 : CollatzResearch.WordTrace tailWord_4725326 prefixEnd_4725326 89865314340277199036801 := by
  unfold tailWord_4725326
  simp only [CollatzResearch.WordTrace]
  refine ⟨21543349759869799784456479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114897865385972265517101221 21543349759869799784456479)
  ·
    refine ⟨32315024639804699676684719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21543349759869799784456479 32315024639804699676684719)
    ·
      refine ⟨48472536959707049515027079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32315024639804699676684719 48472536959707049515027079)
      ·
        refine ⟨72708805439560574272540619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48472536959707049515027079 72708805439560574272540619)
        ·
          refine ⟨109063208159340861408810929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72708805439560574272540619 109063208159340861408810929)
          ·
            refine ⟨81797406119505646056608197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109063208159340861408810929 81797406119505646056608197)
            ·
              refine ⟨15337013647407308635614037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81797406119505646056608197 15337013647407308635614037)
              ·
                refine ⟨89865314340277199036801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15337013647407308635614037 89865314340277199036801)
                ·
                  rfl

theorem cell23_4725326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_4725326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725326 prefixEnd_4725326 := by exact prefixLift 4725326
  have htrace : WordTrace (prefixWord ++ tailWord_4725326) baseStart_4725326 baseEnd_4725326 := by
    simpa [prefixWord, tailWord_4725326, baseEnd_4725326] using wordTrace_append hprefix tailTrace_4725326
  have hstable : (prefixWord ++ tailWord_4725326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725326).length < 2 ^ (prefixWord ++ tailWord_4725326).sum := by decide
  have hdescent : baseEnd_4725326 < baseStart_4725326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725354 : List Nat := [3, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_4725354 : Nat := 118140960795 + 4725354 * 2 ^ 59
def prefixEnd_4725354 : Nat := 4983230072969 + 3 ^ 40 * 4725354 * 2
def baseEnd_4725354 : Nat := 2426377864645810264443499

theorem tailTrace_4725354 : CollatzResearch.WordTrace tailWord_4725354 prefixEnd_4725354 2426377864645810264443499 := by
  unfold tailWord_4725354
  simp only [CollatzResearch.WordTrace]
  refine ⟨43086954830714239764417779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114898546215237972705114077 43086954830714239764417779)
  ·
    refine ⟨64630432246071359646626669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43086954830714239764417779 64630432246071359646626669)
    ·
      refine ⟨24236412092276759867485001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64630432246071359646626669 24236412092276759867485001)
      ·
        refine ⟨18177309069207569900613751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24236412092276759867485001 18177309069207569900613751)
        ·
          refine ⟨27265963603811354850920627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18177309069207569900613751 27265963603811354850920627)
          ·
            refine ⟨40898945405717032276380941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27265963603811354850920627 40898945405717032276380941)
            ·
              refine ⟨15337104527143887103642853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40898945405717032276380941 15337104527143887103642853)
              ·
                refine ⟨2875707098839478831933035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15337104527143887103642853 2875707098839478831933035)
                ·
                  refine ⟨4313560648259218247899553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875707098839478831933035 4313560648259218247899553)
                  ·
                    refine ⟨3235170486194413685924665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4313560648259218247899553 3235170486194413685924665)
                    ·
                      refine ⟨2426377864645810264443499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235170486194413685924665 2426377864645810264443499)
                      ·
                        rfl

theorem cell23_4725354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_4725354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725354 prefixEnd_4725354 := by exact prefixLift 4725354
  have htrace : WordTrace (prefixWord ++ tailWord_4725354) baseStart_4725354 baseEnd_4725354 := by
    simpa [prefixWord, tailWord_4725354, baseEnd_4725354] using wordTrace_append hprefix tailTrace_4725354
  have hstable : (prefixWord ++ tailWord_4725354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725354).length < 2 ^ (prefixWord ++ tailWord_4725354).sum := by decide
  have hdescent : baseEnd_4725354 < baseStart_4725354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725356 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_4725356 : Nat := 118140960795 + 4725356 * 2 ^ 59
def prefixEnd_4725356 : Nat := 4983230072969 + 3 ^ 40 * 4725356 * 2
def baseEnd_4725356 : Nat := 808792963869039752206163

theorem tailTrace_4725356 : CollatzResearch.WordTrace tailWord_4725356 prefixEnd_4725356 808792963869039752206163 := by
  unfold tailWord_4725356
  simp only [CollatzResearch.WordTrace]
  refine ⟨86173946134424856699621961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114898594845899808932829281 86173946134424856699621961)
  ·
    refine ⟨64630459600818642524716471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86173946134424856699621961 64630459600818642524716471)
    ·
      refine ⟨96945689401227963787074707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64630459600818642524716471 96945689401227963787074707)
      ·
        refine ⟨145418534101841945680612061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96945689401227963787074707 145418534101841945680612061)
        ·
          refine ⟨54531950288190729630229523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145418534101841945680612061 54531950288190729630229523)
          ·
            refine ⟨81797925432286094445344285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54531950288190729630229523 81797925432286094445344285)
            ·
              refine ⟨30674222037107285417004107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81797925432286094445344285 30674222037107285417004107)
              ·
                refine ⟨46011333055660928125506161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30674222037107285417004107 46011333055660928125506161)
                ·
                  refine ⟨34508499791745696094129621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46011333055660928125506161 34508499791745696094129621)
                  ·
                    refine ⟨808792963869039752206163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34508499791745696094129621 808792963869039752206163)
                    ·
                      rfl

theorem cell23_4725356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_4725356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725356 prefixEnd_4725356 := by exact prefixLift 4725356
  have htrace : WordTrace (prefixWord ++ tailWord_4725356) baseStart_4725356 baseEnd_4725356 := by
    simpa [prefixWord, tailWord_4725356, baseEnd_4725356] using wordTrace_append hprefix tailTrace_4725356
  have hstable : (prefixWord ++ tailWord_4725356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725356).length < 2 ^ (prefixWord ++ tailWord_4725356).sum := by decide
  have hdescent : baseEnd_4725356 < baseStart_4725356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725360 : List Nat := [2, 1, 1, 1, 8, 1, 1, 8]
def baseStart_4725360 : Nat := 118140960795 + 4725360 * 2 ^ 59
def prefixEnd_4725360 : Nat := 4983230072969 + 3 ^ 40 * 4725360 * 2
def baseEnd_4725360 : Nat := 89865960945545823739573

theorem tailTrace_4725360 : CollatzResearch.WordTrace tailWord_4725360 prefixEnd_4725360 89865960945545823739573 := by
  unfold tailWord_4725360
  simp only [CollatzResearch.WordTrace]
  refine ⟨86174019080417611041194767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114898692107223481388259689 86174019080417611041194767)
  ·
    refine ⟨129261028620626416561792151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86174019080417611041194767 129261028620626416561792151)
    ·
      refine ⟨193891542930939624842688227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129261028620626416561792151 193891542930939624842688227)
      ·
        refine ⟨290837314396409437264032341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193891542930939624842688227 290837314396409437264032341)
        ·
          refine ⟨3408249778082923092937879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 290837314396409437264032341 3408249778082923092937879)
          ·
            refine ⟨5112374667124384639406819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408249778082923092937879 5112374667124384639406819)
            ·
              refine ⟨7668562000686576959110229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112374667124384639406819 7668562000686576959110229)
              ·
                refine ⟨89865960945545823739573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7668562000686576959110229 89865960945545823739573)
                ·
                  rfl

theorem cell23_4725360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 8].length) (baseStart_4725360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725360 prefixEnd_4725360 := by exact prefixLift 4725360
  have htrace : WordTrace (prefixWord ++ tailWord_4725360) baseStart_4725360 baseEnd_4725360 := by
    simpa [prefixWord, tailWord_4725360, baseEnd_4725360] using wordTrace_append hprefix tailTrace_4725360
  have hstable : (prefixWord ++ tailWord_4725360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725360).length < 2 ^ (prefixWord ++ tailWord_4725360).sum := by decide
  have hdescent : baseEnd_4725360 < baseStart_4725360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725393 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 8, 2]
def baseStart_4725393 : Nat := 118140960795 + 4725393 * 2 ^ 59
def prefixEnd_4725393 : Nat := 4983230072969 + 3 ^ 40 * 4725393 * 2
def baseEnd_4725393 : Nat := 2426397890391335611855819

theorem tailTrace_4725393 : CollatzResearch.WordTrace tailWord_4725393 prefixEnd_4725393 2426397890391335611855819 := by
  unfold tailWord_4725393
  simp only [CollatzResearch.WordTrace]
  refine ⟨172349241769715668718340833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114899494513143779145560555 172349241769715668718340833)
  ·
    refine ⟨129261931327286751538755625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172349241769715668718340833 129261931327286751538755625)
    ·
      refine ⟨96946448495465063654066719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129261931327286751538755625 96946448495465063654066719)
      ·
        refine ⟨145419672743197595481100079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96946448495465063654066719 145419672743197595481100079)
        ·
          refine ⟨218129509114796393221650119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145419672743197595481100079 218129509114796393221650119)
          ·
            refine ⟨327194263672194589832475179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218129509114796393221650119 327194263672194589832475179)
            ·
              refine ⟨490791395508291884748712769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327194263672194589832475179 490791395508291884748712769)
              ·
                refine ⟨368093546631218913561534577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 490791395508291884748712769 368093546631218913561534577)
                ·
                  refine ⟨276070159973414185171150933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368093546631218913561534577 276070159973414185171150933)
                  ·
                    refine ⟨3235197187188447482474425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 276070159973414185171150933 3235197187188447482474425)
                    ·
                      refine ⟨2426397890391335611855819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235197187188447482474425 2426397890391335611855819)
                      ·
                        rfl

theorem cell23_4725393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_4725393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725393 prefixEnd_4725393 := by exact prefixLift 4725393
  have htrace : WordTrace (prefixWord ++ tailWord_4725393) baseStart_4725393 baseEnd_4725393 := by
    simpa [prefixWord, tailWord_4725393, baseEnd_4725393] using wordTrace_append hprefix tailTrace_4725393
  have hstable : (prefixWord ++ tailWord_4725393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725393).length < 2 ^ (prefixWord ++ tailWord_4725393).sum := by decide
  have hdescent : baseEnd_4725393 < baseStart_4725393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725404 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4725404 : Nat := 118140960795 + 4725404 * 2 ^ 59
def prefixEnd_4725404 : Nat := 4983230072969 + 3 ^ 40 * 4725404 * 2
def baseEnd_4725404 : Nat := 2426403538678535068818269

theorem tailTrace_4725404 : CollatzResearch.WordTrace tailWord_4725404 prefixEnd_4725404 2426403538678535068818269 := by
  unfold tailWord_4725404
  simp only [CollatzResearch.WordTrace]
  refine ⟨86174821486337908798495633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114899761981783878397994177 86174821486337908798495633)
  ·
    refine ⟨64631116114753431598871725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86174821486337908798495633 64631116114753431598871725)
    ·
      refine ⟨24236668543032536849576897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64631116114753431598871725 24236668543032536849576897)
      ·
        refine ⟨18177501407274402637182673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24236668543032536849576897 18177501407274402637182673)
        ·
          refine ⟨13633126055455801977887005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18177501407274402637182673 13633126055455801977887005)
          ·
            refine ⟨5112422270795925741707627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13633126055455801977887005 5112422270795925741707627)
            ·
              refine ⟨7668633406193888612561441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112422270795925741707627 7668633406193888612561441)
              ·
                refine ⟨5751475054645416459421081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7668633406193888612561441 5751475054645416459421081)
                ·
                  refine ⟨4313606290984062344565811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5751475054645416459421081 4313606290984062344565811)
                  ·
                    refine ⟨6470409436476093516848717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4313606290984062344565811 6470409436476093516848717)
                    ·
                      refine ⟨2426403538678535068818269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6470409436476093516848717 2426403538678535068818269)
                      ·
                        rfl

theorem cell23_4725404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4725404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725404 prefixEnd_4725404 := by exact prefixLift 4725404
  have htrace : WordTrace (prefixWord ++ tailWord_4725404) baseStart_4725404 baseEnd_4725404 := by
    simpa [prefixWord, tailWord_4725404, baseEnd_4725404] using wordTrace_append hprefix tailTrace_4725404
  have hstable : (prefixWord ++ tailWord_4725404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725404).length < 2 ^ (prefixWord ++ tailWord_4725404).sum := by decide
  have hdescent : baseEnd_4725404 < baseStart_4725404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725423 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_4725423 : Nat := 118140960795 + 4725423 * 2 ^ 59
def prefixEnd_4725423 : Nat := 4983230072969 + 3 ^ 40 * 4725423 * 2
def baseEnd_4725423 : Nat := 2426413294810970494480681

theorem tailTrace_4725423 : CollatzResearch.WordTrace tailWord_4725423 prefixEnd_4725423 2426413294810970494480681 := by
  unfold tailWord_4725423
  simp only [CollatzResearch.WordTrace]
  refine ⟨172350335959606983841932923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114900223973071322561288615 172350335959606983841932923)
  ·
    refine ⟨258525503939410475762899385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172350335959606983841932923 258525503939410475762899385)
    ·
      refine ⟨193894127954557856822174539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258525503939410475762899385 193894127954557856822174539)
      ·
        refine ⟨290841191931836785233261809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193894127954557856822174539 290841191931836785233261809)
        ·
          refine ⟨218130893948877588924946357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290841191931836785233261809 218130893948877588924946357)
          ·
            refine ⟨20449771307707273961713721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 218130893948877588924946357 20449771307707273961713721)
            ·
              refine ⟨15337328480780455471285291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20449771307707273961713721 15337328480780455471285291)
              ·
                refine ⟨23005992721170683206927937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15337328480780455471285291 23005992721170683206927937)
                ·
                  refine ⟨17254494540878012405195953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23005992721170683206927937 17254494540878012405195953)
                  ·
                    refine ⟨12940870905658509303896965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17254494540878012405195953 12940870905658509303896965)
                    ·
                      refine ⟨2426413294810970494480681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12940870905658509303896965 2426413294810970494480681)
                      ·
                        rfl

theorem cell23_4725423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_4725423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725423 prefixEnd_4725423 := by exact prefixLift 4725423
  have htrace : WordTrace (prefixWord ++ tailWord_4725423) baseStart_4725423 baseEnd_4725423 := by
    simpa [prefixWord, tailWord_4725423, baseEnd_4725423] using wordTrace_append hprefix tailTrace_4725423
  have hstable : (prefixWord ++ tailWord_4725423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725423).length < 2 ^ (prefixWord ++ tailWord_4725423).sum := by decide
  have hdescent : baseEnd_4725423 < baseStart_4725423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725427 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 1, 4, 2]
def baseStart_4725427 : Nat := 118140960795 + 4725427 * 2 ^ 59
def prefixEnd_4725427 : Nat := 4983230072969 + 3 ^ 40 * 4725427 * 2
def baseEnd_4725427 : Nat := 2426415348733588478830663

theorem tailTrace_4725427 : CollatzResearch.WordTrace tailWord_4725427 prefixEnd_4725427 2426415348733588478830663 := by
  unfold tailWord_4725427
  simp only [CollatzResearch.WordTrace]
  refine ⟨172350481851592492525078535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114900321234394995016719023 172350481851592492525078535)
  ·
    refine ⟨258525722777388738787617803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172350481851592492525078535 258525722777388738787617803)
    ·
      refine ⟨387788584166083108181426705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258525722777388738787617803 387788584166083108181426705)
      ·
        refine ⟨290841438124562331136070029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387788584166083108181426705 290841438124562331136070029)
        ·
          refine ⟨109065539296710874176026261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290841438124562331136070029 109065539296710874176026261)
          ·
            refine ⟨5112447154533322227001231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109065539296710874176026261 5112447154533322227001231)
            ·
              refine ⟨7668670731799983340501847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112447154533322227001231 7668670731799983340501847)
              ·
                refine ⟨11503006097699975010752771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7668670731799983340501847 11503006097699975010752771)
                ·
                  refine ⟨17254509146549962516129157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11503006097699975010752771 17254509146549962516129157)
                  ·
                    refine ⟨3235220464978117971774217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17254509146549962516129157 3235220464978117971774217)
                    ·
                      refine ⟨2426415348733588478830663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235220464978117971774217 2426415348733588478830663)
                      ·
                        rfl

theorem cell23_4725427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 4, 2].length) (baseStart_4725427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725427 prefixEnd_4725427 := by exact prefixLift 4725427
  have htrace : WordTrace (prefixWord ++ tailWord_4725427) baseStart_4725427 baseEnd_4725427 := by
    simpa [prefixWord, tailWord_4725427, baseEnd_4725427] using wordTrace_append hprefix tailTrace_4725427
  have hstable : (prefixWord ++ tailWord_4725427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725427).length < 2 ^ (prefixWord ++ tailWord_4725427).sum := by decide
  have hdescent : baseEnd_4725427 < baseStart_4725427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725463 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 4, 5]
def baseStart_4725463 : Nat := 118140960795 + 4725463 * 2 ^ 59
def prefixEnd_4725463 : Nat := 4983230072969 + 3 ^ 40 * 4725463 * 2
def baseEnd_4725463 : Nat := 808811278012383445993499

theorem tailTrace_4725463 : CollatzResearch.WordTrace tailWord_4725463 prefixEnd_4725463 808811278012383445993499 := by
  unfold tailWord_4725463
  simp only [CollatzResearch.WordTrace]
  refine ⟨172351794879462070673389043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114901196586308047115592695 172351794879462070673389043)
  ·
    refine ⟨258527692319193106010083565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172351794879462070673389043 258527692319193106010083565)
    ·
      refine ⟨96947884619697414753781337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 258527692319193106010083565 96947884619697414753781337)
      ·
        refine ⟨72710913464773061065336003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96947884619697414753781337 72710913464773061065336003)
        ·
          refine ⟨109066370197159591598004005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72710913464773061065336003 109066370197159591598004005)
          ·
            refine ⟨20449944411967423424625751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109066370197159591598004005 20449944411967423424625751)
            ·
              refine ⟨30674916617951135136938627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20449944411967423424625751 30674916617951135136938627)
              ·
                refine ⟨46012374926926702705407941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30674916617951135136938627 46012374926926702705407941)
                ·
                  refine ⟨8627320298798756757263989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46012374926926702705407941 8627320298798756757263989)
                  ·
                    refine ⟨808811278012383445993499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8627320298798756757263989 808811278012383445993499)
                    ·
                      rfl

theorem cell23_4725463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_4725463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725463 prefixEnd_4725463 := by exact prefixLift 4725463
  have htrace : WordTrace (prefixWord ++ tailWord_4725463) baseStart_4725463 baseEnd_4725463 := by
    simpa [prefixWord, tailWord_4725463, baseEnd_4725463] using wordTrace_append hprefix tailTrace_4725463
  have hstable : (prefixWord ++ tailWord_4725463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725463).length < 2 ^ (prefixWord ++ tailWord_4725463).sum := by decide
  have hdescent : baseEnd_4725463 < baseStart_4725463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725473 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_4725473 : Nat := 118140960795 + 4725473 * 2 ^ 59
def prefixEnd_4725473 : Nat := 4983230072969 + 3 ^ 40 * 4725473 * 2
def baseEnd_4725473 : Nat := 2426438968843695298855451

theorem tailTrace_4725473 : CollatzResearch.WordTrace tailWord_4725473 prefixEnd_4725473 2426438968843695298855451 := by
  unfold tailWord_4725473
  simp only [CollatzResearch.WordTrace]
  refine ⟨172352159609425842381253073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114901439739617228254168715 172352159609425842381253073)
  ·
    refine ⟨129264119707069381785939805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172352159609425842381253073 129264119707069381785939805)
    ·
      refine ⟨48474044890151018169727427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129264119707069381785939805 48474044890151018169727427)
      ·
        refine ⟨72711067335226527254591141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48474044890151018169727427 72711067335226527254591141)
        ·
          refine ⟨13633325125354973860235839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72711067335226527254591141 13633325125354973860235839)
          ·
            refine ⟨20449987688032460790353759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13633325125354973860235839 20449987688032460790353759)
            ·
              refine ⟨30674981532048691185530639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20449987688032460790353759 30674981532048691185530639)
              ·
                refine ⟨46012472298073036778295959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30674981532048691185530639 46012472298073036778295959)
                ·
                  refine ⟨69018708447109555167443939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46012472298073036778295959 69018708447109555167443939)
                  ·
                    refine ⟨103528062670664332751165909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69018708447109555167443939 103528062670664332751165909)
                    ·
                      refine ⟨2426438968843695298855451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103528062670664332751165909 2426438968843695298855451)
                      ·
                        rfl

theorem cell23_4725473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_4725473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725473 prefixEnd_4725473 := by exact prefixLift 4725473
  have htrace : WordTrace (prefixWord ++ tailWord_4725473) baseStart_4725473 baseEnd_4725473 := by
    simpa [prefixWord, tailWord_4725473, baseEnd_4725473] using wordTrace_append hprefix tailTrace_4725473
  have hstable : (prefixWord ++ tailWord_4725473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725473).length < 2 ^ (prefixWord ++ tailWord_4725473).sum := by decide
  have hdescent : baseEnd_4725473 < baseStart_4725473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725483 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 4]
def baseStart_4725483 : Nat := 118140960795 + 4725483 * 2 ^ 59
def prefixEnd_4725483 : Nat := 4983230072969 + 3 ^ 40 * 4725483 * 2
def baseEnd_4725483 : Nat := 2426444103650240259730405

theorem tailTrace_4725483 : CollatzResearch.WordTrace tailWord_4725483 prefixEnd_4725483 2426444103650240259730405 := by
  unfold tailWord_4725483
  simp only [CollatzResearch.WordTrace]
  refine ⟨172352524339389614089117103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114901682892926409392744735 172352524339389614089117103)
  ·
    refine ⟨258528786509084421133675655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172352524339389614089117103 258528786509084421133675655)
    ·
      refine ⟨387793179763626631700513483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258528786509084421133675655 387793179763626631700513483)
      ·
        refine ⟨581689769645439947550770225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387793179763626631700513483 581689769645439947550770225)
        ·
          refine ⟨436267327234079960663077669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581689769645439947550770225 436267327234079960663077669)
          ·
            refine ⟨81800123856389992624327063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 436267327234079960663077669 81800123856389992624327063)
            ·
              refine ⟨122700185784584988936490595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81800123856389992624327063 122700185784584988936490595)
              ·
                refine ⟨184050278676877483404735893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122700185784584988936490595 184050278676877483404735893)
                ·
                  refine ⟨8627356812978632034596995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184050278676877483404735893 8627356812978632034596995)
                  ·
                    refine ⟨12941035219467948051895493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8627356812978632034596995 12941035219467948051895493)
                    ·
                      refine ⟨2426444103650240259730405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12941035219467948051895493 2426444103650240259730405)
                      ·
                        rfl

theorem cell23_4725483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 4].length) (baseStart_4725483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725483 prefixEnd_4725483 := by exact prefixLift 4725483
  have htrace : WordTrace (prefixWord ++ tailWord_4725483) baseStart_4725483 baseEnd_4725483 := by
    simpa [prefixWord, tailWord_4725483, baseEnd_4725483] using wordTrace_append hprefix tailTrace_4725483
  have hstable : (prefixWord ++ tailWord_4725483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725483).length < 2 ^ (prefixWord ++ tailWord_4725483).sum := by decide
  have hdescent : baseEnd_4725483 < baseStart_4725483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725500 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 2, 1, 4]
def baseStart_4725500 : Nat := 118140960795 + 4725500 * 2 ^ 59
def prefixEnd_4725500 : Nat := 4983230072969 + 3 ^ 40 * 4725500 * 2
def baseEnd_4725500 : Nat := 2426452832821366693217827

theorem tailTrace_4725500 : CollatzResearch.WordTrace tailWord_4725500 prefixEnd_4725500 2426452832821366693217827 := by
  unfold tailWord_4725500
  simp only [CollatzResearch.WordTrace]
  refine ⟨86176572190164012996242977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114902096253552017328323969 86176572190164012996242977)
  ·
    refine ⟨64632429142623009747182233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86176572190164012996242977 64632429142623009747182233)
    ·
      refine ⟨48474321856967257310386675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64632429142623009747182233 48474321856967257310386675)
      ·
        refine ⟨72711482785450885965580013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48474321856967257310386675 72711482785450885965580013)
        ·
          refine ⟨27266806044544082237092505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72711482785450885965580013 27266806044544082237092505)
          ·
            refine ⟨20450104533408061677819379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27266806044544082237092505 20450104533408061677819379)
            ·
              refine ⟨30675156800112092516729069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20450104533408061677819379 30675156800112092516729069)
              ·
                refine ⟨11503183800042034693773401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30675156800112092516729069 11503183800042034693773401)
                ·
                  refine ⟨8627387850031526020330051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11503183800042034693773401 8627387850031526020330051)
                  ·
                    refine ⟨12941081775047289030495077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8627387850031526020330051 12941081775047289030495077)
                    ·
                      refine ⟨2426452832821366693217827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12941081775047289030495077 2426452832821366693217827)
                      ·
                        rfl

theorem cell23_4725500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_4725500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725500 prefixEnd_4725500 := by exact prefixLift 4725500
  have htrace : WordTrace (prefixWord ++ tailWord_4725500) baseStart_4725500 baseEnd_4725500 := by
    simpa [prefixWord, tailWord_4725500, baseEnd_4725500] using wordTrace_append hprefix tailTrace_4725500
  have hstable : (prefixWord ++ tailWord_4725500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725500).length < 2 ^ (prefixWord ++ tailWord_4725500).sum := by decide
  have hdescent : baseEnd_4725500 < baseStart_4725500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725574 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 8]
def baseStart_4725574 : Nat := 118140960795 + 4725574 * 2 ^ 59
def prefixEnd_4725574 : Nat := 4983230072969 + 3 ^ 40 * 4725574 * 2
def baseEnd_4725574 : Nat := 269610092265533267076943

theorem tailTrace_4725574 : CollatzResearch.WordTrace tailWord_4725574 prefixEnd_4725574 269610092265533267076943 := by
  unfold tailWord_4725574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5386120105689373019708743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114903895588039957753786517 5386120105689373019708743)
  ·
    refine ⟨8079180158534059529563115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5386120105689373019708743 8079180158534059529563115)
    ·
      refine ⟨12118770237801089294344673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8079180158534059529563115 12118770237801089294344673)
      ·
        refine ⟨9089077678350816970758505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12118770237801089294344673 9089077678350816970758505)
        ·
          refine ⟨6816808258763112728068879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9089077678350816970758505 6816808258763112728068879)
          ·
            refine ⟨10225212388144669092103319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6816808258763112728068879 10225212388144669092103319)
            ·
              refine ⟨15337818582217003638154979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10225212388144669092103319 15337818582217003638154979)
              ·
                refine ⟨23006727873325505457232469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15337818582217003638154979 23006727873325505457232469)
                ·
                  refine ⟨269610092265533267076943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23006727873325505457232469 269610092265533267076943)
                  ·
                    rfl

theorem cell23_4725574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_4725574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725574 prefixEnd_4725574 := by exact prefixLift 4725574
  have htrace : WordTrace (prefixWord ++ tailWord_4725574) baseStart_4725574 baseEnd_4725574 := by
    simpa [prefixWord, tailWord_4725574, baseEnd_4725574] using wordTrace_append hprefix tailTrace_4725574
  have hstable : (prefixWord ++ tailWord_4725574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725574).length < 2 ^ (prefixWord ++ tailWord_4725574).sum := by decide
  have hdescent : baseEnd_4725574 < baseStart_4725574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725584 : List Nat := [2, 1, 1, 1, 1, 4, 4, 4, 1, 1, 3]
def baseStart_4725584 : Nat := 118140960795 + 4725584 * 2 ^ 59
def prefixEnd_4725584 : Nat := 4983230072969 + 3 ^ 40 * 4725584 * 2
def baseEnd_4725584 : Nat := 2426495965196344364567441

theorem tailTrace_4725584 : CollatzResearch.WordTrace tailWord_4725584 prefixEnd_4725584 2426495965196344364567441 := by
  unfold tailWord_4725584
  simp only [CollatzResearch.WordTrace]
  refine ⟨86178104056011854169271903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114904138741349138892362537 86178104056011854169271903)
  ·
    refine ⟨129267156084017781253907855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86178104056011854169271903 129267156084017781253907855)
    ·
      refine ⟨193900734126026671880861783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129267156084017781253907855 193900734126026671880861783)
      ·
        refine ⟨290851101189040007821292675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193900734126026671880861783 290851101189040007821292675)
        ·
          refine ⟨436276651783560011731939013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290851101189040007821292675 436276651783560011731939013)
          ·
            refine ⟨81801872209417502199738565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 436276651783560011731939013 81801872209417502199738565)
            ·
              refine ⟨15337851039265781662450981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81801872209417502199738565 15337851039265781662450981)
              ·
                refine ⟨2875847069862334061709559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15337851039265781662450981 2875847069862334061709559)
                ·
                  refine ⟨4313770604793501092564339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875847069862334061709559 4313770604793501092564339)
                  ·
                    refine ⟨6470655907190251638846509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4313770604793501092564339 6470655907190251638846509)
                    ·
                      refine ⟨2426495965196344364567441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6470655907190251638846509 2426495965196344364567441)
                      ·
                        rfl

theorem cell23_4725584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 1, 1, 3].length) (baseStart_4725584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725584 prefixEnd_4725584 := by exact prefixLift 4725584
  have htrace : WordTrace (prefixWord ++ tailWord_4725584) baseStart_4725584 baseEnd_4725584 := by
    simpa [prefixWord, tailWord_4725584, baseEnd_4725584] using wordTrace_append hprefix tailTrace_4725584
  have hstable : (prefixWord ++ tailWord_4725584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725584).length < 2 ^ (prefixWord ++ tailWord_4725584).sum := by decide
  have hdescent : baseEnd_4725584 < baseStart_4725584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725607 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_4725607 : Nat := 118140960795 + 4725607 * 2 ^ 59
def prefixEnd_4725607 : Nat := 4983230072969 + 3 ^ 40 * 4725607 * 2
def baseEnd_4725607 : Nat := 2426507775251397774579835

theorem tailTrace_4725607 : CollatzResearch.WordTrace tailWord_4725607 prefixEnd_4725607 2426507775251397774579835 := by
  unfold tailWord_4725607
  simp only [CollatzResearch.WordTrace]
  refine ⟨172357046990940383266631075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114904697993960255511087383 172357046990940383266631075)
  ·
    refine ⟨258535570486410574899946613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172357046990940383266631075 258535570486410574899946613)
    ·
      refine ⟨24237709733100991396869995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 258535570486410574899946613 24237709733100991396869995)
      ·
        refine ⟨36356564599651487095304993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24237709733100991396869995 36356564599651487095304993)
        ·
          refine ⟨27267423449738615321478745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36356564599651487095304993 27267423449738615321478745)
          ·
            refine ⟨20450567587303961491109059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27267423449738615321478745 20450567587303961491109059)
            ·
              refine ⟨30675851380955942236663589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20450567587303961491109059 30675851380955942236663589)
              ·
                refine ⟨5751722133929239169374423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30675851380955942236663589 5751722133929239169374423)
                ·
                  refine ⟨8627583200893858754061635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5751722133929239169374423 8627583200893858754061635)
                  ·
                    refine ⟨12941374801340788131092453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8627583200893858754061635 12941374801340788131092453)
                    ·
                      refine ⟨2426507775251397774579835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12941374801340788131092453 2426507775251397774579835)
                      ·
                        rfl

theorem cell23_4725607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_4725607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725607 prefixEnd_4725607 := by exact prefixLift 4725607
  have htrace : WordTrace (prefixWord ++ tailWord_4725607) baseStart_4725607 baseEnd_4725607 := by
    simpa [prefixWord, tailWord_4725607, baseEnd_4725607] using wordTrace_append hprefix tailTrace_4725607
  have hstable : (prefixWord ++ tailWord_4725607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725607).length < 2 ^ (prefixWord ++ tailWord_4725607).sum := by decide
  have hdescent : baseEnd_4725607 < baseStart_4725607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725627 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 3]
def baseStart_4725627 : Nat := 118140960795 + 4725627 * 2 ^ 59
def prefixEnd_4725627 : Nat := 4983230072969 + 3 ^ 40 * 4725627 * 2
def baseEnd_4725627 : Nat := 2426518044864487696329743

theorem tailTrace_4725627 : CollatzResearch.WordTrace tailWord_4725627 prefixEnd_4725627 2426518044864487696329743 := by
  unfold tailWord_4725627
  simp only [CollatzResearch.WordTrace]
  refine ⟨172357776450867926682359135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114905184300578617788239423 172357776450867926682359135)
  ·
    refine ⟨258536664676301890023538703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172357776450867926682359135 258536664676301890023538703)
    ·
      refine ⟨387804997014452835035308055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258536664676301890023538703 387804997014452835035308055)
      ·
        refine ⟨581707495521679252552962083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387804997014452835035308055 581707495521679252552962083)
        ·
          refine ⟨872561243282518878829443125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581707495521679252552962083 872561243282518878829443125)
          ·
            refine ⟨81802616557736144890260293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 872561243282518878829443125 81802616557736144890260293)
            ·
              refine ⟨15337990604575527166923805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81802616557736144890260293 15337990604575527166923805)
              ·
                refine ⟨5751746476715822687596427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15337990604575527166923805 5751746476715822687596427)
                ·
                  refine ⟨8627619715073734031394641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5751746476715822687596427 8627619715073734031394641)
                  ·
                    refine ⟨6470714786305300523545981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8627619715073734031394641 6470714786305300523545981)
                    ·
                      refine ⟨2426518044864487696329743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6470714786305300523545981 2426518044864487696329743)
                      ·
                        rfl

theorem cell23_4725627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 3].length) (baseStart_4725627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725627 prefixEnd_4725627 := by exact prefixLift 4725627
  have htrace : WordTrace (prefixWord ++ tailWord_4725627) baseStart_4725627 baseEnd_4725627 := by
    simpa [prefixWord, tailWord_4725627, baseEnd_4725627] using wordTrace_append hprefix tailTrace_4725627
  have hstable : (prefixWord ++ tailWord_4725627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725627).length < 2 ^ (prefixWord ++ tailWord_4725627).sum := by decide
  have hdescent : baseEnd_4725627 < baseStart_4725627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725641 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 3, 2, 2]
def baseStart_4725641 : Nat := 118140960795 + 4725641 * 2 ^ 59
def prefixEnd_4725641 : Nat := 4983230072969 + 3 ^ 40 * 4725641 * 2
def baseEnd_4725641 : Nat := 2426525233593650641554679

theorem tailTrace_4725641 : CollatzResearch.WordTrace tailWord_4725641 prefixEnd_4725641 2426525233593650641554679 := by
  unfold tailWord_4725641
  simp only [CollatzResearch.WordTrace]
  refine ⟨172358287072817207073368777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114905524715211471382245851 172358287072817207073368777)
  ·
    refine ⟨129268715304612905305026583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 172358287072817207073368777 129268715304612905305026583)
    ·
      refine ⟨193903072956919357957539875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129268715304612905305026583 193903072956919357957539875)
      ·
        refine ⟨290854609435379036936309813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193903072956919357957539875 290854609435379036936309813)
        ·
          refine ⟨27267619634566784712779045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 290854609435379036936309813 27267619634566784712779045)
          ·
            refine ⟨5112678681481272133646071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27267619634566784712779045 5112678681481272133646071)
            ·
              refine ⟨7669018022221908200469107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112678681481272133646071 7669018022221908200469107)
              ·
                refine ⟨11503527033332862300703661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7669018022221908200469107 11503527033332862300703661)
                ·
                  refine ⟨4313822637499823362763873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11503527033332862300703661 4313822637499823362763873)
                  ·
                    refine ⟨3235366978124867522072905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4313822637499823362763873 3235366978124867522072905)
                    ·
                      refine ⟨2426525233593650641554679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3235366978124867522072905 2426525233593650641554679)
                      ·
                        rfl

theorem cell23_4725641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 2, 2].length) (baseStart_4725641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725641 prefixEnd_4725641 := by exact prefixLift 4725641
  have htrace : WordTrace (prefixWord ++ tailWord_4725641) baseStart_4725641 baseEnd_4725641 := by
    simpa [prefixWord, tailWord_4725641, baseEnd_4725641] using wordTrace_append hprefix tailTrace_4725641
  have hstable : (prefixWord ++ tailWord_4725641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725641).length < 2 ^ (prefixWord ++ tailWord_4725641).sum := by decide
  have hdescent : baseEnd_4725641 < baseStart_4725641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725686 : List Nat := [5, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4725686 : Nat := 118140960795 + 4725686 * 2 ^ 59
def prefixEnd_4725686 : Nat := 4983230072969 + 3 ^ 40 * 4725686 * 2
def baseEnd_4725686 : Nat := 2426548340223102965491973

theorem tailTrace_4725686 : CollatzResearch.WordTrace tailWord_4725686 prefixEnd_4725686 2426548340223102965491973 := by
  unfold tailWord_4725686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772495522353386234922307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114906618905102786505837941 10772495522353386234922307)
  ·
    refine ⟨16158743283530079352383461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10772495522353386234922307 16158743283530079352383461)
    ·
      refine ⟨3029764365661889878571899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16158743283530079352383461 3029764365661889878571899)
      ·
        refine ⟨4544646548492834817857849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029764365661889878571899 4544646548492834817857849)
        ·
          refine ⟨3408484911369626113393387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4544646548492834817857849 3408484911369626113393387)
          ·
            refine ⟨5112727367054439170090081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408484911369626113393387 5112727367054439170090081)
            ·
              refine ⟨3834545525290829377567561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5112727367054439170090081 3834545525290829377567561)
              ·
                refine ⟨2875909143968122033175671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834545525290829377567561 2875909143968122033175671)
                ·
                  refine ⟨4313863715952183049763507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875909143968122033175671 4313863715952183049763507)
                  ·
                    refine ⟨6470795573928274574645261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4313863715952183049763507 6470795573928274574645261)
                    ·
                      refine ⟨2426548340223102965491973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6470795573928274574645261 2426548340223102965491973)
                      ·
                        rfl

theorem cell23_4725686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4725686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725686 prefixEnd_4725686 := by exact prefixLift 4725686
  have htrace : WordTrace (prefixWord ++ tailWord_4725686) baseStart_4725686 baseEnd_4725686 := by
    simpa [prefixWord, tailWord_4725686, baseEnd_4725686] using wordTrace_append hprefix tailTrace_4725686
  have hstable : (prefixWord ++ tailWord_4725686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725686).length < 2 ^ (prefixWord ++ tailWord_4725686).sum := by decide
  have hdescent : baseEnd_4725686 < baseStart_4725686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4725690 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_4725690 : Nat := 118140960795 + 4725690 * 2 ^ 59
def prefixEnd_4725690 : Nat := 4983230072969 + 3 ^ 40 * 4725690 * 2
def baseEnd_4725690 : Nat := 808850131381906983280651

theorem tailTrace_4725690 : CollatzResearch.WordTrace tailWord_4725690 prefixEnd_4725690 808850131381906983280651 := by
  unfold tailWord_4725690
  simp only [CollatzResearch.WordTrace]
  refine ⟨43090018562409922110475631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114906716166426458961268349 43090018562409922110475631)
  ·
    refine ⟨64635027843614883165713447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43090018562409922110475631 64635027843614883165713447)
    ·
      refine ⟨96952541765422324748570171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64635027843614883165713447 96952541765422324748570171)
      ·
        refine ⟨145428812648133487122855257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96952541765422324748570171 145428812648133487122855257)
        ·
          refine ⟨109071609486100115342141443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145428812648133487122855257 109071609486100115342141443)
          ·
            refine ⟨163607414229150173013212165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109071609486100115342141443 163607414229150173013212165)
            ·
              refine ⟨30676390167965657439977281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163607414229150173013212165 30676390167965657439977281)
              ·
                refine ⟨23007292625974243079982961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30676390167965657439977281 23007292625974243079982961)
                ·
                  refine ⟨17255469469480682309987221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23007292625974243079982961 17255469469480682309987221)
                  ·
                    refine ⟨808850131381906983280651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17255469469480682309987221 808850131381906983280651)
                    ·
                      rfl

theorem cell23_4725690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_4725690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4725690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4725690 prefixEnd_4725690 := by exact prefixLift 4725690
  have htrace : WordTrace (prefixWord ++ tailWord_4725690) baseStart_4725690 baseEnd_4725690 := by
    simpa [prefixWord, tailWord_4725690, baseEnd_4725690] using wordTrace_append hprefix tailTrace_4725690
  have hstable : (prefixWord ++ tailWord_4725690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4725690).length < 2 ^ (prefixWord ++ tailWord_4725690).sum := by decide
  have hdescent : baseEnd_4725690 < baseStart_4725690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4725690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
