import V185TrunkScan23Chunk1273

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7547567 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 4]
def baseStart_7547567 : Nat := 118140960795 + 7547567 * 2 ^ 59
def prefixEnd_7547567 : Nat := 4983230072969 + 3 ^ 40 * 7547567 * 2
def baseEnd_7547567 : Nat := 3875529643013176843101877

theorem tailTrace_7547567 : CollatzResearch.WordTrace tailWord_7547567 prefixEnd_7547567 3875529643013176843101877 := by
  unfold tailWord_7547567
  simp only [CollatzResearch.WordTrace]
  refine ⟨275282383847461255664440955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183521589231640837109627303 275282383847461255664440955)
  ·
    refine ⟨412923575771191883496661433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275282383847461255664440955 412923575771191883496661433)
    ·
      refine ⟨309692681828393912622496075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 412923575771191883496661433 309692681828393912622496075)
      ·
        refine ⟨464539022742590868933744113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309692681828393912622496075 464539022742590868933744113)
        ·
          refine ⟨348404267056943151700308085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464539022742590868933744113 348404267056943151700308085)
          ·
            refine ⟨32662900036588420471903883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348404267056943151700308085 32662900036588420471903883)
            ·
              refine ⟨48994350054882630707855825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32662900036588420471903883 48994350054882630707855825)
              ·
                refine ⟨36745762541161973030891869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48994350054882630707855825 36745762541161973030891869)
                ·
                  refine ⟨13779660952935739886584451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36745762541161973030891869 13779660952935739886584451)
                  ·
                    refine ⟨20669491429403609829876677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13779660952935739886584451 20669491429403609829876677)
                    ·
                      refine ⟨3875529643013176843101877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20669491429403609829876677 3875529643013176843101877)
                      ·
                        rfl

theorem cell23_7547567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_7547567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547567 prefixEnd_7547567 := by exact prefixLift 7547567
  have htrace : WordTrace (prefixWord ++ tailWord_7547567) baseStart_7547567 baseEnd_7547567 := by
    simpa [prefixWord, tailWord_7547567, baseEnd_7547567] using wordTrace_append hprefix tailTrace_7547567
  have hstable : (prefixWord ++ tailWord_7547567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547567).length < 2 ^ (prefixWord ++ tailWord_7547567).sum := by decide
  have hdescent : baseEnd_7547567 < baseStart_7547567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547577 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 6, 4]
def baseStart_7547577 : Nat := 118140960795 + 7547577 * 2 ^ 59
def prefixEnd_7547577 : Nat := 4983230072969 + 3 ^ 40 * 7547577 * 2
def baseEnd_7547577 : Nat := 1291844925939907267992277

theorem tailTrace_7547577 : CollatzResearch.WordTrace tailWord_7547577 prefixEnd_7547577 1291844925939907267992277 := by
  unfold tailWord_7547577
  simp only [CollatzResearch.WordTrace]
  refine ⟨275282748577425027372304985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183521832384950018248203323 275282748577425027372304985)
  ·
    refine ⟨206462061433068770529228739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275282748577425027372304985 206462061433068770529228739)
    ·
      refine ⟨309693092149603155793843109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206462061433068770529228739 309693092149603155793843109)
      ·
        refine ⟨58067454778050591711345583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309693092149603155793843109 58067454778050591711345583)
        ·
          refine ⟨87101182167075887567018375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58067454778050591711345583 87101182167075887567018375)
          ·
            refine ⟨130651773250613831350527563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87101182167075887567018375 130651773250613831350527563)
            ·
              refine ⟨195977659875920747025791345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130651773250613831350527563 195977659875920747025791345)
              ·
                refine ⟨146983244906940560269343509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195977659875920747025791345 146983244906940560269343509)
                ·
                  refine ⟨6889839605012838762625477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146983244906940560269343509 6889839605012838762625477)
                  ·
                    refine ⟨1291844925939907267992277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6889839605012838762625477 1291844925939907267992277)
                    ·
                      rfl

theorem cell23_7547577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 4].length) (baseStart_7547577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547577 prefixEnd_7547577 := by exact prefixLift 7547577
  have htrace : WordTrace (prefixWord ++ tailWord_7547577) baseStart_7547577 baseEnd_7547577 := by
    simpa [prefixWord, tailWord_7547577, baseEnd_7547577] using wordTrace_append hprefix tailTrace_7547577
  have hstable : (prefixWord ++ tailWord_7547577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547577).length < 2 ^ (prefixWord ++ tailWord_7547577).sum := by decide
  have hdescent : baseEnd_7547577 < baseStart_7547577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547588 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_7547588 : Nat := 118140960795 + 7547588 * 2 ^ 59
def prefixEnd_7547588 : Nat := 4983230072969 + 3 ^ 40 * 7547588 * 2
def baseEnd_7547588 : Nat := 3875540426106921260939281

theorem tailTrace_7547588 : CollatzResearch.WordTrace tailWord_7547588 prefixEnd_7547588 3875540426106921260939281 := by
  unfold tailWord_7547588
  simp only [CollatzResearch.WordTrace]
  refine ⟨137641574890192588125477709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183522099853590117500636945 137641574890192588125477709)
  ·
    refine ⟨51615590583822220547054141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137641574890192588125477709 51615590583822220547054141)
    ·
      refine ⟨19355846468933332705145303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51615590583822220547054141 19355846468933332705145303)
      ·
        refine ⟨29033769703399999057717955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19355846468933332705145303 29033769703399999057717955)
        ·
          refine ⟨43550654555099998586576933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29033769703399999057717955 43550654555099998586576933)
          ·
            refine ⟨8165747729081249734983175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43550654555099998586576933 8165747729081249734983175)
            ·
              refine ⟨12248621593621874602474763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8165747729081249734983175 12248621593621874602474763)
              ·
                refine ⟨18372932390432811903712145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248621593621874602474763 18372932390432811903712145)
                ·
                  refine ⟨13779699292824608927784109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18372932390432811903712145 13779699292824608927784109)
                  ·
                    refine ⟨5167387234809228347919041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13779699292824608927784109 5167387234809228347919041)
                    ·
                      refine ⟨3875540426106921260939281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167387234809228347919041 3875540426106921260939281)
                      ·
                        rfl

theorem cell23_7547588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_7547588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547588 prefixEnd_7547588 := by exact prefixLift 7547588
  have htrace : WordTrace (prefixWord ++ tailWord_7547588) baseStart_7547588 baseEnd_7547588 := by
    simpa [prefixWord, tailWord_7547588, baseEnd_7547588] using wordTrace_append hprefix tailTrace_7547588
  have hstable : (prefixWord ++ tailWord_7547588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547588).length < 2 ^ (prefixWord ++ tailWord_7547588).sum := by decide
  have hdescent : baseEnd_7547588 < baseStart_7547588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547600 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_7547600 : Nat := 118140960795 + 7547600 * 2 ^ 59
def prefixEnd_7547600 : Nat := 4983230072969 + 3 ^ 40 * 7547600 * 2
def baseEnd_7547600 : Nat := 3875546587874775213989225

theorem tailTrace_7547600 : CollatzResearch.WordTrace tailWord_7547600 prefixEnd_7547600 3875546587874775213989225 := by
  unfold tailWord_7547600
  simp only [CollatzResearch.WordTrace]
  refine ⟨137641793728170851150196127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183522391637561134866928169 137641793728170851150196127)
  ·
    refine ⟨206462690592256276725294191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137641793728170851150196127 206462690592256276725294191)
    ·
      refine ⟨309694035888384415087941287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206462690592256276725294191 309694035888384415087941287)
      ·
        refine ⟨464541053832576622631911931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309694035888384415087941287 464541053832576622631911931)
        ·
          refine ⟨696811580748864933947867897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464541053832576622631911931 696811580748864933947867897)
          ·
            refine ⟨522608685561648700460900923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696811580748864933947867897 522608685561648700460900923)
            ·
              refine ⟨783913028342473050691351385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522608685561648700460900923 783913028342473050691351385)
              ·
                refine ⟨587934771256854788018513539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783913028342473050691351385 587934771256854788018513539)
                ·
                  refine ⟨881902156885282182027770309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587934771256854788018513539 881902156885282182027770309)
                  ·
                    refine ⟨165356654415990409130206933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 881902156885282182027770309 165356654415990409130206933)
                    ·
                      refine ⟨3875546587874775213989225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165356654415990409130206933 3875546587874775213989225)
                      ·
                        rfl

theorem cell23_7547600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_7547600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547600 prefixEnd_7547600 := by exact prefixLift 7547600
  have htrace : WordTrace (prefixWord ++ tailWord_7547600) baseStart_7547600 baseEnd_7547600 := by
    simpa [prefixWord, tailWord_7547600, baseEnd_7547600] using wordTrace_append hprefix tailTrace_7547600
  have hstable : (prefixWord ++ tailWord_7547600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547600).length < 2 ^ (prefixWord ++ tailWord_7547600).sum := by decide
  have hdescent : baseEnd_7547600 < baseStart_7547600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547697 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 9]
def baseStart_7547697 : Nat := 118140960795 + 7547697 * 2 ^ 59
def prefixEnd_7547697 : Nat := 4983230072969 + 3 ^ 40 * 7547697 * 2
def baseEnd_7547697 : Nat := 430621821722029037164031

theorem tailTrace_7547697 : CollatzResearch.WordTrace tailWord_7547697 prefixEnd_7547697 430621821722029037164031 := by
  unfold tailWord_7547697
  simp only [CollatzResearch.WordTrace]
  refine ⟨275287125336990287866673345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183524750224660191911115563 275287125336990287866673345)
  ·
    refine ⟨206465344002742715900005009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275287125336990287866673345 206465344002742715900005009)
    ·
      refine ⟨154849008002057036925003757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206465344002742715900005009 154849008002057036925003757)
      ·
        refine ⟨58068378000771388846876409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154849008002057036925003757 58068378000771388846876409)
        ·
          refine ⟨43551283500578541635157307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58068378000771388846876409 43551283500578541635157307)
          ·
            refine ⟨65326925250867812452735961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43551283500578541635157307 65326925250867812452735961)
            ·
              refine ⟨48995193938150859339551971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65326925250867812452735961 48995193938150859339551971)
              ·
                refine ⟨73492790907226289009327957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48995193938150859339551971 73492790907226289009327957)
                ·
                  refine ⟨430621821722029037164031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73492790907226289009327957 430621821722029037164031)
                  ·
                    rfl

theorem cell23_7547697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 9].length) (baseStart_7547697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547697 prefixEnd_7547697 := by exact prefixLift 7547697
  have htrace : WordTrace (prefixWord ++ tailWord_7547697) baseStart_7547697 baseEnd_7547697 := by
    simpa [prefixWord, tailWord_7547697, baseEnd_7547697] using wordTrace_append hprefix tailTrace_7547697
  have hstable : (prefixWord ++ tailWord_7547697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547697).length < 2 ^ (prefixWord ++ tailWord_7547697).sum := by decide
  have hdescent : baseEnd_7547697 < baseStart_7547697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547761 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 2, 5]
def baseStart_7547761 : Nat := 118140960795 + 7547761 * 2 ^ 59
def prefixEnd_7547761 : Nat := 4983230072969 + 3 ^ 40 * 7547761 * 2
def baseEnd_7547761 : Nat := 1291876419420049694691995

theorem tailTrace_7547761 : CollatzResearch.WordTrace tailWord_7547761 prefixEnd_7547761 1291876419420049694691995 := by
  unfold tailWord_7547761
  simp only [CollatzResearch.WordTrace]
  refine ⟨275289459608758426797003137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183526306405838951198002091 275289459608758426797003137)
  ·
    refine ⟨206467094706568820097752353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275289459608758426797003137 206467094706568820097752353)
    ·
      refine ⟨154850321029926615073314265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206467094706568820097752353 154850321029926615073314265)
      ·
        refine ⟨116137740772444961304985699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154850321029926615073314265 116137740772444961304985699)
        ·
          refine ⟨174206611158667441957478549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116137740772444961304985699 174206611158667441957478549)
          ·
            refine ⟨8165934898062536341756807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174206611158667441957478549 8165934898062536341756807)
            ·
              refine ⟨12248902347093804512635211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8165934898062536341756807 12248902347093804512635211)
              ·
                refine ⟨18373353520640706768952817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248902347093804512635211 18373353520640706768952817)
                ·
                  refine ⟨13780015140480530076714613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18373353520640706768952817 13780015140480530076714613)
                  ·
                    refine ⟨1291876419420049694691995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13780015140480530076714613 1291876419420049694691995)
                    ·
                      rfl

theorem cell23_7547761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_7547761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547761 prefixEnd_7547761 := by exact prefixLift 7547761
  have htrace : WordTrace (prefixWord ++ tailWord_7547761) baseStart_7547761 baseEnd_7547761 := by
    simpa [prefixWord, tailWord_7547761, baseEnd_7547761] using wordTrace_append hprefix tailTrace_7547761
  have hstable : (prefixWord ++ tailWord_7547761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547761).length < 2 ^ (prefixWord ++ tailWord_7547761).sum := by decide
  have hdescent : baseEnd_7547761 < baseStart_7547761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547781 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 2, 4, 2]
def baseStart_7547781 : Nat := 118140960795 + 7547781 * 2 ^ 59
def prefixEnd_7547781 : Nat := 4983230072969 + 3 ^ 40 * 7547781 * 2
def baseEnd_7547781 : Nat := 3875639527873239005825893

theorem tailTrace_7547781 : CollatzResearch.WordTrace tailWord_7547781 prefixEnd_7547781 3875639527873239005825893 := by
  unfold tailWord_7547781
  simp only [CollatzResearch.WordTrace]
  refine ⟨275290189068685970212731197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183526792712457313475154131 275290189068685970212731197)
  ·
    refine ⟨103233820900757238829774199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275290189068685970212731197 103233820900757238829774199)
    ·
      refine ⟨154850731351135858244661299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103233820900757238829774199 154850731351135858244661299)
      ·
        refine ⟨232276097026703787366991949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154850731351135858244661299 232276097026703787366991949)
        ·
          refine ⟨87103536385013920262621981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232276097026703787366991949 87103536385013920262621981)
          ·
            refine ⟨32663826144380220098483243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87103536385013920262621981 32663826144380220098483243)
            ·
              refine ⟨48995739216570330147724865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32663826144380220098483243 48995739216570330147724865)
              ·
                refine ⟨36746804412427747610793649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48995739216570330147724865 36746804412427747610793649)
                ·
                  refine ⟨27560103309320810708095237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36746804412427747610793649 27560103309320810708095237)
                  ·
                    refine ⟨5167519370497652007767857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27560103309320810708095237 5167519370497652007767857)
                    ·
                      refine ⟨3875639527873239005825893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167519370497652007767857 3875639527873239005825893)
                      ·
                        rfl

theorem cell23_7547781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_7547781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547781 prefixEnd_7547781 := by exact prefixLift 7547781
  have htrace : WordTrace (prefixWord ++ tailWord_7547781) baseStart_7547781 baseEnd_7547781 := by
    simpa [prefixWord, tailWord_7547781, baseEnd_7547781] using wordTrace_append hprefix tailTrace_7547781
  have hstable : (prefixWord ++ tailWord_7547781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547781).length < 2 ^ (prefixWord ++ tailWord_7547781).sum := by decide
  have hdescent : baseEnd_7547781 < baseStart_7547781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547831 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_7547831 : Nat := 118140960795 + 7547831 * 2 ^ 59
def prefixEnd_7547831 : Nat := 4983230072969 + 3 ^ 40 * 7547831 * 2
def baseEnd_7547831 : Nat := 3875665201905963810200663

theorem tailTrace_7547831 : CollatzResearch.WordTrace tailWord_7547831 prefixEnd_7547831 3875665201905963810200663 := by
  unfold tailWord_7547831
  simp only [CollatzResearch.WordTrace]
  refine ⟨275292012718504828752051347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183528008479003219168034231 275292012718504828752051347)
  ·
    refine ⟨412938019077757243128077021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275292012718504828752051347 412938019077757243128077021)
    ·
      refine ⟨154851757154158966173028883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412938019077757243128077021 154851757154158966173028883)
      ·
        refine ⟨232277635731238449259543325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154851757154158966173028883 232277635731238449259543325)
        ·
          refine ⟨87104113399214418472328747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232277635731238449259543325 87104113399214418472328747)
          ·
            refine ⟨130656170098821627708493121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87104113399214418472328747 130656170098821627708493121)
            ·
              refine ⟨97992127574116220781369841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130656170098821627708493121 97992127574116220781369841)
              ·
                refine ⟨73494095680587165586027381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97992127574116220781369841 73494095680587165586027381)
                ·
                  refine ⟨6890071470055046773690067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73494095680587165586027381 6890071470055046773690067)
                  ·
                    refine ⟨10335107205082570160535101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6890071470055046773690067 10335107205082570160535101)
                    ·
                      refine ⟨3875665201905963810200663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10335107205082570160535101 3875665201905963810200663)
                      ·
                        rfl

theorem cell23_7547831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_7547831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547831 prefixEnd_7547831 := by exact prefixLift 7547831
  have htrace : WordTrace (prefixWord ++ tailWord_7547831) baseStart_7547831 baseEnd_7547831 := by
    simpa [prefixWord, tailWord_7547831, baseEnd_7547831] using wordTrace_append hprefix tailTrace_7547831
  have hstable : (prefixWord ++ tailWord_7547831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547831).length < 2 ^ (prefixWord ++ tailWord_7547831).sum := by decide
  have hdescent : baseEnd_7547831 < baseStart_7547831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547918 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_7547918 : Nat := 118140960795 + 7547918 * 2 ^ 59
def prefixEnd_7547918 : Nat := 4983230072969 + 3 ^ 40 * 7547918 * 2
def baseEnd_7547918 : Nat := 3875709874722904969812763

theorem tailTrace_7547918 : CollatzResearch.WordTrace tailWord_7547918 prefixEnd_7547918 3875709874722904969812763 := by
  unfold tailWord_7547918
  simp only [CollatzResearch.WordTrace]
  refine ⟨34411898233648705326308551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183530123912793095073645605 34411898233648705326308551)
  ·
    refine ⟨51617847350473057989462827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34411898233648705326308551 51617847350473057989462827)
    ·
      refine ⟨77426771025709586984194241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51617847350473057989462827 77426771025709586984194241)
      ·
        refine ⟨58070078269282190238145681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77426771025709586984194241 58070078269282190238145681)
        ·
          refine ⟨43552558701961642678609261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58070078269282190238145681 43552558701961642678609261)
          ·
            refine ⟨16332209513235616004478473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43552558701961642678609261 16332209513235616004478473)
            ·
              refine ⟨12249157134926712003358855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16332209513235616004478473 12249157134926712003358855)
              ·
                refine ⟨18373735702390068005038283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12249157134926712003358855 18373735702390068005038283)
                ·
                  refine ⟨27560603553585102007557425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18373735702390068005038283 27560603553585102007557425)
                  ·
                    refine ⟨20670452665188826505668069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27560603553585102007557425 20670452665188826505668069)
                    ·
                      refine ⟨3875709874722904969812763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20670452665188826505668069 3875709874722904969812763)
                      ·
                        rfl

theorem cell23_7547918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_7547918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547918 prefixEnd_7547918 := by exact prefixLift 7547918
  have htrace : WordTrace (prefixWord ++ tailWord_7547918) baseStart_7547918 baseEnd_7547918 := by
    simpa [prefixWord, tailWord_7547918, baseEnd_7547918] using wordTrace_append hprefix tailTrace_7547918
  have hstable : (prefixWord ++ tailWord_7547918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547918).length < 2 ^ (prefixWord ++ tailWord_7547918).sum := by decide
  have hdescent : baseEnd_7547918 < baseStart_7547918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547938 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_7547938 : Nat := 118140960795 + 7547938 * 2 ^ 59
def prefixEnd_7547938 : Nat := 4983230072969 + 3 ^ 40 * 7547938 * 2
def baseEnd_7547938 : Nat := 3875720144335994891562671

theorem tailTrace_7547938 : CollatzResearch.WordTrace tailWord_7547938 prefixEnd_7547938 3875720144335994891562671 := by
  unfold tailWord_7547938
  simp only [CollatzResearch.WordTrace]
  refine ⟨68823978832279296506549117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183530610219411457350797645 68823978832279296506549117)
  ·
    refine ⟨25808992062104736189955919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68823978832279296506549117 25808992062104736189955919)
    ·
      refine ⟨38713488093157104284933879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25808992062104736189955919 38713488093157104284933879)
      ·
        refine ⟨58070232139735656427400819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38713488093157104284933879 58070232139735656427400819)
        ·
          refine ⟨87105348209603484641101229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58070232139735656427400819 87105348209603484641101229)
          ·
            refine ⟨32664505578601306740412961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87105348209603484641101229 32664505578601306740412961)
            ·
              refine ⟨24498379183950980055309721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32664505578601306740412961 24498379183950980055309721)
              ·
                refine ⟨18373784387963235041482291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24498379183950980055309721 18373784387963235041482291)
                ·
                  refine ⟨27560676581944852562223437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18373784387963235041482291 27560676581944852562223437)
                  ·
                    refine ⟨10335253718229319710833789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27560676581944852562223437 10335253718229319710833789)
                    ·
                      refine ⟨3875720144335994891562671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10335253718229319710833789 3875720144335994891562671)
                      ·
                        rfl

theorem cell23_7547938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_7547938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547938 prefixEnd_7547938 := by exact prefixLift 7547938
  have htrace : WordTrace (prefixWord ++ tailWord_7547938) baseStart_7547938 baseEnd_7547938 := by
    simpa [prefixWord, tailWord_7547938, baseEnd_7547938] using wordTrace_append hprefix tailTrace_7547938
  have hstable : (prefixWord ++ tailWord_7547938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547938).length < 2 ^ (prefixWord ++ tailWord_7547938).sum := by decide
  have hdescent : baseEnd_7547938 < baseStart_7547938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7547990 : List Nat := [5, 2, 2, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_7547990 : Nat := 118140960795 + 7547990 * 2 ^ 59
def prefixEnd_7547990 : Nat := 4983230072969 + 3 ^ 40 * 7547990 * 2
def baseEnd_7547990 : Nat := 3875746845330028688112433

theorem tailTrace_7547990 : CollatzResearch.WordTrace tailWord_7547990 prefixEnd_7547990 3875746845330028688112433 := by
  unfold tailWord_7547990
  simp only [CollatzResearch.WordTrace]
  refine ⟨17206113245308049931693089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183531874616619199271392949 17206113245308049931693089)
  ·
    refine ⟨12904584933981037448769817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17206113245308049931693089 12904584933981037448769817)
    ·
      refine ⟨9678438700485778086577363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12904584933981037448769817 9678438700485778086577363)
      ·
        refine ⟨14517658050728667129866045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9678438700485778086577363 14517658050728667129866045)
        ·
          refine ⟨5444121769023250173699767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14517658050728667129866045 5444121769023250173699767)
          ·
            refine ⟨8166182653534875260549651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5444121769023250173699767 8166182653534875260549651)
            ·
              refine ⟨12249273980302312890824477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8166182653534875260549651 12249273980302312890824477)
              ·
                refine ⟨4593477742613367334059179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12249273980302312890824477 4593477742613367334059179)
                ·
                  refine ⟨6890216613920051001088769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593477742613367334059179 6890216613920051001088769)
                  ·
                    refine ⟨5167662460440038250816577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6890216613920051001088769 5167662460440038250816577)
                    ·
                      refine ⟨3875746845330028688112433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167662460440038250816577 3875746845330028688112433)
                      ·
                        rfl

theorem cell23_7547990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_7547990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7547990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7547990 prefixEnd_7547990 := by exact prefixLift 7547990
  have htrace : WordTrace (prefixWord ++ tailWord_7547990) baseStart_7547990 baseEnd_7547990 := by
    simpa [prefixWord, tailWord_7547990, baseEnd_7547990] using wordTrace_append hprefix tailTrace_7547990
  have hstable : (prefixWord ++ tailWord_7547990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7547990).length < 2 ^ (prefixWord ++ tailWord_7547990).sum := by decide
  have hdescent : baseEnd_7547990 < baseStart_7547990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7547990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548051 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 4]
def baseStart_7548051 : Nat := 118140960795 + 7548051 * 2 ^ 59
def prefixEnd_7548051 : Nat := 4983230072969 + 3 ^ 40 * 7548051 * 2
def baseEnd_7548051 : Nat := 3875778167649952949449651

theorem tailTrace_7548051 : CollatzResearch.WordTrace tailWord_7548051 prefixEnd_7548051 3875778167649952949449651 := by
  unfold tailWord_7548051
  simp only [CollatzResearch.WordTrace]
  refine ⟨275300036777707806325060007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183533357851805204216706671 275300036777707806325060007)
  ·
    refine ⟨412950055166561709487590011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275300036777707806325060007 412950055166561709487590011)
    ·
      refine ⟨619425082749842564231385017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412950055166561709487590011 619425082749842564231385017)
      ·
        refine ⟨464568812062381923173538763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619425082749842564231385017 464568812062381923173538763)
        ·
          refine ⟨696853218093572884760308145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464568812062381923173538763 696853218093572884760308145)
          ·
            refine ⟨522639913570179663570231109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696853218093572884760308145 522639913570179663570231109)
            ·
              refine ⟨97994983794408686919418333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 522639913570179663570231109 97994983794408686919418333)
              ·
                refine ⟨36748118922903257594781875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97994983794408686919418333 36748118922903257594781875)
                ·
                  refine ⟨55122178384354886392172813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36748118922903257594781875 55122178384354886392172813)
                  ·
                    refine ⟨20670816894133082397064805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55122178384354886392172813 20670816894133082397064805)
                    ·
                      refine ⟨3875778167649952949449651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20670816894133082397064805 3875778167649952949449651)
                      ·
                        rfl

theorem cell23_7548051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_7548051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548051 prefixEnd_7548051 := by exact prefixLift 7548051
  have htrace : WordTrace (prefixWord ++ tailWord_7548051) baseStart_7548051 baseEnd_7548051 := by
    simpa [prefixWord, tailWord_7548051, baseEnd_7548051] using wordTrace_append hprefix tailTrace_7548051
  have hstable : (prefixWord ++ tailWord_7548051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548051).length < 2 ^ (prefixWord ++ tailWord_7548051).sum := by decide
  have hdescent : baseEnd_7548051 < baseStart_7548051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548058 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7548058 : Nat := 118140960795 + 7548058 * 2 ^ 59
def prefixEnd_7548058 : Nat := 4983230072969 + 3 ^ 40 * 7548058 * 2
def baseEnd_7548058 : Nat := 3875781762014534422062119

theorem tailTrace_7548058 : CollatzResearch.WordTrace tailWord_7548058 prefixEnd_7548058 3875781762014534422062119 := by
  unfold tailWord_7548058
  simp only [CollatzResearch.WordTrace]
  refine ⟨68825073022170611630141207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183533528059121631013709885 68825073022170611630141207)
  ·
    refine ⟨103237609533255917445211811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68825073022170611630141207 103237609533255917445211811)
    ·
      refine ⟨154856414299883876167817717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103237609533255917445211811 154856414299883876167817717)
      ·
        refine ⟨14517788840614113390732911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154856414299883876167817717 14517788840614113390732911)
        ·
          refine ⟨21776683260921170086099367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14517788840614113390732911 21776683260921170086099367)
          ·
            refine ⟨32665024891381755129149051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21776683260921170086099367 32665024891381755129149051)
            ·
              refine ⟨48997537337072632693723577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32665024891381755129149051 48997537337072632693723577)
              ·
                refine ⟨36748153002804474520292683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48997537337072632693723577 36748153002804474520292683)
                ·
                  refine ⟨55122229504206711780439025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36748153002804474520292683 55122229504206711780439025)
                  ·
                    refine ⟨41341672128155033835329269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55122229504206711780439025 41341672128155033835329269)
                    ·
                      refine ⟨3875781762014534422062119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41341672128155033835329269 3875781762014534422062119)
                      ·
                        rfl

theorem cell23_7548058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7548058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548058 prefixEnd_7548058 := by exact prefixLift 7548058
  have htrace : WordTrace (prefixWord ++ tailWord_7548058) baseStart_7548058 baseEnd_7548058 := by
    simpa [prefixWord, tailWord_7548058, baseEnd_7548058] using wordTrace_append hprefix tailTrace_7548058
  have hstable : (prefixWord ++ tailWord_7548058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548058).length < 2 ^ (prefixWord ++ tailWord_7548058).sum := by decide
  have hdescent : baseEnd_7548058 < baseStart_7548058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548125 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 8]
def baseStart_7548125 : Nat := 118140960795 + 7548125 * 2 ^ 59
def prefixEnd_7548125 : Nat := 4983230072969 + 3 ^ 40 * 7548125 * 2
def baseEnd_7548125 : Nat := 430646240579820628880479

theorem tailTrace_7548125 : CollatzResearch.WordTrace tailWord_7548125 prefixEnd_7548125 430646240579820628880479 := by
  unfold tailWord_7548125
  simp only [CollatzResearch.WordTrace]
  refine ⟨275302735779439716963253829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183535157186293144642169219 275302735779439716963253829)
  ·
    refine ⟨51619262958644946930610093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275302735779439716963253829 51619262958644946930610093)
    ·
      refine ⟨19357223609491855098978785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51619262958644946930610093 19357223609491855098978785)
      ·
        refine ⟨14517917707118891324234089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19357223609491855098978785 14517917707118891324234089)
        ·
          refine ⟨10888438280339168493175567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14517917707118891324234089 10888438280339168493175567)
          ·
            refine ⟨16332657420508752739763351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10888438280339168493175567 16332657420508752739763351)
            ·
              refine ⟨24498986130763129109645027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16332657420508752739763351 24498986130763129109645027)
              ·
                refine ⟨36748479196144693664467541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24498986130763129109645027 36748479196144693664467541)
                ·
                  refine ⟨430646240579820628880479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36748479196144693664467541 430646240579820628880479)
                  ·
                    rfl

theorem cell23_7548125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_7548125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548125 prefixEnd_7548125 := by exact prefixLift 7548125
  have htrace : WordTrace (prefixWord ++ tailWord_7548125) baseStart_7548125 baseEnd_7548125 := by
    simpa [prefixWord, tailWord_7548125, baseEnd_7548125] using wordTrace_append hprefix tailTrace_7548125
  have hstable : (prefixWord ++ tailWord_7548125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548125).length < 2 ^ (prefixWord ++ tailWord_7548125).sum := by decide
  have hdescent : baseEnd_7548125 < baseStart_7548125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548186 : List Nat := [3, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3]
def baseStart_7548186 : Nat := 118140960795 + 7548186 * 2 ^ 59
def prefixEnd_7548186 : Nat := 4983230072969 + 3 ^ 40 * 7548186 * 2
def baseEnd_7548186 : Nat := 3875847487538309921261531

theorem tailTrace_7548186 : CollatzResearch.WordTrace tailWord_7548186 prefixEnd_7548186 3875847487538309921261531 := by
  unfold tailWord_7548186
  simp only [CollatzResearch.WordTrace]
  refine ⟨68826240158054681095306103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183536640421479149587482941 68826240158054681095306103)
  ·
    refine ⟨103239360237082021642959155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68826240158054681095306103 103239360237082021642959155)
    ·
      refine ⟨154859040355623032464438733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103239360237082021642959155 154859040355623032464438733)
      ·
        refine ⟨58072140133358637174164525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154859040355623032464438733 58072140133358637174164525)
        ·
          refine ⟨21777052550009488940311697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58072140133358637174164525 21777052550009488940311697)
          ·
            refine ⟨16332789412507116705233773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21777052550009488940311697 16332789412507116705233773)
            ·
              refine ⟨6124796029690168764462665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16332789412507116705233773 6124796029690168764462665)
              ·
                refine ⟨4593597022267626573346999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6124796029690168764462665 4593597022267626573346999)
                ·
                  refine ⟨6890395533401439860020499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593597022267626573346999 6890395533401439860020499)
                  ·
                    refine ⟨10335593300102159790030749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6890395533401439860020499 10335593300102159790030749)
                    ·
                      refine ⟨3875847487538309921261531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10335593300102159790030749 3875847487538309921261531)
                      ·
                        rfl

theorem cell23_7548186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_7548186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548186 prefixEnd_7548186 := by exact prefixLift 7548186
  have htrace : WordTrace (prefixWord ++ tailWord_7548186) baseStart_7548186 baseEnd_7548186 := by
    simpa [prefixWord, tailWord_7548186, baseEnd_7548186] using wordTrace_append hprefix tailTrace_7548186
  have hstable : (prefixWord ++ tailWord_7548186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548186).length < 2 ^ (prefixWord ++ tailWord_7548186).sum := by decide
  have hdescent : baseEnd_7548186 < baseStart_7548186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548188 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_7548188 : Nat := 118140960795 + 7548188 * 2 ^ 59
def prefixEnd_7548188 : Nat := 4983230072969 + 3 ^ 40 * 7548188 * 2
def baseEnd_7548188 : Nat := 3875848514499618913436521

theorem tailTrace_7548188 : CollatzResearch.WordTrace tailWord_7548188 prefixEnd_7548188 3875848514499618913436521 := by
  unfold tailWord_7548188
  simp only [CollatzResearch.WordTrace]
  refine ⟨137652516789105739361398609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183536689052140985815198145 137652516789105739361398609)
  ·
    refine ⟨103239387591829304521048957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137652516789105739361398609 103239387591829304521048957)
    ·
      refine ⟨38714770346935989195393359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103239387591829304521048957 38714770346935989195393359)
      ·
        refine ⟨58072155520403983793090039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38714770346935989195393359 58072155520403983793090039)
        ·
          refine ⟨87108233280605975689635059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58072155520403983793090039 87108233280605975689635059)
          ·
            refine ⟨130662349920908963534452589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87108233280605975689635059 130662349920908963534452589)
            ·
              refine ⟨48998381220340861325419721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130662349920908963534452589 48998381220340861325419721)
              ·
                refine ⟨36748785915255645994064791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48998381220340861325419721 36748785915255645994064791)
                ·
                  refine ⟨55123178872883468991097187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36748785915255645994064791 55123178872883468991097187)
                  ·
                    refine ⟨82684768309325203486645781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55123178872883468991097187 82684768309325203486645781)
                    ·
                      refine ⟨3875848514499618913436521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82684768309325203486645781 3875848514499618913436521)
                      ·
                        rfl

theorem cell23_7548188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_7548188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548188 prefixEnd_7548188 := by exact prefixLift 7548188
  have htrace : WordTrace (prefixWord ++ tailWord_7548188) baseStart_7548188 baseEnd_7548188 := by
    simpa [prefixWord, tailWord_7548188, baseEnd_7548188] using wordTrace_append hprefix tailTrace_7548188
  have hstable : (prefixWord ++ tailWord_7548188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548188).length < 2 ^ (prefixWord ++ tailWord_7548188).sum := by decide
  have hdescent : baseEnd_7548188 < baseStart_7548188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548212 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_7548212 : Nat := 118140960795 + 7548212 * 2 ^ 59
def prefixEnd_7548212 : Nat := 4983230072969 + 3 ^ 40 * 7548212 * 2
def baseEnd_7548212 : Nat := 3875860838035326819536411

theorem tailTrace_7548212 : CollatzResearch.WordTrace tailWord_7548212 prefixEnd_7548212 3875860838035326819536411 := by
  unfold tailWord_7548212
  simp only [CollatzResearch.WordTrace]
  refine ⟨137652954465062265410835445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183537272620083020547780593 137652954465062265410835445)
  ·
    refine ⟨12904964481099587382265823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137652954465062265410835445 12904964481099587382265823)
    ·
      refine ⟨19357446721649381073398735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12904964481099587382265823 19357446721649381073398735)
      ·
        refine ⟨29036170082474071610098103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19357446721649381073398735 29036170082474071610098103)
        ·
          refine ⟨43554255123711107415147155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29036170082474071610098103 43554255123711107415147155)
          ·
            refine ⟨65331382685566661122720733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43554255123711107415147155 65331382685566661122720733)
            ·
              refine ⟨24499268507087497921020275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65331382685566661122720733 24499268507087497921020275)
              ·
                refine ⟨36748902760631246881530413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24499268507087497921020275 36748902760631246881530413)
                ·
                  refine ⟨13780838535236717580573905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36748902760631246881530413 13780838535236717580573905)
                  ·
                    refine ⟨10335628901427538185430429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13780838535236717580573905 10335628901427538185430429)
                    ·
                      refine ⟨3875860838035326819536411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10335628901427538185430429 3875860838035326819536411)
                      ·
                        rfl

theorem cell23_7548212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_7548212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548212 prefixEnd_7548212 := by exact prefixLift 7548212
  have htrace : WordTrace (prefixWord ++ tailWord_7548212) baseStart_7548212 baseEnd_7548212 := by
    simpa [prefixWord, tailWord_7548212, baseEnd_7548212] using wordTrace_append hprefix tailTrace_7548212
  have hstable : (prefixWord ++ tailWord_7548212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548212).length < 2 ^ (prefixWord ++ tailWord_7548212).sum := by decide
  have hdescent : baseEnd_7548212 < baseStart_7548212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548237 : List Nat := [1, 6, 1, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7548237 : Nat := 118140960795 + 7548237 * 2 ^ 59
def prefixEnd_7548237 : Nat := 4983230072969 + 3 ^ 40 * 7548237 * 2
def baseEnd_7548237 : Nat := 3875873675051689221723797

theorem tailTrace_7548237 : CollatzResearch.WordTrace tailWord_7548237 prefixEnd_7548237 3875873675051689221723797 := by
  unfold tailWord_7548237
  simp only [CollatzResearch.WordTrace]
  refine ⟨275306820755033960091330965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183537880503355973394220643 275306820755033960091330965)
  ·
    refine ⟨12905007222892216879281139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 275306820755033960091330965 12905007222892216879281139)
    ·
      refine ⟨19357510834338325318921709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12905007222892216879281139 19357510834338325318921709)
      ·
        refine ⟨7259066562876871994595641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19357510834338325318921709 7259066562876871994595641)
        ·
          refine ⟨5444299922157653995946731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7259066562876871994595641 5444299922157653995946731)
          ·
            refine ⟨8166449883236480993920097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5444299922157653995946731 8166449883236480993920097)
            ·
              refine ⟨6124837412427360745440073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8166449883236480993920097 6124837412427360745440073)
              ·
                refine ⟨4593628059320520559080055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6124837412427360745440073 4593628059320520559080055)
                ·
                  refine ⟨6890442088980780838620083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593628059320520559080055 6890442088980780838620083)
                  ·
                    refine ⟨10335663133471171257930125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6890442088980780838620083 10335663133471171257930125)
                    ·
                      refine ⟨3875873675051689221723797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10335663133471171257930125 3875873675051689221723797)
                      ·
                        rfl

theorem cell23_7548237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7548237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548237 prefixEnd_7548237 := by exact prefixLift 7548237
  have htrace : WordTrace (prefixWord ++ tailWord_7548237) baseStart_7548237 baseEnd_7548237 := by
    simpa [prefixWord, tailWord_7548237, baseEnd_7548237] using wordTrace_append hprefix tailTrace_7548237
  have hstable : (prefixWord ++ tailWord_7548237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548237).length < 2 ^ (prefixWord ++ tailWord_7548237).sum := by decide
  have hdescent : baseEnd_7548237 < baseStart_7548237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548248 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_7548248 : Nat := 118140960795 + 7548248 * 2 ^ 59
def prefixEnd_7548248 : Nat := 4983230072969 + 3 ^ 40 * 7548248 * 2
def baseEnd_7548248 : Nat := 3875879323338888678686245

theorem tailTrace_7548248 : CollatzResearch.WordTrace tailWord_7548248 prefixEnd_7548248 3875879323338888678686245 := by
  unfold tailWord_7548248
  simp only [CollatzResearch.WordTrace]
  refine ⟨137653610978997054484990699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183538147971996072646654265 137653610978997054484990699)
  ·
    refine ⟨206480416468495581727486049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137653610978997054484990699 206480416468495581727486049)
    ·
      refine ⟨154860312351371686295614537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206480416468495581727486049 154860312351371686295614537)
      ·
        refine ⟨116145234263528764721710903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154860312351371686295614537 116145234263528764721710903)
        ·
          refine ⟨174217851395293147082566355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116145234263528764721710903 174217851395293147082566355)
          ·
            refine ⟨261326777092939720623849533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174217851395293147082566355 261326777092939720623849533)
            ·
              refine ⟨97997541409852395233943575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261326777092939720623849533 97997541409852395233943575)
              ·
                refine ⟨146996312114778592850915363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97997541409852395233943575 146996312114778592850915363)
                ·
                  refine ⟨220494468172167889276373045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146996312114778592850915363 220494468172167889276373045)
                  ·
                    refine ⟨20671356391140739619659973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220494468172167889276373045 20671356391140739619659973)
                    ·
                      refine ⟨3875879323338888678686245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20671356391140739619659973 3875879323338888678686245)
                      ·
                        rfl

theorem cell23_7548248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_7548248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548248 prefixEnd_7548248 := by exact prefixLift 7548248
  have htrace : WordTrace (prefixWord ++ tailWord_7548248) baseStart_7548248 baseEnd_7548248 := by
    simpa [prefixWord, tailWord_7548248, baseEnd_7548248] using wordTrace_append hprefix tailTrace_7548248
  have hstable : (prefixWord ++ tailWord_7548248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548248).length < 2 ^ (prefixWord ++ tailWord_7548248).sum := by decide
  have hdescent : baseEnd_7548248 < baseStart_7548248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548282 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2]
def baseStart_7548282 : Nat := 118140960795 + 7548282 * 2 ^ 59
def prefixEnd_7548282 : Nat := 4983230072969 + 3 ^ 40 * 7548282 * 2
def baseEnd_7548282 : Nat := 3875896781681141545661089

theorem tailTrace_7548282 : CollatzResearch.WordTrace tailWord_7548282 prefixEnd_7548282 3875896781681141545661089 := by
  unfold tailWord_7548282
  simp only [CollatzResearch.WordTrace]
  refine ⟨68827115509967733194179775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183538974693247288517812733 68827115509967733194179775)
  ·
    refine ⟨103240673264951599791269663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68827115509967733194179775 103240673264951599791269663)
    ·
      refine ⟨154861009897427399686904495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103240673264951599791269663 154861009897427399686904495)
      ·
        refine ⟨232291514846141099530356743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154861009897427399686904495 232291514846141099530356743)
        ·
          refine ⟨348437272269211649295535115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232291514846141099530356743 348437272269211649295535115)
          ·
            refine ⟨522655908403817473943302673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348437272269211649295535115 522655908403817473943302673)
            ·
              refine ⟨391991931302863105457477005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522655908403817473943302673 391991931302863105457477005)
              ·
                refine ⟨146996974238573664546553877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391991931302863105457477005 146996974238573664546553877)
                ·
                  refine ⟨6890483167433140525619713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146996974238573664546553877 6890483167433140525619713)
                  ·
                    refine ⟨5167862375574855394214785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6890483167433140525619713 5167862375574855394214785)
                    ·
                      refine ⟨3875896781681141545661089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167862375574855394214785 3875896781681141545661089)
                      ·
                        rfl

theorem cell23_7548282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_7548282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548282 prefixEnd_7548282 := by exact prefixLift 7548282
  have htrace : WordTrace (prefixWord ++ tailWord_7548282) baseStart_7548282 baseEnd_7548282 := by
    simpa [prefixWord, tailWord_7548282, baseEnd_7548282] using wordTrace_append hprefix tailTrace_7548282
  have hstable : (prefixWord ++ tailWord_7548282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548282).length < 2 ^ (prefixWord ++ tailWord_7548282).sum := by decide
  have hdescent : baseEnd_7548282 < baseStart_7548282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548295 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_7548295 : Nat := 118140960795 + 7548295 * 2 ^ 59
def prefixEnd_7548295 : Nat := 4983230072969 + 3 ^ 40 * 7548295 * 2
def baseEnd_7548295 : Nat := 3875903456929649994798529

theorem tailTrace_7548295 : CollatzResearch.WordTrace tailWord_7548295 prefixEnd_7548295 3875903456929649994798529 := by
  unfold tailWord_7548295
  simp only [CollatzResearch.WordTrace]
  refine ⟨275308936188823835996942339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183539290792549223997961559 275308936188823835996942339)
  ·
    refine ⟨412963404283235753995413509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275308936188823835996942339 412963404283235753995413509)
    ·
      refine ⟨77430638303106703874140033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 412963404283235753995413509 77430638303106703874140033)
      ·
        refine ⟨58072978727330027905605025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77430638303106703874140033 58072978727330027905605025)
        ·
          refine ⟨43554734045497520929203769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58072978727330027905605025 43554734045497520929203769)
          ·
            refine ⟨32666050534123140696902827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43554734045497520929203769 32666050534123140696902827)
            ·
              refine ⟨48999075801184711045354241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32666050534123140696902827 48999075801184711045354241)
              ·
                refine ⟨36749306850888533284015681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48999075801184711045354241 36749306850888533284015681)
                ·
                  refine ⟨27561980138166399963011761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36749306850888533284015681 27561980138166399963011761)
                  ·
                    refine ⟨20671485103624799972258821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27561980138166399963011761 20671485103624799972258821)
                    ·
                      refine ⟨3875903456929649994798529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20671485103624799972258821 3875903456929649994798529)
                      ·
                        rfl

theorem cell23_7548295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_7548295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548295 prefixEnd_7548295 := by exact prefixLift 7548295
  have htrace : WordTrace (prefixWord ++ tailWord_7548295) baseStart_7548295 baseEnd_7548295 := by
    simpa [prefixWord, tailWord_7548295, baseEnd_7548295] using wordTrace_append hprefix tailTrace_7548295
  have hstable : (prefixWord ++ tailWord_7548295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548295).length < 2 ^ (prefixWord ++ tailWord_7548295).sum := by decide
  have hdescent : baseEnd_7548295 < baseStart_7548295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548355 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 4]
def baseStart_7548355 : Nat := 118140960795 + 7548355 * 2 ^ 59
def prefixEnd_7548355 : Nat := 4983230072969 + 3 ^ 40 * 7548355 * 2
def baseEnd_7548355 : Nat := 3875934265768919760048253

theorem tailTrace_7548355 : CollatzResearch.WordTrace tailWord_7548355 prefixEnd_7548355 3875934265768919760048253 := by
  unfold tailWord_7548355
  simp only [CollatzResearch.WordTrace]
  refine ⟨275311124568606466244126519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183540749712404310829417679 275311124568606466244126519)
  ·
    refine ⟨412966686852909699366189779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275311124568606466244126519 412966686852909699366189779)
    ·
      refine ⟨619450030279364549049284669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412966686852909699366189779 619450030279364549049284669)
      ·
        refine ⟨232293761354761705893481751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 619450030279364549049284669 232293761354761705893481751)
        ·
          refine ⟨348440642032142558840222627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232293761354761705893481751 348440642032142558840222627)
          ·
            refine ⟨522660963048213838260333941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348440642032142558840222627 522660963048213838260333941)
            ·
              refine ⟨48999465285770047336906307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 522660963048213838260333941 48999465285770047336906307)
              ·
                refine ⟨73499197928655071005359461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48999465285770047336906307 73499197928655071005359461)
                ·
                  refine ⟨13781099611622825813504899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73499197928655071005359461 13781099611622825813504899)
                  ·
                    refine ⟨20671649417434238720257349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13781099611622825813504899 20671649417434238720257349)
                    ·
                      refine ⟨3875934265768919760048253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20671649417434238720257349 3875934265768919760048253)
                      ·
                        rfl

theorem cell23_7548355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_7548355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548355 prefixEnd_7548355 := by exact prefixLift 7548355
  have htrace : WordTrace (prefixWord ++ tailWord_7548355) baseStart_7548355 baseEnd_7548355 := by
    simpa [prefixWord, tailWord_7548355, baseEnd_7548355] using wordTrace_append hprefix tailTrace_7548355
  have hstable : (prefixWord ++ tailWord_7548355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548355).length < 2 ^ (prefixWord ++ tailWord_7548355).sum := by decide
  have hdescent : baseEnd_7548355 < baseStart_7548355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548356 : List Nat := [2, 3, 3, 2, 1, 2, 3, 2, 5]
def baseStart_7548356 : Nat := 118140960795 + 7548356 * 2 ^ 59
def prefixEnd_7548356 : Nat := 4983230072969 + 3 ^ 40 * 7548356 * 2
def baseEnd_7548356 : Nat := 430659419916619361792861

theorem tailTrace_7548356 : CollatzResearch.WordTrace tailWord_7548356 prefixEnd_7548356 430659419916619361792861 := by
  unfold tailWord_7548356
  simp only [CollatzResearch.WordTrace]
  refine ⟨137655580520801421707456461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183540774027735228943275281 137655580520801421707456461)
  ·
    refine ⟨51620842695300533140296173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137655580520801421707456461 51620842695300533140296173)
    ·
      refine ⟨19357816010737699927611065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51620842695300533140296173 19357816010737699927611065)
      ·
        refine ⟨14518362008053274945708299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19357816010737699927611065 14518362008053274945708299)
        ·
          refine ⟨21777543012079912418562449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14518362008053274945708299 21777543012079912418562449)
          ·
            refine ⟨16333157259059934313921837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21777543012079912418562449 16333157259059934313921837)
            ·
              refine ⟨6124933972147475367720689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16333157259059934313921837 6124933972147475367720689)
              ·
                refine ⟨4593700479110606525790517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6124933972147475367720689 4593700479110606525790517)
                ·
                  refine ⟨430659419916619361792861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4593700479110606525790517 430659419916619361792861)
                  ·
                    rfl

theorem cell23_7548356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_7548356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548356 prefixEnd_7548356 := by exact prefixLift 7548356
  have htrace : WordTrace (prefixWord ++ tailWord_7548356) baseStart_7548356 baseEnd_7548356 := by
    simpa [prefixWord, tailWord_7548356, baseEnd_7548356] using wordTrace_append hprefix tailTrace_7548356
  have hstable : (prefixWord ++ tailWord_7548356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548356).length < 2 ^ (prefixWord ++ tailWord_7548356).sum := by decide
  have hdescent : baseEnd_7548356 < baseStart_7548356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548375 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_7548375 : Nat := 118140960795 + 7548375 * 2 ^ 59
def prefixEnd_7548375 : Nat := 4983230072969 + 3 ^ 40 * 7548375 * 2
def baseEnd_7548375 : Nat := 3875944535382009681798161

theorem tailTrace_7548375 : CollatzResearch.WordTrace tailWord_7548375 prefixEnd_7548375 3875944535382009681798161 := by
  unfold tailWord_7548375
  simp only [CollatzResearch.WordTrace]
  refine ⟨275311854028534009659854579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183541236019022673106569719 275311854028534009659854579)
  ·
    refine ⟨412967781042801014489781869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275311854028534009659854579 412967781042801014489781869)
    ·
      refine ⟨154862917891050380433668201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412967781042801014489781869 154862917891050380433668201)
      ·
        refine ⟨116147188418287785325251151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154862917891050380433668201 116147188418287785325251151)
        ·
          refine ⟨174220782627431677987876727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116147188418287785325251151 174220782627431677987876727)
          ·
            refine ⟨261331173941147516981815091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174220782627431677987876727 261331173941147516981815091)
            ·
              refine ⟨391996760911721275472722637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261331173941147516981815091 391996760911721275472722637)
              ·
                refine ⟨146998785341895478302270989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391996760911721275472722637 146998785341895478302270989)
                ·
                  refine ⟨55124544503210804363351621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146998785341895478302270989 55124544503210804363351621)
                  ·
                    refine ⟨10335852094352025818128429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55124544503210804363351621 10335852094352025818128429)
                    ·
                      refine ⟨3875944535382009681798161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10335852094352025818128429 3875944535382009681798161)
                      ·
                        rfl

theorem cell23_7548375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_7548375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548375 prefixEnd_7548375 := by exact prefixLift 7548375
  have htrace : WordTrace (prefixWord ++ tailWord_7548375) baseStart_7548375 baseEnd_7548375 := by
    simpa [prefixWord, tailWord_7548375, baseEnd_7548375] using wordTrace_append hprefix tailTrace_7548375
  have hstable : (prefixWord ++ tailWord_7548375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548375).length < 2 ^ (prefixWord ++ tailWord_7548375).sum := by decide
  have hdescent : baseEnd_7548375 < baseStart_7548375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548389 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7548389 : Nat := 118140960795 + 7548389 * 2 ^ 59
def prefixEnd_7548389 : Nat := 4983230072969 + 3 ^ 40 * 7548389 * 2
def baseEnd_7548389 : Nat := 3875951724111172627023097

theorem tailTrace_7548389 : CollatzResearch.WordTrace tailWord_7548389 prefixEnd_7548389 3875951724111172627023097 := by
  unfold tailWord_7548389
  simp only [CollatzResearch.WordTrace]
  refine ⟨275312364650483290050864221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183541576433655526700576147 275312364650483290050864221)
  ·
    refine ⟨103242136743931233769074083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275312364650483290050864221 103242136743931233769074083)
    ·
      refine ⟨154863205115896850653611125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103242136743931233769074083 154863205115896850653611125)
      ·
        refine ⟨14518425479615329748776043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154863205115896850653611125 14518425479615329748776043)
        ·
          refine ⟨21777638219422994623164065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14518425479615329748776043 21777638219422994623164065)
          ·
            refine ⟨16333228664567245967373049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21777638219422994623164065 16333228664567245967373049)
            ·
              refine ⟨12249921498425434475529787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16333228664567245967373049 12249921498425434475529787)
              ·
                refine ⟨18374882247638151713294681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12249921498425434475529787 18374882247638151713294681)
                ·
                  refine ⟨13781161685728613784971011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18374882247638151713294681 13781161685728613784971011)
                  ·
                    refine ⟨20671742528592920677456517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13781161685728613784971011 20671742528592920677456517)
                    ·
                      refine ⟨3875951724111172627023097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20671742528592920677456517 3875951724111172627023097)
                      ·
                        rfl

theorem cell23_7548389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7548389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548389 prefixEnd_7548389 := by exact prefixLift 7548389
  have htrace : WordTrace (prefixWord ++ tailWord_7548389) baseStart_7548389 baseEnd_7548389 := by
    simpa [prefixWord, tailWord_7548389, baseEnd_7548389] using wordTrace_append hprefix tailTrace_7548389
  have hstable : (prefixWord ++ tailWord_7548389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548389).length < 2 ^ (prefixWord ++ tailWord_7548389).sum := by decide
  have hdescent : baseEnd_7548389 < baseStart_7548389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548425 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 5, 5]
def baseStart_7548425 : Nat := 118140960795 + 7548425 * 2 ^ 59
def prefixEnd_7548425 : Nat := 4983230072969 + 3 ^ 40 * 7548425 * 2
def baseEnd_7548425 : Nat := 1291990069804911495390977

theorem tailTrace_7548425 : CollatzResearch.WordTrace tailWord_7548425 prefixEnd_7548425 1291990069804911495390977 := by
  unfold tailWord_7548425
  simp only [CollatzResearch.WordTrace]
  refine ⟨275313677678352868199174729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183542451785568578799449819 275313677678352868199174729)
  ·
    refine ⟨206485258258764651149381047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275313677678352868199174729 206485258258764651149381047)
    ·
      refine ⟨309727887388146976724071571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206485258258764651149381047 309727887388146976724071571)
      ·
        refine ⟨464591831082220465086107357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309727887388146976724071571 464591831082220465086107357)
        ·
          refine ⟨174221936655832674407290259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464591831082220465086107357 174221936655832674407290259)
          ·
            refine ⟨261332904983749011610935389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174221936655832674407290259 261332904983749011610935389)
            ·
              refine ⟨97999839368905879354100771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261332904983749011610935389 97999839368905879354100771)
              ·
                refine ⟨146999759053358819031151157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97999839368905879354100771 146999759053358819031151157)
                ·
                  refine ⟨13781227411252389284170421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146999759053358819031151157 13781227411252389284170421)
                  ·
                    refine ⟨1291990069804911495390977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13781227411252389284170421 1291990069804911495390977)
                    ·
                      rfl

theorem cell23_7548425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_7548425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548425 prefixEnd_7548425 := by exact prefixLift 7548425
  have htrace : WordTrace (prefixWord ++ tailWord_7548425) baseStart_7548425 baseEnd_7548425 := by
    simpa [prefixWord, tailWord_7548425, baseEnd_7548425] using wordTrace_append hprefix tailTrace_7548425
  have hstable : (prefixWord ++ tailWord_7548425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548425).length < 2 ^ (prefixWord ++ tailWord_7548425).sum := by decide
  have hdescent : baseEnd_7548425 < baseStart_7548425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548442 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_7548442 : Nat := 118140960795 + 7548442 * 2 ^ 59
def prefixEnd_7548442 : Nat := 4983230072969 + 3 ^ 40 * 7548442 * 2
def baseEnd_7548442 : Nat := 1291992979528620306553451

theorem tailTrace_7548442 : CollatzResearch.WordTrace tailWord_7548442 prefixEnd_7548442 1291992979528620306553451 := by
  unfold tailWord_7548442
  simp only [CollatzResearch.WordTrace]
  refine ⟨68828574429822820025635895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183542865146194186735029053 68828574429822820025635895)
  ·
    refine ⟨103242861644734230038453843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68828574429822820025635895 103242861644734230038453843)
    ·
      refine ⟨154864292467101345057680765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103242861644734230038453843 154864292467101345057680765)
      ·
        refine ⟨58074109675163004396630287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154864292467101345057680765 58074109675163004396630287)
        ·
          refine ⟨87111164512744506594945431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58074109675163004396630287 87111164512744506594945431)
          ·
            refine ⟨130666746769116759892418147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87111164512744506594945431 130666746769116759892418147)
            ·
              refine ⟨196000120153675139838627221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130666746769116759892418147 196000120153675139838627221)
              ·
                refine ⟨9187505632203522179935651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196000120153675139838627221 9187505632203522179935651)
                ·
                  refine ⟨13781258448305283269903477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9187505632203522179935651 13781258448305283269903477)
                  ·
                    refine ⟨1291992979528620306553451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13781258448305283269903477 1291992979528620306553451)
                    ·
                      rfl

theorem cell23_7548442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_7548442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548442 prefixEnd_7548442 := by exact prefixLift 7548442
  have htrace : WordTrace (prefixWord ++ tailWord_7548442) baseStart_7548442 baseEnd_7548442 := by
    simpa [prefixWord, tailWord_7548442, baseEnd_7548442] using wordTrace_append hprefix tailTrace_7548442
  have hstable : (prefixWord ++ tailWord_7548442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548442).length < 2 ^ (prefixWord ++ tailWord_7548442).sum := by decide
  have hdescent : baseEnd_7548442 < baseStart_7548442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548449 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_7548449 : Nat := 118140960795 + 7548449 * 2 ^ 59
def prefixEnd_7548449 : Nat := 4983230072969 + 3 ^ 40 * 7548449 * 2
def baseEnd_7548449 : Nat := 3875982532950442392272821

theorem tailTrace_7548449 : CollatzResearch.WordTrace tailWord_7548449 prefixEnd_7548449 3875982532950442392272821 := by
  unfold tailWord_7548449
  simp only [CollatzResearch.WordTrace]
  refine ⟨275314553030265920298048401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183543035353510613532032267 275314553030265920298048401)
  ·
    refine ⟨206485914772699440223536301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275314553030265920298048401 206485914772699440223536301)
    ·
      refine ⟨77432218039762290083826113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206485914772699440223536301 77432218039762290083826113)
      ·
        refine ⟨58074163529821717562869585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77432218039762290083826113 58074163529821717562869585)
        ·
          refine ⟨43555622647366288172152189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58074163529821717562869585 43555622647366288172152189)
          ·
            refine ⟨16333358492762358064557071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43555622647366288172152189 16333358492762358064557071)
            ·
              refine ⟨24500037739143537096835607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16333358492762358064557071 24500037739143537096835607)
              ·
                refine ⟨36750056608715305645253411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24500037739143537096835607 36750056608715305645253411)
                ·
                  refine ⟨55125084913072958467880117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36750056608715305645253411 55125084913072958467880117)
                  ·
                    refine ⟨5167976710600589856363761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55125084913072958467880117 5167976710600589856363761)
                    ·
                      refine ⟨3875982532950442392272821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5167976710600589856363761 3875982532950442392272821)
                      ·
                        rfl

theorem cell23_7548449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_7548449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548449 prefixEnd_7548449 := by exact prefixLift 7548449
  have htrace : WordTrace (prefixWord ++ tailWord_7548449) baseStart_7548449 baseEnd_7548449 := by
    simpa [prefixWord, tailWord_7548449, baseEnd_7548449] using wordTrace_append hprefix tailTrace_7548449
  have hstable : (prefixWord ++ tailWord_7548449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548449).length < 2 ^ (prefixWord ++ tailWord_7548449).sum := by decide
  have hdescent : baseEnd_7548449 < baseStart_7548449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548485 : List Nat := [1, 3, 1, 1, 1, 4, 2, 10]
def baseStart_7548485 : Nat := 118140960795 + 7548485 * 2 ^ 59
def prefixEnd_7548485 : Nat := 4983230072969 + 3 ^ 40 * 7548485 * 2
def baseEnd_7548485 : Nat := 143555593268666824126765

theorem tailTrace_7548485 : CollatzResearch.WordTrace tailWord_7548485 prefixEnd_7548485 143555593268666824126765 := by
  unfold tailWord_7548485
  simp only [CollatzResearch.WordTrace]
  refine ⟨275315866058135498446358909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183543910705423665630905939 275315866058135498446358909)
  ·
    refine ⟨103243449771800811917384591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275315866058135498446358909 103243449771800811917384591)
    ·
      refine ⟨154865174657701217876076887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103243449771800811917384591 154865174657701217876076887)
      ·
        refine ⟨232297761986551826814115331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154865174657701217876076887 232297761986551826814115331)
        ·
          refine ⟨348446642979827740221172997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232297761986551826814115331 348446642979827740221172997)
          ·
            refine ⟨65333745558717701291469937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348446642979827740221172997 65333745558717701291469937)
            ·
              refine ⟨49000309169038275968602453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65333745558717701291469937 49000309169038275968602453)
              ·
                refine ⟨143555593268666824126765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49000309169038275968602453 143555593268666824126765)
                ·
                  rfl

theorem cell23_7548485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 10].length) (baseStart_7548485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548485 prefixEnd_7548485 := by exact prefixLift 7548485
  have htrace : WordTrace (prefixWord ++ tailWord_7548485) baseStart_7548485 baseEnd_7548485 := by
    simpa [prefixWord, tailWord_7548485, baseEnd_7548485] using wordTrace_append hprefix tailTrace_7548485
  have hstable : (prefixWord ++ tailWord_7548485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548485).length < 2 ^ (prefixWord ++ tailWord_7548485).sum := by decide
  have hdescent : baseEnd_7548485 < baseStart_7548485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548492 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_7548492 : Nat := 118140960795 + 7548492 * 2 ^ 59
def prefixEnd_7548492 : Nat := 4983230072969 + 3 ^ 40 * 7548492 * 2
def baseEnd_7548492 : Nat := 3876004612618585724035123

theorem tailTrace_7548492 : CollatzResearch.WordTrace tailWord_7548492 prefixEnd_7548492 3876004612618585724035123 := by
  unfold tailWord_7548492
  simp only [CollatzResearch.WordTrace]
  refine ⟨137658060684555069320931865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183544080912740092427909153 137658060684555069320931865)
  ·
    refine ⟨103243545513416301990698899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137658060684555069320931865 103243545513416301990698899)
    ·
      refine ⟨154865318270124452986048349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103243545513416301990698899 154865318270124452986048349)
      ·
        refine ⟨58074494351296669869768131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154865318270124452986048349 58074494351296669869768131)
        ·
          refine ⟨87111741526945004804652197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58074494351296669869768131 87111741526945004804652197)
          ·
            refine ⟨16333451536302188400872287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87111741526945004804652197 16333451536302188400872287)
            ·
              refine ⟨24500177304453282601308431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16333451536302188400872287 24500177304453282601308431)
              ·
                refine ⟨36750265956679923901962647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24500177304453282601308431 36750265956679923901962647)
                ·
                  refine ⟨55125398935019885852943971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36750265956679923901962647 55125398935019885852943971)
                  ·
                    refine ⟨82688098402529828779415957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55125398935019885852943971 82688098402529828779415957)
                    ·
                      refine ⟨3876004612618585724035123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82688098402529828779415957 3876004612618585724035123)
                      ·
                        rfl

theorem cell23_7548492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_7548492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548492 prefixEnd_7548492 := by exact prefixLift 7548492
  have htrace : WordTrace (prefixWord ++ tailWord_7548492) baseStart_7548492 baseEnd_7548492 := by
    simpa [prefixWord, tailWord_7548492, baseEnd_7548492] using wordTrace_append hprefix tailTrace_7548492
  have hstable : (prefixWord ++ tailWord_7548492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548492).length < 2 ^ (prefixWord ++ tailWord_7548492).sum := by decide
  have hdescent : baseEnd_7548492 < baseStart_7548492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548505 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_7548505 : Nat := 118140960795 + 7548505 * 2 ^ 59
def prefixEnd_7548505 : Nat := 4983230072969 + 3 ^ 40 * 7548505 * 2
def baseEnd_7548505 : Nat := 3876011287867094173172563

theorem tailTrace_7548505 : CollatzResearch.WordTrace tailWord_7548505 prefixEnd_7548505 3876011287867094173172563 := by
  unfold tailWord_7548505
  simp only [CollatzResearch.WordTrace]
  refine ⟨275316595518063041862086969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183544397012042027908057979 275316595518063041862086969)
  ·
    refine ⟨206487446638547281396565227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275316595518063041862086969 206487446638547281396565227)
    ·
      refine ⟨309731169957820922094847841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206487446638547281396565227 309731169957820922094847841)
      ·
        refine ⟨232298377468365691571135881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309731169957820922094847841 232298377468365691571135881)
        ·
          refine ⟨174223783101274268678351911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232298377468365691571135881 174223783101274268678351911)
          ·
            refine ⟨261335674651911403017527867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174223783101274268678351911 261335674651911403017527867)
            ·
              refine ⟨392003511977867104526291801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261335674651911403017527867 392003511977867104526291801)
              ·
                refine ⟨294002633983400328394718851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392003511977867104526291801 294002633983400328394718851)
                ·
                  refine ⟨441003950975100492592078277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294002633983400328394718851 441003950975100492592078277)
                  ·
                    refine ⟨82688240807831342361014677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441003950975100492592078277 82688240807831342361014677)
                    ·
                      refine ⟨3876011287867094173172563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82688240807831342361014677 3876011287867094173172563)
                      ·
                        rfl

theorem cell23_7548505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_7548505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548505 prefixEnd_7548505 := by exact prefixLift 7548505
  have htrace : WordTrace (prefixWord ++ tailWord_7548505) baseStart_7548505 baseEnd_7548505 := by
    simpa [prefixWord, tailWord_7548505, baseEnd_7548505] using wordTrace_append hprefix tailTrace_7548505
  have hstable : (prefixWord ++ tailWord_7548505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548505).length < 2 ^ (prefixWord ++ tailWord_7548505).sum := by decide
  have hdescent : baseEnd_7548505 < baseStart_7548505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548512 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 3]
def baseStart_7548512 : Nat := 118140960795 + 7548512 * 2 ^ 59
def prefixEnd_7548512 : Nat := 4983230072969 + 3 ^ 40 * 7548512 * 2
def baseEnd_7548512 : Nat := 3876014882231675645785031

theorem tailTrace_7548512 : CollatzResearch.WordTrace tailWord_7548512 prefixEnd_7548512 3876014882231675645785031 := by
  unfold tailWord_7548512
  simp only [CollatzResearch.WordTrace]
  refine ⟨137658425414518841028795895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183544567219358454705061193 137658425414518841028795895)
  ·
    refine ⟨206487638121778261543193843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137658425414518841028795895 206487638121778261543193843)
    ·
      refine ⟨309731457182667392314790765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206487638121778261543193843 309731457182667392314790765)
      ·
        refine ⟨116149296443500272118046537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309731457182667392314790765 116149296443500272118046537)
        ·
          refine ⟨87111972332625204088534903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116149296443500272118046537 87111972332625204088534903)
          ·
            refine ⟨130667958498937806132802355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87111972332625204088534903 130667958498937806132802355)
            ·
              refine ⟨196001937748406709199203533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130667958498937806132802355 196001937748406709199203533)
              ·
                refine ⟨73500726655652515949701325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196001937748406709199203533 73500726655652515949701325)
                ·
                  refine ⟨27562772495869693481137997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73500726655652515949701325 27562772495869693481137997)
                  ·
                    refine ⟨10336039685951135055426749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27562772495869693481137997 10336039685951135055426749)
                    ·
                      refine ⟨3876014882231675645785031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10336039685951135055426749 3876014882231675645785031)
                      ·
                        rfl

theorem cell23_7548512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_7548512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548512 prefixEnd_7548512 := by exact prefixLift 7548512
  have htrace : WordTrace (prefixWord ++ tailWord_7548512) baseStart_7548512 baseEnd_7548512 := by
    simpa [prefixWord, tailWord_7548512, baseEnd_7548512] using wordTrace_append hprefix tailTrace_7548512
  have hstable : (prefixWord ++ tailWord_7548512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548512).length < 2 ^ (prefixWord ++ tailWord_7548512).sum := by decide
  have hdescent : baseEnd_7548512 < baseStart_7548512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548539 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 3, 3, 2]
def baseStart_7548539 : Nat := 118140960795 + 7548539 * 2 ^ 59
def prefixEnd_7548539 : Nat := 4983230072969 + 3 ^ 40 * 7548539 * 2
def baseEnd_7548539 : Nat := 3876028746209347040147407

theorem tailTrace_7548539 : CollatzResearch.WordTrace tailWord_7548539 prefixEnd_7548539 3876028746209347040147407 := by
  unfold tailWord_7548539
  simp only [CollatzResearch.WordTrace]
  refine ⟨275317835599939865668824671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183545223733293243779216447 275317835599939865668824671)
  ·
    refine ⟨412976753399909798503237007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275317835599939865668824671 412976753399909798503237007)
    ·
      refine ⟨619465130099864697754855511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412976753399909798503237007 619465130099864697754855511)
      ·
        refine ⟨929197695149797046632283267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619465130099864697754855511 929197695149797046632283267)
        ·
          refine ⟨1393796542724695569948424901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929197695149797046632283267 1393796542724695569948424901)
          ·
            refine ⟨261336851760880419365329669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1393796542724695569948424901 261336851760880419365329669)
            ·
              refine ⟨49000659705165078630999313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261336851760880419365329669 49000659705165078630999313)
              ·
                refine ⟨36750494778873808973249485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49000659705165078630999313 36750494778873808973249485)
                ·
                  refine ⟨13781435542077678364968557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36750494778873808973249485 13781435542077678364968557)
                  ·
                    refine ⟨5168038328279129386863209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13781435542077678364968557 5168038328279129386863209)
                    ·
                      refine ⟨3876028746209347040147407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168038328279129386863209 3876028746209347040147407)
                      ·
                        rfl

theorem cell23_7548539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 3, 2].length) (baseStart_7548539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548539 prefixEnd_7548539 := by exact prefixLift 7548539
  have htrace : WordTrace (prefixWord ++ tailWord_7548539) baseStart_7548539 baseEnd_7548539 := by
    simpa [prefixWord, tailWord_7548539, baseEnd_7548539] using wordTrace_append hprefix tailTrace_7548539
  have hstable : (prefixWord ++ tailWord_7548539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548539).length < 2 ^ (prefixWord ++ tailWord_7548539).sum := by decide
  have hdescent : baseEnd_7548539 < baseStart_7548539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548589 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_7548589 : Nat := 118140960795 + 7548589 * 2 ^ 59
def prefixEnd_7548589 : Nat := 4983230072969 + 3 ^ 40 * 7548589 * 2
def baseEnd_7548589 : Nat := 3876054420242071844522177

theorem tailTrace_7548589 : CollatzResearch.WordTrace tailWord_7548589 prefixEnd_7548589 3876054420242071844522177 := by
  unfold tailWord_7548589
  simp only [CollatzResearch.WordTrace]
  refine ⟨275319659249758724208144821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183546439499839149472096547 275319659249758724208144821)
  ·
    refine ⟨25811218054664880394513577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275319659249758724208144821 25811218054664880394513577)
    ·
      refine ⟨19358413540998660295885183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25811218054664880394513577 19358413540998660295885183)
      ·
        refine ⟨29037620311497990443827775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19358413540998660295885183 29037620311497990443827775)
        ·
          refine ⟨43556430467246985665741663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29037620311497990443827775 43556430467246985665741663)
          ·
            refine ⟨65334645700870478498612495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43556430467246985665741663 65334645700870478498612495)
            ·
              refine ⟨98001968551305717747918743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65334645700870478498612495 98001968551305717747918743)
              ·
                refine ⟨147002952826958576621878115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98001968551305717747918743 147002952826958576621878115)
                ·
                  refine ⟨220504429240437864932817173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147002952826958576621878115 220504429240437864932817173)
                  ·
                    refine ⟨10336145120645524918725805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 220504429240437864932817173 10336145120645524918725805)
                    ·
                      refine ⟨3876054420242071844522177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10336145120645524918725805 3876054420242071844522177)
                      ·
                        rfl

theorem cell23_7548589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_7548589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548589 prefixEnd_7548589 := by exact prefixLift 7548589
  have htrace : WordTrace (prefixWord ++ tailWord_7548589) baseStart_7548589 baseEnd_7548589 := by
    simpa [prefixWord, tailWord_7548589, baseEnd_7548589] using wordTrace_append hprefix tailTrace_7548589
  have hstable : (prefixWord ++ tailWord_7548589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548589).length < 2 ^ (prefixWord ++ tailWord_7548589).sum := by decide
  have hdescent : baseEnd_7548589 < baseStart_7548589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548599 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_7548599 : Nat := 118140960795 + 7548599 * 2 ^ 59
def prefixEnd_7548599 : Nat := 4983230072969 + 3 ^ 40 * 7548599 * 2
def baseEnd_7548599 : Nat := 3876059555048616805397131

theorem tailTrace_7548599 : CollatzResearch.WordTrace tailWord_7548599 prefixEnd_7548599 3876059555048616805397131 := by
  unfold tailWord_7548599
  simp only [CollatzResearch.WordTrace]
  refine ⟨275320023979722495916008851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183546682653148330610672567 275320023979722495916008851)
  ·
    refine ⟨412980035969583743874013277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275320023979722495916008851 412980035969583743874013277)
    ·
      refine ⟨154867513488593903952754979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412980035969583743874013277 154867513488593903952754979)
      ·
        refine ⟨232301270232890855929132469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154867513488593903952754979 232301270232890855929132469)
        ·
          refine ⟨21778244084333517743356169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232301270232890855929132469 21778244084333517743356169)
          ·
            refine ⟨16333683063250138307517127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21778244084333517743356169 16333683063250138307517127)
            ·
              refine ⟨24500524594875207461275691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16333683063250138307517127 24500524594875207461275691)
              ·
                refine ⟨36750786892312811191913537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24500524594875207461275691 36750786892312811191913537)
                ·
                  refine ⟨27563090169234608393935153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36750786892312811191913537 27563090169234608393935153)
                  ·
                    refine ⟨20672317626925956295451365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27563090169234608393935153 20672317626925956295451365)
                    ·
                      refine ⟨3876059555048616805397131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20672317626925956295451365 3876059555048616805397131)
                      ·
                        rfl

theorem cell23_7548599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_7548599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548599 prefixEnd_7548599 := by exact prefixLift 7548599
  have htrace : WordTrace (prefixWord ++ tailWord_7548599) baseStart_7548599 baseEnd_7548599 := by
    simpa [prefixWord, tailWord_7548599, baseEnd_7548599] using wordTrace_append hprefix tailTrace_7548599
  have hstable : (prefixWord ++ tailWord_7548599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548599).length < 2 ^ (prefixWord ++ tailWord_7548599).sum := by decide
  have hdescent : baseEnd_7548599 < baseStart_7548599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548626 : List Nat := [3, 2, 2, 2, 2, 1, 1, 5, 5]
def baseStart_7548626 : Nat := 118140960795 + 7548626 * 2 ^ 59
def prefixEnd_7548626 : Nat := 4983230072969 + 3 ^ 40 * 7548626 * 2
def baseEnd_7548626 : Nat := 430674824336254244417723

theorem tailTrace_7548626 : CollatzResearch.WordTrace tailWord_7548626 prefixEnd_7548626 430674824336254244417723 := by
  unfold tailWord_7548626
  simp only [CollatzResearch.WordTrace]
  refine ⟨68830252187656169881810433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183547339167083119684827821 68830252187656169881810433)
  ·
    refine ⟨51622689140742127411357825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68830252187656169881810433 51622689140742127411357825)
    ·
      refine ⟨38717016855556595558518369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51622689140742127411357825 38717016855556595558518369)
      ·
        refine ⟨29037762641667446668888777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38717016855556595558518369 29037762641667446668888777)
        ·
          refine ⟨21778321981250585001666583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29037762641667446668888777 21778321981250585001666583)
          ·
            refine ⟨32667482971875877502499875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21778321981250585001666583 32667482971875877502499875)
            ·
              refine ⟨49001224457813816253749813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32667482971875877502499875 49001224457813816253749813)
              ·
                refine ⟨4593864792920045273789045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49001224457813816253749813 4593864792920045273789045)
                ·
                  refine ⟨430674824336254244417723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4593864792920045273789045 430674824336254244417723)
                  ·
                    rfl

theorem cell23_7548626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_7548626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548626 prefixEnd_7548626 := by exact prefixLift 7548626
  have htrace : WordTrace (prefixWord ++ tailWord_7548626) baseStart_7548626 baseEnd_7548626 := by
    simpa [prefixWord, tailWord_7548626, baseEnd_7548626] using wordTrace_append hprefix tailTrace_7548626
  have hstable : (prefixWord ++ tailWord_7548626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548626).length < 2 ^ (prefixWord ++ tailWord_7548626).sum := by decide
  have hdescent : baseEnd_7548626 < baseStart_7548626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548669 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_7548669 : Nat := 118140960795 + 7548669 * 2 ^ 59
def prefixEnd_7548669 : Nat := 4983230072969 + 3 ^ 40 * 7548669 * 2
def baseEnd_7548669 : Nat := 1292031832898143843840603

theorem tailTrace_7548669 : CollatzResearch.WordTrace tailWord_7548669 prefixEnd_7548669 1292031832898143843840603 := by
  unfold tailWord_7548669
  simp only [CollatzResearch.WordTrace]
  refine ⟨275322577089468897871057061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183548384726312598580704707 275322577089468897871057061)
  ·
    refine ⟨51622983204275418350823199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275322577089468897871057061 51622983204275418350823199)
    ·
      refine ⟨77434474806413127526234799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51622983204275418350823199 77434474806413127526234799)
      ·
        refine ⟨116151712209619691289352199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77434474806413127526234799 116151712209619691289352199)
        ·
          refine ⟨174227568314429536934028299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116151712209619691289352199 174227568314429536934028299)
          ·
            refine ⟨261341352471644305401042449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174227568314429536934028299 261341352471644305401042449)
            ·
              refine ⟨196006014353733229050781837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261341352471644305401042449 196006014353733229050781837)
              ·
                refine ⟨73502255382649960894043189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196006014353733229050781837 73502255382649960894043189)
                ·
                  refine ⟨6890836442123433833816549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73502255382649960894043189 6890836442123433833816549)
                  ·
                    refine ⟨1292031832898143843840603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6890836442123433833816549 1292031832898143843840603)
                    ·
                      rfl

theorem cell23_7548669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_7548669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548669 prefixEnd_7548669 := by exact prefixLift 7548669
  have htrace : WordTrace (prefixWord ++ tailWord_7548669) baseStart_7548669 baseEnd_7548669 := by
    simpa [prefixWord, tailWord_7548669, baseEnd_7548669] using wordTrace_append hprefix tailTrace_7548669
  have hstable : (prefixWord ++ tailWord_7548669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548669).length < 2 ^ (prefixWord ++ tailWord_7548669).sum := by decide
  have hdescent : baseEnd_7548669 < baseStart_7548669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548672 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_7548672 : Nat := 118140960795 + 7548672 * 2 ^ 59
def prefixEnd_7548672 : Nat := 4983230072969 + 3 ^ 40 * 7548672 * 2
def baseEnd_7548672 : Nat := 3876097039136395019784295

theorem tailTrace_7548672 : CollatzResearch.WordTrace tailWord_7548672 prefixEnd_7548672 3876097039136395019784295 := by
  unfold tailWord_7548672
  simp only [CollatzResearch.WordTrace]
  refine ⟨137661343254229014691708135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183548457672305352922277513 137661343254229014691708135)
  ·
    refine ⟨206492014881343522037562203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137661343254229014691708135 206492014881343522037562203)
    ·
      refine ⟨309738022322015283056343305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206492014881343522037562203 309738022322015283056343305)
      ·
        refine ⟨232303516741511462292257479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309738022322015283056343305 232303516741511462292257479)
        ·
          refine ⟨348455275112267193438386219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232303516741511462292257479 348455275112267193438386219)
          ·
            refine ⟨522682912668400790157579329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348455275112267193438386219 522682912668400790157579329)
            ·
              refine ⟨392012184501300592618184497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522682912668400790157579329 392012184501300592618184497)
              ·
                refine ⟨294009138375975444463638373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392012184501300592618184497 294009138375975444463638373)
                ·
                  refine ⟨55126713445495395836932195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294009138375975444463638373 55126713445495395836932195)
                  ·
                    refine ⟨82690070168243093755398293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55126713445495395836932195 82690070168243093755398293)
                    ·
                      refine ⟨3876097039136395019784295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82690070168243093755398293 3876097039136395019784295)
                      ·
                        rfl

theorem cell23_7548672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_7548672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548672 prefixEnd_7548672 := by exact prefixLift 7548672
  have htrace : WordTrace (prefixWord ++ tailWord_7548672) baseStart_7548672 baseEnd_7548672 := by
    simpa [prefixWord, tailWord_7548672, baseEnd_7548672] using wordTrace_append hprefix tailTrace_7548672
  have hstable : (prefixWord ++ tailWord_7548672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548672).length < 2 ^ (prefixWord ++ tailWord_7548672).sum := by decide
  have hdescent : baseEnd_7548672 < baseStart_7548672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548716 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 6]
def baseStart_7548716 : Nat := 118140960795 + 7548716 * 2 ^ 59
def prefixEnd_7548716 : Nat := 4983230072969 + 3 ^ 40 * 7548716 * 2
def baseEnd_7548716 : Nat := 430679959142799205292677

theorem tailTrace_7548716 : CollatzResearch.WordTrace tailWord_7548716 prefixEnd_7548716 430679959142799205292677 := by
  unfold tailWord_7548716
  simp only [CollatzResearch.WordTrace]
  refine ⟨137662145660149312449009001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183549527546865749932012001 137662145660149312449009001)
  ·
    refine ⟨103246609245111984336756751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137662145660149312449009001 103246609245111984336756751)
    ·
      refine ⟨154869913867667976505135127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103246609245111984336756751 154869913867667976505135127)
      ·
        refine ⟨232304870801501964757702691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154869913867667976505135127 232304870801501964757702691)
        ·
          refine ⟨348457306202252947136554037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232304870801501964757702691 348457306202252947136554037)
          ·
            refine ⟨32667872456461213794051941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348457306202252947136554037 32667872456461213794051941)
            ·
              refine ⟨6125226085586477586384739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32667872456461213794051941 6125226085586477586384739)
              ·
                refine ⟨9187839128379716379577109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125226085586477586384739 9187839128379716379577109)
                ·
                  refine ⟨430679959142799205292677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9187839128379716379577109 430679959142799205292677)
                  ·
                    rfl

theorem cell23_7548716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_7548716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548716 prefixEnd_7548716 := by exact prefixLift 7548716
  have htrace : WordTrace (prefixWord ++ tailWord_7548716) baseStart_7548716 baseEnd_7548716 := by
    simpa [prefixWord, tailWord_7548716, baseEnd_7548716] using wordTrace_append hprefix tailTrace_7548716
  have hstable : (prefixWord ++ tailWord_7548716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548716).length < 2 ^ (prefixWord ++ tailWord_7548716).sum := by decide
  have hdescent : baseEnd_7548716 < baseStart_7548716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548753 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 2, 3, 2]
def baseStart_7548753 : Nat := 118140960795 + 7548753 * 2 ^ 59
def prefixEnd_7548753 : Nat := 4983230072969 + 3 ^ 40 * 7548753 * 2
def baseEnd_7548753 : Nat := 3876138631069409202871423

theorem tailTrace_7548753 : CollatzResearch.WordTrace tailWord_7548753 prefixEnd_7548753 3876138631069409202871423 := by
  unfold tailWord_7548753
  simp only [CollatzResearch.WordTrace]
  refine ⟨275325640821164580217114913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183550427214109720144743275 275325640821164580217114913)
  ·
    refine ⟨206494230615873435162836185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275325640821164580217114913 206494230615873435162836185)
    ·
      refine ⟨154870672961905076372127139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206494230615873435162836185 154870672961905076372127139)
      ·
        refine ⟨232306009442857614558190709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154870672961905076372127139 232306009442857614558190709)
        ·
          refine ⟨21778688385267901364830379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232306009442857614558190709 21778688385267901364830379)
          ·
            refine ⟨32668032577901852047245569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21778688385267901364830379 32668032577901852047245569)
            ·
              refine ⟨24501024433426389035434177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32668032577901852047245569 24501024433426389035434177)
              ·
                refine ⟨18375768325069791776575633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24501024433426389035434177 18375768325069791776575633)
                ·
                  refine ⟨13781826243802343832431725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18375768325069791776575633 13781826243802343832431725)
                  ·
                    refine ⟨5168184841425878937161897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13781826243802343832431725 5168184841425878937161897)
                    ·
                      refine ⟨3876138631069409202871423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168184841425878937161897 3876138631069409202871423)
                      ·
                        rfl

theorem cell23_7548753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_7548753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548753 prefixEnd_7548753 := by exact prefixLift 7548753
  have htrace : WordTrace (prefixWord ++ tailWord_7548753) baseStart_7548753 baseEnd_7548753 := by
    simpa [prefixWord, tailWord_7548753, baseEnd_7548753] using wordTrace_append hprefix tailTrace_7548753
  have hstable : (prefixWord ++ tailWord_7548753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548753).length < 2 ^ (prefixWord ++ tailWord_7548753).sum := by decide
  have hdescent : baseEnd_7548753 < baseStart_7548753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548769 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_7548769 : Nat := 118140960795 + 7548769 * 2 ^ 59
def prefixEnd_7548769 : Nat := 4983230072969 + 3 ^ 40 * 7548769 * 2
def baseEnd_7548769 : Nat := 3876146846759881140271349

theorem tailTrace_7548769 : CollatzResearch.WordTrace tailWord_7548769 prefixEnd_7548769 3876146846759881140271349 := by
  unfold tailWord_7548769
  simp only [CollatzResearch.WordTrace]
  refine ⟨275326224389106614949697361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183550816259404409966464907 275326224389106614949697361)
  ·
    refine ⟨206494668291829961212273021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275326224389106614949697361 206494668291829961212273021)
    ·
      refine ⟨77435500609436235454602383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206494668291829961212273021 77435500609436235454602383)
      ·
        refine ⟨116153250914154353181903575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77435500609436235454602383 116153250914154353181903575)
        ·
          refine ⟨174229876371231529772855363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116153250914154353181903575 174229876371231529772855363)
          ·
            refine ⟨261344814556847294659283045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174229876371231529772855363 261344814556847294659283045)
            ·
              refine ⟨49002152729408867748615571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261344814556847294659283045 49002152729408867748615571)
              ·
                refine ⟨73503229094113301622923357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49002152729408867748615571 73503229094113301622923357)
                ·
                  refine ⟨27563710910292488108596259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73503229094113301622923357 27563710910292488108596259)
                  ·
                    refine ⟨41345566365438732162894389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27563710910292488108596259 41345566365438732162894389)
                    ·
                      refine ⟨3876146846759881140271349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41345566365438732162894389 3876146846759881140271349)
                      ·
                        rfl

theorem cell23_7548769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_7548769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548769 prefixEnd_7548769 := by exact prefixLift 7548769
  have htrace : WordTrace (prefixWord ++ tailWord_7548769) baseStart_7548769 baseEnd_7548769 := by
    simpa [prefixWord, tailWord_7548769, baseEnd_7548769] using wordTrace_append hprefix tailTrace_7548769
  have hstable : (prefixWord ++ tailWord_7548769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548769).length < 2 ^ (prefixWord ++ tailWord_7548769).sum := by decide
  have hdescent : baseEnd_7548769 < baseStart_7548769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548776 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 1, 6]
def baseStart_7548776 : Nat := 118140960795 + 7548776 * 2 ^ 59
def prefixEnd_7548776 : Nat := 4983230072969 + 3 ^ 40 * 7548776 * 2
def baseEnd_7548776 : Nat := 1292050147041487537627939

theorem tailTrace_7548776 : CollatzResearch.WordTrace tailWord_7548776 prefixEnd_7548776 1292050147041487537627939 := by
  unfold tailWord_7548776
  simp only [CollatzResearch.WordTrace]
  refine ⟨137663239850040627572601091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183550986466720836763468121 137663239850040627572601091)
  ·
    refine ⟨206494859775060941358901637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137663239850040627572601091 206494859775060941358901637)
    ·
      refine ⟨38717786207823926504794057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206494859775060941358901637 38717786207823926504794057)
      ·
        refine ⟨29038339655867944878595543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38717786207823926504794057 29038339655867944878595543)
        ·
          refine ⟨43557509483801917317893315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29038339655867944878595543 43557509483801917317893315)
          ·
            refine ⟨65336264225702875976839973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43557509483801917317893315 65336264225702875976839973)
            ·
              refine ⟨12250549542319289245657495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65336264225702875976839973 12250549542319289245657495)
              ·
                refine ⟨18375824313478933868486243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12250549542319289245657495 18375824313478933868486243)
                ·
                  refine ⟨27563736470218400802729365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18375824313478933868486243 27563736470218400802729365)
                  ·
                    refine ⟨1292050147041487537627939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27563736470218400802729365 1292050147041487537627939)
                    ·
                      rfl

theorem cell23_7548776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_7548776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548776 prefixEnd_7548776 := by exact prefixLift 7548776
  have htrace : WordTrace (prefixWord ++ tailWord_7548776) baseStart_7548776 baseEnd_7548776 := by
    simpa [prefixWord, tailWord_7548776, baseEnd_7548776] using wordTrace_append hprefix tailTrace_7548776
  have hstable : (prefixWord ++ tailWord_7548776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548776).length < 2 ^ (prefixWord ++ tailWord_7548776).sum := by decide
  have hdescent : baseEnd_7548776 < baseStart_7548776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548803 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 3]
def baseStart_7548803 : Nat := 118140960795 + 7548803 * 2 ^ 59
def prefixEnd_7548803 : Nat := 4983230072969 + 3 ^ 40 * 7548803 * 2
def baseEnd_7548803 : Nat := 3876164305102134007246193

theorem tailTrace_7548803 : CollatzResearch.WordTrace tailWord_7548803 prefixEnd_7548803 3876164305102134007246193 := by
  unfold tailWord_7548803
  simp only [CollatzResearch.WordTrace]
  refine ⟨275327464470983438756435063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183551642980655625837623375 275327464470983438756435063)
  ·
    refine ⟨412991196706475158134652595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275327464470983438756435063 412991196706475158134652595)
    ·
      refine ⟨619486795059712737201978893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412991196706475158134652595 619486795059712737201978893)
      ·
        refine ⟨232307548147392276450742085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 619486795059712737201978893 232307548147392276450742085)
        ·
          refine ⟨43557665277636051834514141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232307548147392276450742085 43557665277636051834514141)
          ·
            refine ⟨16334124479113519437942803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43557665277636051834514141 16334124479113519437942803)
            ·
              refine ⟨24501186718670279156914205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16334124479113519437942803 24501186718670279156914205)
              ·
                refine ⟨9187945019501354683842827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24501186718670279156914205 9187945019501354683842827)
                ·
                  refine ⟨13781917529252032025764241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9187945019501354683842827 13781917529252032025764241)
                  ·
                    refine ⟨10336438146939024019323181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13781917529252032025764241 10336438146939024019323181)
                    ·
                      refine ⟨3876164305102134007246193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10336438146939024019323181 3876164305102134007246193)
                      ·
                        rfl

theorem cell23_7548803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_7548803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548803 prefixEnd_7548803 := by exact prefixLift 7548803
  have htrace : WordTrace (prefixWord ++ tailWord_7548803) baseStart_7548803 baseEnd_7548803 := by
    simpa [prefixWord, tailWord_7548803, baseEnd_7548803] using wordTrace_append hprefix tailTrace_7548803
  have hstable : (prefixWord ++ tailWord_7548803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548803).length < 2 ^ (prefixWord ++ tailWord_7548803).sum := by decide
  have hdescent : baseEnd_7548803 < baseStart_7548803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548830 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7548830 : Nat := 118140960795 + 7548830 * 2 ^ 59
def prefixEnd_7548830 : Nat := 4983230072969 + 3 ^ 40 * 7548830 * 2
def baseEnd_7548830 : Nat := 3876178169079805401608569

theorem tailTrace_7548830 : CollatzResearch.WordTrace tailWord_7548830 prefixEnd_7548830 3876178169079805401608569 := by
  unfold tailWord_7548830
  simp only [CollatzResearch.WordTrace]
  refine ⟨34416056155235702795958493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183552299494590414911778629 34416056155235702795958493)
  ·
    refine ⟨12906021058213388548484435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34416056155235702795958493 12906021058213388548484435)
    ·
      refine ⟨19359031587320082822726653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12906021058213388548484435 19359031587320082822726653)
      ·
        refine ⟨7259636845245031058522495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19359031587320082822726653 7259636845245031058522495)
        ·
          refine ⟨10889455267867546587783743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259636845245031058522495 10889455267867546587783743)
          ·
            refine ⟨16334182901801319881675615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10889455267867546587783743 16334182901801319881675615)
            ·
              refine ⟨24501274352701979822513423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16334182901801319881675615 24501274352701979822513423)
              ·
                refine ⟨36751911529052969733770135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24501274352701979822513423 36751911529052969733770135)
                ·
                  refine ⟨55127867293579454600655203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36751911529052969733770135 55127867293579454600655203)
                  ·
                    refine ⟨82691800940369181900982805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55127867293579454600655203 82691800940369181900982805)
                    ·
                      refine ⟨3876178169079805401608569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82691800940369181900982805 3876178169079805401608569)
                      ·
                        rfl

theorem cell23_7548830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7548830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548830 prefixEnd_7548830 := by exact prefixLift 7548830
  have htrace : WordTrace (prefixWord ++ tailWord_7548830) baseStart_7548830 baseEnd_7548830 := by
    simpa [prefixWord, tailWord_7548830, baseEnd_7548830] using wordTrace_append hprefix tailTrace_7548830
  have hstable : (prefixWord ++ tailWord_7548830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548830).length < 2 ^ (prefixWord ++ tailWord_7548830).sum := by decide
  have hdescent : baseEnd_7548830 < baseStart_7548830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548859 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 5]
def baseStart_7548859 : Nat := 118140960795 + 7548859 * 2 ^ 59
def prefixEnd_7548859 : Nat := 4983230072969 + 3 ^ 40 * 7548859 * 2
def baseEnd_7548859 : Nat := 3876193060018785788145935

theorem tailTrace_7548859 : CollatzResearch.WordTrace tailWord_7548859 prefixEnd_7548859 3876193060018785788145935 := by
  unfold tailWord_7548859
  simp only [CollatzResearch.WordTrace]
  refine ⟨275329506958780560320473631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183553004639187040213649087 275329506958780560320473631)
  ·
    refine ⟨412994260438170840480710447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275329506958780560320473631 412994260438170840480710447)
    ·
      refine ⟨619491390657256260721065671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412994260438170840480710447 619491390657256260721065671)
      ·
        refine ⟨929237085985884391081598507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619491390657256260721065671 929237085985884391081598507)
        ·
          refine ⟨1393855628978826586622397761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929237085985884391081598507 1393855628978826586622397761)
          ·
            refine ⟨1045391721734119939966798321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393855628978826586622397761 1045391721734119939966798321)
            ·
              refine ⟨784043791300589954975098741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045391721734119939966798321 784043791300589954975098741)
              ·
                refine ⟨73504105434430308278915507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 784043791300589954975098741 73504105434430308278915507)
                ·
                  refine ⟨110256158151645462418373261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73504105434430308278915507 110256158151645462418373261)
                  ·
                    refine ⟨41346059306867048406889973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110256158151645462418373261 41346059306867048406889973)
                    ·
                      refine ⟨3876193060018785788145935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41346059306867048406889973 3876193060018785788145935)
                      ·
                        rfl

theorem cell23_7548859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_7548859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548859 prefixEnd_7548859 := by exact prefixLift 7548859
  have htrace : WordTrace (prefixWord ++ tailWord_7548859) baseStart_7548859 baseEnd_7548859 := by
    simpa [prefixWord, tailWord_7548859, baseEnd_7548859] using wordTrace_append hprefix tailTrace_7548859
  have hstable : (prefixWord ++ tailWord_7548859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548859).length < 2 ^ (prefixWord ++ tailWord_7548859).sum := by decide
  have hdescent : baseEnd_7548859 < baseStart_7548859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548869 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_7548869 : Nat := 118140960795 + 7548869 * 2 ^ 59
def prefixEnd_7548869 : Nat := 4983230072969 + 3 ^ 40 * 7548869 * 2
def baseEnd_7548869 : Nat := 3876198194825330749020889

theorem tailTrace_7548869 : CollatzResearch.WordTrace tailWord_7548869 prefixEnd_7548869 3876198194825330749020889 := by
  unfold tailWord_7548869
  simp only [CollatzResearch.WordTrace]
  refine ⟨275329871688744332028337661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183553247792496221352225107 275329871688744332028337661)
  ·
    refine ⟨103248701883279124510626623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275329871688744332028337661 103248701883279124510626623)
    ·
      refine ⟨154873052824918686765939935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103248701883279124510626623 154873052824918686765939935)
      ·
        refine ⟨232309579237378030148909903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154873052824918686765939935 232309579237378030148909903)
        ·
          refine ⟨348464368856067045223364855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232309579237378030148909903 348464368856067045223364855)
          ·
            refine ⟨522696553284100567835047283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348464368856067045223364855 522696553284100567835047283)
            ·
              refine ⟨784044829926150851752570925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522696553284100567835047283 784044829926150851752570925)
              ·
                refine ⟨294016811222306569407214097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 784044829926150851752570925 294016811222306569407214097)
                ·
                  refine ⟨220512608416729927055410573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294016811222306569407214097 220512608416729927055410573)
                  ·
                    refine ⟨82692228156273722645778965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220512608416729927055410573 82692228156273722645778965)
                    ·
                      refine ⟨3876198194825330749020889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82692228156273722645778965 3876198194825330749020889)
                      ·
                        rfl

theorem cell23_7548869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_7548869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548869 prefixEnd_7548869 := by exact prefixLift 7548869
  have htrace : WordTrace (prefixWord ++ tailWord_7548869) baseStart_7548869 baseEnd_7548869 := by
    simpa [prefixWord, tailWord_7548869, baseEnd_7548869] using wordTrace_append hprefix tailTrace_7548869
  have hstable : (prefixWord ++ tailWord_7548869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548869).length < 2 ^ (prefixWord ++ tailWord_7548869).sum := by decide
  have hdescent : baseEnd_7548869 < baseStart_7548869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548933 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 2, 5, 2]
def baseStart_7548933 : Nat := 118140960795 + 7548933 * 2 ^ 59
def prefixEnd_7548933 : Nat := 4983230072969 + 3 ^ 40 * 7548933 * 2
def baseEnd_7548933 : Nat := 3876231057587218498620595

theorem tailTrace_7548933 : CollatzResearch.WordTrace tailWord_7548933 prefixEnd_7548933 3876231057587218498620595 := by
  unfold tailWord_7548933
  simp only [CollatzResearch.WordTrace]
  refine ⟨275332205960512470958667453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183554803973674980639111635 275332205960512470958667453)
  ·
    refine ⟨103249577235192176609500295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275332205960512470958667453 103249577235192176609500295)
    ·
      refine ⟨154874365852788264914250443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103249577235192176609500295 154874365852788264914250443)
      ·
        refine ⟨232311548779182397371375665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154874365852788264914250443 232311548779182397371375665)
        ·
          refine ⟨174233661584386798028531749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232311548779182397371375665 174233661584386798028531749)
          ·
            refine ⟨32668811547072524630349703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174233661584386798028531749 32668811547072524630349703)
            ·
              refine ⟨49003217320608786945524555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32668811547072524630349703 49003217320608786945524555)
              ·
                refine ⟨73504825980913180418286833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49003217320608786945524555 73504825980913180418286833)
                ·
                  refine ⟨55128619485684885313715125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73504825980913180418286833 55128619485684885313715125)
                  ·
                    refine ⟨5168308076782957998160793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55128619485684885313715125 5168308076782957998160793)
                    ·
                      refine ⟨3876231057587218498620595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168308076782957998160793 3876231057587218498620595)
                      ·
                        rfl

theorem cell23_7548933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_7548933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548933 prefixEnd_7548933 := by exact prefixLift 7548933
  have htrace : WordTrace (prefixWord ++ tailWord_7548933) baseStart_7548933 baseEnd_7548933 := by
    simpa [prefixWord, tailWord_7548933, baseEnd_7548933] using wordTrace_append hprefix tailTrace_7548933
  have hstable : (prefixWord ++ tailWord_7548933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548933).length < 2 ^ (prefixWord ++ tailWord_7548933).sum := by decide
  have hdescent : baseEnd_7548933 < baseStart_7548933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548934 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7548934 : Nat := 118140960795 + 7548934 * 2 ^ 59
def prefixEnd_7548934 : Nat := 4983230072969 + 3 ^ 40 * 7548934 * 2
def baseEnd_7548934 : Nat := 1292077190355957664902697

theorem tailTrace_7548934 : CollatzResearch.WordTrace tailWord_7548934 prefixEnd_7548934 1292077190355957664902697 := by
  unfold tailWord_7548934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8604132576047151504045433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 183554828289005898752969237 8604132576047151504045433)
  ·
    refine ⟨6453099432035363628034075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8604132576047151504045433 6453099432035363628034075)
    ·
      refine ⟨9679649148053045442051113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453099432035363628034075 9679649148053045442051113)
      ·
        refine ⟨7259736861039784081538335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9679649148053045442051113 7259736861039784081538335)
        ·
          refine ⟨10889605291559676122307503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259736861039784081538335 10889605291559676122307503)
          ·
            refine ⟨16334407937339514183461255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10889605291559676122307503 16334407937339514183461255)
            ·
              refine ⟨24501611906009271275191883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16334407937339514183461255 24501611906009271275191883)
              ·
                refine ⟨36752417859013906912787825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24501611906009271275191883 36752417859013906912787825)
                ·
                  refine ⟨27564313394260430184590869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36752417859013906912787825 27564313394260430184590869)
                  ·
                    refine ⟨1292077190355957664902697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27564313394260430184590869 1292077190355957664902697)
                    ·
                      rfl

theorem cell23_7548934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7548934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548934 prefixEnd_7548934 := by exact prefixLift 7548934
  have htrace : WordTrace (prefixWord ++ tailWord_7548934) baseStart_7548934 baseEnd_7548934 := by
    simpa [prefixWord, tailWord_7548934, baseEnd_7548934] using wordTrace_append hprefix tailTrace_7548934
  have hstable : (prefixWord ++ tailWord_7548934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548934).length < 2 ^ (prefixWord ++ tailWord_7548934).sum := by decide
  have hdescent : baseEnd_7548934 < baseStart_7548934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548936 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_7548936 : Nat := 118140960795 + 7548936 * 2 ^ 59
def prefixEnd_7548936 : Nat := 4983230072969 + 3 ^ 40 * 7548936 * 2
def baseEnd_7548936 : Nat := 3876232598029181986883081

theorem tailTrace_7548936 : CollatzResearch.WordTrace tailWord_7548936 prefixEnd_7548936 3876232598029181986883081 := by
  unfold tailWord_7548936
  simp only [CollatzResearch.WordTrace]
  refine ⟨137666157689750801235513331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183554876919667734980684441 137666157689750801235513331)
  ·
    refine ⟨206499236534626201853269997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137666157689750801235513331 206499236534626201853269997)
    ·
      refine ⟨77437213700484825694976249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206499236534626201853269997 77437213700484825694976249)
      ·
        refine ⟨58077910275363619271232187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77437213700484825694976249 58077910275363619271232187)
        ·
          refine ⟨87116865413045428906848281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58077910275363619271232187 87116865413045428906848281)
          ·
            refine ⟨65337649059784071680136211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87116865413045428906848281 65337649059784071680136211)
            ·
              refine ⟨98006473589676107520204317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65337649059784071680136211 98006473589676107520204317)
              ·
                refine ⟨36752427596128540320076619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98006473589676107520204317 36752427596128540320076619)
                ·
                  refine ⟨55128641394192810480114929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36752427596128540320076619 55128641394192810480114929)
                  ·
                    refine ⟨41346481045644607860086197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55128641394192810480114929 41346481045644607860086197)
                    ·
                      refine ⟨3876232598029181986883081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41346481045644607860086197 3876232598029181986883081)
                      ·
                        rfl

theorem cell23_7548936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_7548936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548936 prefixEnd_7548936 := by exact prefixLift 7548936
  have htrace : WordTrace (prefixWord ++ tailWord_7548936) baseStart_7548936 baseEnd_7548936 := by
    simpa [prefixWord, tailWord_7548936, baseEnd_7548936] using wordTrace_append hprefix tailTrace_7548936
  have hstable : (prefixWord ++ tailWord_7548936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548936).length < 2 ^ (prefixWord ++ tailWord_7548936).sum := by decide
  have hdescent : baseEnd_7548936 < baseStart_7548936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548941 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_7548941 : Nat := 118140960795 + 7548941 * 2 ^ 59
def prefixEnd_7548941 : Nat := 4983230072969 + 3 ^ 40 * 7548941 * 2
def baseEnd_7548941 : Nat := 3876235165432454467320559

theorem tailTrace_7548941 : CollatzResearch.WordTrace tailWord_7548941 prefixEnd_7548941 3876235165432454467320559 := by
  unfold tailWord_7548941
  simp only [CollatzResearch.WordTrace]
  refine ⟨275332497744483488324958677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183554998496322325549972451 275332497744483488324958677)
  ·
    refine ⟨6453105415886331757616219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 275332497744483488324958677 6453105415886331757616219)
    ·
      refine ⟨9679658123829497636424329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453105415886331757616219 9679658123829497636424329)
      ·
        refine ⟨7259743592872123227318247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9679658123829497636424329 7259743592872123227318247)
        ·
          refine ⟨10889615389308184840977371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259743592872123227318247 10889615389308184840977371)
          ·
            refine ⟨16334423083962277261466057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10889615389308184840977371 16334423083962277261466057)
            ·
              refine ⟨12250817312971707946099543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16334423083962277261466057 12250817312971707946099543)
              ·
                refine ⟨18376225969457561919149315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12250817312971707946099543 18376225969457561919149315)
                ·
                  refine ⟨27564338954186342878723973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18376225969457561919149315 27564338954186342878723973)
                  ·
                    refine ⟨5168313553909939289760745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27564338954186342878723973 5168313553909939289760745)
                    ·
                      refine ⟨3876235165432454467320559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168313553909939289760745 3876235165432454467320559)
                      ·
                        rfl

theorem cell23_7548941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_7548941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548941 prefixEnd_7548941 := by exact prefixLift 7548941
  have htrace : WordTrace (prefixWord ++ tailWord_7548941) baseStart_7548941 baseEnd_7548941 := by
    simpa [prefixWord, tailWord_7548941, baseEnd_7548941] using wordTrace_append hprefix tailTrace_7548941
  have hstable : (prefixWord ++ tailWord_7548941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548941).length < 2 ^ (prefixWord ++ tailWord_7548941).sum := by decide
  have hdescent : baseEnd_7548941 < baseStart_7548941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548963 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 1, 6, 2]
def baseStart_7548963 : Nat := 118140960795 + 7548963 * 2 ^ 59
def prefixEnd_7548963 : Nat := 4983230072969 + 3 ^ 40 * 7548963 * 2
def baseEnd_7548963 : Nat := 3876246462006853381245457

theorem tailTrace_7548963 : CollatzResearch.WordTrace tailWord_7548963 prefixEnd_7548963 3876246462006853381245457 := by
  unfold tailWord_7548963
  simp only [CollatzResearch.WordTrace]
  refine ⟨275333300150403786082259543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183555533433602524054839695 275333300150403786082259543)
  ·
    refine ⟨412999950225605679123389315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275333300150403786082259543 412999950225605679123389315)
    ·
      refine ⟨619499925338408518685083973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412999950225605679123389315 619499925338408518685083973)
      ·
        refine ⟨116156236000951597253453245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 619499925338408518685083973 116156236000951597253453245)
        ·
          refine ⟨43558588500356848970044967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116156236000951597253453245 43558588500356848970044967)
          ·
            refine ⟨65337882750535273455067451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43558588500356848970044967 65337882750535273455067451)
            ·
              refine ⟨98006824125802910182601177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65337882750535273455067451 98006824125802910182601177)
              ·
                refine ⟨73505118094352182636950883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98006824125802910182601177 73505118094352182636950883)
                ·
                  refine ⟨110257677141528273955426325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73505118094352182636950883 110257677141528273955426325)
                  ·
                    refine ⟨5168328616009137841660609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110257677141528273955426325 5168328616009137841660609)
                    ·
                      refine ⟨3876246462006853381245457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168328616009137841660609 3876246462006853381245457)
                      ·
                        rfl

theorem cell23_7548963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_7548963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548963 prefixEnd_7548963 := by exact prefixLift 7548963
  have htrace : WordTrace (prefixWord ++ tailWord_7548963) baseStart_7548963 baseEnd_7548963 := by
    simpa [prefixWord, tailWord_7548963, baseEnd_7548963] using wordTrace_append hprefix tailTrace_7548963
  have hstable : (prefixWord ++ tailWord_7548963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548963).length < 2 ^ (prefixWord ++ tailWord_7548963).sum := by decide
  have hdescent : baseEnd_7548963 < baseStart_7548963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548976 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_7548976 : Nat := 118140960795 + 7548976 * 2 ^ 59
def prefixEnd_7548976 : Nat := 4983230072969 + 3 ^ 40 * 7548976 * 2
def baseEnd_7548976 : Nat := 3876253137255361830382897

theorem tailTrace_7548976 : CollatzResearch.WordTrace tailWord_7548976 prefixEnd_7548976 3876253137255361830382897 := by
  unfold tailWord_7548976
  simp only [CollatzResearch.WordTrace]
  refine ⟨137666887149678344651241391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183555849532904459534988521 137666887149678344651241391)
  ·
    refine ⟨206500330724517516976862087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137666887149678344651241391 206500330724517516976862087)
    ·
      refine ⟨309750496086776275465293131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206500330724517516976862087 309750496086776275465293131)
      ·
        refine ⟨464625744130164413197939697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309750496086776275465293131 464625744130164413197939697)
        ·
          refine ⟨348469308097623309898454773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464625744130164413197939697 348469308097623309898454773)
          ·
            refine ⟨32668997634152185302980135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348469308097623309898454773 32668997634152185302980135)
            ·
              refine ⟨49003496451228277954470203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32668997634152185302980135 49003496451228277954470203)
              ·
                refine ⟨73505244676842416931705305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49003496451228277954470203 73505244676842416931705305)
                ·
                  refine ⟨55128933507631812698778979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73505244676842416931705305 55128933507631812698778979)
                  ·
                    refine ⟨82693400261447719048168469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55128933507631812698778979 82693400261447719048168469)
                    ·
                      refine ⟨3876253137255361830382897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82693400261447719048168469 3876253137255361830382897)
                      ·
                        rfl

theorem cell23_7548976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_7548976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548976 prefixEnd_7548976 := by exact prefixLift 7548976
  have htrace : WordTrace (prefixWord ++ tailWord_7548976) baseStart_7548976 baseEnd_7548976 := by
    simpa [prefixWord, tailWord_7548976, baseEnd_7548976] using wordTrace_append hprefix tailTrace_7548976
  have hstable : (prefixWord ++ tailWord_7548976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548976).length < 2 ^ (prefixWord ++ tailWord_7548976).sum := by decide
  have hdescent : baseEnd_7548976 < baseStart_7548976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7548983 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_7548983 : Nat := 118140960795 + 7548983 * 2 ^ 59
def prefixEnd_7548983 : Nat := 4983230072969 + 3 ^ 40 * 7548983 * 2
def baseEnd_7548983 : Nat := 3876256731619943302995365

theorem tailTrace_7548983 : CollatzResearch.WordTrace tailWord_7548983 prefixEnd_7548983 3876256731619943302995365 := by
  unfold tailWord_7548983
  simp only [CollatzResearch.WordTrace]
  refine ⟨275334029610331329497987603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183556019740220886331991735 275334029610331329497987603)
  ·
    refine ⟨413001044415496994246981405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275334029610331329497987603 413001044415496994246981405)
    ·
      refine ⟨154875391655811372842618027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413001044415496994246981405 154875391655811372842618027)
      ·
        refine ⟨232313087483717059263927041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154875391655811372842618027 232313087483717059263927041)
        ·
          refine ⟨174234815612787794447945281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232313087483717059263927041 174234815612787794447945281)
          ·
            refine ⟨130676111709590845835958961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174234815612787794447945281 130676111709590845835958961)
            ·
              refine ⟨98007083782193134376969221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130676111709590845835958961 98007083782193134376969221)
              ·
                refine ⟨18376328209161212695681729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98007083782193134376969221 18376328209161212695681729)
                ·
                  refine ⟨13782246156870909521761297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18376328209161212695681729 13782246156870909521761297)
                  ·
                    refine ⟨10336684617653182141320973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13782246156870909521761297 10336684617653182141320973)
                    ·
                      refine ⟨3876256731619943302995365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10336684617653182141320973 3876256731619943302995365)
                      ·
                        rfl

theorem cell23_7548983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_7548983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7548983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7548983 prefixEnd_7548983 := by exact prefixLift 7548983
  have htrace : WordTrace (prefixWord ++ tailWord_7548983) baseStart_7548983 baseEnd_7548983 := by
    simpa [prefixWord, tailWord_7548983, baseEnd_7548983] using wordTrace_append hprefix tailTrace_7548983
  have hstable : (prefixWord ++ tailWord_7548983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7548983).length < 2 ^ (prefixWord ++ tailWord_7548983).sum := by decide
  have hdescent : baseEnd_7548983 < baseStart_7548983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7548983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549033 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 1, 5]
def baseStart_7549033 : Nat := 118140960795 + 7549033 * 2 ^ 59
def prefixEnd_7549033 : Nat := 4983230072969 + 3 ^ 40 * 7549033 * 2
def baseEnd_7549033 : Nat := 1292094135217556035790045

theorem tailTrace_7549033 : CollatzResearch.WordTrace tailWord_7549033 prefixEnd_7549033 1292094135217556035790045 := by
  unfold tailWord_7549033
  simp only [CollatzResearch.WordTrace]
  refine ⟨275335853260150188037307753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183557235506766792024871835 275335853260150188037307753)
  ·
    refine ⟨206501889945112641027980815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275335853260150188037307753 206501889945112641027980815)
    ·
      refine ⟨309752834917668961541971223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206501889945112641027980815 309752834917668961541971223)
      ·
        refine ⟨464629252376503442312956835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309752834917668961541971223 464629252376503442312956835)
        ·
          refine ⟨696943878564755163469435253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464629252376503442312956835 696943878564755163469435253)
          ·
            refine ⟨65338488615445796575259555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 696943878564755163469435253 65338488615445796575259555)
            ·
              refine ⟨98007732923168694862889333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65338488615445796575259555 98007732923168694862889333)
              ·
                refine ⟨9188224961547065143395875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98007732923168694862889333 9188224961547065143395875)
                ·
                  refine ⟨13782337442320597715093813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9188224961547065143395875 13782337442320597715093813)
                  ·
                    refine ⟨1292094135217556035790045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13782337442320597715093813 1292094135217556035790045)
                    ·
                      rfl

theorem cell23_7549033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_7549033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549033 prefixEnd_7549033 := by exact prefixLift 7549033
  have htrace : WordTrace (prefixWord ++ tailWord_7549033) baseStart_7549033 baseEnd_7549033 := by
    simpa [prefixWord, tailWord_7549033, baseEnd_7549033] using wordTrace_append hprefix tailTrace_7549033
  have hstable : (prefixWord ++ tailWord_7549033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549033).length < 2 ^ (prefixWord ++ tailWord_7549033).sum := by decide
  have hdescent : baseEnd_7549033 < baseStart_7549033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549040 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 4, 3, 2]
def baseStart_7549040 : Nat := 118140960795 + 7549040 * 2 ^ 59
def prefixEnd_7549040 : Nat := 4983230072969 + 3 ^ 40 * 7549040 * 2
def baseEnd_7549040 : Nat := 3876286000017249579982603

theorem tailTrace_7549040 : CollatzResearch.WordTrace tailWord_7549040 prefixEnd_7549040 3876286000017249579982603 := by
  unfold tailWord_7549040
  simp only [CollatzResearch.WordTrace]
  refine ⟨137668054285562414116406287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183557405714083218821875049 137668054285562414116406287)
  ·
    refine ⟨206502081428343621174609431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137668054285562414116406287 206502081428343621174609431)
    ·
      refine ⟨309753122142515431761914147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206502081428343621174609431 309753122142515431761914147)
      ·
        refine ⟨464629683213773147642871221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309753122142515431761914147 464629683213773147642871221)
        ·
          refine ⟨43559032801291232591519177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 464629683213773147642871221 43559032801291232591519177)
          ·
            refine ⟨32669274600968424443639383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43559032801291232591519177 32669274600968424443639383)
            ·
              refine ⟨49003911901452636665459075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32669274600968424443639383 49003911901452636665459075)
              ·
                refine ⟨73505867852178954998188613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49003911901452636665459075 73505867852178954998188613)
                ·
                  refine ⟨13782350222283554062160365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73505867852178954998188613 13782350222283554062160365)
                  ·
                    refine ⟨5168381333356332773310137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13782350222283554062160365 5168381333356332773310137)
                    ·
                      refine ⟨3876286000017249579982603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168381333356332773310137 3876286000017249579982603)
                      ·
                        rfl

theorem cell23_7549040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4, 3, 2].length) (baseStart_7549040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549040 prefixEnd_7549040 := by exact prefixLift 7549040
  have htrace : WordTrace (prefixWord ++ tailWord_7549040) baseStart_7549040 baseEnd_7549040 := by
    simpa [prefixWord, tailWord_7549040, baseEnd_7549040] using wordTrace_append hprefix tailTrace_7549040
  have hstable : (prefixWord ++ tailWord_7549040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549040).length < 2 ^ (prefixWord ++ tailWord_7549040).sum := by decide
  have hdescent : baseEnd_7549040 < baseStart_7549040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549047 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_7549047 : Nat := 118140960795 + 7549047 * 2 ^ 59
def prefixEnd_7549047 : Nat := 4983230072969 + 3 ^ 40 * 7549047 * 2
def baseEnd_7549047 : Nat := 3876289594381831052595071

theorem tailTrace_7549047 : CollatzResearch.WordTrace tailWord_7549047 prefixEnd_7549047 3876289594381831052595071 := by
  unfold tailWord_7549047
  simp only [CollatzResearch.WordTrace]
  refine ⟨275336363882099468428317395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183557575921399645618878263 275336363882099468428317395)
  ·
    refine ⟨413004545823149202642476093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275336363882099468428317395 413004545823149202642476093)
    ·
      refine ⟨154876704683680950990928535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413004545823149202642476093 154876704683680950990928535)
      ·
        refine ⟨232315057025521426486392803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154876704683680950990928535 232315057025521426486392803)
        ·
          refine ⟨348472585538282139729589205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232315057025521426486392803 348472585538282139729589205)
          ·
            refine ⟨8167326223553487649912247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 348472585538282139729589205 8167326223553487649912247)
            ·
              refine ⟨12250989335330231474868371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8167326223553487649912247 12250989335330231474868371)
              ·
                refine ⟨18376484002995347212302557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12250989335330231474868371 18376484002995347212302557)
                ·
                  refine ⟨6891181501123255204613459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18376484002995347212302557 6891181501123255204613459)
                  ·
                    refine ⟨10336772251684882806920189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6891181501123255204613459 10336772251684882806920189)
                    ·
                      refine ⟨3876289594381831052595071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10336772251684882806920189 3876289594381831052595071)
                      ·
                        rfl

theorem cell23_7549047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_7549047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549047 prefixEnd_7549047 := by exact prefixLift 7549047
  have htrace : WordTrace (prefixWord ++ tailWord_7549047) baseStart_7549047 baseEnd_7549047 := by
    simpa [prefixWord, tailWord_7549047, baseEnd_7549047] using wordTrace_append hprefix tailTrace_7549047
  have hstable : (prefixWord ++ tailWord_7549047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549047).length < 2 ^ (prefixWord ++ tailWord_7549047).sum := by decide
  have hdescent : baseEnd_7549047 < baseStart_7549047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549080 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 1, 6]
def baseStart_7549080 : Nat := 118140960795 + 7549080 * 2 ^ 59
def prefixEnd_7549080 : Nat := 4983230072969 + 3 ^ 40 * 7549080 * 2
def baseEnd_7549080 : Nat := 1292102179747809807827473

theorem tailTrace_7549080 : CollatzResearch.WordTrace tailWord_7549080 prefixEnd_7549080 1292102179747809807827473 := by
  unfold tailWord_7549080
  simp only [CollatzResearch.WordTrace]
  refine ⟨137668783745489957532134347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183558378327319943376179129 137668783745489957532134347)
  ·
    refine ⟨206503175618234936298201521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137668783745489957532134347 206503175618234936298201521)
    ·
      refine ⟨154877381713676202223651141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206503175618234936298201521 154877381713676202223651141)
      ·
        refine ⟨29039509071314287916934589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154877381713676202223651141 29039509071314287916934589)
        ·
          refine ⟨10889815901742857968850471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29039509071314287916934589 10889815901742857968850471)
          ·
            refine ⟨16334723852614286953275707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10889815901742857968850471 16334723852614286953275707)
            ·
              refine ⟨24502085778921430429913561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16334723852614286953275707 24502085778921430429913561)
              ·
                refine ⟨18376564334191072822435171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24502085778921430429913561 18376564334191072822435171)
                ·
                  refine ⟨27564846501286609233652757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18376564334191072822435171 27564846501286609233652757)
                  ·
                    refine ⟨1292102179747809807827473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27564846501286609233652757 1292102179747809807827473)
                    ·
                      rfl

theorem cell23_7549080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_7549080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549080 prefixEnd_7549080 := by exact prefixLift 7549080
  have htrace : WordTrace (prefixWord ++ tailWord_7549080) baseStart_7549080 baseEnd_7549080 := by
    simpa [prefixWord, tailWord_7549080, baseEnd_7549080] using wordTrace_append hprefix tailTrace_7549080
  have hstable : (prefixWord ++ tailWord_7549080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549080).length < 2 ^ (prefixWord ++ tailWord_7549080).sum := by decide
  have hdescent : baseEnd_7549080 < baseStart_7549080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549103 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 3]
def baseStart_7549103 : Nat := 118140960795 + 7549103 * 2 ^ 59
def prefixEnd_7549103 : Nat := 4983230072969 + 3 ^ 40 * 7549103 * 2
def baseEnd_7549103 : Nat := 3876318349298482833494813

theorem tailTrace_7549103 : CollatzResearch.WordTrace tailWord_7549103 prefixEnd_7549103 3876318349298482833494813 := by
  unfold tailWord_7549103
  simp only [CollatzResearch.WordTrace]
  refine ⟨275338406369896589992355963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183558937579931059994903975 275338406369896589992355963)
  ·
    refine ⟨413007609554844884988533945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275338406369896589992355963 413007609554844884988533945)
    ·
      refine ⟨309755707166133663741400459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413007609554844884988533945 309755707166133663741400459)
      ·
        refine ⟨464633560749200495612100689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309755707166133663741400459 464633560749200495612100689)
        ·
          refine ⟨348475170561900371709075517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464633560749200495612100689 348475170561900371709075517)
          ·
            refine ⟨130678188960712639390903319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348475170561900371709075517 130678188960712639390903319)
            ·
              refine ⟨196017283441068959086354979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130678188960712639390903319 196017283441068959086354979)
              ·
                refine ⟨294025925161603438629532469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196017283441068959086354979 294025925161603438629532469)
                ·
                  refine ⟨27564930483900322371518669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 294025925161603438629532469 27564930483900322371518669)
                  ·
                    refine ⟨10336848931462620889319501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27564930483900322371518669 10336848931462620889319501)
                    ·
                      refine ⟨3876318349298482833494813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10336848931462620889319501 3876318349298482833494813)
                      ·
                        rfl

theorem cell23_7549103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_7549103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549103 prefixEnd_7549103 := by exact prefixLift 7549103
  have htrace : WordTrace (prefixWord ++ tailWord_7549103) baseStart_7549103 baseEnd_7549103 := by
    simpa [prefixWord, tailWord_7549103, baseEnd_7549103] using wordTrace_append hprefix tailTrace_7549103
  have hstable : (prefixWord ++ tailWord_7549103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549103).length < 2 ^ (prefixWord ++ tailWord_7549103).sum := by decide
  have hdescent : baseEnd_7549103 < baseStart_7549103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549120 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 3]
def baseStart_7549120 : Nat := 118140960795 + 7549120 * 2 ^ 59
def prefixEnd_7549120 : Nat := 4983230072969 + 3 ^ 40 * 7549120 * 2
def baseEnd_7549120 : Nat := 3876327078469609266982235

theorem tailTrace_7549120 : CollatzResearch.WordTrace tailWord_7549120 prefixEnd_7549120 3876327078469609266982235 := by
  unfold tailWord_7549120
  simp only [CollatzResearch.WordTrace]
  refine ⟨137669513205417500947862407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183559350940556667930483209 137669513205417500947862407)
  ·
    refine ⟨206504269808126251421793611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137669513205417500947862407 206504269808126251421793611)
    ·
      refine ⟨309756404712189377132690417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206504269808126251421793611 309756404712189377132690417)
      ·
        refine ⟨232317303534142032849517813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309756404712189377132690417 232317303534142032849517813)
        ·
          refine ⟨21779747206325815579642295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232317303534142032849517813 21779747206325815579642295)
          ·
            refine ⟨32669620809488723369463443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21779747206325815579642295 32669620809488723369463443)
            ·
              refine ⟨49004431214233085054195165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32669620809488723369463443 49004431214233085054195165)
              ·
                refine ⟨18376661705337406895323187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49004431214233085054195165 18376661705337406895323187)
                ·
                  refine ⟨27564992558006110342984781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18376661705337406895323187 27564992558006110342984781)
                  ·
                    refine ⟨10336872209252291378619293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27564992558006110342984781 10336872209252291378619293)
                    ·
                      refine ⟨3876327078469609266982235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10336872209252291378619293 3876327078469609266982235)
                      ·
                        rfl

theorem cell23_7549120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_7549120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549120 prefixEnd_7549120 := by exact prefixLift 7549120
  have htrace : WordTrace (prefixWord ++ tailWord_7549120) baseStart_7549120 baseEnd_7549120 := by
    simpa [prefixWord, tailWord_7549120, baseEnd_7549120] using wordTrace_append hprefix tailTrace_7549120
  have hstable : (prefixWord ++ tailWord_7549120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549120).length < 2 ^ (prefixWord ++ tailWord_7549120).sum := by decide
  have hdescent : baseEnd_7549120 < baseStart_7549120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549121 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7549121 : Nat := 118140960795 + 7549121 * 2 ^ 59
def prefixEnd_7549121 : Nat := 4983230072969 + 3 ^ 40 * 7549121 * 2
def baseEnd_7549121 : Nat := 3876327591950263763069731

theorem tailTrace_7549121 : CollatzResearch.WordTrace tailWord_7549121 prefixEnd_7549121 3876327591950263763069731 := by
  unfold tailWord_7549121
  simp only [CollatzResearch.WordTrace]
  refine ⟨275339062883831379066511217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183559375255887586044340811 275339062883831379066511217)
  ·
    refine ⟨206504297162873534299883413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275339062883831379066511217 206504297162873534299883413)
    ·
      refine ⟨9679888929509696920307035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206504297162873534299883413 9679888929509696920307035)
      ·
        refine ⟨14519833394264545380460553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679888929509696920307035 14519833394264545380460553)
        ·
          refine ⟨10889875045698409035345415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14519833394264545380460553 10889875045698409035345415)
          ·
            refine ⟨16334812568547613553018123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10889875045698409035345415 16334812568547613553018123)
            ·
              refine ⟨24502218852821420329527185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16334812568547613553018123 24502218852821420329527185)
              ·
                refine ⟨18376664139616065247145389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24502218852821420329527185 18376664139616065247145389)
                ·
                  refine ⟨6891249052356024467679521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18376664139616065247145389 6891249052356024467679521)
                  ·
                    refine ⟨5168436789267018350759641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6891249052356024467679521 5168436789267018350759641)
                    ·
                      refine ⟨3876327591950263763069731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168436789267018350759641 3876327591950263763069731)
                      ·
                        rfl

theorem cell23_7549121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7549121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549121 prefixEnd_7549121 := by exact prefixLift 7549121
  have htrace : WordTrace (prefixWord ++ tailWord_7549121) baseStart_7549121 baseEnd_7549121 := by
    simpa [prefixWord, tailWord_7549121, baseEnd_7549121] using wordTrace_append hprefix tailTrace_7549121
  have hstable : (prefixWord ++ tailWord_7549121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549121).length < 2 ^ (prefixWord ++ tailWord_7549121).sum := by decide
  have hdescent : baseEnd_7549121 < baseStart_7549121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549141 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7549141 : Nat := 118140960795 + 7549141 * 2 ^ 59
def prefixEnd_7549141 : Nat := 4983230072969 + 3 ^ 40 * 7549141 * 2
def baseEnd_7549141 : Nat := 3876337861563353684819639

theorem tailTrace_7549141 : CollatzResearch.WordTrace tailWord_7549141 prefixEnd_7549141 3876337861563353684819639 := by
  unfold tailWord_7549141
  simp only [CollatzResearch.WordTrace]
  refine ⟨275339792343758922482239277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183559861562505948321492851 275339792343758922482239277)
  ·
    refine ⟨103252422128909595930839729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275339792343758922482239277 103252422128909595930839729)
    ·
      refine ⟨77439316596682196948129797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103252422128909595930839729 77439316596682196948129797)
      ·
        refine ⟨14519871861877911927774337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77439316596682196948129797 14519871861877911927774337)
        ·
          refine ⟨10889903896408433945830753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14519871861877911927774337 10889903896408433945830753)
          ·
            refine ⟨8167427922306325459373065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10889903896408433945830753 8167427922306325459373065)
            ·
              refine ⟨6125570941729744094529799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8167427922306325459373065 6125570941729744094529799)
              ·
                refine ⟨9188356412594616141794699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125570941729744094529799 9188356412594616141794699)
                ·
                  refine ⟨13782534618891924212692049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9188356412594616141794699 13782534618891924212692049)
                  ·
                    refine ⟨10336900964168943159519037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13782534618891924212692049 10336900964168943159519037)
                    ·
                      refine ⟨3876337861563353684819639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10336900964168943159519037 3876337861563353684819639)
                      ·
                        rfl

theorem cell23_7549141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7549141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549141 prefixEnd_7549141 := by exact prefixLift 7549141
  have htrace : WordTrace (prefixWord ++ tailWord_7549141) baseStart_7549141 baseEnd_7549141 := by
    simpa [prefixWord, tailWord_7549141, baseEnd_7549141] using wordTrace_append hprefix tailTrace_7549141
  have hstable : (prefixWord ++ tailWord_7549141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549141).length < 2 ^ (prefixWord ++ tailWord_7549141).sum := by decide
  have hdescent : baseEnd_7549141 < baseStart_7549141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549148 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_7549148 : Nat := 118140960795 + 7549148 * 2 ^ 59
def prefixEnd_7549148 : Nat := 4983230072969 + 3 ^ 40 * 7549148 * 2
def baseEnd_7549148 : Nat := 1292113818642645052477369

theorem tailTrace_7549148 : CollatzResearch.WordTrace tailWord_7549148 prefixEnd_7549148 1292113818642645052477369 := by
  unfold tailWord_7549148
  simp only [CollatzResearch.WordTrace]
  refine ⟨137670023827366781338872049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183560031769822375118496065 137670023827366781338872049)
  ·
    refine ⟨103252517870525086004154037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137670023827366781338872049 103252517870525086004154037)
    ·
      refine ⟨9679923550361726812889441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103252517870525086004154037 9679923550361726812889441)
      ·
        refine ⟨7259942662771295109667081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9679923550361726812889441 7259942662771295109667081)
        ·
          refine ⟨5444956997078471332250311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7259942662771295109667081 5444956997078471332250311)
          ·
            refine ⟨8167435495617706998375467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5444956997078471332250311 8167435495617706998375467)
            ·
              refine ⟨12251153243426560497563201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8167435495617706998375467 12251153243426560497563201)
              ·
                refine ⟨9188364932569920373172401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12251153243426560497563201 9188364932569920373172401)
                ·
                  refine ⟨6891273699427440279879301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9188364932569920373172401 6891273699427440279879301)
                  ·
                    refine ⟨1292113818642645052477369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6891273699427440279879301 1292113818642645052477369)
                    ·
                      rfl

theorem cell23_7549148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_7549148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549148 prefixEnd_7549148 := by exact prefixLift 7549148
  have htrace : WordTrace (prefixWord ++ tailWord_7549148) baseStart_7549148 baseEnd_7549148 := by
    simpa [prefixWord, tailWord_7549148, baseEnd_7549148] using wordTrace_append hprefix tailTrace_7549148
  have hstable : (prefixWord ++ tailWord_7549148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549148).length < 2 ^ (prefixWord ++ tailWord_7549148).sum := by decide
  have hdescent : baseEnd_7549148 < baseStart_7549148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549153 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 4, 6]
def baseStart_7549153 : Nat := 118140960795 + 7549153 * 2 ^ 59
def prefixEnd_7549153 : Nat := 4983230072969 + 3 ^ 40 * 7549153 * 2
def baseEnd_7549153 : Nat := 1292114674443735879289861

theorem tailTrace_7549153 : CollatzResearch.WordTrace tailWord_7549153 prefixEnd_7549153 1292114674443735879289861 := by
  unfold tailWord_7549153
  simp only [CollatzResearch.WordTrace]
  refine ⟨275340230019715448531676113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183560153346476965687784075 275340230019715448531676113)
  ·
    refine ⟨206505172514786586398757085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275340230019715448531676113 206505172514786586398757085)
    ·
      refine ⟨77439439693044969899533907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206505172514786586398757085 77439439693044969899533907)
      ·
        refine ⟨116159159539567454849300861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77439439693044969899533907 116159159539567454849300861)
        ·
          refine ⟨43559684827337795568487823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116159159539567454849300861 43559684827337795568487823)
          ·
            refine ⟨65339527241006693352731735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43559684827337795568487823 65339527241006693352731735)
            ·
              refine ⟨98009290861510040029097603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65339527241006693352731735 98009290861510040029097603)
              ·
                refine ⟨147013936292265060043646405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98009290861510040029097603 147013936292265060043646405)
                ·
                  refine ⟨27565113054799698758183701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147013936292265060043646405 27565113054799698758183701)
                  ·
                    refine ⟨1292114674443735879289861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27565113054799698758183701 1292114674443735879289861)
                    ·
                      rfl

theorem cell23_7549153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_7549153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549153 prefixEnd_7549153 := by exact prefixLift 7549153
  have htrace : WordTrace (prefixWord ++ tailWord_7549153) baseStart_7549153 baseEnd_7549153 := by
    simpa [prefixWord, tailWord_7549153, baseEnd_7549153] using wordTrace_append hprefix tailTrace_7549153
  have hstable : (prefixWord ++ tailWord_7549153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549153).length < 2 ^ (prefixWord ++ tailWord_7549153).sum := by decide
  have hdescent : baseEnd_7549153 < baseStart_7549153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549170 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_7549170 : Nat := 118140960795 + 7549170 * 2 ^ 59
def prefixEnd_7549170 : Nat := 4983230072969 + 3 ^ 40 * 7549170 * 2
def baseEnd_7549170 : Nat := 1292117584167444690452335

theorem tailTrace_7549170 : CollatzResearch.WordTrace tailWord_7549170 prefixEnd_7549170 1292117584167444690452335 := by
  unfold tailWord_7549170
  simp only [CollatzResearch.WordTrace]
  refine ⟨68835212515163465108761241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183560566707102573623363309 68835212515163465108761241)
  ·
    refine ⟨51626409386372598831570931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68835212515163465108761241 51626409386372598831570931)
    ·
      refine ⟨77439614079558898247356397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51626409386372598831570931 77439614079558898247356397)
      ·
        refine ⟨29039855279834586842758649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77439614079558898247356397 29039855279834586842758649)
        ·
          refine ⟨21779891459875940132068987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29039855279834586842758649 21779891459875940132068987)
          ·
            refine ⟨32669837189813910198103481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21779891459875940132068987 32669837189813910198103481)
            ·
              refine ⟨24502377892360432648577611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32669837189813910198103481 24502377892360432648577611)
              ·
                refine ⟨36753566838540648972866417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24502377892360432648577611 36753566838540648972866417)
                ·
                  refine ⟨27565175128905486729649813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36753566838540648972866417 27565175128905486729649813)
                  ·
                    refine ⟨1292117584167444690452335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27565175128905486729649813 1292117584167444690452335)
                    ·
                      rfl

theorem cell23_7549170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_7549170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549170 prefixEnd_7549170 := by exact prefixLift 7549170
  have htrace : WordTrace (prefixWord ++ tailWord_7549170) baseStart_7549170 baseEnd_7549170 := by
    simpa [prefixWord, tailWord_7549170, baseEnd_7549170] using wordTrace_append hprefix tailTrace_7549170
  have hstable : (prefixWord ++ tailWord_7549170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549170).length < 2 ^ (prefixWord ++ tailWord_7549170).sum := by decide
  have hdescent : baseEnd_7549170 < baseStart_7549170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549183 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 7]
def baseStart_7549183 : Nat := 118140960795 + 7549183 * 2 ^ 59
def prefixEnd_7549183 : Nat := 4983230072969 + 3 ^ 40 * 7549183 * 2
def baseEnd_7549183 : Nat := 430706603083426946721605

theorem tailTrace_7549183 : CollatzResearch.WordTrace tailWord_7549183 prefixEnd_7549183 430706603083426946721605 := by
  unfold tailWord_7549183
  simp only [CollatzResearch.WordTrace]
  refine ⟨275341324209606763655268203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183560882806404509103512135 275341324209606763655268203)
  ·
    refine ⟨413011986314410145482902305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275341324209606763655268203 413011986314410145482902305)
    ·
      refine ⟨309758989735807609112176729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413011986314410145482902305 309758989735807609112176729)
      ·
        refine ⟨232319242301855706834132547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309758989735807609112176729 232319242301855706834132547)
        ·
          refine ⟨348478863452783560251198821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232319242301855706834132547 348478863452783560251198821)
          ·
            refine ⟨65339786897396917547099779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348478863452783560251198821 65339786897396917547099779)
            ·
              refine ⟨98009680346095376320649669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65339786897396917547099779 98009680346095376320649669)
              ·
                refine ⟨18376815064892883060121813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98009680346095376320649669 18376815064892883060121813)
                ·
                  refine ⟨430706603083426946721605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18376815064892883060121813 430706603083426946721605)
                  ·
                    rfl

theorem cell23_7549183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 7].length) (baseStart_7549183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549183 prefixEnd_7549183 := by exact prefixLift 7549183
  have htrace : WordTrace (prefixWord ++ tailWord_7549183) baseStart_7549183 baseEnd_7549183 := by
    simpa [prefixWord, tailWord_7549183, baseEnd_7549183] using wordTrace_append hprefix tailTrace_7549183
  have hstable : (prefixWord ++ tailWord_7549183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549183).length < 2 ^ (prefixWord ++ tailWord_7549183).sum := by decide
  have hdescent : baseEnd_7549183 < baseStart_7549183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549253 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_7549253 : Nat := 118140960795 + 7549253 * 2 ^ 59
def prefixEnd_7549253 : Nat := 4983230072969 + 3 ^ 40 * 7549253 * 2
def baseEnd_7549253 : Nat := 3876395371396657246619123

theorem tailTrace_7549253 : CollatzResearch.WordTrace tailWord_7549253 prefixEnd_7549253 3876395371396657246619123 := by
  unfold tailWord_7549253
  simp only [CollatzResearch.WordTrace]
  refine ⟨275343877319353165610316413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183562584879568777073544275 275343877319353165610316413)
  ·
    refine ⟨103253953994757437103868655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275343877319353165610316413 103253953994757437103868655)
    ·
      refine ⟨154880930992136155655802983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103253953994757437103868655 154880930992136155655802983)
      ·
        refine ⟨232321396488204233483704475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154880930992136155655802983 232321396488204233483704475)
        ·
          refine ⟨348482094732306350225556713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232321396488204233483704475 348482094732306350225556713)
          ·
            refine ⟨261361571049229762669167535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348482094732306350225556713 261361571049229762669167535)
            ·
              refine ⟨392042356573844644003751303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261361571049229762669167535 392042356573844644003751303)
              ·
                refine ⟨588063534860766966005626955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392042356573844644003751303 588063534860766966005626955)
                ·
                  refine ⟨882095302291150449008440433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588063534860766966005626955 882095302291150449008440433)
                  ·
                    refine ⟨661571476718362836756330325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 882095302291150449008440433 661571476718362836756330325)
                    ·
                      refine ⟨3876395371396657246619123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 661571476718362836756330325 3876395371396657246619123)
                      ·
                        rfl

theorem cell23_7549253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_7549253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549253 prefixEnd_7549253 := by exact prefixLift 7549253
  have htrace : WordTrace (prefixWord ++ tailWord_7549253) baseStart_7549253 baseEnd_7549253 := by
    simpa [prefixWord, tailWord_7549253, baseEnd_7549253] using wordTrace_append hprefix tailTrace_7549253
  have hstable : (prefixWord ++ tailWord_7549253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549253).length < 2 ^ (prefixWord ++ tailWord_7549253).sum := by decide
  have hdescent : baseEnd_7549253 < baseStart_7549253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549317 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_7549317 : Nat := 118140960795 + 7549317 * 2 ^ 59
def prefixEnd_7549317 : Nat := 4983230072969 + 3 ^ 40 * 7549317 * 2
def baseEnd_7549317 : Nat := 3876428234158544996218829

theorem tailTrace_7549317 : CollatzResearch.WordTrace tailWord_7549317 prefixEnd_7549317 3876428234158544996218829 := by
  unfold tailWord_7549317
  simp only [CollatzResearch.WordTrace]
  refine ⟨275346211591121304540646205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183564141060747536360430803 275346211591121304540646205)
  ·
    refine ⟨103254829346670489202742327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275346211591121304540646205 103254829346670489202742327)
    ·
      refine ⟨154882244020005733804113491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103254829346670489202742327 154882244020005733804113491)
      ·
        refine ⟨232323366030008600706170237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154882244020005733804113491 232323366030008600706170237)
        ·
          refine ⟨87121262261253225264813839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232323366030008600706170237 87121262261253225264813839)
          ·
            refine ⟨130681893391879837897220759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87121262261253225264813839 130681893391879837897220759)
            ·
              refine ⟨196022840087819756845831139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130681893391879837897220759 196022840087819756845831139)
              ·
                refine ⟨294034260131729635268746709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196022840087819756845831139 294034260131729635268746709)
                ·
                  refine ⟨6891427971837413326611251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 294034260131729635268746709 6891427971837413326611251)
                  ·
                    refine ⟨10337141957756119989916877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6891427971837413326611251 10337141957756119989916877)
                    ·
                      refine ⟨3876428234158544996218829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337141957756119989916877 3876428234158544996218829)
                      ·
                        rfl

theorem cell23_7549317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_7549317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549317 prefixEnd_7549317 := by exact prefixLift 7549317
  have htrace : WordTrace (prefixWord ++ tailWord_7549317) baseStart_7549317 baseEnd_7549317 := by
    simpa [prefixWord, tailWord_7549317, baseEnd_7549317] using wordTrace_append hprefix tailTrace_7549317
  have hstable : (prefixWord ++ tailWord_7549317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549317).length < 2 ^ (prefixWord ++ tailWord_7549317).sum := by decide
  have hdescent : baseEnd_7549317 < baseStart_7549317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549367 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 4, 4]
def baseStart_7549367 : Nat := 118140960795 + 7549367 * 2 ^ 59
def prefixEnd_7549367 : Nat := 4983230072969 + 3 ^ 40 * 7549367 * 2
def baseEnd_7549367 : Nat := 1292151302730423266864533

theorem tailTrace_7549367 : CollatzResearch.WordTrace tailWord_7549367 prefixEnd_7549367 1292151302730423266864533 := by
  unfold tailWord_7549367
  simp only [CollatzResearch.WordTrace]
  refine ⟨275348035240940163079966355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183565356827293442053310903 275348035240940163079966355)
  ·
    refine ⟨413022052861410244619949533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275348035240940163079966355 413022052861410244619949533)
    ·
      refine ⟨154883269823028841732481075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413022052861410244619949533 154883269823028841732481075)
      ·
        refine ⟨232324904734543262598721613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154883269823028841732481075 232324904734543262598721613)
        ·
          refine ⟨87121839275453723474520605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232324904734543262598721613 87121839275453723474520605)
          ·
            refine ⟨32670689728295146302945227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87121839275453723474520605 32670689728295146302945227)
            ·
              refine ⟨49006034592442719454417841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32670689728295146302945227 49006034592442719454417841)
              ·
                refine ⟨36754525944332039590813381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49006034592442719454417841 36754525944332039590813381)
                ·
                  refine ⟨6891473614562257423277509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36754525944332039590813381 6891473614562257423277509)
                  ·
                    refine ⟨1292151302730423266864533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6891473614562257423277509 1292151302730423266864533)
                    ·
                      rfl

theorem cell23_7549367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_7549367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549367 prefixEnd_7549367 := by exact prefixLift 7549367
  have htrace : WordTrace (prefixWord ++ tailWord_7549367) baseStart_7549367 baseEnd_7549367 := by
    simpa [prefixWord, tailWord_7549367, baseEnd_7549367] using wordTrace_append hprefix tailTrace_7549367
  have hstable : (prefixWord ++ tailWord_7549367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549367).length < 2 ^ (prefixWord ++ tailWord_7549367).sum := by decide
  have hdescent : baseEnd_7549367 < baseStart_7549367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549374 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_7549374 : Nat := 118140960795 + 7549374 * 2 ^ 59
def prefixEnd_7549374 : Nat := 4983230072969 + 3 ^ 40 * 7549374 * 2
def baseEnd_7549374 : Nat := 3876457502555851273206067

theorem tailTrace_7549374 : CollatzResearch.WordTrace tailWord_7549374 prefixEnd_7549374 3876457502555851273206067 := by
  unfold tailWord_7549374
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418536318989350409433897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183565527034609868850314117 34418536318989350409433897)
  ·
    refine ⟨25813902239242012807075423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34418536318989350409433897 25813902239242012807075423)
    ·
      refine ⟨38720853358863019210613135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25813902239242012807075423 38720853358863019210613135)
      ·
        refine ⟨58081280038294528815919703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38720853358863019210613135 58081280038294528815919703)
        ·
          refine ⟨87121920057441793223879555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58081280038294528815919703 87121920057441793223879555)
          ·
            refine ⟨130682880086162689835819333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87121920057441793223879555 130682880086162689835819333)
            ·
              refine ⟨24503040016155504344216125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130682880086162689835819333 24503040016155504344216125)
              ·
                refine ⟨9188640006058314129081047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24503040016155504344216125 9188640006058314129081047)
                ·
                  refine ⟨13782960009087471193621571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9188640006058314129081047 13782960009087471193621571)
                  ·
                    refine ⟨20674440013631206790432357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13782960009087471193621571 20674440013631206790432357)
                    ·
                      refine ⟨3876457502555851273206067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20674440013631206790432357 3876457502555851273206067)
                      ·
                        rfl

theorem cell23_7549374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_7549374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549374 prefixEnd_7549374 := by exact prefixLift 7549374
  have htrace : WordTrace (prefixWord ++ tailWord_7549374) baseStart_7549374 baseEnd_7549374 := by
    simpa [prefixWord, tailWord_7549374, baseEnd_7549374] using wordTrace_append hprefix tailTrace_7549374
  have hstable : (prefixWord ++ tailWord_7549374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549374).length < 2 ^ (prefixWord ++ tailWord_7549374).sum := by decide
  have hdescent : baseEnd_7549374 < baseStart_7549374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549397 : List Nat := [1, 3, 2, 3, 1, 3, 2, 8]
def baseStart_7549397 : Nat := 118140960795 + 7549397 * 2 ^ 59
def prefixEnd_7549397 : Nat := 4983230072969 + 3 ^ 40 * 7549397 * 2
def baseEnd_7549397 : Nat := 143572937504107580859943

theorem tailTrace_7549397 : CollatzResearch.WordTrace tailWord_7549397 prefixEnd_7549397 143572937504107580859943 := by
  unfold tailWord_7549397
  simp only [CollatzResearch.WordTrace]
  refine ⟨275349129430831478203558445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183566086287220985469038963 275349129430831478203558445)
  ·
    refine ⟨103255923536561804326334417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275349129430831478203558445 103255923536561804326334417)
    ·
      refine ⟨77441942652421353244750813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103255923536561804326334417 77441942652421353244750813)
      ·
        refine ⟨29040728494658007466781555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77441942652421353244750813 29040728494658007466781555)
        ·
          refine ⟨43561092741987011200172333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29040728494658007466781555 43561092741987011200172333)
          ·
            refine ⟨16335409778245129200064625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43561092741987011200172333 16335409778245129200064625)
            ·
              refine ⟨12251557333683846900048469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16335409778245129200064625 12251557333683846900048469)
              ·
                refine ⟨143572937504107580859943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12251557333683846900048469 143572937504107580859943)
                ·
                  rfl

theorem cell23_7549397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 8].length) (baseStart_7549397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549397 prefixEnd_7549397 := by exact prefixLift 7549397
  have htrace : WordTrace (prefixWord ++ tailWord_7549397) baseStart_7549397 baseEnd_7549397 := by
    simpa [prefixWord, tailWord_7549397, baseEnd_7549397] using wordTrace_append hprefix tailTrace_7549397
  have hstable : (prefixWord ++ tailWord_7549397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549397).length < 2 ^ (prefixWord ++ tailWord_7549397).sum := by decide
  have hdescent : baseEnd_7549397 < baseStart_7549397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549400 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_7549400 : Nat := 118140960795 + 7549400 * 2 ^ 59
def prefixEnd_7549400 : Nat := 4983230072969 + 3 ^ 40 * 7549400 * 2
def baseEnd_7549400 : Nat := 3876470853052868171480947

theorem tailTrace_7549400 : CollatzResearch.WordTrace tailWord_7549400 prefixEnd_7549400 3876470853052868171480947 := by
  unfold tailWord_7549400
  simp only [CollatzResearch.WordTrace]
  refine ⟨137674619424910304857958827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183566159233213739810611769 137674619424910304857958827)
  ·
    refine ⟨206511929137365457286938241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137674619424910304857958827 206511929137365457286938241)
    ·
      refine ⟨154883946853024092965203681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206511929137365457286938241 154883946853024092965203681)
      ·
        refine ⟨116162960139768069723902761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154883946853024092965203681 116162960139768069723902761)
        ·
          refine ⟨87122220104826052292927071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116162960139768069723902761 87122220104826052292927071)
          ·
            refine ⟨130683330157239078439390607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87122220104826052292927071 130683330157239078439390607)
            ·
              refine ⟨196024995235858617659085911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130683330157239078439390607 196024995235858617659085911)
              ·
                refine ⟨294037492853787926488628867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196024995235858617659085911 294037492853787926488628867)
                ·
                  refine ⟨441056239280681889732943301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294037492853787926488628867 441056239280681889732943301)
                  ·
                    refine ⟨82698044865127854324926869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 441056239280681889732943301 82698044865127854324926869)
                    ·
                      refine ⟨3876470853052868171480947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82698044865127854324926869 3876470853052868171480947)
                      ·
                        rfl

theorem cell23_7549400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_7549400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549400 prefixEnd_7549400 := by exact prefixLift 7549400
  have htrace : WordTrace (prefixWord ++ tailWord_7549400) baseStart_7549400 baseEnd_7549400 := by
    simpa [prefixWord, tailWord_7549400, baseEnd_7549400] using wordTrace_append hprefix tailTrace_7549400
  have hstable : (prefixWord ++ tailWord_7549400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549400).length < 2 ^ (prefixWord ++ tailWord_7549400).sum := by decide
  have hdescent : baseEnd_7549400 < baseStart_7549400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549440 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 5, 8]
def baseStart_7549440 : Nat := 118140960795 + 7549440 * 2 ^ 59
def prefixEnd_7549440 : Nat := 4983230072969 + 3 ^ 40 * 7549440 * 2
def baseEnd_7549440 : Nat := 1292163797426349338326921

theorem tailTrace_7549440 : CollatzResearch.WordTrace tailWord_7549440 prefixEnd_7549440 1292163797426349338326921 := by
  unfold tailWord_7549440
  simp only [CollatzResearch.WordTrace]
  refine ⟨137675348884837848273686887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183567131846450464364915849 137675348884837848273686887)
  ·
    refine ⟨206513023327256772410530331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137675348884837848273686887 206513023327256772410530331)
    ·
      refine ⟨309769534990885158615795497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206513023327256772410530331 309769534990885158615795497)
      ·
        refine ⟨232327151243163868961846623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309769534990885158615795497 232327151243163868961846623)
        ·
          refine ⟨348490726864745803442769935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232327151243163868961846623 348490726864745803442769935)
          ·
            refine ⟨522736090297118705164154903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348490726864745803442769935 522736090297118705164154903)
            ·
              refine ⟨784104135445678057746232355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522736090297118705164154903 784104135445678057746232355)
              ·
                refine ⟨1176156203168517086619348533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784104135445678057746232355 1176156203168517086619348533)
                ·
                  refine ⟨110264644047048476870563925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176156203168517086619348533 110264644047048476870563925)
                  ·
                    refine ⟨1292163797426349338326921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110264644047048476870563925 1292163797426349338326921)
                    ·
                      rfl

theorem cell23_7549440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_7549440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549440 prefixEnd_7549440 := by exact prefixLift 7549440
  have htrace : WordTrace (prefixWord ++ tailWord_7549440) baseStart_7549440 baseEnd_7549440 := by
    simpa [prefixWord, tailWord_7549440, baseEnd_7549440] using wordTrace_append hprefix tailTrace_7549440
  have hstable : (prefixWord ++ tailWord_7549440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549440).length < 2 ^ (prefixWord ++ tailWord_7549440).sum := by decide
  have hdescent : baseEnd_7549440 < baseStart_7549440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549441 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_7549441 : Nat := 118140960795 + 7549441 * 2 ^ 59
def prefixEnd_7549441 : Nat := 4983230072969 + 3 ^ 40 * 7549441 * 2
def baseEnd_7549441 : Nat := 3876491905759702511068259

theorem tailTrace_7549441 : CollatzResearch.WordTrace tailWord_7549441 prefixEnd_7549441 3876491905759702511068259 := by
  unfold tailWord_7549441
  simp only [CollatzResearch.WordTrace]
  refine ⟨275350734242672073718160177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183567156161781382478773451 275350734242672073718160177)
  ·
    refine ⟨206513050682004055288620133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275350734242672073718160177 206513050682004055288620133)
    ·
      refine ⟨38721197002875760366616275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206513050682004055288620133 38721197002875760366616275)
      ·
        refine ⟨58081795504313640549924413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38721197002875760366616275 58081795504313640549924413)
        ·
          refine ⟨21780673314117615206221655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58081795504313640549924413 21780673314117615206221655)
          ·
            refine ⟨32671009971176422809332483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21780673314117615206221655 32671009971176422809332483)
            ·
              refine ⟨49006514956764634213998725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32671009971176422809332483 49006514956764634213998725)
              ·
                refine ⟨9188721554393368915124761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49006514956764634213998725 9188721554393368915124761)
                ·
                  refine ⟨6891541165795026686343571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9188721554393368915124761 6891541165795026686343571)
                  ·
                    refine ⟨10337311748692540029515357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6891541165795026686343571 10337311748692540029515357)
                    ·
                      refine ⟨3876491905759702511068259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337311748692540029515357 3876491905759702511068259)
                      ·
                        rfl

theorem cell23_7549441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_7549441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549441 prefixEnd_7549441 := by exact prefixLift 7549441
  have htrace : WordTrace (prefixWord ++ tailWord_7549441) baseStart_7549441 baseEnd_7549441 := by
    simpa [prefixWord, tailWord_7549441, baseEnd_7549441] using wordTrace_append hprefix tailTrace_7549441
  have hstable : (prefixWord ++ tailWord_7549441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549441).length < 2 ^ (prefixWord ++ tailWord_7549441).sum := by decide
  have hdescent : baseEnd_7549441 < baseStart_7549441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549442 : List Nat := [3, 4, 1, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7549442 : Nat := 118140960795 + 7549442 * 2 ^ 59
def prefixEnd_7549442 : Nat := 4983230072969 + 3 ^ 40 * 7549442 * 2
def baseEnd_7549442 : Nat := 3876492419240357007155755

theorem tailTrace_7549442 : CollatzResearch.WordTrace tailWord_7549442 prefixEnd_7549442 3876492419240357007155755 := by
  unfold tailWord_7549442
  simp only [CollatzResearch.WordTrace]
  refine ⟨68837692678917112722236645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183567180477112300592631053 68837692678917112722236645)
  ·
    refine ⟨12907067377296958635419371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68837692678917112722236645 12907067377296958635419371)
    ·
      refine ⟨19360601065945437953129057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12907067377296958635419371 19360601065945437953129057)
      ·
        refine ⟨14520450799459078464846793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19360601065945437953129057 14520450799459078464846793)
        ·
          refine ⟨10890338099594308848635095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14520450799459078464846793 10890338099594308848635095)
          ·
            refine ⟨16335507149391463272952643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10890338099594308848635095 16335507149391463272952643)
            ·
              refine ⟨24503260724087194909428965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16335507149391463272952643 24503260724087194909428965)
              ·
                refine ⟨4594361385766349045517931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24503260724087194909428965 4594361385766349045517931)
                ·
                  refine ⟨6891542078649523568276897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594361385766349045517931 6891542078649523568276897)
                  ·
                    refine ⟨5168656558987142676207673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6891542078649523568276897 5168656558987142676207673)
                    ·
                      refine ⟨3876492419240357007155755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168656558987142676207673 3876492419240357007155755)
                      ·
                        rfl

theorem cell23_7549442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7549442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549442 prefixEnd_7549442 := by exact prefixLift 7549442
  have htrace : WordTrace (prefixWord ++ tailWord_7549442) baseStart_7549442 baseEnd_7549442 := by
    simpa [prefixWord, tailWord_7549442, baseEnd_7549442] using wordTrace_append hprefix tailTrace_7549442
  have hstable : (prefixWord ++ tailWord_7549442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549442).length < 2 ^ (prefixWord ++ tailWord_7549442).sum := by decide
  have hdescent : baseEnd_7549442 < baseStart_7549442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549492 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7549492 : Nat := 118140960795 + 7549492 * 2 ^ 59
def prefixEnd_7549492 : Nat := 4983230072969 + 3 ^ 40 * 7549492 * 2
def baseEnd_7549492 : Nat := 3876518093273081811530525

theorem tailTrace_7549492 : CollatzResearch.WordTrace tailWord_7549492 prefixEnd_7549492 3876518093273081811530525 := by
  unfold tailWord_7549492
  simp only [CollatzResearch.WordTrace]
  refine ⟨137676297182743654714133365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183568396243658206285511153 137676297182743654714133365)
  ·
    refine ⟨12907152860882217629450003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137676297182743654714133365 12907152860882217629450003)
    ·
      refine ⟨19360729291323326444175005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12907152860882217629450003 19360729291323326444175005)
      ·
        refine ⟨7260273484246247416565627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19360729291323326444175005 7260273484246247416565627)
        ·
          refine ⟨10890410226369371124848441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7260273484246247416565627 10890410226369371124848441)
          ·
            refine ⟨8167807669777028343636331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10890410226369371124848441 8167807669777028343636331)
            ·
              refine ⟨12251711504665542515454497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8167807669777028343636331 12251711504665542515454497)
              ·
                refine ⟨9188783628499156886590873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12251711504665542515454497 9188783628499156886590873)
                ·
                  refine ⟨6891587721374367664943155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9188783628499156886590873 6891587721374367664943155)
                  ·
                    refine ⟨10337381582061551497414733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6891587721374367664943155 10337381582061551497414733)
                    ·
                      refine ⟨3876518093273081811530525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337381582061551497414733 3876518093273081811530525)
                      ·
                        rfl

theorem cell23_7549492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7549492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549492 prefixEnd_7549492 := by exact prefixLift 7549492
  have htrace : WordTrace (prefixWord ++ tailWord_7549492) baseStart_7549492 baseEnd_7549492 := by
    simpa [prefixWord, tailWord_7549492, baseEnd_7549492] using wordTrace_append hprefix tailTrace_7549492
  have hstable : (prefixWord ++ tailWord_7549492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549492).length < 2 ^ (prefixWord ++ tailWord_7549492).sum := by decide
  have hdescent : baseEnd_7549492 < baseStart_7549492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549498 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2]
def baseStart_7549498 : Nat := 118140960795 + 7549498 * 2 ^ 59
def prefixEnd_7549498 : Nat := 4983230072969 + 3 ^ 40 * 7549498 * 2
def baseEnd_7549498 : Nat := 3876521174157008788055497

theorem tailTrace_7549498 : CollatzResearch.WordTrace tailWord_7549498 prefixEnd_7549498 3876521174157008788055497 := by
  unfold tailWord_7549498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68838203300866393113246287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183568542135643714968656765 68838203300866393113246287)
  ·
    refine ⟨103257304951299589669869431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68838203300866393113246287 103257304951299589669869431)
    ·
      refine ⟨154885957426949384504804147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103257304951299589669869431 154885957426949384504804147)
      ·
        refine ⟨232328936140424076757206221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154885957426949384504804147 232328936140424076757206221)
        ·
          refine ⟨87123351052659028783952333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232328936140424076757206221 87123351052659028783952333)
          ·
            refine ⟨32671256644747135793982125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87123351052659028783952333 32671256644747135793982125)
            ·
              refine ⟨12251721241780175922743297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32671256644747135793982125 12251721241780175922743297)
              ·
                refine ⟨9188790931335131942057473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12251721241780175922743297 9188790931335131942057473)
                ·
                  refine ⟨6891593198501348956543105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9188790931335131942057473 6891593198501348956543105)
                  ·
                    refine ⟨5168694898876011717407329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6891593198501348956543105 5168694898876011717407329)
                    ·
                      refine ⟨3876521174157008788055497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168694898876011717407329 3876521174157008788055497)
                      ·
                        rfl

theorem cell23_7549498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_7549498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549498 prefixEnd_7549498 := by exact prefixLift 7549498
  have htrace : WordTrace (prefixWord ++ tailWord_7549498) baseStart_7549498 baseEnd_7549498 := by
    simpa [prefixWord, tailWord_7549498, baseEnd_7549498] using wordTrace_append hprefix tailTrace_7549498
  have hstable : (prefixWord ++ tailWord_7549498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549498).length < 2 ^ (prefixWord ++ tailWord_7549498).sum := by decide
  have hdescent : baseEnd_7549498 < baseStart_7549498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549504 : List Nat := [2, 1, 1, 2, 2, 2, 4, 4, 5]
def baseStart_7549504 : Nat := 118140960795 + 7549504 * 2 ^ 59
def prefixEnd_7549504 : Nat := 4983230072969 + 3 ^ 40 * 7549504 * 2
def baseEnd_7549504 : Nat := 430724917226770640508941

theorem tailTrace_7549504 : CollatzResearch.WordTrace tailWord_7549504 prefixEnd_7549504 430724917226770640508941 := by
  unfold tailWord_7549504
  simp only [CollatzResearch.WordTrace]
  refine ⟨137676516020721917738851783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183568688027629223651802377 137676516020721917738851783)
  ·
    refine ⟨206514774031082876608277675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137676516020721917738851783 206514774031082876608277675)
    ·
      refine ⟨309772161046624314912416513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206514774031082876608277675 309772161046624314912416513)
      ·
        refine ⟨232329120784968236184312385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309772161046624314912416513 232329120784968236184312385)
        ·
          refine ⟨174246840588726177138234289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232329120784968236184312385 174246840588726177138234289)
          ·
            refine ⟨130685130441544632853675717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174246840588726177138234289 130685130441544632853675717)
            ·
              refine ⟨24503461957789618660064197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130685130441544632853675717 24503461957789618660064197)
              ·
                refine ⟨4594399117085553498762037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24503461957789618660064197 4594399117085553498762037)
                ·
                  refine ⟨430724917226770640508941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4594399117085553498762037 430724917226770640508941)
                  ·
                    rfl

theorem cell23_7549504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 5].length) (baseStart_7549504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549504 prefixEnd_7549504 := by exact prefixLift 7549504
  have htrace : WordTrace (prefixWord ++ tailWord_7549504) baseStart_7549504 baseEnd_7549504 := by
    simpa [prefixWord, tailWord_7549504, baseEnd_7549504] using wordTrace_append hprefix tailTrace_7549504
  have hstable : (prefixWord ++ tailWord_7549504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549504).length < 2 ^ (prefixWord ++ tailWord_7549504).sum := by decide
  have hdescent : baseEnd_7549504 < baseStart_7549504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549514 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_7549514 : Nat := 118140960795 + 7549514 * 2 ^ 59
def prefixEnd_7549514 : Nat := 4983230072969 + 3 ^ 40 * 7549514 * 2
def baseEnd_7549514 : Nat := 3876529389847480725455423

theorem tailTrace_7549514 : CollatzResearch.WordTrace tailWord_7549514 prefixEnd_7549514 3876529389847480725455423 := by
  unfold tailWord_7549514
  simp only [CollatzResearch.WordTrace]
  refine ⟨68838349192851901796391899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183568931180938404790378397 68838349192851901796391899)
  ·
    refine ⟨103257523789277852694587849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68838349192851901796391899 103257523789277852694587849)
    ·
      refine ⟨77443142841958389520940887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103257523789277852694587849 77443142841958389520940887)
      ·
        refine ⟨116164714262937584281411331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77443142841958389520940887 116164714262937584281411331)
        ·
          refine ⟨174247071394406376422116997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116164714262937584281411331 174247071394406376422116997)
          ·
            refine ⟨32671325886451195579146937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174247071394406376422116997 32671325886451195579146937)
            ·
              refine ⟨24503494414838396684360203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32671325886451195579146937 24503494414838396684360203)
              ·
                refine ⟨36755241622257595026540305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24503494414838396684360203 36755241622257595026540305)
                ·
                  refine ⟨27566431216693196269905229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36755241622257595026540305 27566431216693196269905229)
                  ·
                    refine ⟨10337411706259948601214461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27566431216693196269905229 10337411706259948601214461)
                    ·
                      refine ⟨3876529389847480725455423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337411706259948601214461 3876529389847480725455423)
                      ·
                        rfl

theorem cell23_7549514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_7549514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549514 prefixEnd_7549514 := by exact prefixLift 7549514
  have htrace : WordTrace (prefixWord ++ tailWord_7549514) baseStart_7549514 baseEnd_7549514 := by
    simpa [prefixWord, tailWord_7549514, baseEnd_7549514] using wordTrace_append hprefix tailTrace_7549514
  have hstable : (prefixWord ++ tailWord_7549514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549514).length < 2 ^ (prefixWord ++ tailWord_7549514).sum := by decide
  have hdescent : baseEnd_7549514 < baseStart_7549514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549567 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_7549567 : Nat := 118140960795 + 7549567 * 2 ^ 59
def prefixEnd_7549567 : Nat := 4983230072969 + 3 ^ 40 * 7549567 * 2
def baseEnd_7549567 : Nat := 3876556604322169018092679

theorem tailTrace_7549567 : CollatzResearch.WordTrace tailWord_7549567 prefixEnd_7549567 3876556604322169018092679 := by
  unfold tailWord_7549567
  simp only [CollatzResearch.WordTrace]
  refine ⟨275355329840215597237246955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183570219893477064824831303 275355329840215597237246955)
  ·
    refine ⟨413032994760323395855870433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275355329840215597237246955 413032994760323395855870433)
    ·
      refine ⟨309774746070242546891902825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413032994760323395855870433 309774746070242546891902825)
      ·
        refine ⟨232331059552681910168927119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309774746070242546891902825 232331059552681910168927119)
        ·
          refine ⟨348496589329022865253390679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232331059552681910168927119 348496589329022865253390679)
          ·
            refine ⟨522744883993534297880086019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348496589329022865253390679 522744883993534297880086019)
            ·
              refine ⟨784117325990301446820129029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522744883993534297880086019 784117325990301446820129029)
              ·
                refine ⟨147021998623181521278774193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 784117325990301446820129029 147021998623181521278774193)
                ·
                  refine ⟨110266498967386140959080645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147021998623181521278774193 110266498967386140959080645)
                  ·
                    refine ⟨20674968556384901429827621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110266498967386140959080645 20674968556384901429827621)
                    ·
                      refine ⟨3876556604322169018092679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20674968556384901429827621 3876556604322169018092679)
                      ·
                        rfl

theorem cell23_7549567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_7549567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549567 prefixEnd_7549567 := by exact prefixLift 7549567
  have htrace : WordTrace (prefixWord ++ tailWord_7549567) baseStart_7549567 baseEnd_7549567 := by
    simpa [prefixWord, tailWord_7549567, baseEnd_7549567] using wordTrace_append hprefix tailTrace_7549567
  have hstable : (prefixWord ++ tailWord_7549567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549567).length < 2 ^ (prefixWord ++ tailWord_7549567).sum := by decide
  have hdescent : baseEnd_7549567 < baseStart_7549567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549588 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7549588 : Nat := 118140960795 + 7549588 * 2 ^ 59
def prefixEnd_7549588 : Nat := 4983230072969 + 3 ^ 40 * 7549588 * 2
def baseEnd_7549588 : Nat := 3876567387415913435930083

theorem tailTrace_7549588 : CollatzResearch.WordTrace tailWord_7549588 prefixEnd_7549588 3876567387415913435930083 := by
  unfold tailWord_7549588
  simp only [CollatzResearch.WordTrace]
  refine ⟨137678047886569758911880709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183570730515426345215840945 137678047886569758911880709)
  ·
    refine ⟨25814633978731829795977633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137678047886569758911880709 25814633978731829795977633)
    ·
      refine ⟨19360975484048872346983225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25814633978731829795977633 19360975484048872346983225)
      ·
        refine ⟨14520731613036654260237419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19360975484048872346983225 14520731613036654260237419)
        ·
          refine ⟨21781097419554981390356129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14520731613036654260237419 21781097419554981390356129)
          ·
            refine ⟨16335823064666236042767097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21781097419554981390356129 16335823064666236042767097)
            ·
              refine ⟨12251867298499677032075323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16335823064666236042767097 12251867298499677032075323)
              ·
                refine ⟨18377800947749515548112985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12251867298499677032075323 18377800947749515548112985)
                ·
                  refine ⟨13783350710812136661084739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18377800947749515548112985 13783350710812136661084739)
                  ·
                    refine ⟨20675026066218204991627109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13783350710812136661084739 20675026066218204991627109)
                    ·
                      refine ⟨3876567387415913435930083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20675026066218204991627109 3876567387415913435930083)
                      ·
                        rfl

theorem cell23_7549588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7549588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549588 prefixEnd_7549588 := by exact prefixLift 7549588
  have htrace : WordTrace (prefixWord ++ tailWord_7549588) baseStart_7549588 baseEnd_7549588 := by
    simpa [prefixWord, tailWord_7549588, baseEnd_7549588] using wordTrace_append hprefix tailTrace_7549588
  have hstable : (prefixWord ++ tailWord_7549588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549588).length < 2 ^ (prefixWord ++ tailWord_7549588).sum := by decide
  have hdescent : baseEnd_7549588 < baseStart_7549588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549591 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_7549591 : Nat := 118140960795 + 7549591 * 2 ^ 59
def prefixEnd_7549591 : Nat := 4983230072969 + 3 ^ 40 * 7549591 * 2
def baseEnd_7549591 : Nat := 3876568927857876924192569

theorem tailTrace_7549591 : CollatzResearch.WordTrace tailWord_7549591 prefixEnd_7549591 3876568927857876924192569 := by
  unfold tailWord_7549591
  simp only [CollatzResearch.WordTrace]
  refine ⟨275356205192128649336120627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183570803461419099557413751 275356205192128649336120627)
  ·
    refine ⟨413034307788192974004180941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275356205192128649336120627 413034307788192974004180941)
    ·
      refine ⟨154887865420572365251567853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413034307788192974004180941 154887865420572365251567853)
      ·
        refine ⟨58082949532714636969337945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154887865420572365251567853 58082949532714636969337945)
        ·
          refine ⟨43562212149535977727003459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58082949532714636969337945 43562212149535977727003459)
          ·
            refine ⟨65343318224303966590505189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43562212149535977727003459 65343318224303966590505189)
            ·
              refine ⟨12251872167056993735719723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65343318224303966590505189 12251872167056993735719723)
              ·
                refine ⟨18377808250585490603579585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12251872167056993735719723 18377808250585490603579585)
                ·
                  refine ⟨13783356187939117952684689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18377808250585490603579585 13783356187939117952684689)
                  ·
                    refine ⟨10337517140954338464513517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13783356187939117952684689 10337517140954338464513517)
                    ·
                      refine ⟨3876568927857876924192569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337517140954338464513517 3876568927857876924192569)
                      ·
                        rfl

theorem cell23_7549591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_7549591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549591 prefixEnd_7549591 := by exact prefixLift 7549591
  have htrace : WordTrace (prefixWord ++ tailWord_7549591) baseStart_7549591 baseEnd_7549591 := by
    simpa [prefixWord, tailWord_7549591, baseEnd_7549591] using wordTrace_append hprefix tailTrace_7549591
  have hstable : (prefixWord ++ tailWord_7549591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549591).length < 2 ^ (prefixWord ++ tailWord_7549591).sum := by decide
  have hdescent : baseEnd_7549591 < baseStart_7549591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549615 : List Nat := [1, 1, 2, 1, 2, 7, 2, 2, 1, 4]
def baseStart_7549615 : Nat := 118140960795 + 7549615 * 2 ^ 59
def prefixEnd_7549615 : Nat := 4983230072969 + 3 ^ 40 * 7549615 * 2
def baseEnd_7549615 : Nat := 1292193750464528276764153

theorem tailTrace_7549615 : CollatzResearch.WordTrace tailWord_7549615 prefixEnd_7549615 1292193750464528276764153 := by
  unfold tailWord_7549615
  simp only [CollatzResearch.WordTrace]
  refine ⟨275357080544041701434994299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183571387029361134289996199 275357080544041701434994299)
  ·
    refine ⟨413035620816062552152491449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275357080544041701434994299 413035620816062552152491449)
    ·
      refine ⟨309776715612046914114368587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413035620816062552152491449 309776715612046914114368587)
      ·
        refine ⟨464665073418070371171552881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309776715612046914114368587 464665073418070371171552881)
        ·
          refine ⟨348498805063552778378664661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464665073418070371171552881 348498805063552778378664661)
          ·
            refine ⟨8167940743677018243249953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 348498805063552778378664661 8167940743677018243249953)
            ·
              refine ⟨6125955557757763682437465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8167940743677018243249953 6125955557757763682437465)
              ·
                refine ⟨4594466668318322761828099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125955557757763682437465 4594466668318322761828099)
                ·
                  refine ⟨6891700002477484142742149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594466668318322761828099 6891700002477484142742149)
                  ·
                    refine ⟨1292193750464528276764153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6891700002477484142742149 1292193750464528276764153)
                    ·
                      rfl

theorem cell23_7549615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 1, 4].length) (baseStart_7549615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549615 prefixEnd_7549615 := by exact prefixLift 7549615
  have htrace : WordTrace (prefixWord ++ tailWord_7549615) baseStart_7549615 baseEnd_7549615 := by
    simpa [prefixWord, tailWord_7549615, baseEnd_7549615] using wordTrace_append hprefix tailTrace_7549615
  have hstable : (prefixWord ++ tailWord_7549615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549615).length < 2 ^ (prefixWord ++ tailWord_7549615).sum := by decide
  have hdescent : baseEnd_7549615 < baseStart_7549615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549655 : List Nat := [1, 1, 3, 2, 1, 5, 2, 3, 1, 1, 3]
def baseStart_7549655 : Nat := 118140960795 + 7549655 * 2 ^ 59
def prefixEnd_7549655 : Nat := 4983230072969 + 3 ^ 40 * 7549655 * 2
def baseEnd_7549655 : Nat := 3876601790619764673792275

theorem tailTrace_7549655 : CollatzResearch.WordTrace tailWord_7549655 prefixEnd_7549655 3876601790619764673792275 := by
  unfold tailWord_7549655
  simp only [CollatzResearch.WordTrace]
  refine ⟨275358539463896788266450419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183572359642597858844300279 275358539463896788266450419)
  ·
    refine ⟨413037809195845182399675629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275358539463896788266450419 413037809195845182399675629)
    ·
      refine ⟨154889178448441943399878361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413037809195845182399675629 154889178448441943399878361)
      ·
        refine ⟨116166883836331457549908771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154889178448441943399878361 116166883836331457549908771)
        ·
          refine ⟨174250325754497186324863157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116166883836331457549908771 174250325754497186324863157)
          ·
            refine ⟨16335968039484111217955921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174250325754497186324863157 16335968039484111217955921)
            ·
              refine ⟨12251976029613083413466941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16335968039484111217955921 12251976029613083413466941)
              ·
                refine ⟨4594491011104906280050103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12251976029613083413466941 4594491011104906280050103)
                ·
                  refine ⟨6891736516657359420075155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594491011104906280050103 6891736516657359420075155)
                  ·
                    refine ⟨10337604774986039130112733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6891736516657359420075155 10337604774986039130112733)
                    ·
                      refine ⟨3876601790619764673792275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337604774986039130112733 3876601790619764673792275)
                      ·
                        rfl

theorem cell23_7549655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_7549655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549655 prefixEnd_7549655 := by exact prefixLift 7549655
  have htrace : WordTrace (prefixWord ++ tailWord_7549655) baseStart_7549655 baseEnd_7549655 := by
    simpa [prefixWord, tailWord_7549655, baseEnd_7549655] using wordTrace_append hprefix tailTrace_7549655
  have hstable : (prefixWord ++ tailWord_7549655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549655).length < 2 ^ (prefixWord ++ tailWord_7549655).sum := by decide
  have hdescent : baseEnd_7549655 < baseStart_7549655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549664 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_7549664 : Nat := 118140960795 + 7549664 * 2 ^ 59
def prefixEnd_7549664 : Nat := 4983230072969 + 3 ^ 40 * 7549664 * 2
def baseEnd_7549664 : Nat := 3876606411945655138579733

theorem tailTrace_7549664 : CollatzResearch.WordTrace tailWord_7549664 prefixEnd_7549664 3876606411945655138579733 := by
  unfold tailWord_7549664
  simp only [CollatzResearch.WordTrace]
  refine ⟨137679433860432091401764023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183572578480576121869018697 137679433860432091401764023)
  ·
    refine ⟨206519150790648137102646035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137679433860432091401764023 206519150790648137102646035)
    ·
      refine ⟨309778726185972205653969053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206519150790648137102646035 309778726185972205653969053)
      ·
        refine ⟨116167022319739577120238395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309778726185972205653969053 116167022319739577120238395)
        ·
          refine ⟨174250533479609365680357593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116167022319739577120238395 174250533479609365680357593)
          ·
            refine ⟨130687900109707024260268195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174250533479609365680357593 130687900109707024260268195)
            ·
              refine ⟨196031850164560536390402293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130687900109707024260268195 196031850164560536390402293)
              ·
                refine ⟨18377985952927550286600215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196031850164560536390402293 18377985952927550286600215)
                ·
                  refine ⟨27566978929391325429900323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18377985952927550286600215 27566978929391325429900323)
                  ·
                    refine ⟨41350468394086988144850485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27566978929391325429900323 41350468394086988144850485)
                    ·
                      refine ⟨3876606411945655138579733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41350468394086988144850485 3876606411945655138579733)
                      ·
                        rfl

theorem cell23_7549664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_7549664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549664 prefixEnd_7549664 := by exact prefixLift 7549664
  have htrace : WordTrace (prefixWord ++ tailWord_7549664) baseStart_7549664 baseEnd_7549664 := by
    simpa [prefixWord, tailWord_7549664, baseEnd_7549664] using wordTrace_append hprefix tailTrace_7549664
  have hstable : (prefixWord ++ tailWord_7549664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549664).length < 2 ^ (prefixWord ++ tailWord_7549664).sum := by decide
  have hdescent : baseEnd_7549664 < baseStart_7549664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549674 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_7549674 : Nat := 118140960795 + 7549674 * 2 ^ 59
def prefixEnd_7549674 : Nat := 4983230072969 + 3 ^ 40 * 7549674 * 2
def baseEnd_7549674 : Nat := 3876611546752200099454687

theorem tailTrace_7549674 : CollatzResearch.WordTrace tailWord_7549674 prefixEnd_7549674 3876611546752200099454687 := by
  unfold tailWord_7549674
  simp only [CollatzResearch.WordTrace]
  refine ⟨68839808112706988627848019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183572821633885303007594717 68839808112706988627848019)
  ·
    refine ⟨103259712169060482941772029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68839808112706988627848019 103259712169060482941772029)
    ·
      refine ⟨38722392063397681103164511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103259712169060482941772029 38722392063397681103164511)
      ·
        refine ⟨58083588095096521654746767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38722392063397681103164511 58083588095096521654746767)
        ·
          refine ⟨87125382142644782482120151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58083588095096521654746767 87125382142644782482120151)
          ·
            refine ⟨130688073213967173723180227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87125382142644782482120151 130688073213967173723180227)
            ·
              refine ⟨196032109820950760584770341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130688073213967173723180227 196032109820950760584770341)
              ·
                refine ⟨36756020591428267609644439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196032109820950760584770341 36756020591428267609644439)
                ·
                  refine ⟨55134030887142401414466659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36756020591428267609644439 55134030887142401414466659)
                  ·
                    refine ⟨82701046330713602121699989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55134030887142401414466659 82701046330713602121699989)
                    ·
                      refine ⟨3876611546752200099454687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82701046330713602121699989 3876611546752200099454687)
                      ·
                        rfl

theorem cell23_7549674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_7549674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549674 prefixEnd_7549674 := by exact prefixLift 7549674
  have htrace : WordTrace (prefixWord ++ tailWord_7549674) baseStart_7549674 baseEnd_7549674 := by
    simpa [prefixWord, tailWord_7549674, baseEnd_7549674] using wordTrace_append hprefix tailTrace_7549674
  have hstable : (prefixWord ++ tailWord_7549674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549674).length < 2 ^ (prefixWord ++ tailWord_7549674).sum := by decide
  have hdescent : baseEnd_7549674 < baseStart_7549674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549688 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 2, 4]
def baseStart_7549688 : Nat := 118140960795 + 7549688 * 2 ^ 59
def prefixEnd_7549688 : Nat := 4983230072969 + 3 ^ 40 * 7549688 * 2
def baseEnd_7549688 : Nat := 1292206245160454348226541

theorem tailTrace_7549688 : CollatzResearch.WordTrace tailWord_7549688 prefixEnd_7549688 1292206245160454348226541 := by
  unfold tailWord_7549688
  simp only [CollatzResearch.WordTrace]
  refine ⟨137679871536388617451200859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183573162048518156601601145 137679871536388617451200859)
  ·
    refine ⟨206519807304582926176801289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137679871536388617451200859 206519807304582926176801289)
    ·
      refine ⟨154889855478437194632600967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206519807304582926176801289 154889855478437194632600967)
      ·
        refine ⟨232334783217655791948901451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154889855478437194632600967 232334783217655791948901451)
        ·
          refine ⟨348502174826483687923352177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232334783217655791948901451 348502174826483687923352177)
          ·
            refine ⟨261376631119862765942514133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348502174826483687923352177 261376631119862765942514133)
            ·
              refine ⟨6126014791871783576777675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 261376631119862765942514133 6126014791871783576777675)
              ·
                refine ⟨9189022187807675365166513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126014791871783576777675 9189022187807675365166513)
                ·
                  refine ⟨6891766640855756523874885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9189022187807675365166513 6891766640855756523874885)
                  ·
                    refine ⟨1292206245160454348226541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6891766640855756523874885 1292206245160454348226541)
                    ·
                      rfl

theorem cell23_7549688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_7549688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549688 prefixEnd_7549688 := by exact prefixLift 7549688
  have htrace : WordTrace (prefixWord ++ tailWord_7549688) baseStart_7549688 baseEnd_7549688 := by
    simpa [prefixWord, tailWord_7549688, baseEnd_7549688] using wordTrace_append hprefix tailTrace_7549688
  have hstable : (prefixWord ++ tailWord_7549688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549688).length < 2 ^ (prefixWord ++ tailWord_7549688).sum := by decide
  have hdescent : baseEnd_7549688 < baseStart_7549688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549711 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 3]
def baseStart_7549711 : Nat := 118140960795 + 7549711 * 2 ^ 59
def prefixEnd_7549711 : Nat := 4983230072969 + 3 ^ 40 * 7549711 * 2
def baseEnd_7549711 : Nat := 3876630545536416454692017

theorem tailTrace_7549711 : CollatzResearch.WordTrace tailWord_7549711 prefixEnd_7549711 3876630545536416454692017 := by
  unfold tailWord_7549711
  simp only [CollatzResearch.WordTrace]
  refine ⟨275360581951693909830488987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183573721301129273220325991 275360581951693909830488987)
  ·
    refine ⟨413040872927540864745733481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275360581951693909830488987 413040872927540864745733481)
    ·
      refine ⟨309780654695655648559300111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413040872927540864745733481 309780654695655648559300111)
      ·
        refine ⟨464670982043483472838950167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309780654695655648559300111 464670982043483472838950167)
        ·
          refine ⟨697006473065225209258425251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464670982043483472838950167 697006473065225209258425251)
          ·
            refine ⟨1045509709597837813887637877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697006473065225209258425251 1045509709597837813887637877)
            ·
              refine ⟨98016535274797295051966051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1045509709597837813887637877 98016535274797295051966051)
              ·
                refine ⟨147024802912195942577949077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98016535274797295051966051 147024802912195942577949077)
                ·
                  refine ⟨6891787636509184808341363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147024802912195942577949077 6891787636509184808341363)
                  ·
                    refine ⟨10337681454763777212512045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6891787636509184808341363 10337681454763777212512045)
                    ·
                      refine ⟨3876630545536416454692017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337681454763777212512045 3876630545536416454692017)
                      ·
                        rfl

theorem cell23_7549711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 1, 3].length) (baseStart_7549711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549711 prefixEnd_7549711 := by exact prefixLift 7549711
  have htrace : WordTrace (prefixWord ++ tailWord_7549711) baseStart_7549711 baseEnd_7549711 := by
    simpa [prefixWord, tailWord_7549711, baseEnd_7549711] using wordTrace_append hprefix tailTrace_7549711
  have hstable : (prefixWord ++ tailWord_7549711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549711).length < 2 ^ (prefixWord ++ tailWord_7549711).sum := by decide
  have hdescent : baseEnd_7549711 < baseStart_7549711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549728 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 4, 1, 3]
def baseStart_7549728 : Nat := 118140960795 + 7549728 * 2 ^ 59
def prefixEnd_7549728 : Nat := 4983230072969 + 3 ^ 40 * 7549728 * 2
def baseEnd_7549728 : Nat := 3876639274707542888179439

theorem tailTrace_7549728 : CollatzResearch.WordTrace tailWord_7549728 prefixEnd_7549728 3876639274707542888179439 := by
  unfold tailWord_7549728
  simp only [CollatzResearch.WordTrace]
  refine ⟨137680600996316160866928919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183574134661754881155905225 137680600996316160866928919)
  ·
    refine ⟨206520901494474241300393379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137680600996316160866928919 206520901494474241300393379)
    ·
      refine ⟨309781352241711361950590069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206520901494474241300393379 309781352241711361950590069)
      ·
        refine ⟨29042001772660440182867819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309781352241711361950590069 29042001772660440182867819)
        ·
          refine ⟨43563002658990660274301729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29042001772660440182867819 43563002658990660274301729)
          ·
            refine ⟨32672251994242995205726297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43563002658990660274301729 32672251994242995205726297)
            ·
              refine ⟨24504188995682246404294723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32672251994242995205726297 24504188995682246404294723)
              ·
                refine ⟨36756283493523369606442085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24504188995682246404294723 36756283493523369606442085)
                ·
                  refine ⟨6891803155035631801207891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36756283493523369606442085 6891803155035631801207891)
                  ·
                    refine ⟨10337704732553447701811837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6891803155035631801207891 10337704732553447701811837)
                    ·
                      refine ⟨3876639274707542888179439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337704732553447701811837 3876639274707542888179439)
                      ·
                        rfl

theorem cell23_7549728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_7549728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549728 prefixEnd_7549728 := by exact prefixLift 7549728
  have htrace : WordTrace (prefixWord ++ tailWord_7549728) baseStart_7549728 baseEnd_7549728 := by
    simpa [prefixWord, tailWord_7549728, baseEnd_7549728] using wordTrace_append hprefix tailTrace_7549728
  have hstable : (prefixWord ++ tailWord_7549728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549728).length < 2 ^ (prefixWord ++ tailWord_7549728).sum := by decide
  have hdescent : baseEnd_7549728 < baseStart_7549728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549744 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 2, 6]
def baseStart_7549744 : Nat := 118140960795 + 7549744 * 2 ^ 59
def prefixEnd_7549744 : Nat := 4983230072969 + 3 ^ 40 * 7549744 * 2
def baseEnd_7549744 : Nat := 1292215830132671608526455

theorem tailTrace_7549744 : CollatzResearch.WordTrace tailWord_7549744 prefixEnd_7549744 1292215830132671608526455 := by
  unfold tailWord_7549744
  simp only [CollatzResearch.WordTrace]
  refine ⟨137680892780287178233220143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183574523707049570977626857 137680892780287178233220143)
  ·
    refine ⟨206521339170430767349830215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137680892780287178233220143 206521339170430767349830215)
    ·
      refine ⟨309782008755646151024745323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206521339170430767349830215 309782008755646151024745323)
      ·
        refine ⟨464673013133469226537117985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309782008755646151024745323 464673013133469226537117985)
        ·
          refine ⟨348504759850101919902838489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464673013133469226537117985 348504759850101919902838489)
          ·
            refine ⟨261378569887576439927128867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348504759850101919902838489 261378569887576439927128867)
            ·
              refine ⟨392067854831364659890693301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261378569887576439927128867 392067854831364659890693301)
              ·
                refine ⟨36756361390440436864752497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392067854831364659890693301 36756361390440436864752497)
                ·
                  refine ⟨27567271042830327648564373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36756361390440436864752497 27567271042830327648564373)
                  ·
                    refine ⟨1292215830132671608526455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27567271042830327648564373 1292215830132671608526455)
                    ·
                      rfl

theorem cell23_7549744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_7549744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549744 prefixEnd_7549744 := by exact prefixLift 7549744
  have htrace : WordTrace (prefixWord ++ tailWord_7549744) baseStart_7549744 baseEnd_7549744 := by
    simpa [prefixWord, tailWord_7549744, baseEnd_7549744] using wordTrace_append hprefix tailTrace_7549744
  have hstable : (prefixWord ++ tailWord_7549744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549744).length < 2 ^ (prefixWord ++ tailWord_7549744).sum := by decide
  have hdescent : baseEnd_7549744 < baseStart_7549744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549768 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_7549768 : Nat := 118140960795 + 7549768 * 2 ^ 59
def prefixEnd_7549768 : Nat := 4983230072969 + 3 ^ 40 * 7549768 * 2
def baseEnd_7549768 : Nat := 3876659813933722731679255

theorem tailTrace_7549768 : CollatzResearch.WordTrace tailWord_7549768 prefixEnd_7549768 3876659813933722731679255 := by
  unfold tailWord_7549768
  simp only [CollatzResearch.WordTrace]
  refine ⟨137681330456243704282656979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183575107274991605710209305 137681330456243704282656979)
  ·
    refine ⟨206521995684365556423985469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137681330456243704282656979 206521995684365556423985469)
    ·
      refine ⟨77445748381637083658994551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206521995684365556423985469 77445748381637083658994551)
      ·
        refine ⟨116168622572455625488491827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77445748381637083658994551 116168622572455625488491827)
        ·
          refine ⟨174252933858683438232737741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116168622572455625488491827 174252933858683438232737741)
          ·
            refine ⟨65344850197006289337276653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174252933858683438232737741 65344850197006289337276653)
            ·
              refine ⟨24504318823877358501478745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65344850197006289337276653 24504318823877358501478745)
              ·
                refine ⟨18378239117908018876109059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24504318823877358501478745 18378239117908018876109059)
                ·
                  refine ⟨27567358676862028314163589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18378239117908018876109059 27567358676862028314163589)
                  ·
                    refine ⟨5168879751911630308905673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27567358676862028314163589 5168879751911630308905673)
                    ·
                      refine ⟨3876659813933722731679255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168879751911630308905673 3876659813933722731679255)
                      ·
                        rfl

theorem cell23_7549768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_7549768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549768 prefixEnd_7549768 := by exact prefixLift 7549768
  have htrace : WordTrace (prefixWord ++ tailWord_7549768) baseStart_7549768 baseEnd_7549768 := by
    simpa [prefixWord, tailWord_7549768, baseEnd_7549768] using wordTrace_append hprefix tailTrace_7549768
  have hstable : (prefixWord ++ tailWord_7549768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549768).length < 2 ^ (prefixWord ++ tailWord_7549768).sum := by decide
  have hdescent : baseEnd_7549768 < baseStart_7549768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549772 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 1, 3, 2]
def baseStart_7549772 : Nat := 118140960795 + 7549772 * 2 ^ 59
def prefixEnd_7549772 : Nat := 4983230072969 + 3 ^ 40 * 7549772 * 2
def baseEnd_7549772 : Nat := 3876661867856340716029237

theorem tailTrace_7549772 : CollatzResearch.WordTrace tailWord_7549772 prefixEnd_7549772 3876661867856340716029237 := by
  unfold tailWord_7549772
  simp only [CollatzResearch.WordTrace]
  refine ⟨137681403402236458624229785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183575204536315278165639713 137681403402236458624229785)
  ·
    refine ⟨103261052551677343968172339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137681403402236458624229785 103261052551677343968172339)
    ·
      refine ⟨154891578827516015952258509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103261052551677343968172339 154891578827516015952258509)
      ·
        refine ⟨58084342060318505982096941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154891578827516015952258509 58084342060318505982096941)
        ·
          refine ⟨21781628272619439743286353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58084342060318505982096941 21781628272619439743286353)
          ·
            refine ⟨16336221204464579807464765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21781628272619439743286353 16336221204464579807464765)
            ·
              refine ⟨6126082951674217427799287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16336221204464579807464765 6126082951674217427799287)
              ·
                refine ⟨9189124427511326141698931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126082951674217427799287 9189124427511326141698931)
                ·
                  refine ⟨13783686641266989212548397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189124427511326141698931 13783686641266989212548397)
                  ·
                    refine ⟨5168882490475120954705649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13783686641266989212548397 5168882490475120954705649)
                    ·
                      refine ⟨3876661867856340716029237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168882490475120954705649 3876661867856340716029237)
                      ·
                        rfl

theorem cell23_7549772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_7549772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549772 prefixEnd_7549772 := by exact prefixLift 7549772
  have htrace : WordTrace (prefixWord ++ tailWord_7549772) baseStart_7549772 baseEnd_7549772 := by
    simpa [prefixWord, tailWord_7549772, baseEnd_7549772] using wordTrace_append hprefix tailTrace_7549772
  have hstable : (prefixWord ++ tailWord_7549772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549772).length < 2 ^ (prefixWord ++ tailWord_7549772).sum := by decide
  have hdescent : baseEnd_7549772 < baseStart_7549772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549781 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_7549781 : Nat := 118140960795 + 7549781 * 2 ^ 59
def prefixEnd_7549781 : Nat := 4983230072969 + 3 ^ 40 * 7549781 * 2
def baseEnd_7549781 : Nat := 3876666489182231180816695

theorem tailTrace_7549781 : CollatzResearch.WordTrace tailWord_7549781 prefixEnd_7549781 3876666489182231180816695 := by
  unfold tailWord_7549781
  simp only [CollatzResearch.WordTrace]
  refine ⟨275363135061440311785537197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183575423374293541190358131 275363135061440311785537197)
  ·
    refine ⟨103261175648040116919576449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275363135061440311785537197 103261175648040116919576449)
    ·
      refine ⟨77445881736030087689682337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103261175648040116919576449 77445881736030087689682337)
      ·
        refine ⟨58084411302022565767261753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77445881736030087689682337 58084411302022565767261753)
        ·
          refine ⟨43563308476516924325446315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58084411302022565767261753 43563308476516924325446315)
          ·
            refine ⟨65344962714775386488169473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43563308476516924325446315 65344962714775386488169473)
            ·
              refine ⟨49008722036081539866127105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65344962714775386488169473 49008722036081539866127105)
              ·
                refine ⟨36756541527061154899595329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49008722036081539866127105 36756541527061154899595329)
                ·
                  refine ⟨27567406145295866174696497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36756541527061154899595329 27567406145295866174696497)
                  ·
                    refine ⟨20675554608971899631022373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27567406145295866174696497 20675554608971899631022373)
                    ·
                      refine ⟨3876666489182231180816695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20675554608971899631022373 3876666489182231180816695)
                      ·
                        rfl

theorem cell23_7549781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_7549781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549781 prefixEnd_7549781 := by exact prefixLift 7549781
  have htrace : WordTrace (prefixWord ++ tailWord_7549781) baseStart_7549781 baseEnd_7549781 := by
    simpa [prefixWord, tailWord_7549781, baseEnd_7549781] using wordTrace_append hprefix tailTrace_7549781
  have hstable : (prefixWord ++ tailWord_7549781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549781).length < 2 ^ (prefixWord ++ tailWord_7549781).sum := by decide
  have hdescent : baseEnd_7549781 < baseStart_7549781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549784 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_7549784 : Nat := 118140960795 + 7549784 * 2 ^ 59
def prefixEnd_7549784 : Nat := 4983230072969 + 3 ^ 40 * 7549784 * 2
def baseEnd_7549784 : Nat := 3876668029624194669079181

theorem tailTrace_7549784 : CollatzResearch.WordTrace tailWord_7549784 prefixEnd_7549784 3876668029624194669079181 := by
  unfold tailWord_7549784
  simp only [CollatzResearch.WordTrace]
  refine ⟨137681622240214721648948203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183575496320286295531930937 137681622240214721648948203)
  ·
    refine ⟨206522433360322082473422305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137681622240214721648948203 206522433360322082473422305)
    ·
      refine ⟨154891825020241561855066729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206522433360322082473422305 154891825020241561855066729)
      ·
        refine ⟨116168868765181171391300047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154891825020241561855066729 116168868765181171391300047)
        ·
          refine ⟨174253303147771757086950071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116168868765181171391300047 174253303147771757086950071)
          ·
            refine ⟨261379954721657635630425107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174253303147771757086950071 261379954721657635630425107)
            ·
              refine ⟨392069932082486453445637661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261379954721657635630425107 392069932082486453445637661)
              ·
                refine ⟨147026224530932420042114123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392069932082486453445637661 147026224530932420042114123)
                ·
                  refine ⟨220539336796398630063171185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147026224530932420042114123 220539336796398630063171185)
                  ·
                    refine ⟨165404502597298972547378389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220539336796398630063171185 165404502597298972547378389)
                    ·
                      refine ⟨3876668029624194669079181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165404502597298972547378389 3876668029624194669079181)
                      ·
                        rfl

theorem cell23_7549784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_7549784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549784 prefixEnd_7549784 := by exact prefixLift 7549784
  have htrace : WordTrace (prefixWord ++ tailWord_7549784) baseStart_7549784 baseEnd_7549784 := by
    simpa [prefixWord, tailWord_7549784, baseEnd_7549784] using wordTrace_append hprefix tailTrace_7549784
  have hstable : (prefixWord ++ tailWord_7549784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549784).length < 2 ^ (prefixWord ++ tailWord_7549784).sum := by decide
  have hdescent : baseEnd_7549784 < baseStart_7549784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549785 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 2, 2, 2]
def baseStart_7549785 : Nat := 118140960795 + 7549785 * 2 ^ 59
def prefixEnd_7549785 : Nat := 4983230072969 + 3 ^ 40 * 7549785 * 2
def baseEnd_7549785 : Nat := 3876668543104849165166677

theorem tailTrace_7549785 : CollatzResearch.WordTrace tailWord_7549785 prefixEnd_7549785 3876668543104849165166677 := by
  unfold tailWord_7549785
  simp only [CollatzResearch.WordTrace]
  refine ⟨275363280953425820468682809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183575520635617213645788539 275363280953425820468682809)
  ·
    refine ⟨206522460715069365351512107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275363280953425820468682809 206522460715069365351512107)
    ·
      refine ⟨309783691072604048027268161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206522460715069365351512107 309783691072604048027268161)
      ·
        refine ⟨232337768304453036020451121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309783691072604048027268161 232337768304453036020451121)
        ·
          refine ⟨174253326228339777015338341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232337768304453036020451121 174253326228339777015338341)
          ·
            refine ⟨32672498667813708190375939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174253326228339777015338341 32672498667813708190375939)
            ·
              refine ⟨49008748001720562285563909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32672498667813708190375939 49008748001720562285563909)
              ·
                refine ⟨9189140250322605428543233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49008748001720562285563909 9189140250322605428543233)
                ·
                  refine ⟨6891855187741954071407425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9189140250322605428543233 6891855187741954071407425)
                  ·
                    refine ⟨5168891390806465553555569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6891855187741954071407425 5168891390806465553555569)
                    ·
                      refine ⟨3876668543104849165166677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168891390806465553555569 3876668543104849165166677)
                      ·
                        rfl

theorem cell23_7549785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_7549785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549785 prefixEnd_7549785 := by exact prefixLift 7549785
  have htrace : WordTrace (prefixWord ++ tailWord_7549785) baseStart_7549785 baseEnd_7549785 := by
    simpa [prefixWord, tailWord_7549785, baseEnd_7549785] using wordTrace_append hprefix tailTrace_7549785
  have hstable : (prefixWord ++ tailWord_7549785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549785).length < 2 ^ (prefixWord ++ tailWord_7549785).sum := by decide
  have hdescent : baseEnd_7549785 < baseStart_7549785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549788 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_7549788 : Nat := 118140960795 + 7549788 * 2 ^ 59
def prefixEnd_7549788 : Nat := 4983230072969 + 3 ^ 40 * 7549788 * 2
def baseEnd_7549788 : Nat := 3876670083546812653429163

theorem tailTrace_7549788 : CollatzResearch.WordTrace tailWord_7549788 prefixEnd_7549788 3876670083546812653429163 := by
  unfold tailWord_7549788
  simp only [CollatzResearch.WordTrace]
  refine ⟨137681695186207475990521009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183575593581609967987361345 137681695186207475990521009)
  ·
    refine ⟨103261271389655606992890757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137681695186207475990521009 103261271389655606992890757)
    ·
      refine ⟨19361488385560426311167017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103261271389655606992890757 19361488385560426311167017)
      ·
        refine ⟨14521116289170319733375263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19361488385560426311167017 14521116289170319733375263)
        ·
          refine ⟨21781674433755479600062895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14521116289170319733375263 21781674433755479600062895)
          ·
            refine ⟨32672511650633219400094343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21781674433755479600062895 32672511650633219400094343)
            ·
              refine ⟨49008767475949829100141515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32672511650633219400094343 49008767475949829100141515)
              ·
                refine ⟨73513151213924743650212273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49008767475949829100141515 73513151213924743650212273)
                ·
                  refine ⟨55134863410443557737659205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73513151213924743650212273 55134863410443557737659205)
                  ·
                    refine ⟨10337786889458167075811101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55134863410443557737659205 10337786889458167075811101)
                    ·
                      refine ⟨3876670083546812653429163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337786889458167075811101 3876670083546812653429163)
                      ·
                        rfl

theorem cell23_7549788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_7549788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549788 prefixEnd_7549788 := by exact prefixLift 7549788
  have htrace : WordTrace (prefixWord ++ tailWord_7549788) baseStart_7549788 baseEnd_7549788 := by
    simpa [prefixWord, tailWord_7549788, baseEnd_7549788] using wordTrace_append hprefix tailTrace_7549788
  have hstable : (prefixWord ++ tailWord_7549788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549788).length < 2 ^ (prefixWord ++ tailWord_7549788).sum := by decide
  have hdescent : baseEnd_7549788 < baseStart_7549788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549841 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_7549841 : Nat := 118140960795 + 7549841 * 2 ^ 59
def prefixEnd_7549841 : Nat := 4983230072969 + 3 ^ 40 * 7549841 * 2
def baseEnd_7549841 : Nat := 3876697298021500946066419

theorem tailTrace_7549841 : CollatzResearch.WordTrace tailWord_7549841 prefixEnd_7549841 3876697298021500946066419 := by
  unfold tailWord_7549841
  simp only [CollatzResearch.WordTrace]
  refine ⟨275365323441222942032721377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183576882294148628021814251 275365323441222942032721377)
  ·
    refine ⟨206523992580917206524541033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275365323441222942032721377 206523992580917206524541033)
    ·
      refine ⟨154892994435687904893405775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206523992580917206524541033 154892994435687904893405775)
      ·
        refine ⟨232339491653531857340108663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154892994435687904893405775 232339491653531857340108663)
        ·
          refine ⟨348509237480297786010162995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232339491653531857340108663 348509237480297786010162995)
          ·
            refine ⟨522763856220446679015244493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348509237480297786010162995 522763856220446679015244493)
            ·
              refine ⟨196036446082667504630716685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522763856220446679015244493 196036446082667504630716685)
              ·
                refine ⟨73513667281000314236518757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196036446082667504630716685 73513667281000314236518757)
                ·
                  refine ⟨13783812615187558919347267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73513667281000314236518757 13783812615187558919347267)
                  ·
                    refine ⟨20675718922781338379020901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13783812615187558919347267 20675718922781338379020901)
                    ·
                      refine ⟨3876697298021500946066419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20675718922781338379020901 3876697298021500946066419)
                      ·
                        rfl

theorem cell23_7549841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_7549841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549841 prefixEnd_7549841 := by exact prefixLift 7549841
  have htrace : WordTrace (prefixWord ++ tailWord_7549841) baseStart_7549841 baseEnd_7549841 := by
    simpa [prefixWord, tailWord_7549841, baseEnd_7549841] using wordTrace_append hprefix tailTrace_7549841
  have hstable : (prefixWord ++ tailWord_7549841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549841).length < 2 ^ (prefixWord ++ tailWord_7549841).sum := by decide
  have hdescent : baseEnd_7549841 < baseStart_7549841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549858 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_7549858 : Nat := 118140960795 + 7549858 * 2 ^ 59
def prefixEnd_7549858 : Nat := 4983230072969 + 3 ^ 40 * 7549858 * 2
def baseEnd_7549858 : Nat := 3876706027192627379553841

theorem tailTrace_7549858 : CollatzResearch.WordTrace tailWord_7549858 prefixEnd_7549858 3876706027192627379553841 := by
  unfold tailWord_7549858
  simp only [CollatzResearch.WordTrace]
  refine ⟨68841485870540338484022557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183577295654774235957393485 68841485870540338484022557)
  ·
    refine ⟨25815557201452626931508459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68841485870540338484022557 25815557201452626931508459)
    ·
      refine ⟨38723335802178940397262689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25815557201452626931508459 38723335802178940397262689)
      ·
        refine ⟨29042501851634205297947017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38723335802178940397262689 29042501851634205297947017)
        ·
          refine ⟨21781876388725653973460263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29042501851634205297947017 21781876388725653973460263)
          ·
            refine ⟨32672814583088480960190395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21781876388725653973460263 32672814583088480960190395)
            ·
              refine ⟨49009221874632721440285593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32672814583088480960190395 49009221874632721440285593)
              ·
                refine ⟨36756916405974541080214195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49009221874632721440285593 36756916405974541080214195)
                ·
                  refine ⟨55135374608961811620321293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36756916405974541080214195 55135374608961811620321293)
                  ·
                    refine ⟨20675765478360679357620485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55135374608961811620321293 20675765478360679357620485)
                    ·
                      refine ⟨3876706027192627379553841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20675765478360679357620485 3876706027192627379553841)
                      ·
                        rfl

theorem cell23_7549858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_7549858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549858 prefixEnd_7549858 := by exact prefixLift 7549858
  have htrace : WordTrace (prefixWord ++ tailWord_7549858) baseStart_7549858 baseEnd_7549858 := by
    simpa [prefixWord, tailWord_7549858, baseEnd_7549858] using wordTrace_append hprefix tailTrace_7549858
  have hstable : (prefixWord ++ tailWord_7549858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549858).length < 2 ^ (prefixWord ++ tailWord_7549858).sum := by decide
  have hdescent : baseEnd_7549858 < baseStart_7549858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549881 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 8]
def baseStart_7549881 : Nat := 118140960795 + 7549881 * 2 ^ 59
def prefixEnd_7549881 : Nat := 4983230072969 + 3 ^ 40 * 7549881 * 2
def baseEnd_7549881 : Nat := 430746426360853421062915

theorem tailTrace_7549881 : CollatzResearch.WordTrace tailWord_7549881 prefixEnd_7549881 430746426360853421062915 := by
  unfold tailWord_7549881
  simp only [CollatzResearch.WordTrace]
  refine ⟨275366782361078028864177497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183577854907385352576118331 275366782361078028864177497)
  ·
    refine ⟨206525086770808521648133123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275366782361078028864177497 206525086770808521648133123)
    ·
      refine ⟨309787630156212782472199685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206525086770808521648133123 309787630156212782472199685)
      ·
        refine ⟨58085180654289896713537441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309787630156212782472199685 58085180654289896713537441)
        ·
          refine ⟨43563885490717422535153081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58085180654289896713537441 43563885490717422535153081)
          ·
            refine ⟨32672914118038066901364811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43563885490717422535153081 32672914118038066901364811)
            ·
              refine ⟨49009371177057100352047217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32672914118038066901364811 49009371177057100352047217)
              ·
                refine ⟨36757028382792825264035413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49009371177057100352047217 36757028382792825264035413)
                ·
                  refine ⟨430746426360853421062915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36757028382792825264035413 430746426360853421062915)
                  ·
                    rfl

theorem cell23_7549881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 8].length) (baseStart_7549881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549881 prefixEnd_7549881 := by exact prefixLift 7549881
  have htrace : WordTrace (prefixWord ++ tailWord_7549881) baseStart_7549881 baseEnd_7549881 := by
    simpa [prefixWord, tailWord_7549881, baseEnd_7549881] using wordTrace_append hprefix tailTrace_7549881
  have hstable : (prefixWord ++ tailWord_7549881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549881).length < 2 ^ (prefixWord ++ tailWord_7549881).sum := by decide
  have hdescent : baseEnd_7549881 < baseStart_7549881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549891 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 3]
def baseStart_7549891 : Nat := 118140960795 + 7549891 * 2 ^ 59
def prefixEnd_7549891 : Nat := 4983230072969 + 3 ^ 40 * 7549891 * 2
def baseEnd_7549891 : Nat := 3876722972054225750441189

theorem tailTrace_7549891 : CollatzResearch.WordTrace tailWord_7549891 prefixEnd_7549891 3876722972054225750441189 := by
  unfold tailWord_7549891
  simp only [CollatzResearch.WordTrace]
  refine ⟨275367147091041800572041527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183578098060694533714694351 275367147091041800572041527)
  ·
    refine ⟨413050720636562700858062291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275367147091041800572041527 413050720636562700858062291)
    ·
      refine ⟨619576080954844051287093437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413050720636562700858062291 619576080954844051287093437)
      ·
        refine ⟨232341030358066519232660039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 619576080954844051287093437 232341030358066519232660039)
        ·
          refine ⟨348511545537099778848990059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232341030358066519232660039 348511545537099778848990059)
          ·
            refine ⟨522767318305649668273485089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348511545537099778848990059 522767318305649668273485089)
            ·
              refine ⟨392075488729237251205113817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522767318305649668273485089 392075488729237251205113817)
              ·
                refine ⟨294056616546927938403835363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392075488729237251205113817 294056616546927938403835363)
                ·
                  refine ⟨441084924820391907605753045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294056616546927938403835363 441084924820391907605753045)
                  ·
                    refine ⟨10337927925477935334509837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 441084924820391907605753045 10337927925477935334509837)
                    ·
                      refine ⟨3876722972054225750441189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10337927925477935334509837 3876722972054225750441189)
                      ·
                        rfl

theorem cell23_7549891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_7549891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549891 prefixEnd_7549891 := by exact prefixLift 7549891
  have htrace : WordTrace (prefixWord ++ tailWord_7549891) baseStart_7549891 baseEnd_7549891 := by
    simpa [prefixWord, tailWord_7549891, baseEnd_7549891] using wordTrace_append hprefix tailTrace_7549891
  have hstable : (prefixWord ++ tailWord_7549891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549891).length < 2 ^ (prefixWord ++ tailWord_7549891).sum := by decide
  have hdescent : baseEnd_7549891 < baseStart_7549891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549892 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_7549892 : Nat := 118140960795 + 7549892 * 2 ^ 59
def prefixEnd_7549892 : Nat := 4983230072969 + 3 ^ 40 * 7549892 * 2
def baseEnd_7549892 : Nat := 3876723485534880246528685

theorem tailTrace_7549892 : CollatzResearch.WordTrace tailWord_7549892 prefixEnd_7549892 3876723485534880246528685 := by
  unfold tailWord_7549892
  simp only [CollatzResearch.WordTrace]
  refine ⟨137683591782019088871413965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183578122376025451828551953 137683591782019088871413965)
  ·
    refine ⟨51631346918257158326780237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137683591782019088871413965 51631346918257158326780237)
    ·
      refine ⟨19361755094346434372542589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51631346918257158326780237 19361755094346434372542589)
      ·
        refine ⟨7260658160379912889703471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19361755094346434372542589 7260658160379912889703471)
        ·
          refine ⟨10890987240569869334555207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7260658160379912889703471 10890987240569869334555207)
          ·
            refine ⟨16336480860854804001832811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10890987240569869334555207 16336480860854804001832811)
            ·
              refine ⟨24504721291282206002749217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16336480860854804001832811 24504721291282206002749217)
              ·
                refine ⟨18378540968461654502061913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24504721291282206002749217 18378540968461654502061913)
                ·
                  refine ⟨13783905726346240876546435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18378540968461654502061913 13783905726346240876546435)
                  ·
                    refine ⟨20675858589519361314819653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13783905726346240876546435 20675858589519361314819653)
                    ·
                      refine ⟨3876723485534880246528685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20675858589519361314819653 3876723485534880246528685)
                      ·
                        rfl

theorem cell23_7549892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_7549892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549892 prefixEnd_7549892 := by exact prefixLift 7549892
  have htrace : WordTrace (prefixWord ++ tailWord_7549892) baseStart_7549892 baseEnd_7549892 := by
    simpa [prefixWord, tailWord_7549892, baseEnd_7549892] using wordTrace_append hprefix tailTrace_7549892
  have hstable : (prefixWord ++ tailWord_7549892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549892).length < 2 ^ (prefixWord ++ tailWord_7549892).sum := by decide
  have hdescent : baseEnd_7549892 < baseStart_7549892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549935 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 2, 3, 2]
def baseStart_7549935 : Nat := 118140960795 + 7549935 * 2 ^ 59
def prefixEnd_7549935 : Nat := 4983230072969 + 3 ^ 40 * 7549935 * 2
def baseEnd_7549935 : Nat := 3876745565203023578290987

theorem tailTrace_7549935 : CollatzResearch.WordTrace tailWord_7549935 prefixEnd_7549935 3876745565203023578290987 := by
  unfold tailWord_7549935
  simp only [CollatzResearch.WordTrace]
  refine ⟨275368751902882396086643259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183579167935254930724428839 275368751902882396086643259)
  ·
    refine ⟨413053127854323594129964889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275368751902882396086643259 413053127854323594129964889)
    ·
      refine ⟨309789845890742695597473667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413053127854323594129964889 309789845890742695597473667)
      ·
        refine ⟨464684768836114043396210501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309789845890742695597473667 464684768836114043396210501)
        ·
          refine ⟨87128394156771383136789469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464684768836114043396210501 87128394156771383136789469)
          ·
            refine ⟨32673147808789268676296051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87128394156771383136789469 32673147808789268676296051)
            ·
              refine ⟨49009721713183903014444077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32673147808789268676296051 49009721713183903014444077)
              ·
                refine ⟨18378645642443963630416529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49009721713183903014444077 18378645642443963630416529)
                ·
                  refine ⟨13783984231832972722812397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18378645642443963630416529 13783984231832972722812397)
                  ·
                    refine ⟨5168994086937364771054649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13783984231832972722812397 5168994086937364771054649)
                    ·
                      refine ⟨3876745565203023578290987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5168994086937364771054649 3876745565203023578290987)
                      ·
                        rfl

theorem cell23_7549935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 3, 2].length) (baseStart_7549935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549935 prefixEnd_7549935 := by exact prefixLift 7549935
  have htrace : WordTrace (prefixWord ++ tailWord_7549935) baseStart_7549935 baseEnd_7549935 := by
    simpa [prefixWord, tailWord_7549935, baseEnd_7549935] using wordTrace_append hprefix tailTrace_7549935
  have hstable : (prefixWord ++ tailWord_7549935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549935).length < 2 ^ (prefixWord ++ tailWord_7549935).sum := by decide
  have hdescent : baseEnd_7549935 < baseStart_7549935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549945 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 1, 5]
def baseStart_7549945 : Nat := 118140960795 + 7549945 * 2 ^ 59
def prefixEnd_7549945 : Nat := 4983230072969 + 3 ^ 40 * 7549945 * 2
def baseEnd_7549945 : Nat := 1292250233336522846388647

theorem tailTrace_7549945 : CollatzResearch.WordTrace tailWord_7549945 prefixEnd_7549945 1292250233336522846388647 := by
  unfold tailWord_7549945
  simp only [CollatzResearch.WordTrace]
  refine ⟨275369116632846167794507289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183579411088564111863004859 275369116632846167794507289)
  ·
    refine ⟨206526837474634625845880467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275369116632846167794507289 206526837474634625845880467)
    ·
      refine ⟨309790256211951938768820701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206526837474634625845880467 309790256211951938768820701)
      ·
        refine ⟨116171346079481977038307763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309790256211951938768820701 116171346079481977038307763)
        ·
          refine ⟨174257019119222965557461645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116171346079481977038307763 174257019119222965557461645)
          ·
            refine ⟨65346382169708612084048117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174257019119222965557461645 65346382169708612084048117)
            ·
              refine ⟨6126223328410182382879511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65346382169708612084048117 6126223328410182382879511)
              ·
                refine ⟨9189334992615273574319267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126223328410182382879511 9189334992615273574319267)
                ·
                  refine ⟨13784002488922910361478901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189334992615273574319267 13784002488922910361478901)
                  ·
                    refine ⟨1292250233336522846388647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13784002488922910361478901 1292250233336522846388647)
                    ·
                      rfl

theorem cell23_7549945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 5].length) (baseStart_7549945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549945 prefixEnd_7549945 := by exact prefixLift 7549945
  have htrace : WordTrace (prefixWord ++ tailWord_7549945) baseStart_7549945 baseEnd_7549945 := by
    simpa [prefixWord, tailWord_7549945, baseEnd_7549945] using wordTrace_append hprefix tailTrace_7549945
  have hstable : (prefixWord ++ tailWord_7549945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549945).length < 2 ^ (prefixWord ++ tailWord_7549945).sum := by decide
  have hdescent : baseEnd_7549945 < baseStart_7549945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549961 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_7549961 : Nat := 118140960795 + 7549961 * 2 ^ 59
def prefixEnd_7549961 : Nat := 4983230072969 + 3 ^ 40 * 7549961 * 2
def baseEnd_7549961 : Nat := 3876758915700040476565867

theorem tailTrace_7549961 : CollatzResearch.WordTrace tailWord_7549961 prefixEnd_7549961 3876758915700040476565867 := by
  unfold tailWord_7549961
  simp only [CollatzResearch.WordTrace]
  refine ⟨275369700200788202527089737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183579800133858801684726491 275369700200788202527089737)
  ·
    refine ⟨206527275150591151895317303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275369700200788202527089737 206527275150591151895317303)
    ·
      refine ⟨309790912725886727842975955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206527275150591151895317303 309790912725886727842975955)
      ·
        refine ⟨464686369088830091764463933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309790912725886727842975955 464686369088830091764463933)
        ·
          refine ⟨174257388408311284411673975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464686369088830091764463933 174257388408311284411673975)
          ·
            refine ⟨261386082612466926617510963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174257388408311284411673975 261386082612466926617510963)
            ·
              refine ⟨392079123918700389926266445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261386082612466926617510963 392079123918700389926266445)
              ·
                refine ⟨147029671469512646222349917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392079123918700389926266445 147029671469512646222349917)
                ·
                  refine ⟨55136126801067242333381219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147029671469512646222349917 55136126801067242333381219)
                  ·
                    refine ⟨82704190201600863500071829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55136126801067242333381219 82704190201600863500071829)
                    ·
                      refine ⟨3876758915700040476565867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82704190201600863500071829 3876758915700040476565867)
                      ·
                        rfl

theorem cell23_7549961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_7549961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549961 prefixEnd_7549961 := by exact prefixLift 7549961
  have htrace : WordTrace (prefixWord ++ tailWord_7549961) baseStart_7549961 baseEnd_7549961 := by
    simpa [prefixWord, tailWord_7549961, baseEnd_7549961] using wordTrace_append hprefix tailTrace_7549961
  have hstable : (prefixWord ++ tailWord_7549961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549961).length < 2 ^ (prefixWord ++ tailWord_7549961).sum := by decide
  have hdescent : baseEnd_7549961 < baseStart_7549961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549975 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 1, 6]
def baseStart_7549975 : Nat := 118140960795 + 7549975 * 2 ^ 59
def prefixEnd_7549975 : Nat := 4983230072969 + 3 ^ 40 * 7549975 * 2
def baseEnd_7549975 : Nat := 1292255368143067807263601

theorem tailTrace_7549975 : CollatzResearch.WordTrace tailWord_7549975 prefixEnd_7549975 1292255368143067807263601 := by
  unfold tailWord_7549975
  simp only [CollatzResearch.WordTrace]
  refine ⟨275370210822737482918099379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183580140548491655278732919 275370210822737482918099379)
  ·
    refine ⟨413055316234106224377149069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275370210822737482918099379 413055316234106224377149069)
    ·
      refine ⟨154895743587789834141430901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413055316234106224377149069 154895743587789834141430901)
      ·
        refine ⟨14521475961355296950759147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154895743587789834141430901 14521475961355296950759147)
        ·
          refine ⟨21782213942032945426138721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14521475961355296950759147 21782213942032945426138721)
          ·
            refine ⟨16336660456524709069604041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21782213942032945426138721 16336660456524709069604041)
            ·
              refine ⟨12252495342393531802203031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16336660456524709069604041 12252495342393531802203031)
              ·
                refine ⟨18378743013590297703304547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12252495342393531802203031 18378743013590297703304547)
                ·
                  refine ⟨27568114520385446554956821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18378743013590297703304547 27568114520385446554956821)
                  ·
                    refine ⟨1292255368143067807263601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27568114520385446554956821 1292255368143067807263601)
                    ·
                      rfl

theorem cell23_7549975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_7549975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549975 prefixEnd_7549975 := by exact prefixLift 7549975
  have htrace : WordTrace (prefixWord ++ tailWord_7549975) baseStart_7549975 baseEnd_7549975 := by
    simpa [prefixWord, tailWord_7549975, baseEnd_7549975] using wordTrace_append hprefix tailTrace_7549975
  have hstable : (prefixWord ++ tailWord_7549975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549975).length < 2 ^ (prefixWord ++ tailWord_7549975).sum := by decide
  have hdescent : baseEnd_7549975 < baseStart_7549975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7549985 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_7549985 : Nat := 118140960795 + 7549985 * 2 ^ 59
def prefixEnd_7549985 : Nat := 4983230072969 + 3 ^ 40 * 7549985 * 2
def baseEnd_7549985 : Nat := 3876771239235748382665757

theorem tailTrace_7549985 : CollatzResearch.WordTrace tailWord_7549985 prefixEnd_7549985 3876771239235748382665757 := by
  unfold tailWord_7549985
  simp only [CollatzResearch.WordTrace]
  refine ⟨275370575552701254625963409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183580383701800836417308939 275370575552701254625963409)
  ·
    refine ⟨206527931664525940969472557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275370575552701254625963409 206527931664525940969472557)
    ·
      refine ⟨77447974374197227863552209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206527931664525940969472557 77447974374197227863552209)
      ·
        refine ⟨58085980780647920897664157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77447974374197227863552209 58085980780647920897664157)
        ·
          refine ⟨21782242792742970336624059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58085980780647920897664157 21782242792742970336624059)
          ·
            refine ⟨32673364189114455504936089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21782242792742970336624059 32673364189114455504936089)
            ·
              refine ⟨24505023141835841628702067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32673364189114455504936089 24505023141835841628702067)
              ·
                refine ⟨36757534712753762443053101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24505023141835841628702067 36757534712753762443053101)
                ·
                  refine ⟨13784075517282660916144913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36757534712753762443053101 13784075517282660916144913)
                  ·
                    refine ⟨10338056637961995687108685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13784075517282660916144913 10338056637961995687108685)
                    ·
                      refine ⟨3876771239235748382665757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10338056637961995687108685 3876771239235748382665757)
                      ·
                        rfl

theorem cell23_7549985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_7549985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7549985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7549985 prefixEnd_7549985 := by exact prefixLift 7549985
  have htrace : WordTrace (prefixWord ++ tailWord_7549985) baseStart_7549985 baseEnd_7549985 := by
    simpa [prefixWord, tailWord_7549985, baseEnd_7549985] using wordTrace_append hprefix tailTrace_7549985
  have hstable : (prefixWord ++ tailWord_7549985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7549985).length < 2 ^ (prefixWord ++ tailWord_7549985).sum := by decide
  have hdescent : baseEnd_7549985 < baseStart_7549985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7549985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550011 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 7]
def baseStart_7550011 : Nat := 118140960795 + 7550011 * 2 ^ 59
def prefixEnd_7550011 : Nat := 4983230072969 + 3 ^ 40 * 7550011 * 2
def baseEnd_7550011 : Nat := 3876784589732765280940637

theorem tailTrace_7550011 : CollatzResearch.WordTrace tailWord_7550011 prefixEnd_7550011 3876784589732765280940637 := by
  unfold tailWord_7550011
  simp only [CollatzResearch.WordTrace]
  refine ⟨275371523850607061066409887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183581015900404707377606591 275371523850607061066409887)
  ·
    refine ⟨413057285775910591599614831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275371523850607061066409887 413057285775910591599614831)
    ·
      refine ⟨619585928663865887399422247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413057285775910591599614831 619585928663865887399422247)
      ·
        refine ⟨929378892995798831099133371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619585928663865887399422247 929378892995798831099133371)
        ·
          refine ⟨1394068339493698246648700057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929378892995798831099133371 1394068339493698246648700057)
          ·
            refine ⟨1045551254620273684986525043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394068339493698246648700057 1045551254620273684986525043)
            ·
              refine ⟨1568326881930410527479787565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045551254620273684986525043 1568326881930410527479787565)
              ·
                refine ⟨588122580723903947804920337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1568326881930410527479787565 588122580723903947804920337)
                ·
                  refine ⟨441091935542927960853690253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588122580723903947804920337 441091935542927960853690253)
                  ·
                    refine ⟨165409475828597985320133845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441091935542927960853690253 165409475828597985320133845)
                    ·
                      refine ⟨3876784589732765280940637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165409475828597985320133845 3876784589732765280940637)
                      ·
                        rfl

theorem cell23_7550011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_7550011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550011 prefixEnd_7550011 := by exact prefixLift 7550011
  have htrace : WordTrace (prefixWord ++ tailWord_7550011) baseStart_7550011 baseEnd_7550011 := by
    simpa [prefixWord, tailWord_7550011, baseEnd_7550011] using wordTrace_append hprefix tailTrace_7550011
  have hstable : (prefixWord ++ tailWord_7550011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550011).length < 2 ^ (prefixWord ++ tailWord_7550011).sum := by decide
  have hdescent : baseEnd_7550011 < baseStart_7550011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550025 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 3, 3, 2]
def baseStart_7550025 : Nat := 118140960795 + 7550025 * 2 ^ 59
def prefixEnd_7550025 : Nat := 4983230072969 + 3 ^ 40 * 7550025 * 2
def baseEnd_7550025 : Nat := 3876791778461928226165573

theorem tailTrace_7550025 : CollatzResearch.WordTrace tailWord_7550025 prefixEnd_7550025 3876791778461928226165573 := by
  unfold tailWord_7550025
  simp only [CollatzResearch.WordTrace]
  refine ⟨275372034472556341457419529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183581356315037560971613019 275372034472556341457419529)
  ·
    refine ⟨206529025854417256093064647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275372034472556341457419529 206529025854417256093064647)
    ·
      refine ⟨309793538781625884139596971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206529025854417256093064647 309793538781625884139596971)
      ·
        refine ⟨464690308172438826209395457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309793538781625884139596971 464690308172438826209395457)
        ·
          refine ⟨348517731129329119657046593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464690308172438826209395457 348517731129329119657046593)
          ·
            refine ⟨261388298346996839742784945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348517731129329119657046593 261388298346996839742784945)
            ·
              refine ⟨196041223760247629807088709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261388298346996839742784945 196041223760247629807088709)
              ·
                refine ⟨36757729455046430588829133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196041223760247629807088709 36757729455046430588829133)
                ·
                  refine ⟨13784148545642411470810925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36757729455046430588829133 13784148545642411470810925)
                  ·
                    refine ⟨5169055704615904301554097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13784148545642411470810925 5169055704615904301554097)
                    ·
                      refine ⟨3876791778461928226165573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169055704615904301554097 3876791778461928226165573)
                      ·
                        rfl

theorem cell23_7550025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 3, 2].length) (baseStart_7550025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550025 prefixEnd_7550025 := by exact prefixLift 7550025
  have htrace : WordTrace (prefixWord ++ tailWord_7550025) baseStart_7550025 baseEnd_7550025 := by
    simpa [prefixWord, tailWord_7550025, baseEnd_7550025] using wordTrace_append hprefix tailTrace_7550025
  have hstable : (prefixWord ++ tailWord_7550025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550025).length < 2 ^ (prefixWord ++ tailWord_7550025).sum := by decide
  have hdescent : baseEnd_7550025 < baseStart_7550025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550072 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 4, 2, 2]
def baseStart_7550072 : Nat := 118140960795 + 7550072 * 2 ^ 59
def prefixEnd_7550072 : Nat := 4983230072969 + 3 ^ 40 * 7550072 * 2
def baseEnd_7550072 : Nat := 3876815912052689542277857

theorem tailTrace_7550072 : CollatzResearch.WordTrace tailWord_7550072 prefixEnd_7550072 3876815912052689542277857 := by
  unfold tailWord_7550072
  simp only [CollatzResearch.WordTrace]
  refine ⟨137686874351693034242190235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183582499135590712322920313 137686874351693034242190235)
  ·
    refine ⟨206530311527539551363285353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137686874351693034242190235 206530311527539551363285353)
    ·
      refine ⟨154897733645654663522464015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206530311527539551363285353 154897733645654663522464015)
      ·
        refine ⟨232346600468481995283696023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154897733645654663522464015 232346600468481995283696023)
        ·
          refine ⟨348519900702722992925544035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232346600468481995283696023 348519900702722992925544035)
          ·
            refine ⟨522779851054084489388316053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348519900702722992925544035 522779851054084489388316053)
            ·
              refine ⟨24505305518160210440077315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 522779851054084489388316053 24505305518160210440077315)
              ·
                refine ⟨36757958277240315660115973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24505305518160210440077315 36757958277240315660115973)
                ·
                  refine ⟨6892117176982559186271745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36757958277240315660115973 6892117176982559186271745)
                  ·
                    refine ⟨5169087882736919389703809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6892117176982559186271745 5169087882736919389703809)
                    ·
                      refine ⟨3876815912052689542277857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169087882736919389703809 3876815912052689542277857)
                      ·
                        rfl

theorem cell23_7550072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_7550072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550072 prefixEnd_7550072 := by exact prefixLift 7550072
  have htrace : WordTrace (prefixWord ++ tailWord_7550072) baseStart_7550072 baseEnd_7550072 := by
    simpa [prefixWord, tailWord_7550072, baseEnd_7550072] using wordTrace_append hprefix tailTrace_7550072
  have hstable : (prefixWord ++ tailWord_7550072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550072).length < 2 ^ (prefixWord ++ tailWord_7550072).sum := by decide
  have hdescent : baseEnd_7550072 < baseStart_7550072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550089 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 2, 2, 2]
def baseStart_7550089 : Nat := 118140960795 + 7550089 * 2 ^ 59
def prefixEnd_7550089 : Nat := 4983230072969 + 3 ^ 40 * 7550089 * 2
def baseEnd_7550089 : Nat := 3876824641223815975765279

theorem tailTrace_7550089 : CollatzResearch.WordTrace tailWord_7550089 prefixEnd_7550089 3876824641223815975765279 := by
  unfold tailWord_7550089
  simp only [CollatzResearch.WordTrace]
  refine ⟨275374368744324480387749321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183582912496216320258499547 275374368744324480387749321)
  ·
    refine ⟨206530776558243360290811991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275374368744324480387749321 206530776558243360290811991)
    ·
      refine ⟨309796164837365040436217987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206530776558243360290811991 309796164837365040436217987)
      ·
        refine ⟨464694247256047560654326981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309796164837365040436217987 464694247256047560654326981)
        ·
          refine ⟨87130171360508917622686309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464694247256047560654326981 87130171360508917622686309)
          ·
            refine ⟨16336907130095422054253683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87130171360508917622686309 16336907130095422054253683)
            ·
              refine ⟨24505360695143133081380525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16336907130095422054253683 24505360695143133081380525)
              ·
                refine ⟨9189510260678674905517697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24505360695143133081380525 9189510260678674905517697)
                ·
                  refine ⟨6892132695509006179138273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9189510260678674905517697 6892132695509006179138273)
                  ·
                    refine ⟨5169099521631754634353705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6892132695509006179138273 5169099521631754634353705)
                    ·
                      refine ⟨3876824641223815975765279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169099521631754634353705 3876824641223815975765279)
                      ·
                        rfl

theorem cell23_7550089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 2, 2].length) (baseStart_7550089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550089 prefixEnd_7550089 := by exact prefixLift 7550089
  have htrace : WordTrace (prefixWord ++ tailWord_7550089) baseStart_7550089 baseEnd_7550089 := by
    simpa [prefixWord, tailWord_7550089, baseEnd_7550089] using wordTrace_append hprefix tailTrace_7550089
  have hstable : (prefixWord ++ tailWord_7550089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550089).length < 2 ^ (prefixWord ++ tailWord_7550089).sum := by decide
  have hdescent : baseEnd_7550089 < baseStart_7550089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550115 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 4, 5, 2]
def baseStart_7550115 : Nat := 118140960795 + 7550115 * 2 ^ 59
def prefixEnd_7550115 : Nat := 4983230072969 + 3 ^ 40 * 7550115 * 2
def baseEnd_7550115 : Nat := 3876837991720832874040159

theorem tailTrace_7550115 : CollatzResearch.WordTrace tailWord_7550115 prefixEnd_7550115 3876837991720832874040159 := by
  unfold tailWord_7550115
  simp only [CollatzResearch.WordTrace]
  refine ⟨275375317042230286828195799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183583544694820191218797199 275375317042230286828195799)
  ·
    refine ⟨413062975563345430242293699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275375317042230286828195799 413062975563345430242293699)
    ·
      refine ⟨619594463345018145363440549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413062975563345430242293699 619594463345018145363440549)
      ·
        refine ⟨116173961877190902255645103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 619594463345018145363440549 116173961877190902255645103)
        ·
          refine ⟨174260942815786353383467655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116173961877190902255645103 174260942815786353383467655)
          ·
            refine ⟨261391414223679530075201483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174260942815786353383467655 261391414223679530075201483)
            ·
              refine ⟨392087121335519295112802225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261391414223679530075201483 392087121335519295112802225)
              ·
                refine ⟨294065341001639471334601669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 392087121335519295112802225 294065341001639471334601669)
                ·
                  refine ⟨55137251437807400875237813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294065341001639471334601669 55137251437807400875237813)
                  ·
                    refine ⟨5169117322294443832053545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55137251437807400875237813 5169117322294443832053545)
                    ·
                      refine ⟨3876837991720832874040159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169117322294443832053545 3876837991720832874040159)
                      ·
                        rfl

theorem cell23_7550115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_7550115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550115 prefixEnd_7550115 := by exact prefixLift 7550115
  have htrace : WordTrace (prefixWord ++ tailWord_7550115) baseStart_7550115 baseEnd_7550115 := by
    simpa [prefixWord, tailWord_7550115, baseEnd_7550115] using wordTrace_append hprefix tailTrace_7550115
  have hstable : (prefixWord ++ tailWord_7550115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550115).length < 2 ^ (prefixWord ++ tailWord_7550115).sum := by decide
  have hdescent : baseEnd_7550115 < baseStart_7550115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550129 : List Nat := [1, 2, 2, 5, 1, 1, 4, 2, 5]
def baseStart_7550129 : Nat := 118140960795 + 7550129 * 2 ^ 59
def prefixEnd_7550129 : Nat := 4983230072969 + 3 ^ 40 * 7550129 * 2
def baseEnd_7550129 : Nat := 430760575605555091029455

theorem tailTrace_7550129 : CollatzResearch.WordTrace tailWord_7550129 prefixEnd_7550129 430760575605555091029455 := by
  unfold tailWord_7550129
  simp only [CollatzResearch.WordTrace]
  refine ⟨275375827664179567219205441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183583885109453044812803627 275375827664179567219205441)
  ·
    refine ⟨206531870748134675414404081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275375827664179567219205441 206531870748134675414404081)
    ·
      refine ⟨154898903061101006560803061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206531870748134675414404081 154898903061101006560803061)
      ·
        refine ⟨14521772161978219365075287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154898903061101006560803061 14521772161978219365075287)
        ·
          refine ⟨21782658242967329047612931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14521772161978219365075287 21782658242967329047612931)
          ·
            refine ⟨32673987364450993571419397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21782658242967329047612931 32673987364450993571419397)
            ·
              refine ⟨6126372630834561294641137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32673987364450993571419397 6126372630834561294641137)
              ·
                refine ⟨4594779473125920970980853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6126372630834561294641137 4594779473125920970980853)
                ·
                  refine ⟨430760575605555091029455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4594779473125920970980853 430760575605555091029455)
                  ·
                    rfl

theorem cell23_7550129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 5].length) (baseStart_7550129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550129 prefixEnd_7550129 := by exact prefixLift 7550129
  have htrace : WordTrace (prefixWord ++ tailWord_7550129) baseStart_7550129 baseEnd_7550129 := by
    simpa [prefixWord, tailWord_7550129, baseEnd_7550129] using wordTrace_append hprefix tailTrace_7550129
  have hstable : (prefixWord ++ tailWord_7550129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550129).length < 2 ^ (prefixWord ++ tailWord_7550129).sum := by decide
  have hdescent : baseEnd_7550129 < baseStart_7550129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550138 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_7550138 : Nat := 118140960795 + 7550138 * 2 ^ 59
def prefixEnd_7550138 : Nat := 4983230072969 + 3 ^ 40 * 7550138 * 2
def baseEnd_7550138 : Nat := 1292283267258628761350851

theorem tailTrace_7550138 : CollatzResearch.WordTrace tailWord_7550138 prefixEnd_7550138 1292283267258628761350851 := by
  unfold tailWord_7550138
  simp only [CollatzResearch.WordTrace]
  refine ⟨68844038980286740439070767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183584103947431307837522045 68844038980286740439070767)
  ·
    refine ⟨103266058470430110658606151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68844038980286740439070767 103266058470430110658606151)
    ·
      refine ⟨154899087705645165987909227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103266058470430110658606151 154899087705645165987909227)
      ·
        refine ⟨232348631558467748981863841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154899087705645165987909227 232348631558467748981863841)
        ·
          refine ⟨174261473668850811736397881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232348631558467748981863841 174261473668850811736397881)
          ·
            refine ⟨130696105251638108802298411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174261473668850811736397881 130696105251638108802298411)
            ·
              refine ⟨196044157877457163203447617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130696105251638108802298411 196044157877457163203447617)
              ·
                refine ⟨147033118408092872402585713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196044157877457163203447617 147033118408092872402585713)
                ·
                  refine ⟨110274838806069654301939285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147033118408092872402585713 110274838806069654301939285)
                  ·
                    refine ⟨1292283267258628761350851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110274838806069654301939285 1292283267258628761350851)
                    ·
                      rfl

theorem cell23_7550138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_7550138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550138 prefixEnd_7550138 := by exact prefixLift 7550138
  have htrace : WordTrace (prefixWord ++ tailWord_7550138) baseStart_7550138 baseEnd_7550138 := by
    simpa [prefixWord, tailWord_7550138, baseEnd_7550138] using wordTrace_append hprefix tailTrace_7550138
  have hstable : (prefixWord ++ tailWord_7550138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550138).length < 2 ^ (prefixWord ++ tailWord_7550138).sum := by decide
  have hdescent : baseEnd_7550138 < baseStart_7550138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550162 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_7550162 : Nat := 118140960795 + 7550162 * 2 ^ 59
def prefixEnd_7550162 : Nat := 4983230072969 + 3 ^ 40 * 7550162 * 2
def baseEnd_7550162 : Nat := 3876862125311594190152443

theorem tailTrace_7550162 : CollatzResearch.WordTrace tailWord_7550162 prefixEnd_7550162 3876862125311594190152443 := by
  unfold tailWord_7550162
  simp only [CollatzResearch.WordTrace]
  refine ⟨68844257818265003463789185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183584687515373342570104493 68844257818265003463789185)
  ·
    refine ⟨51633193363698752597841889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68844257818265003463789185 51633193363698752597841889)
    ·
      refine ⟨38724895022774064448381417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51633193363698752597841889 38724895022774064448381417)
      ·
        refine ⟨29043671267080548336286063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38724895022774064448381417 29043671267080548336286063)
        ·
          refine ⟨43565506900620822504429095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29043671267080548336286063 43565506900620822504429095)
          ·
            refine ⟨65348260350931233756643643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43565506900620822504429095 65348260350931233756643643)
            ·
              refine ⟨98022390526396850634965465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65348260350931233756643643 98022390526396850634965465)
              ·
                refine ⟨73516792894797637976224099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98022390526396850634965465 73516792894797637976224099)
                ·
                  refine ⟨110275189342196456964336149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73516792894797637976224099 110275189342196456964336149)
                  ·
                    refine ⟨5169149500415458920203257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110275189342196456964336149 5169149500415458920203257)
                    ·
                      refine ⟨3876862125311594190152443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169149500415458920203257 3876862125311594190152443)
                      ·
                        rfl

theorem cell23_7550162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_7550162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550162 prefixEnd_7550162 := by exact prefixLift 7550162
  have htrace : WordTrace (prefixWord ++ tailWord_7550162) baseStart_7550162 baseEnd_7550162 := by
    simpa [prefixWord, tailWord_7550162, baseEnd_7550162] using wordTrace_append hprefix tailTrace_7550162
  have hstable : (prefixWord ++ tailWord_7550162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550162).length < 2 ^ (prefixWord ++ tailWord_7550162).sum := by decide
  have hdescent : baseEnd_7550162 < baseStart_7550162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550189 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_7550189 : Nat := 118140960795 + 7550189 * 2 ^ 59
def prefixEnd_7550189 : Nat := 4983230072969 + 3 ^ 40 * 7550189 * 2
def baseEnd_7550189 : Nat := 1292291996429755194838273

theorem tailTrace_7550189 : CollatzResearch.WordTrace tailWord_7550189 prefixEnd_7550189 1292291996429755194838273 := by
  unfold tailWord_7550189
  simp only [CollatzResearch.WordTrace]
  refine ⟨275378016043962197466389621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183585344029308131644259747 275378016043962197466389621)
  ·
    refine ⟨25816689004121456012474027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275378016043962197466389621 25816689004121456012474027)
    ·
      refine ⟨38725033506182184018711041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25816689004121456012474027 38725033506182184018711041)
      ·
        refine ⟨29043775129636638014033281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38725033506182184018711041 29043775129636638014033281)
        ·
          refine ⟨21782831347227478510524961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29043775129636638014033281 21782831347227478510524961)
          ·
            refine ⟨16337123510420608882893721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21782831347227478510524961 16337123510420608882893721)
            ·
              refine ⟨12252842632815456662170291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16337123510420608882893721 12252842632815456662170291)
              ·
                refine ⟨18379263949223184993255437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12252842632815456662170291 18379263949223184993255437)
                ·
                  refine ⟨6892223980958694372470789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18379263949223184993255437 6892223980958694372470789)
                  ·
                    refine ⟨1292291996429755194838273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6892223980958694372470789 1292291996429755194838273)
                    ·
                      rfl

theorem cell23_7550189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_7550189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550189 prefixEnd_7550189 := by exact prefixLift 7550189
  have htrace : WordTrace (prefixWord ++ tailWord_7550189) baseStart_7550189 baseEnd_7550189 := by
    simpa [prefixWord, tailWord_7550189, baseEnd_7550189] using wordTrace_append hprefix tailTrace_7550189
  have hstable : (prefixWord ++ tailWord_7550189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550189).length < 2 ^ (prefixWord ++ tailWord_7550189).sum := by decide
  have hdescent : baseEnd_7550189 < baseStart_7550189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550202 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 6]
def baseStart_7550202 : Nat := 118140960795 + 7550202 * 2 ^ 59
def prefixEnd_7550202 : Nat := 4983230072969 + 3 ^ 40 * 7550202 * 2
def baseEnd_7550202 : Nat := 430764740504197114850251

theorem tailTrace_7550202 : CollatzResearch.WordTrace tailWord_7550202 prefixEnd_7550202 430764740504197114850251 := by
  unfold tailWord_7550202
  simp only [CollatzResearch.WordTrace]
  refine ⟨68844622548228775171653215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183585660128610067124408573 68844622548228775171653215)
  ·
    refine ⟨103266933822343162757479823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68844622548228775171653215 103266933822343162757479823)
    ·
      refine ⟨154900400733514744136219735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103266933822343162757479823 154900400733514744136219735)
      ·
        refine ⟨232350601100272116204329603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154900400733514744136219735 232350601100272116204329603)
        ·
          refine ⟨348525901650408174306494405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232350601100272116204329603 348525901650408174306494405)
          ·
            refine ⟨65348606559451532682467701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348525901650408174306494405 65348606559451532682467701)
            ·
              refine ⟨6126431864948581188981347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65348606559451532682467701 6126431864948581188981347)
              ·
                refine ⟨9189647797422871783472021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126431864948581188981347 9189647797422871783472021)
                ·
                  refine ⟨430764740504197114850251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9189647797422871783472021 430764740504197114850251)
                  ·
                    rfl

theorem cell23_7550202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_7550202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550202 prefixEnd_7550202 := by exact prefixLift 7550202
  have htrace : WordTrace (prefixWord ++ tailWord_7550202) baseStart_7550202 baseEnd_7550202 := by
    simpa [prefixWord, tailWord_7550202, baseEnd_7550202] using wordTrace_append hprefix tailTrace_7550202
  have hstable : (prefixWord ++ tailWord_7550202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550202).length < 2 ^ (prefixWord ++ tailWord_7550202).sum := by decide
  have hdescent : baseEnd_7550202 < baseStart_7550202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550232 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 1, 5]
def baseStart_7550232 : Nat := 118140960795 + 7550232 * 2 ^ 59
def prefixEnd_7550232 : Nat := 4983230072969 + 3 ^ 40 * 7550232 * 2
def baseEnd_7550232 : Nat := 1292299356319136305425707

theorem tailTrace_7550232 : CollatzResearch.WordTrace tailWord_7550232 prefixEnd_7550232 1292299356319136305425707 := by
  unfold tailWord_7550232
  simp only [CollatzResearch.WordTrace]
  refine ⟨137689792191403207905102475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183586389588537610540136633 137689792191403207905102475)
  ·
    refine ⟨206534688287104811857653713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137689792191403207905102475 206534688287104811857653713)
    ·
      refine ⟨154901016215328608893240285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206534688287104811857653713 154901016215328608893240285)
      ·
        refine ⟨58087881080748228334965107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154901016215328608893240285 58087881080748228334965107)
        ·
          refine ⟨87131821621122342502447661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58087881080748228334965107 87131821621122342502447661)
          ·
            refine ⟨32674433107920878438417873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87131821621122342502447661 32674433107920878438417873)
            ·
              refine ⟨24505824830940658828813405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32674433107920878438417873 24505824830940658828813405)
              ·
                refine ⟨9189684311602747060805027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24505824830940658828813405 9189684311602747060805027)
                ·
                  refine ⟨13784526467404120591207541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189684311602747060805027 13784526467404120591207541)
                  ·
                    refine ⟨1292299356319136305425707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13784526467404120591207541 1292299356319136305425707)
                    ·
                      rfl

theorem cell23_7550232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_7550232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550232 prefixEnd_7550232 := by exact prefixLift 7550232
  have htrace : WordTrace (prefixWord ++ tailWord_7550232) baseStart_7550232 baseEnd_7550232 := by
    simpa [prefixWord, tailWord_7550232, baseEnd_7550232] using wordTrace_append hprefix tailTrace_7550232
  have hstable : (prefixWord ++ tailWord_7550232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550232).length < 2 ^ (prefixWord ++ tailWord_7550232).sum := by decide
  have hdescent : baseEnd_7550232 < baseStart_7550232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550235 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 4]
def baseStart_7550235 : Nat := 118140960795 + 7550235 * 2 ^ 59
def prefixEnd_7550235 : Nat := 4983230072969 + 3 ^ 40 * 7550235 * 2
def baseEnd_7550235 : Nat := 3876899609399372404539607

theorem tailTrace_7550235 : CollatzResearch.WordTrace tailWord_7550235 prefixEnd_7550235 3876899609399372404539607 := by
  unfold tailWord_7550235
  simp only [CollatzResearch.WordTrace]
  refine ⟨275379693801795547322564159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183586462534530364881709439 275379693801795547322564159)
  ·
    refine ⟨413069540702693320983846239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275379693801795547322564159 413069540702693320983846239)
    ·
      refine ⟨619604311054039981475769359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413069540702693320983846239 619604311054039981475769359)
      ·
        refine ⟨929406466581059972213654039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619604311054039981475769359 929406466581059972213654039)
        ·
          refine ⟨1394109699871589958320481059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929406466581059972213654039 1394109699871589958320481059)
          ·
            refine ⟨2091164549807384937480721589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394109699871589958320481059 2091164549807384937480721589)
            ·
              refine ⟨196046676544442337888817649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2091164549807384937480721589 196046676544442337888817649)
              ·
                refine ⟨147035007408331753416613237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196046676544442337888817649 147035007408331753416613237)
                ·
                  refine ⟨13784531944531101882807491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147035007408331753416613237 13784531944531101882807491)
                  ·
                    refine ⟨20676797916796652824211237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13784531944531101882807491 20676797916796652824211237)
                    ·
                      refine ⟨3876899609399372404539607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20676797916796652824211237 3876899609399372404539607)
                      ·
                        rfl

theorem cell23_7550235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 4].length) (baseStart_7550235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550235 prefixEnd_7550235 := by exact prefixLift 7550235
  have htrace : WordTrace (prefixWord ++ tailWord_7550235) baseStart_7550235 baseEnd_7550235 := by
    simpa [prefixWord, tailWord_7550235, baseEnd_7550235] using wordTrace_append hprefix tailTrace_7550235
  have hstable : (prefixWord ++ tailWord_7550235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550235).length < 2 ^ (prefixWord ++ tailWord_7550235).sum := by decide
  have hdescent : baseEnd_7550235 < baseStart_7550235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550255 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 3]
def baseStart_7550255 : Nat := 118140960795 + 7550255 * 2 ^ 59
def prefixEnd_7550255 : Nat := 4983230072969 + 3 ^ 40 * 7550255 * 2
def baseEnd_7550255 : Nat := 3876909879012462326289515

theorem tailTrace_7550255 : CollatzResearch.WordTrace tailWord_7550255 prefixEnd_7550255 3876909879012462326289515 := by
  unfold tailWord_7550255
  simp only [CollatzResearch.WordTrace]
  refine ⟨275380423261723090738292219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183586948841148727158861479 275380423261723090738292219)
  ·
    refine ⟨413070634892584636107438329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275380423261723090738292219 413070634892584636107438329)
    ·
      refine ⟨309802976169438477080578747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413070634892584636107438329 309802976169438477080578747)
      ·
        refine ⟨464704464254157715620868121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309802976169438477080578747 464704464254157715620868121)
        ·
          refine ⟨348528348190618286715651091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464704464254157715620868121 348528348190618286715651091)
          ·
            refine ⟨522792522285927430073476637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348528348190618286715651091 522792522285927430073476637)
            ·
              refine ⟨196047195857222786277553739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522792522285927430073476637 196047195857222786277553739)
              ·
                refine ⟨294070793785834179416330609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196047195857222786277553739 294070793785834179416330609)
                ·
                  refine ⟨220553095339375634562247957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294070793785834179416330609 220553095339375634562247957)
                  ·
                    refine ⟨10338426344033232870105373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 220553095339375634562247957 10338426344033232870105373)
                    ·
                      refine ⟨3876909879012462326289515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10338426344033232870105373 3876909879012462326289515)
                      ·
                        rfl

theorem cell23_7550255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_7550255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550255 prefixEnd_7550255 := by exact prefixLift 7550255
  have htrace : WordTrace (prefixWord ++ tailWord_7550255) baseStart_7550255 baseEnd_7550255 := by
    simpa [prefixWord, tailWord_7550255, baseEnd_7550255] using wordTrace_append hprefix tailTrace_7550255
  have hstable : (prefixWord ++ tailWord_7550255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550255).length < 2 ^ (prefixWord ++ tailWord_7550255).sum := by decide
  have hdescent : baseEnd_7550255 < baseStart_7550255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550272 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 3]
def baseStart_7550272 : Nat := 118140960795 + 7550272 * 2 ^ 59
def prefixEnd_7550272 : Nat := 4983230072969 + 3 ^ 40 * 7550272 * 2
def baseEnd_7550272 : Nat := 3876918608183588759776937

theorem tailTrace_7550272 : CollatzResearch.WordTrace tailWord_7550272 prefixEnd_7550272 3876918608183588759776937 := by
  unfold tailWord_7550272
  simp only [CollatzResearch.WordTrace]
  refine ⟨137690521651330751320830535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183587362201774335094440713 137690521651330751320830535)
  ·
    refine ⟨206535782476996126981245803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137690521651330751320830535 206535782476996126981245803)
    ·
      refine ⟨309803673715494190471868705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206535782476996126981245803 309803673715494190471868705)
      ·
        refine ⟨232352755286620642853901529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309803673715494190471868705 232352755286620642853901529)
        ·
          refine ⟨174264566464965482140426147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232352755286620642853901529 174264566464965482140426147)
          ·
            refine ⟨261396849697448223210639221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174264566464965482140426147 261396849697448223210639221)
            ·
              refine ⟨24505954659135770925997427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261396849697448223210639221 24505954659135770925997427)
              ·
                refine ⟨36758931988703656388996141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24505954659135770925997427 36758931988703656388996141)
                ·
                  refine ⟨13784599495763871145873553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36758931988703656388996141 13784599495763871145873553)
                  ·
                    refine ⟨10338449621822903359405165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13784599495763871145873553 10338449621822903359405165)
                    ·
                      refine ⟨3876918608183588759776937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10338449621822903359405165 3876918608183588759776937)
                      ·
                        rfl

theorem cell23_7550272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_7550272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550272 prefixEnd_7550272 := by exact prefixLift 7550272
  have htrace : WordTrace (prefixWord ++ tailWord_7550272) baseStart_7550272 baseEnd_7550272 := by
    simpa [prefixWord, tailWord_7550272, baseEnd_7550272] using wordTrace_append hprefix tailTrace_7550272
  have hstable : (prefixWord ++ tailWord_7550272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550272).length < 2 ^ (prefixWord ++ tailWord_7550272).sum := by decide
  have hdescent : baseEnd_7550272 < baseStart_7550272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550319 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 3]
def baseStart_7550319 : Nat := 118140960795 + 7550319 * 2 ^ 59
def prefixEnd_7550319 : Nat := 4983230072969 + 3 ^ 40 * 7550319 * 2
def baseEnd_7550319 : Nat := 3876942741774350075889221

theorem tailTrace_7550319 : CollatzResearch.WordTrace tailWord_7550319 prefixEnd_7550319 3876942741774350075889221 := by
  unfold tailWord_7550319
  simp only [CollatzResearch.WordTrace]
  refine ⟨275382757533491229668622011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183588505022327486445748007 275382757533491229668622011)
  ·
    refine ⟨413074136300236844502933017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275382757533491229668622011 413074136300236844502933017)
    ·
      refine ⟨309805602225177633377199763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413074136300236844502933017 309805602225177633377199763)
      ·
        refine ⟨464708403337766450065799645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309805602225177633377199763 464708403337766450065799645)
        ·
          refine ⟨174265651251662418774674867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464708403337766450065799645 174265651251662418774674867)
          ·
            refine ⟨261398476877493628162012301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174265651251662418774674867 261398476877493628162012301)
            ·
              refine ⟨98024428829060110560754613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261398476877493628162012301 98024428829060110560754613)
              ·
                refine ⟨9189790202724385365070745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98024428829060110560754613 9189790202724385365070745)
                ·
                  refine ⟨6892342652043289023803059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9189790202724385365070745 6892342652043289023803059)
                  ·
                    refine ⟨10338513978064933535704589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6892342652043289023803059 10338513978064933535704589)
                    ·
                      refine ⟨3876942741774350075889221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10338513978064933535704589 3876942741774350075889221)
                      ·
                        rfl

theorem cell23_7550319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 3].length) (baseStart_7550319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550319 prefixEnd_7550319 := by exact prefixLift 7550319
  have htrace : WordTrace (prefixWord ++ tailWord_7550319) baseStart_7550319 baseEnd_7550319 := by
    simpa [prefixWord, tailWord_7550319, baseEnd_7550319] using wordTrace_append hprefix tailTrace_7550319
  have hstable : (prefixWord ++ tailWord_7550319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550319).length < 2 ^ (prefixWord ++ tailWord_7550319).sum := by decide
  have hdescent : baseEnd_7550319 < baseStart_7550319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550329 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 3, 3, 2]
def baseStart_7550329 : Nat := 118140960795 + 7550329 * 2 ^ 59
def prefixEnd_7550329 : Nat := 4983230072969 + 3 ^ 40 * 7550329 * 2
def baseEnd_7550329 : Nat := 3876947876580895036764175

theorem tailTrace_7550329 : CollatzResearch.WordTrace tailWord_7550329 prefixEnd_7550329 3876947876580895036764175 := by
  unfold tailWord_7550329
  simp only [CollatzResearch.WordTrace]
  refine ⟨275383122263455001376486041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183588748175636667584324027 275383122263455001376486041)
  ·
    refine ⟨206537341697591251032364531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275383122263455001376486041 206537341697591251032364531)
    ·
      refine ⟨309806012546386876548546797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206537341697591251032364531 309806012546386876548546797)
      ·
        refine ⟨116177254704895078705705049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309806012546386876548546797 116177254704895078705705049)
        ·
          refine ⟨87132941028671309029278787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116177254704895078705705049 87132941028671309029278787)
          ·
            refine ⟨130699411543006963543918181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87132941028671309029278787 130699411543006963543918181)
            ·
              refine ⟨24506139664313805664484659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130699411543006963543918181 24506139664313805664484659)
              ·
                refine ⟨36759209496470708496726989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24506139664313805664484659 36759209496470708496726989)
                ·
                  refine ⟨13784703561176515686272621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36759209496470708496726989 13784703561176515686272621)
                  ·
                    refine ⟨5169263835441193382352233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13784703561176515686272621 5169263835441193382352233)
                    ·
                      refine ⟨3876947876580895036764175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169263835441193382352233 3876947876580895036764175)
                      ·
                        rfl

theorem cell23_7550329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_7550329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550329 prefixEnd_7550329 := by exact prefixLift 7550329
  have htrace : WordTrace (prefixWord ++ tailWord_7550329) baseStart_7550329 baseEnd_7550329 := by
    simpa [prefixWord, tailWord_7550329, baseEnd_7550329] using wordTrace_append hprefix tailTrace_7550329
  have hstable : (prefixWord ++ tailWord_7550329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550329).length < 2 ^ (prefixWord ++ tailWord_7550329).sum := by decide
  have hdescent : baseEnd_7550329 < baseStart_7550329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550335 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 6, 6]
def baseStart_7550335 : Nat := 118140960795 + 7550335 * 2 ^ 59
def prefixEnd_7550335 : Nat := 4983230072969 + 3 ^ 40 * 7550335 * 2
def baseEnd_7550335 : Nat := 1292316985821607337763049

theorem tailTrace_7550335 : CollatzResearch.WordTrace tailWord_7550335 prefixEnd_7550335 1292316985821607337763049 := by
  unfold tailWord_7550335
  simp only [CollatzResearch.WordTrace]
  refine ⟨275383341101433264401204459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183588894067622176267469639 275383341101433264401204459)
  ·
    refine ⟨413075011652149896601806689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275383341101433264401204459 413075011652149896601806689)
    ·
      refine ⟨309806258739112422451355017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413075011652149896601806689 309806258739112422451355017)
      ·
        refine ⟨232354694054334316838516263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309806258739112422451355017 232354694054334316838516263)
        ·
          refine ⟨348532041081501475257774395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232354694054334316838516263 348532041081501475257774395)
          ·
            refine ⟨522798061622252212886661593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348532041081501475257774395 522798061622252212886661593)
            ·
              refine ⟨392098546216689159664996195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522798061622252212886661593 392098546216689159664996195)
              ·
                refine ⟨588147819325033739497494293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392098546216689159664996195 588147819325033739497494293)
                ·
                  refine ⟨27569429030860956538945045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 588147819325033739497494293 27569429030860956538945045)
                  ·
                    refine ⟨1292316985821607337763049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27569429030860956538945045 1292316985821607337763049)
                    ·
                      rfl

theorem cell23_7550335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_7550335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550335 prefixEnd_7550335 := by exact prefixLift 7550335
  have htrace : WordTrace (prefixWord ++ tailWord_7550335) baseStart_7550335 baseEnd_7550335 := by
    simpa [prefixWord, tailWord_7550335, baseEnd_7550335] using wordTrace_append hprefix tailTrace_7550335
  have hstable : (prefixWord ++ tailWord_7550335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550335).length < 2 ^ (prefixWord ++ tailWord_7550335).sum := by decide
  have hdescent : baseEnd_7550335 < baseStart_7550335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550392 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 1, 5, 3]
def baseStart_7550392 : Nat := 118140960795 + 7550392 * 2 ^ 59
def prefixEnd_7550392 : Nat := 4983230072969 + 3 ^ 40 * 7550392 * 2
def baseEnd_7550392 : Nat := 3876980225862128290276385

theorem tailTrace_7550392 : CollatzResearch.WordTrace tailWord_7550392 prefixEnd_7550392 3876980225862128290276385 := by
  unfold tailWord_7550392
  simp only [CollatzResearch.WordTrace]
  refine ⟨137692710031113381568014715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183590280041484508757352953 137692710031113381568014715)
  ·
    refine ⟨206539065046670072352022073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137692710031113381568014715 206539065046670072352022073)
    ·
      refine ⟨154904298785002554264016555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206539065046670072352022073 154904298785002554264016555)
      ·
        refine ⟨232356448177503831396024833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154904298785002554264016555 232356448177503831396024833)
        ·
          refine ⟨174267336133127873547018625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232356448177503831396024833 174267336133127873547018625)
          ·
            refine ⟨130700502099845905160263969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174267336133127873547018625 130700502099845905160263969)
            ·
              refine ⟨98025376574884428870197977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130700502099845905160263969 98025376574884428870197977)
              ·
                refine ⟨73519032431163321652648483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98025376574884428870197977 73519032431163321652648483)
                ·
                  refine ⟨110278548646744982478972725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73519032431163321652648483 110278548646744982478972725)
                  ·
                    refine ⟨10338613935632342107403693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110278548646744982478972725 10338613935632342107403693)
                    ·
                      refine ⟨3876980225862128290276385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10338613935632342107403693 3876980225862128290276385)
                      ·
                        rfl

theorem cell23_7550392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_7550392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550392 prefixEnd_7550392 := by exact prefixLift 7550392
  have htrace : WordTrace (prefixWord ++ tailWord_7550392) baseStart_7550392 baseEnd_7550392 := by
    simpa [prefixWord, tailWord_7550392, baseEnd_7550392] using wordTrace_append hprefix tailTrace_7550392
  have hstable : (prefixWord ++ tailWord_7550392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550392).length < 2 ^ (prefixWord ++ tailWord_7550392).sum := by decide
  have hdescent : baseEnd_7550392 < baseStart_7550392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550432 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 4]
def baseStart_7550432 : Nat := 118140960795 + 7550432 * 2 ^ 59
def prefixEnd_7550432 : Nat := 4983230072969 + 3 ^ 40 * 7550432 * 2
def baseEnd_7550432 : Nat := 3877000765088308133776201

theorem tailTrace_7550432 : CollatzResearch.WordTrace tailWord_7550432 prefixEnd_7550432 3877000765088308133776201 := by
  unfold tailWord_7550432
  simp only [CollatzResearch.WordTrace]
  refine ⟨137693439491040924983742775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183591252654721233311657033 137693439491040924983742775)
  ·
    refine ⟨206540159236561387475614163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137693439491040924983742775 206540159236561387475614163)
    ·
      refine ⟨309810238854842081213421245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206540159236561387475614163 309810238854842081213421245)
      ·
        refine ⟨116178839570565780455032967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309810238854842081213421245 116178839570565780455032967)
        ·
          refine ⟨174268259355848670682549451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116178839570565780455032967 174268259355848670682549451)
          ·
            refine ⟨261402389033773006023824177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174268259355848670682549451 261402389033773006023824177)
            ·
              refine ⟨196051791775329754517868133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261402389033773006023824177 196051791775329754517868133)
              ·
                refine ⟨36759710957874328972100275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196051791775329754517868133 36759710957874328972100275)
                ·
                  refine ⟨55139566436811493458150413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36759710957874328972100275 55139566436811493458150413)
                  ·
                    refine ⟨20677337413804310046806405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55139566436811493458150413 20677337413804310046806405)
                    ·
                      refine ⟨3877000765088308133776201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20677337413804310046806405 3877000765088308133776201)
                      ·
                        rfl

theorem cell23_7550432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_7550432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550432 prefixEnd_7550432 := by exact prefixLift 7550432
  have htrace : WordTrace (prefixWord ++ tailWord_7550432) baseStart_7550432 baseEnd_7550432 := by
    simpa [prefixWord, tailWord_7550432, baseEnd_7550432] using wordTrace_append hprefix tailTrace_7550432
  have hstable : (prefixWord ++ tailWord_7550432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550432).length < 2 ^ (prefixWord ++ tailWord_7550432).sum := by decide
  have hdescent : baseEnd_7550432 < baseStart_7550432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550449 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_7550449 : Nat := 118140960795 + 7550449 * 2 ^ 59
def prefixEnd_7550449 : Nat := 4983230072969 + 3 ^ 40 * 7550449 * 2
def baseEnd_7550449 : Nat := 3877009494259434567263623

theorem tailTrace_7550449 : CollatzResearch.WordTrace tailWord_7550449 prefixEnd_7550449 3877009494259434567263623 := by
  unfold tailWord_7550449
  simp only [CollatzResearch.WordTrace]
  refine ⟨275387499023020261870854401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183591666015346841247236267 275387499023020261870854401)
  ·
    refine ⟨206540624267265196403140801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275387499023020261870854401 206540624267265196403140801)
    ·
      refine ⟨154905468200448897302355601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206540624267265196403140801 154905468200448897302355601)
      ·
        refine ⟨116179101150336672976766701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154905468200448897302355601 116179101150336672976766701)
        ·
          refine ⟨43567162931376252366287513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116179101150336672976766701 43567162931376252366287513)
          ·
            refine ⟨32675372198532189274715635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43567162931376252366287513 32675372198532189274715635)
            ·
              refine ⟨49013058297798283912073453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32675372198532189274715635 49013058297798283912073453)
              ·
                refine ⟨18379896861674356467027545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49013058297798283912073453 18379896861674356467027545)
                ·
                  refine ⟨13784922646255767350270659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18379896861674356467027545 13784922646255767350270659)
                  ·
                    refine ⟨20677383969383651025405989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13784922646255767350270659 20677383969383651025405989)
                    ·
                      refine ⟨3877009494259434567263623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20677383969383651025405989 3877009494259434567263623)
                      ·
                        rfl

theorem cell23_7550449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_7550449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550449 prefixEnd_7550449 := by exact prefixLift 7550449
  have htrace : WordTrace (prefixWord ++ tailWord_7550449) baseStart_7550449 baseEnd_7550449 := by
    simpa [prefixWord, tailWord_7550449, baseEnd_7550449] using wordTrace_append hprefix tailTrace_7550449
  have hstable : (prefixWord ++ tailWord_7550449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550449).length < 2 ^ (prefixWord ++ tailWord_7550449).sum := by decide
  have hdescent : baseEnd_7550449 < baseStart_7550449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550472 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 8]
def baseStart_7550472 : Nat := 118140960795 + 7550472 * 2 ^ 59
def prefixEnd_7550472 : Nat := 4983230072969 + 3 ^ 40 * 7550472 * 2
def baseEnd_7550472 : Nat := 430780144923831997475113

theorem tailTrace_7550472 : CollatzResearch.WordTrace tailWord_7550472 prefixEnd_7550472 430780144923831997475113 := by
  unfold tailWord_7550472
  simp only [CollatzResearch.WordTrace]
  refine ⟨137694168950968468399470835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183592225267957957865961113 137694168950968468399470835)
  ·
    refine ⟨206541253426452702599206253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137694168950968468399470835 206541253426452702599206253)
    ·
      refine ⟨77452970034919763474702345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206541253426452702599206253 77452970034919763474702345)
      ·
        refine ⟨58089727526189822606026759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77452970034919763474702345 58089727526189822606026759)
        ·
          refine ⟨87134591289284733909040139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58089727526189822606026759 87134591289284733909040139)
          ·
            refine ⟨130701886933927100863560209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87134591289284733909040139 130701886933927100863560209)
            ·
              refine ⟨98026415200445325647670157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130701886933927100863560209 98026415200445325647670157)
              ·
                refine ⟨36759905700166997117876309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98026415200445325647670157 36759905700166997117876309)
                ·
                  refine ⟨430780144923831997475113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36759905700166997117876309 430780144923831997475113)
                  ·
                    rfl

theorem cell23_7550472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 8].length) (baseStart_7550472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550472 prefixEnd_7550472 := by exact prefixLift 7550472
  have htrace : WordTrace (prefixWord ++ tailWord_7550472) baseStart_7550472 baseEnd_7550472 := by
    simpa [prefixWord, tailWord_7550472, baseEnd_7550472] using wordTrace_append hprefix tailTrace_7550472
  have hstable : (prefixWord ++ tailWord_7550472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550472).length < 2 ^ (prefixWord ++ tailWord_7550472).sum := by decide
  have hdescent : baseEnd_7550472 < baseStart_7550472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550510 : List Nat := [4, 1, 3, 1, 2, 2, 2, 3, 1, 4]
def baseStart_7550510 : Nat := 118140960795 + 7550510 * 2 ^ 59
def prefixEnd_7550510 : Nat := 4983230072969 + 3 ^ 40 * 7550510 * 2
def baseEnd_7550510 : Nat := 1292346938859786276200281

theorem tailTrace_7550510 : CollatzResearch.WordTrace tailWord_7550510 prefixEnd_7550510 1292346938859786276200281 := by
  unfold tailWord_7550510
  simp only [CollatzResearch.WordTrace]
  refine ⟨34423715484474908661103123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183593149250532846192549989 34423715484474908661103123)
  ·
    refine ⟨51635573226712362991654685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34423715484474908661103123 51635573226712362991654685)
    ·
      refine ⟨19363339960017136121870507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51635573226712362991654685 19363339960017136121870507)
      ·
        refine ⟨29045009940025704182805761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19363339960017136121870507 29045009940025704182805761)
        ·
          refine ⟨21783757455019278137104321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29045009940025704182805761 21783757455019278137104321)
          ·
            refine ⟨16337818091264458602828241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21783757455019278137104321 16337818091264458602828241)
            ·
              refine ⟨12253363568448343952121181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16337818091264458602828241 12253363568448343952121181)
              ·
                refine ⟨4595011338168128982045443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12253363568448343952121181 4595011338168128982045443)
                ·
                  refine ⟨6892517007252193473068165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595011338168128982045443 6892517007252193473068165)
                  ·
                    refine ⟨1292346938859786276200281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6892517007252193473068165 1292346938859786276200281)
                    ·
                      rfl

theorem cell23_7550510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_7550510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550510 prefixEnd_7550510 := by exact prefixLift 7550510
  have htrace : WordTrace (prefixWord ++ tailWord_7550510) baseStart_7550510 baseEnd_7550510 := by
    simpa [prefixWord, tailWord_7550510, baseEnd_7550510] using wordTrace_append hprefix tailTrace_7550510
  have hstable : (prefixWord ++ tailWord_7550510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550510).length < 2 ^ (prefixWord ++ tailWord_7550510).sum := by decide
  have hdescent : baseEnd_7550510 < baseStart_7550510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550512 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 5]
def baseStart_7550512 : Nat := 118140960795 + 7550512 * 2 ^ 59
def prefixEnd_7550512 : Nat := 4983230072969 + 3 ^ 40 * 7550512 * 2
def baseEnd_7550512 : Nat := 3877041843540667820775833

theorem tailTrace_7550512 : CollatzResearch.WordTrace tailWord_7550512 prefixEnd_7550512 3877041843540667820775833 := by
  unfold tailWord_7550512
  simp only [CollatzResearch.WordTrace]
  refine ⟨137694898410896011815198895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183593197881194682420265193 137694898410896011815198895)
  ·
    refine ⟨206542347616344017722798343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137694898410896011815198895 206542347616344017722798343)
    ·
      refine ⟨309813521424516026584197515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206542347616344017722798343 309813521424516026584197515)
      ·
        refine ⟨464720282136774039876296273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309813521424516026584197515 464720282136774039876296273)
        ·
          refine ⟨348540211602580529907222205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464720282136774039876296273 348540211602580529907222205)
          ·
            refine ⟨130702579350967698715208327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348540211602580529907222205 130702579350967698715208327)
            ·
              refine ⟨196053869026451548072812491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130702579350967698715208327 196053869026451548072812491)
              ·
                refine ⟨294080803539677322109218737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196053869026451548072812491 294080803539677322109218737)
                ·
                  refine ⟨220560602654757991581914053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294080803539677322109218737 220560602654757991581914053)
                  ·
                    refine ⟨41355112997767123421608885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 220560602654757991581914053 41355112997767123421608885)
                    ·
                      refine ⟨3877041843540667820775833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41355112997767123421608885 3877041843540667820775833)
                      ·
                        rfl

theorem cell23_7550512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_7550512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550512 prefixEnd_7550512 := by exact prefixLift 7550512
  have htrace : WordTrace (prefixWord ++ tailWord_7550512) baseStart_7550512 baseEnd_7550512 := by
    simpa [prefixWord, tailWord_7550512, baseEnd_7550512] using wordTrace_append hprefix tailTrace_7550512
  have hstable : (prefixWord ++ tailWord_7550512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550512).length < 2 ^ (prefixWord ++ tailWord_7550512).sum := by decide
  have hdescent : baseEnd_7550512 < baseStart_7550512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550533 : List Nat := [1, 3, 1, 1, 1, 4, 1, 6, 1, 1, 3]
def baseStart_7550533 : Nat := 118140960795 + 7550533 * 2 ^ 59
def prefixEnd_7550533 : Nat := 4983230072969 + 3 ^ 40 * 7550533 * 2
def baseEnd_7550533 : Nat := 3877052626634412238613237

theorem tailTrace_7550533 : CollatzResearch.WordTrace tailWord_7550533 prefixEnd_7550533 3877052626634412238613237 := by
  unfold tailWord_7550533
  simp only [CollatzResearch.WordTrace]
  refine ⟨275390562754715944216912253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183593708503143962811274835 275390562754715944216912253)
  ·
    refine ⟨103271461033018479081342095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275390562754715944216912253 103271461033018479081342095)
    ·
      refine ⟨154907191549527718622013143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103271461033018479081342095 154907191549527718622013143)
      ·
        refine ⟨232360787324291577933019715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154907191549527718622013143 232360787324291577933019715)
        ·
          refine ⟨348541180986437366899529573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232360787324291577933019715 348541180986437366899529573)
          ·
            refine ⟨65351471434957006293661795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348541180986437366899529573 65351471434957006293661795)
            ·
              refine ⟨98027207152435509440492693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65351471434957006293661795 98027207152435509440492693)
              ·
                refine ⟨4595025335270414505023095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98027207152435509440492693 4595025335270414505023095)
                ·
                  refine ⟨6892538002905621757534643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595025335270414505023095 6892538002905621757534643)
                  ·
                    refine ⟨10338807004358432636301965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6892538002905621757534643 10338807004358432636301965)
                    ·
                      refine ⟨3877052626634412238613237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10338807004358432636301965 3877052626634412238613237)
                      ·
                        rfl

theorem cell23_7550533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_7550533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550533 prefixEnd_7550533 := by exact prefixLift 7550533
  have htrace : WordTrace (prefixWord ++ tailWord_7550533) baseStart_7550533 baseEnd_7550533 := by
    simpa [prefixWord, tailWord_7550533, baseEnd_7550533] using wordTrace_append hprefix tailTrace_7550533
  have hstable : (prefixWord ++ tailWord_7550533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550533).length < 2 ^ (prefixWord ++ tailWord_7550533).sum := by decide
  have hdescent : baseEnd_7550533 < baseStart_7550533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550569 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_7550569 : Nat := 118140960795 + 7550569 * 2 ^ 59
def prefixEnd_7550569 : Nat := 4983230072969 + 3 ^ 40 * 7550569 * 2
def baseEnd_7550569 : Nat := 3877071111937974097763071

theorem tailTrace_7550569 : CollatzResearch.WordTrace tailWord_7550569 prefixEnd_7550569 3877071111937974097763071 := by
  unfold tailWord_7550569
  simp only [CollatzResearch.WordTrace]
  refine ⟨275391875782585522365222761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183594583855057014910148507 275391875782585522365222761)
  ·
    refine ⟨206543906836939141773917071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275391875782585522365222761 206543906836939141773917071)
    ·
      refine ⟨309815860255408712660875607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206543906836939141773917071 309815860255408712660875607)
      ·
        refine ⟨464723790383113068991313411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309815860255408712660875607 464723790383113068991313411)
        ·
          refine ⟨697085685574669603486970117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464723790383113068991313411 697085685574669603486970117)
          ·
            refine ⟨130703566045250550653806897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 697085685574669603486970117 130703566045250550653806897)
            ·
              refine ⟨98027674533937912990355173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130703566045250550653806897 98027674533937912990355173)
              ·
                refine ⟨18380188975113358685691595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98027674533937912990355173 18380188975113358685691595)
                ·
                  refine ⟨27570283462670038028537393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18380188975113358685691595 27570283462670038028537393)
                  ·
                    refine ⟨20677712597002528521403045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27570283462670038028537393 20677712597002528521403045)
                    ·
                      refine ⟨3877071111937974097763071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20677712597002528521403045 3877071111937974097763071)
                      ·
                        rfl

theorem cell23_7550569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_7550569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550569 prefixEnd_7550569 := by exact prefixLift 7550569
  have htrace : WordTrace (prefixWord ++ tailWord_7550569) baseStart_7550569 baseEnd_7550569 := by
    simpa [prefixWord, tailWord_7550569, baseEnd_7550569] using wordTrace_append hprefix tailTrace_7550569
  have hstable : (prefixWord ++ tailWord_7550569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550569).length < 2 ^ (prefixWord ++ tailWord_7550569).sum := by decide
  have hdescent : baseEnd_7550569 < baseStart_7550569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550576 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 5]
def baseStart_7550576 : Nat := 118140960795 + 7550576 * 2 ^ 59
def prefixEnd_7550576 : Nat := 4983230072969 + 3 ^ 40 * 7550576 * 2
def baseEnd_7550576 : Nat := 3877074706302555570375539

theorem tailTrace_7550576 : CollatzResearch.WordTrace tailWord_7550576 prefixEnd_7550576 3877074706302555570375539 := by
  unfold tailWord_7550576
  simp only [CollatzResearch.WordTrace]
  refine ⟨137696065546780081280363791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183594754062373441707151721 137696065546780081280363791)
  ·
    refine ⟨206544098320170121920545687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137696065546780081280363791 206544098320170121920545687)
    ·
      refine ⟨309816147480255182880818531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206544098320170121920545687 309816147480255182880818531)
      ·
        refine ⟨464724221220382774321227797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309816147480255182880818531 464724221220382774321227797)
        ·
          refine ⟨21783947869705442546307553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 464724221220382774321227797 21783947869705442546307553)
          ·
            refine ⟨16337960902279081909730665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21783947869705442546307553 16337960902279081909730665)
            ·
              refine ⟨12253470676709311432297999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16337960902279081909730665 12253470676709311432297999)
              ·
                refine ⟨18380206015063967148446999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12253470676709311432297999 18380206015063967148446999)
                ·
                  refine ⟨27570309022595950722670499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18380206015063967148446999 27570309022595950722670499)
                  ·
                    refine ⟨41355463533893926084005749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27570309022595950722670499 41355463533893926084005749)
                    ·
                      refine ⟨3877074706302555570375539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41355463533893926084005749 3877074706302555570375539)
                      ·
                        rfl

theorem cell23_7550576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_7550576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550576 prefixEnd_7550576 := by exact prefixLift 7550576
  have htrace : WordTrace (prefixWord ++ tailWord_7550576) baseStart_7550576 baseEnd_7550576 := by
    simpa [prefixWord, tailWord_7550576, baseEnd_7550576] using wordTrace_append hprefix tailTrace_7550576
  have hstable : (prefixWord ++ tailWord_7550576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550576).length < 2 ^ (prefixWord ++ tailWord_7550576).sum := by decide
  have hdescent : baseEnd_7550576 < baseStart_7550576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550596 : List Nat := [2, 3, 2, 1, 4, 1, 2, 8]
def baseStart_7550596 : Nat := 118140960795 + 7550596 * 2 ^ 59
def prefixEnd_7550596 : Nat := 4983230072969 + 3 ^ 40 * 7550596 * 2
def baseEnd_7550596 : Nat := 143595739848727610819461

theorem tailTrace_7550596 : CollatzResearch.WordTrace tailWord_7550596 prefixEnd_7550596 143595739848727610819461 := by
  unfold tailWord_7550596
  simp only [CollatzResearch.WordTrace]
  refine ⟨137696430276743852988227821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183595240368991803984303761 137696430276743852988227821)
  ·
    refine ⟨51636161353778944870585433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137696430276743852988227821 51636161353778944870585433)
    ·
      refine ⟨38727121015334208652939075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51636161353778944870585433 38727121015334208652939075)
      ·
        refine ⟨58090681523001312979408613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38727121015334208652939075 58090681523001312979408613)
        ·
          refine ⟨10892002785562746183639115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58090681523001312979408613 10892002785562746183639115)
          ·
            refine ⟨16338004178344119275458673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10892002785562746183639115 16338004178344119275458673)
            ·
              refine ⟨12253503133758089456594005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16338004178344119275458673 12253503133758089456594005)
              ·
                refine ⟨143595739848727610819461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12253503133758089456594005 143595739848727610819461)
                ·
                  rfl

theorem cell23_7550596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 8].length) (baseStart_7550596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550596 prefixEnd_7550596 := by exact prefixLift 7550596
  have htrace : WordTrace (prefixWord ++ tailWord_7550596) baseStart_7550596 baseEnd_7550596 := by
    simpa [prefixWord, tailWord_7550596, baseEnd_7550596] using wordTrace_append hprefix tailTrace_7550596
  have hstable : (prefixWord ++ tailWord_7550596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550596).length < 2 ^ (prefixWord ++ tailWord_7550596).sum := by decide
  have hdescent : baseEnd_7550596 < baseStart_7550596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550600 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 2, 4]
def baseStart_7550600 : Nat := 118140960795 + 7550600 * 2 ^ 59
def prefixEnd_7550600 : Nat := 4983230072969 + 3 ^ 40 * 7550600 * 2
def baseEnd_7550600 : Nat := 1292362343279421158825143

theorem tailTrace_7550600 : CollatzResearch.WordTrace tailWord_7550600 prefixEnd_7550600 1292362343279421158825143 := by
  unfold tailWord_7550600
  simp only [CollatzResearch.WordTrace]
  refine ⟨137696503222736607329800627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183595337630315476439734169 137696503222736607329800627)
  ·
    refine ⟨206544754834104910994700941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137696503222736607329800627 206544754834104910994700941)
    ·
      refine ⟨77454283062789341623012853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206544754834104910994700941 77454283062789341623012853)
      ·
        refine ⟨7261339037136500777157455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77454283062789341623012853 7261339037136500777157455)
        ·
          refine ⟨10892008555704751165736183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7261339037136500777157455 10892008555704751165736183)
          ·
            refine ⟨16338012833557126748604275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10892008555704751165736183 16338012833557126748604275)
            ·
              refine ⟨24507019250335690122906413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16338012833557126748604275 24507019250335690122906413)
              ·
                refine ⟨9190132218875883796089905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24507019250335690122906413 9190132218875883796089905)
                ·
                  refine ⟨6892599164156912847067429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9190132218875883796089905 6892599164156912847067429)
                  ·
                    refine ⟨1292362343279421158825143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6892599164156912847067429 1292362343279421158825143)
                    ·
                      rfl

theorem cell23_7550600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_7550600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550600 prefixEnd_7550600 := by exact prefixLift 7550600
  have htrace : WordTrace (prefixWord ++ tailWord_7550600) baseStart_7550600 baseEnd_7550600 := by
    simpa [prefixWord, tailWord_7550600, baseEnd_7550600] using wordTrace_append hprefix tailTrace_7550600
  have hstable : (prefixWord ++ tailWord_7550600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550600).length < 2 ^ (prefixWord ++ tailWord_7550600).sum := by decide
  have hdescent : baseEnd_7550600 < baseStart_7550600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550639 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 2, 6]
def baseStart_7550639 : Nat := 118140960795 + 7550639 * 2 ^ 59
def prefixEnd_7550639 : Nat := 4983230072969 + 3 ^ 40 * 7550639 * 2
def baseEnd_7550639 : Nat := 1292369018527929607962583

theorem tailTrace_7550639 : CollatzResearch.WordTrace tailWord_7550639 prefixEnd_7550639 1292369018527929607962583 := by
  unfold tailWord_7550639
  simp only [CollatzResearch.WordTrace]
  refine ⟨275394428892331924320270971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183596285928221282880180647 275394428892331924320270971)
  ·
    refine ⟨413091643338497886480406457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275394428892331924320270971 413091643338497886480406457)
    ·
      refine ⟨309818732503873414860304843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413091643338497886480406457 309818732503873414860304843)
      ·
        refine ⟨464728098755810122290457265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309818732503873414860304843 464728098755810122290457265)
        ·
          refine ⟨348546074066857591717842949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464728098755810122290457265 348546074066857591717842949)
          ·
            refine ⟨65352388887535798447095553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348546074066857591717842949 65352388887535798447095553)
            ·
              refine ⟨49014291665651848835321665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65352388887535798447095553 49014291665651848835321665)
              ·
                refine ⟨36760718749238886626491249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49014291665651848835321665 36760718749238886626491249)
                ·
                  refine ⟨27570539061929164969868437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36760718749238886626491249 27570539061929164969868437)
                  ·
                    refine ⟨1292369018527929607962583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27570539061929164969868437 1292369018527929607962583)
                    ·
                      rfl

theorem cell23_7550639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_7550639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550639 prefixEnd_7550639 := by exact prefixLift 7550639
  have htrace : WordTrace (prefixWord ++ tailWord_7550639) baseStart_7550639 baseEnd_7550639 := by
    simpa [prefixWord, tailWord_7550639, baseEnd_7550639] using wordTrace_append hprefix tailTrace_7550639
  have hstable : (prefixWord ++ tailWord_7550639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550639).length < 2 ^ (prefixWord ++ tailWord_7550639).sum := by decide
  have hdescent : baseEnd_7550639 < baseStart_7550639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550649 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7550649 : Nat := 118140960795 + 7550649 * 2 ^ 59
def prefixEnd_7550649 : Nat := 4983230072969 + 3 ^ 40 * 7550649 * 2
def baseEnd_7550649 : Nat := 3877112190390333784762703

theorem tailTrace_7550649 : CollatzResearch.WordTrace tailWord_7550649 prefixEnd_7550649 3877112190390333784762703 := by
  unfold tailWord_7550649
  simp only [CollatzResearch.WordTrace]
  refine ⟨275394793622295696028135001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183596529081530464018756667 275394793622295696028135001)
  ·
    refine ⟨206546095216721772021101251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275394793622295696028135001 206546095216721772021101251)
    ·
      refine ⟨309819142825082658031651877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206546095216721772021101251 309819142825082658031651877)
      ·
        refine ⟨58091089279702998380934727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309819142825082658031651877 58091089279702998380934727)
        ·
          refine ⟨87136633919554497571402091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58091089279702998380934727 87136633919554497571402091)
          ·
            refine ⟨130704950879331746357103137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87136633919554497571402091 130704950879331746357103137)
            ·
              refine ⟨98028713159498809767827353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130704950879331746357103137 98028713159498809767827353)
              ·
                refine ⟨73521534869624107325870515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98028713159498809767827353 73521534869624107325870515)
                ·
                  refine ⟨110282302304436160988805773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73521534869624107325870515 110282302304436160988805773)
                  ·
                    refine ⟨41355863364163560370802165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110282302304436160988805773 41355863364163560370802165)
                    ·
                      refine ⟨3877112190390333784762703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41355863364163560370802165 3877112190390333784762703)
                      ·
                        rfl

theorem cell23_7550649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7550649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550649 prefixEnd_7550649 := by exact prefixLift 7550649
  have htrace : WordTrace (prefixWord ++ tailWord_7550649) baseStart_7550649 baseEnd_7550649 := by
    simpa [prefixWord, tailWord_7550649, baseEnd_7550649] using wordTrace_append hprefix tailTrace_7550649
  have hstable : (prefixWord ++ tailWord_7550649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550649).length < 2 ^ (prefixWord ++ tailWord_7550649).sum := by decide
  have hdescent : baseEnd_7550649 < baseStart_7550649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550663 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_7550663 : Nat := 118140960795 + 7550663 * 2 ^ 59
def prefixEnd_7550663 : Nat := 4983230072969 + 3 ^ 40 * 7550663 * 2
def baseEnd_7550663 : Nat := 3877119379119496729987639

theorem tailTrace_7550663 : CollatzResearch.WordTrace tailWord_7550663 prefixEnd_7550663 3877119379119496729987639 := by
  unfold tailWord_7550663
  simp only [CollatzResearch.WordTrace]
  refine ⟨275395304244244976419144643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183596869496163317612763095 275395304244244976419144643)
  ·
    refine ⟨413092956366367464628716965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275395304244244976419144643 413092956366367464628716965)
    ·
      refine ⟨77454929318693899617884431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413092956366367464628716965 77454929318693899617884431)
      ·
        refine ⟨116182393978040849426826647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77454929318693899617884431 116182393978040849426826647)
        ·
          refine ⟨174273590967061274140239971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116182393978040849426826647 174273590967061274140239971)
          ·
            refine ⟨261410386450591911210359957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174273590967061274140239971 261410386450591911210359957)
            ·
              refine ⟨12253611864871495837985623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 261410386450591911210359957 12253611864871495837985623)
              ·
                refine ⟨18380417797307243756978435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12253611864871495837985623 18380417797307243756978435)
                ·
                  refine ⟨27570626695960865635467653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18380417797307243756978435 27570626695960865635467653)
                  ·
                    refine ⟨5169492505492662306650185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27570626695960865635467653 5169492505492662306650185)
                    ·
                      refine ⟨3877119379119496729987639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169492505492662306650185 3877119379119496729987639)
                      ·
                        rfl

theorem cell23_7550663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_7550663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550663 prefixEnd_7550663 := by exact prefixLift 7550663
  have htrace : WordTrace (prefixWord ++ tailWord_7550663) baseStart_7550663 baseEnd_7550663 := by
    simpa [prefixWord, tailWord_7550663, baseEnd_7550663] using wordTrace_append hprefix tailTrace_7550663
  have hstable : (prefixWord ++ tailWord_7550663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550663).length < 2 ^ (prefixWord ++ tailWord_7550663).sum := by decide
  have hdescent : baseEnd_7550663 < baseStart_7550663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550729 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 10]
def baseStart_7550729 : Nat := 118140960795 + 7550729 * 2 ^ 59
def prefixEnd_7550729 : Nat := 4983230072969 + 3 ^ 40 * 7550729 * 2
def baseEnd_7550729 : Nat := 1292384422947564490587445

theorem tailTrace_7550729 : CollatzResearch.WordTrace tailWord_7550729 prefixEnd_7550729 1292384422947564490587445 := by
  unfold tailWord_7550729
  simp only [CollatzResearch.WordTrace]
  refine ⟨275397711462005869691047241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183598474308003913127364827 275397711462005869691047241)
  ·
    refine ⟨206548283596504402268285431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275397711462005869691047241 206548283596504402268285431)
    ·
      refine ⟨309822425394756603402428147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206548283596504402268285431 309822425394756603402428147)
      ·
        refine ⟨464733638092134905103642221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309822425394756603402428147 464733638092134905103642221)
        ·
          refine ⟨174275114284550589413865833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464733638092134905103642221 174275114284550589413865833)
          ·
            refine ⟨130706335713412942060399375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174275114284550589413865833 130706335713412942060399375)
            ·
              refine ⟨196059503570119413090599063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130706335713412942060399375 196059503570119413090599063)
              ·
                refine ⟨294089255355179119635898595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196059503570119413090599063 294089255355179119635898595)
                ·
                  refine ⟨441133883032768679453847893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294089255355179119635898595 441133883032768679453847893)
                  ·
                    refine ⟨1292384422947564490587445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 441133883032768679453847893 1292384422947564490587445)
                    ·
                      rfl

theorem cell23_7550729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_7550729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550729 prefixEnd_7550729 := by exact prefixLift 7550729
  have htrace : WordTrace (prefixWord ++ tailWord_7550729) baseStart_7550729 baseEnd_7550729 := by
    simpa [prefixWord, tailWord_7550729, baseEnd_7550729] using wordTrace_append hprefix tailTrace_7550729
  have hstable : (prefixWord ++ tailWord_7550729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550729).length < 2 ^ (prefixWord ++ tailWord_7550729).sum := by decide
  have hdescent : baseEnd_7550729 < baseStart_7550729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550753 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_7550753 : Nat := 118140960795 + 7550753 * 2 ^ 59
def prefixEnd_7550753 : Nat := 4983230072969 + 3 ^ 40 * 7550753 * 2
def baseEnd_7550753 : Nat := 3877165592378401377862225

theorem tailTrace_7550753 : CollatzResearch.WordTrace tailWord_7550753 prefixEnd_7550753 3877165592378401377862225 := by
  unfold tailWord_7550753
  simp only [CollatzResearch.WordTrace]
  refine ⟨275398586813918921789920913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183599057875945947859947275 275398586813918921789920913)
  ·
    refine ⟨206548940110439191342440685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275398586813918921789920913 206548940110439191342440685)
    ·
      refine ⟨77455852541414696753415257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206548940110439191342440685 77455852541414696753415257)
      ·
        refine ⟨58091889406061022565061443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77455852541414696753415257 58091889406061022565061443)
        ·
          refine ⟨87137834109091533847592165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58091889406061022565061443 87137834109091533847592165)
          ·
            refine ⟨16338343895454662596423531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87137834109091533847592165 16338343895454662596423531)
            ·
              refine ⟨24507515843181993894635297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16338343895454662596423531 24507515843181993894635297)
              ·
                refine ⟨18380636882386495420976473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24507515843181993894635297 18380636882386495420976473)
                ·
                  refine ⟨13785477661789871565732355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18380636882386495420976473 13785477661789871565732355)
                  ·
                    refine ⟨20678216492684807348598533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13785477661789871565732355 20678216492684807348598533)
                    ·
                      refine ⟨3877165592378401377862225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20678216492684807348598533 3877165592378401377862225)
                      ·
                        rfl

theorem cell23_7550753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_7550753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550753 prefixEnd_7550753 := by exact prefixLift 7550753
  have htrace : WordTrace (prefixWord ++ tailWord_7550753) baseStart_7550753 baseEnd_7550753 := by
    simpa [prefixWord, tailWord_7550753, baseEnd_7550753] using wordTrace_append hprefix tailTrace_7550753
  have hstable : (prefixWord ++ tailWord_7550753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550753).length < 2 ^ (prefixWord ++ tailWord_7550753).sum := by decide
  have hdescent : baseEnd_7550753 < baseStart_7550753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550843 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 4]
def baseStart_7550843 : Nat := 118140960795 + 7550843 * 2 ^ 59
def prefixEnd_7550843 : Nat := 4983230072969 + 3 ^ 40 * 7550843 * 2
def baseEnd_7550843 : Nat := 3877211805637306025736811

theorem tailTrace_7550843 : CollatzResearch.WordTrace tailWord_7550843 prefixEnd_7550843 3877211805637306025736811 := by
  unfold tailWord_7550843
  simp only [CollatzResearch.WordTrace]
  refine ⟨275401869383592867160697183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183601246255728578107131455 275401869383592867160697183)
  ·
    refine ⟨413102804075389300741045775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275401869383592867160697183 413102804075389300741045775)
    ·
      refine ⟨619654206113083951111568663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413102804075389300741045775 619654206113083951111568663)
      ·
        refine ⟨929481309169625926667352995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619654206113083951111568663 929481309169625926667352995)
        ·
          refine ⟨1394221963754438890001029493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929481309169625926667352995 1394221963754438890001029493)
          ·
            refine ⟨130708309101978645937596515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1394221963754438890001029493 130708309101978645937596515)
            ·
              refine ⟨196062463652967968906394773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130708309101978645937596515 196062463652967968906394773)
              ·
                refine ⟨9190427983732873542487255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196062463652967968906394773 9190427983732873542487255)
                ·
                  refine ⟨13785641975599310313730883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9190427983732873542487255 13785641975599310313730883)
                  ·
                    refine ⟨20678462963398965470596325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13785641975599310313730883 20678462963398965470596325)
                    ·
                      refine ⟨3877211805637306025736811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20678462963398965470596325 3877211805637306025736811)
                      ·
                        rfl

theorem cell23_7550843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 4].length) (baseStart_7550843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550843 prefixEnd_7550843 := by exact prefixLift 7550843
  have htrace : WordTrace (prefixWord ++ tailWord_7550843) baseStart_7550843 baseEnd_7550843 := by
    simpa [prefixWord, tailWord_7550843, baseEnd_7550843] using wordTrace_append hprefix tailTrace_7550843
  have hstable : (prefixWord ++ tailWord_7550843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550843).length < 2 ^ (prefixWord ++ tailWord_7550843).sum := by decide
  have hdescent : baseEnd_7550843 < baseStart_7550843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550853 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_7550853 : Nat := 118140960795 + 7550853 * 2 ^ 59
def prefixEnd_7550853 : Nat := 4983230072969 + 3 ^ 40 * 7550853 * 2
def baseEnd_7550853 : Nat := 1292405646814616995537255

theorem tailTrace_7550853 : CollatzResearch.WordTrace tailWord_7550853 prefixEnd_7550853 1292405646814616995537255 := by
  unfold tailWord_7550853
  simp only [CollatzResearch.WordTrace]
  refine ⟨275402234113556638868561213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183601489409037759245707475 275402234113556638868561213)
  ·
    refine ⟨103275837792583739575710455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275402234113556638868561213 103275837792583739575710455)
    ·
      refine ⟨154913756688875609363565683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103275837792583739575710455 154913756688875609363565683)
      ·
        refine ⟨232370635033313414045348525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154913756688875609363565683 232370635033313414045348525)
        ·
          refine ⟨87138988137492530267005697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232370635033313414045348525 87138988137492530267005697)
          ·
            refine ⟨65354241103119397700254273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87138988137492530267005697 65354241103119397700254273)
            ·
              refine ⟨49015680827339548275190705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65354241103119397700254273 49015680827339548275190705)
              ·
                refine ⟨36761760620504661206393029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49015680827339548275190705 36761760620504661206393029)
                ·
                  refine ⟨6892830116344623976198693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36761760620504661206393029 6892830116344623976198693)
                  ·
                    refine ⟨1292405646814616995537255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6892830116344623976198693 1292405646814616995537255)
                    ·
                      rfl

theorem cell23_7550853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_7550853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550853 prefixEnd_7550853 := by exact prefixLift 7550853
  have htrace : WordTrace (prefixWord ++ tailWord_7550853) baseStart_7550853 baseEnd_7550853 := by
    simpa [prefixWord, tailWord_7550853, baseEnd_7550853] using wordTrace_append hprefix tailTrace_7550853
  have hstable : (prefixWord ++ tailWord_7550853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550853).length < 2 ^ (prefixWord ++ tailWord_7550853).sum := by decide
  have hdescent : baseEnd_7550853 < baseStart_7550853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550860 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 7, 2, 2]
def baseStart_7550860 : Nat := 118140960795 + 7550860 * 2 ^ 59
def prefixEnd_7550860 : Nat := 4983230072969 + 3 ^ 40 * 7550860 * 2
def baseEnd_7550860 : Nat := 3877220534808432459224233

theorem tailTrace_7550860 : CollatzResearch.WordTrace tailWord_7550860 prefixEnd_7550860 3877220534808432459224233 := by
  unfold tailWord_7550860
  simp only [CollatzResearch.WordTrace]
  refine ⟨137701244712265639532033017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183601659616354186042710689 137701244712265639532033017)
  ·
    refine ⟨103275933534199229649024763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137701244712265639532033017 103275933534199229649024763)
    ·
      refine ⟨154913900301298844473537145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103275933534199229649024763 154913900301298844473537145)
      ·
        refine ⟨116185425225974133355152859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154913900301298844473537145 116185425225974133355152859)
        ·
          refine ⟨174278137838961200032729289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116185425225974133355152859 174278137838961200032729289)
          ·
            refine ⟨130708603379220900024546967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174278137838961200032729289 130708603379220900024546967)
            ·
              refine ⟨196062905068831350036820451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130708603379220900024546967 196062905068831350036820451)
              ·
                refine ⟨294094357603247025055230677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196062905068831350036820451 294094357603247025055230677)
                ·
                  refine ⟨6892836506326102149731969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 294094357603247025055230677 6892836506326102149731969)
                  ·
                    refine ⟨5169627379744576612298977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6892836506326102149731969 5169627379744576612298977)
                    ·
                      refine ⟨3877220534808432459224233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169627379744576612298977 3877220534808432459224233)
                      ·
                        rfl

theorem cell23_7550860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_7550860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550860 prefixEnd_7550860 := by exact prefixLift 7550860
  have htrace : WordTrace (prefixWord ++ tailWord_7550860) baseStart_7550860 baseEnd_7550860 := by
    simpa [prefixWord, tailWord_7550860, baseEnd_7550860] using wordTrace_append hprefix tailTrace_7550860
  have hstable : (prefixWord ++ tailWord_7550860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550860).length < 2 ^ (prefixWord ++ tailWord_7550860).sum := by decide
  have hdescent : baseEnd_7550860 < baseStart_7550860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550877 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_7550877 : Nat := 118140960795 + 7550877 * 2 ^ 59
def prefixEnd_7550877 : Nat := 4983230072969 + 3 ^ 40 * 7550877 * 2
def baseEnd_7550877 : Nat := 3877229263979558892711655

theorem tailTrace_7550877 : CollatzResearch.WordTrace tailWord_7550877 prefixEnd_7550877 3877229263979558892711655 := by
  unfold tailWord_7550877
  simp only [CollatzResearch.WordTrace]
  refine ⟨275403109465469690967434885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183602072976979793978289923 275403109465469690967434885)
  ·
    refine ⟨51638083024775567056394041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275403109465469690967434885 51638083024775567056394041)
    ·
      refine ⟨38728562268581675292295531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51638083024775567056394041 38728562268581675292295531)
      ·
        refine ⟨58092843402872512938443297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38728562268581675292295531 58092843402872512938443297)
        ·
          refine ⟨43569632552154384703832473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58092843402872512938443297 43569632552154384703832473)
          ·
            refine ⟨32677224414115788527874355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43569632552154384703832473 32677224414115788527874355)
            ·
              refine ⟨49015836621173682791811533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32677224414115788527874355 49015836621173682791811533)
              ·
                refine ⟨18380938732940131046929325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49015836621173682791811533 18380938732940131046929325)
                ·
                  refine ⟨6892852024852549142598497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18380938732940131046929325 6892852024852549142598497)
                  ·
                    refine ⟨5169639018639411856948873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6892852024852549142598497 5169639018639411856948873)
                    ·
                      refine ⟨3877229263979558892711655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169639018639411856948873 3877229263979558892711655)
                      ·
                        rfl

theorem cell23_7550877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_7550877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550877 prefixEnd_7550877 := by exact prefixLift 7550877
  have htrace : WordTrace (prefixWord ++ tailWord_7550877) baseStart_7550877 baseEnd_7550877 := by
    simpa [prefixWord, tailWord_7550877, baseEnd_7550877] using wordTrace_append hprefix tailTrace_7550877
  have hstable : (prefixWord ++ tailWord_7550877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550877).length < 2 ^ (prefixWord ++ tailWord_7550877).sum := by decide
  have hdescent : baseEnd_7550877 < baseStart_7550877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550897 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_7550897 : Nat := 118140960795 + 7550897 * 2 ^ 59
def prefixEnd_7550897 : Nat := 4983230072969 + 3 ^ 40 * 7550897 * 2
def baseEnd_7550897 : Nat := 3877239533592648814461563

theorem tailTrace_7550897 : CollatzResearch.WordTrace tailWord_7550897 prefixEnd_7550897 3877239533592648814461563 := by
  unfold tailWord_7550897
  simp only [CollatzResearch.WordTrace]
  refine ⟨275403838925397234383162945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183602559283598156255441963 275403838925397234383162945)
  ·
    refine ⟨206552879194047925787372209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275403838925397234383162945 206552879194047925787372209)
    ·
      refine ⟨154914659395535944340529157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206552879194047925787372209 154914659395535944340529157)
      ·
        refine ⟨29046498636662989563849217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154914659395535944340529157 29046498636662989563849217)
        ·
          refine ⟨21784873977497242172886913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29046498636662989563849217 21784873977497242172886913)
          ·
            refine ⟨16338655483122931629665185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21784873977497242172886913 16338655483122931629665185)
            ·
              refine ⟨12253991612342198722248889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16338655483122931629665185 12253991612342198722248889)
              ·
                refine ⟨9190493709256649041686667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12253991612342198722248889 9190493709256649041686667)
                ·
                  refine ⟨13785740563884973562530001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9190493709256649041686667 13785740563884973562530001)
                  ·
                    refine ⟨10339305422913730171897501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13785740563884973562530001 10339305422913730171897501)
                    ·
                      refine ⟨3877239533592648814461563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10339305422913730171897501 3877239533592648814461563)
                      ·
                        rfl

theorem cell23_7550897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_7550897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550897 prefixEnd_7550897 := by exact prefixLift 7550897
  have htrace : WordTrace (prefixWord ++ tailWord_7550897) baseStart_7550897 baseEnd_7550897 := by
    simpa [prefixWord, tailWord_7550897, baseEnd_7550897] using wordTrace_append hprefix tailTrace_7550897
  have hstable : (prefixWord ++ tailWord_7550897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550897).length < 2 ^ (prefixWord ++ tailWord_7550897).sum := by decide
  have hdescent : baseEnd_7550897 < baseStart_7550897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7550984 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_7550984 : Nat := 118140960795 + 7550984 * 2 ^ 59
def prefixEnd_7550984 : Nat := 4983230072969 + 3 ^ 40 * 7550984 * 2
def baseEnd_7550984 : Nat := 3877284206409589974073663

theorem tailTrace_7550984 : CollatzResearch.WordTrace tailWord_7550984 prefixEnd_7550984 3877284206409589974073663 := by
  unfold tailWord_7550984
  simp only [CollatzResearch.WordTrace]
  refine ⟨137703506038041024120790003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183604674717388032161053337 137703506038041024120790003)
  ·
    refine ⟨206555259057061536181185005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137703506038041024120790003 206555259057061536181185005)
    ·
      refine ⟨77458222146398076067944377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206555259057061536181185005 77458222146398076067944377)
      ·
        refine ⟨58093666609798557050958283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77458222146398076067944377 58093666609798557050958283)
        ·
          refine ⟨87140499914697835576437425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58093666609798557050958283 87140499914697835576437425)
          ·
            refine ⟨65355374936023376682328069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87140499914697835576437425 65355374936023376682328069)
            ·
              refine ⟨12254132800504383127936513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65355374936023376682328069 12254132800504383127936513)
              ·
                refine ⟨9190599600378287345952385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12254132800504383127936513 9190599600378287345952385)
                ·
                  refine ⟨6892949700283715509464289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9190599600378287345952385 6892949700283715509464289)
                  ·
                    refine ⟨5169712275212786632098217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6892949700283715509464289 5169712275212786632098217)
                    ·
                      refine ⟨3877284206409589974073663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169712275212786632098217 3877284206409589974073663)
                      ·
                        rfl

theorem cell23_7550984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_7550984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7550984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7550984 prefixEnd_7550984 := by exact prefixLift 7550984
  have htrace : WordTrace (prefixWord ++ tailWord_7550984) baseStart_7550984 baseEnd_7550984 := by
    simpa [prefixWord, tailWord_7550984, baseEnd_7550984] using wordTrace_append hprefix tailTrace_7550984
  have hstable : (prefixWord ++ tailWord_7550984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7550984).length < 2 ^ (prefixWord ++ tailWord_7550984).sum := by decide
  have hdescent : baseEnd_7550984 < baseStart_7550984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7550984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551000 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 2, 3, 3]
def baseStart_7551000 : Nat := 118140960795 + 7551000 * 2 ^ 59
def prefixEnd_7551000 : Nat := 4983230072969 + 3 ^ 40 * 7551000 * 2
def baseEnd_7551000 : Nat := 3877292422100061911473589

theorem tailTrace_7551000 : CollatzResearch.WordTrace tailWord_7551000 prefixEnd_7551000 3877292422100061911473589 := by
  unfold tailWord_7551000
  simp only [CollatzResearch.WordTrace]
  refine ⟨137703797822012041487081227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183605063762682721982774969 137703797822012041487081227)
  ·
    refine ⟨206555696733018062230621841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137703797822012041487081227 206555696733018062230621841)
    ·
      refine ⟨154916772549763546672966381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206555696733018062230621841 154916772549763546672966381)
      ·
        refine ⟨58093789706161330002362393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154916772549763546672966381 58093789706161330002362393)
        ·
          refine ⟨43570342279620997501771795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58093789706161330002362393 43570342279620997501771795)
          ·
            refine ⟨65355513419431496252657693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43570342279620997501771795 65355513419431496252657693)
            ·
              refine ⟨24508317532286811094746635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65355513419431496252657693 24508317532286811094746635)
              ·
                refine ⟨36762476298430216642119953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24508317532286811094746635 36762476298430216642119953)
                ·
                  refine ⟨27571857223822662481589965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36762476298430216642119953 27571857223822662481589965)
                  ·
                    refine ⟨10339446458933498430596237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27571857223822662481589965 10339446458933498430596237)
                    ·
                      refine ⟨3877292422100061911473589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10339446458933498430596237 3877292422100061911473589)
                      ·
                        rfl

theorem cell23_7551000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_7551000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551000 prefixEnd_7551000 := by exact prefixLift 7551000
  have htrace : WordTrace (prefixWord ++ tailWord_7551000) baseStart_7551000 baseEnd_7551000 := by
    simpa [prefixWord, tailWord_7551000, baseEnd_7551000] using wordTrace_append hprefix tailTrace_7551000
  have hstable : (prefixWord ++ tailWord_7551000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551000).length < 2 ^ (prefixWord ++ tailWord_7551000).sum := by decide
  have hdescent : baseEnd_7551000 < baseStart_7551000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551084 : List Nat := [2, 2, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_7551084 : Nat := 118140960795 + 7551084 * 2 ^ 59
def prefixEnd_7551084 : Nat := 4983230072969 + 3 ^ 40 * 7551084 * 2
def baseEnd_7551084 : Nat := 1292445184825013194274401

theorem tailTrace_7551084 : CollatzResearch.WordTrace tailWord_7551084 prefixEnd_7551084 1292445184825013194274401 := by
  unfold tailWord_7551084
  simp only [CollatzResearch.WordTrace]
  refine ⟨137705329687859882660110153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183607106250479843546813537 137705329687859882660110153)
  ·
    refine ⟨103278997265894911995082615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137705329687859882660110153 103278997265894911995082615)
    ·
      refine ⟨154918495898842367992623923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103278997265894911995082615 154918495898842367992623923)
      ·
        refine ⟨232377743848263551988935885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154918495898842367992623923 232377743848263551988935885)
        ·
          refine ⟨87141653943098831995850957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232377743848263551988935885 87141653943098831995850957)
          ·
            refine ⟨32678120228662061998444109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87141653943098831995850957 32678120228662061998444109)
            ·
              refine ⟨12254295085748273249416541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32678120228662061998444109 12254295085748273249416541)
              ·
                refine ⟨4595360657155602468531203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12254295085748273249416541 4595360657155602468531203)
                ·
                  refine ⟨6893040985733403702796805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595360657155602468531203 6893040985733403702796805)
                  ·
                    refine ⟨1292445184825013194274401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6893040985733403702796805 1292445184825013194274401)
                    ·
                      rfl

theorem cell23_7551084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_7551084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551084 prefixEnd_7551084 := by exact prefixLift 7551084
  have htrace : WordTrace (prefixWord ++ tailWord_7551084) baseStart_7551084 baseEnd_7551084 := by
    simpa [prefixWord, tailWord_7551084, baseEnd_7551084] using wordTrace_append hprefix tailTrace_7551084
  have hstable : (prefixWord ++ tailWord_7551084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551084).length < 2 ^ (prefixWord ++ tailWord_7551084).sum := by decide
  have hdescent : baseEnd_7551084 < baseStart_7551084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551094 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_7551094 : Nat := 118140960795 + 7551094 * 2 ^ 59
def prefixEnd_7551094 : Nat := 4983230072969 + 3 ^ 40 * 7551094 * 2
def baseEnd_7551094 : Nat := 3877340689281584543698157

theorem tailTrace_7551094 : CollatzResearch.WordTrace tailWord_7551094 prefixEnd_7551094 3877340689281584543698157 := by
  unfold tailWord_7551094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17213189006605221064255271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183607349403789024685389557 17213189006605221064255271)
  ·
    refine ⟨25819783509907831596382907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17213189006605221064255271 25819783509907831596382907)
    ·
      refine ⟨38729675264861747394574361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25819783509907831596382907 38729675264861747394574361)
      ·
        refine ⟨29047256448646310545930771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38729675264861747394574361 29047256448646310545930771)
        ·
          refine ⟨43570884672969465818896157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29047256448646310545930771 43570884672969465818896157)
          ·
            refine ⟨16339081752363549682086059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43570884672969465818896157 16339081752363549682086059)
            ·
              refine ⟨24508622628545324523129089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16339081752363549682086059 24508622628545324523129089)
              ·
                refine ⟨18381466971408993392346817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24508622628545324523129089 18381466971408993392346817)
                ·
                  refine ⟨13786100228556745044260113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18381466971408993392346817 13786100228556745044260113)
                  ·
                    refine ⟨10339575171417558783195085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13786100228556745044260113 10339575171417558783195085)
                    ·
                      refine ⟨3877340689281584543698157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10339575171417558783195085 3877340689281584543698157)
                      ·
                        rfl

theorem cell23_7551094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_7551094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551094 prefixEnd_7551094 := by exact prefixLift 7551094
  have htrace : WordTrace (prefixWord ++ tailWord_7551094) baseStart_7551094 baseEnd_7551094 := by
    simpa [prefixWord, tailWord_7551094, baseEnd_7551094] using wordTrace_append hprefix tailTrace_7551094
  have hstable : (prefixWord ++ tailWord_7551094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551094).length < 2 ^ (prefixWord ++ tailWord_7551094).sum := by decide
  have hdescent : baseEnd_7551094 < baseStart_7551094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551101 : List Nat := [1, 4, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_7551101 : Nat := 118140960795 + 7551101 * 2 ^ 59
def prefixEnd_7551101 : Nat := 4983230072969 + 3 ^ 40 * 7551101 * 2
def baseEnd_7551101 : Nat := 1292448094548722005436875

theorem tailTrace_7551101 : CollatzResearch.WordTrace tailWord_7551101 prefixEnd_7551101 1292448094548722005436875 := by
  unfold tailWord_7551101
  simp only [CollatzResearch.WordTrace]
  refine ⟨275411279416658177223589157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183607519611105451482392771 275411279416658177223589157)
  ·
    refine ⟨51639614890623408229422967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275411279416658177223589157 51639614890623408229422967)
    ·
      refine ⟨77459422335935112344134451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51639614890623408229422967 77459422335935112344134451)
      ·
        refine ⟨116189133503902668516201677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77459422335935112344134451 116189133503902668516201677)
        ·
          refine ⟨43570925063963500693575629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116189133503902668516201677 43570925063963500693575629)
          ·
            refine ⟨16339096898986312760090861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43570925063963500693575629 16339096898986312760090861)
            ·
              refine ⟨6127161337119867285034073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16339096898986312760090861 6127161337119867285034073)
              ·
                refine ⟨4595371002839900463775555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6127161337119867285034073 4595371002839900463775555)
                ·
                  refine ⟨6893056504259850695663333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595371002839900463775555 6893056504259850695663333)
                  ·
                    refine ⟨1292448094548722005436875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6893056504259850695663333 1292448094548722005436875)
                    ·
                      rfl

theorem cell23_7551101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_7551101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551101 prefixEnd_7551101 := by exact prefixLift 7551101
  have htrace : WordTrace (prefixWord ++ tailWord_7551101) baseStart_7551101 baseEnd_7551101 := by
    simpa [prefixWord, tailWord_7551101, baseEnd_7551101] using wordTrace_append hprefix tailTrace_7551101
  have hstable : (prefixWord ++ tailWord_7551101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551101).length < 2 ^ (prefixWord ++ tailWord_7551101).sum := by decide
  have hdescent : baseEnd_7551101 < baseStart_7551101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551114 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 6]
def baseStart_7551114 : Nat := 118140960795 + 7551114 * 2 ^ 59
def prefixEnd_7551114 : Nat := 4983230072969 + 3 ^ 40 * 7551114 * 2
def baseEnd_7551114 : Nat := 430816773210519385049785

theorem tailTrace_7551114 : CollatzResearch.WordTrace tailWord_7551114 prefixEnd_7551114 430816773210519385049785 := by
  unfold tailWord_7551114
  simp only [CollatzResearch.WordTrace]
  refine ⟨68852938391402770110953099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183607835710407386962541597 68852938391402770110953099)
  ·
    refine ⟨103279407587104155166429649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68852938391402770110953099 103279407587104155166429649)
    ·
      refine ⟨77459555690328116374822237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103279407587104155166429649 77459555690328116374822237)
      ·
        refine ⟨29047333383873043640558339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77459555690328116374822237 29047333383873043640558339)
        ·
          refine ⟨43571000075809565460837509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29047333383873043640558339 43571000075809565460837509)
          ·
            refine ⟨8169562514214293523907033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43571000075809565460837509 8169562514214293523907033)
            ·
              refine ⟨6127171885660720142930275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8169562514214293523907033 6127171885660720142930275)
              ·
                refine ⟨9190757828491080214395413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127171885660720142930275 9190757828491080214395413)
                ·
                  refine ⟨430816773210519385049785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9190757828491080214395413 430816773210519385049785)
                  ·
                    rfl

theorem cell23_7551114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_7551114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551114 prefixEnd_7551114 := by exact prefixLift 7551114
  have htrace : WordTrace (prefixWord ++ tailWord_7551114) baseStart_7551114 baseEnd_7551114 := by
    simpa [prefixWord, tailWord_7551114, baseEnd_7551114] using wordTrace_append hprefix tailTrace_7551114
  have hstable : (prefixWord ++ tailWord_7551114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551114).length < 2 ^ (prefixWord ++ tailWord_7551114).sum := by decide
  have hdescent : baseEnd_7551114 < baseStart_7551114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551127 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 3, 5]
def baseStart_7551127 : Nat := 118140960795 + 7551127 * 2 ^ 59
def prefixEnd_7551127 : Nat := 4983230072969 + 3 ^ 40 * 7551127 * 2
def baseEnd_7551127 : Nat := 1292452544714394304861835

theorem tailTrace_7551127 : CollatzResearch.WordTrace tailWord_7551127 prefixEnd_7551127 1292452544714394304861835 := by
  unfold tailWord_7551127
  simp only [CollatzResearch.WordTrace]
  refine ⟨275412227714563983664035635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183608151809709322442690423 275412227714563983664035635)
  ·
    refine ⟨413118341571845975496053453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275412227714563983664035635 413118341571845975496053453)
    ·
      refine ⟨154919378089442240811020045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413118341571845975496053453 154919378089442240811020045)
      ·
        refine ⟨58094766783540840304132517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154919378089442240811020045 58094766783540840304132517)
        ·
          refine ⟨10892768771913907557024847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58094766783540840304132517 10892768771913907557024847)
          ·
            refine ⟨16339153157870861335537271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10892768771913907557024847 16339153157870861335537271)
            ·
              refine ⟨24508729736806292003305907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16339153157870861335537271 24508729736806292003305907)
              ·
                refine ⟨36763094605209438004958861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24508729736806292003305907 36763094605209438004958861)
                ·
                  refine ⟨13786160476953539251859573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36763094605209438004958861 13786160476953539251859573)
                  ·
                    refine ⟨1292452544714394304861835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13786160476953539251859573 1292452544714394304861835)
                    ·
                      rfl

theorem cell23_7551127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_7551127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551127 prefixEnd_7551127 := by exact prefixLift 7551127
  have htrace : WordTrace (prefixWord ++ tailWord_7551127) baseStart_7551127 baseEnd_7551127 := by
    simpa [prefixWord, tailWord_7551127, baseEnd_7551127] using wordTrace_append hprefix tailTrace_7551127
  have hstable : (prefixWord ++ tailWord_7551127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551127).length < 2 ^ (prefixWord ++ tailWord_7551127).sum := by decide
  have hdescent : baseEnd_7551127 < baseStart_7551127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551160 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_7551160 : Nat := 118140960795 + 7551160 * 2 ^ 59
def prefixEnd_7551160 : Nat := 4983230072969 + 3 ^ 40 * 7551160 * 2
def baseEnd_7551160 : Nat := 3877374579004781285472853

theorem tailTrace_7551160 : CollatzResearch.WordTrace tailWord_7551160 prefixEnd_7551160 3877374579004781285472853 := by
  unfold tailWord_7551160
  simp only [CollatzResearch.WordTrace]
  refine ⟨137706715661722215149993467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183608954215629620199991289 137706715661722215149993467)
  ·
    refine ⟨206560073492583322724990201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137706715661722215149993467 206560073492583322724990201)
    ·
      refine ⟨154920055119437492043742651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206560073492583322724990201 154920055119437492043742651)
      ·
        refine ⟨232380082679156238065613977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154920055119437492043742651 232380082679156238065613977)
        ·
          refine ⟨174285062009367178549210483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232380082679156238065613977 174285062009367178549210483)
          ·
            refine ⟨261427593014050767823815725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174285062009367178549210483 261427593014050767823815725)
            ·
              refine ⟨98035347380269037933930897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261427593014050767823815725 98035347380269037933930897)
              ·
                refine ⟨73526510535201778450448173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98035347380269037933930897 73526510535201778450448173)
                ·
                  refine ⟨27572441450700666918918065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73526510535201778450448173 27572441450700666918918065)
                  ·
                    refine ⟨20679331088025500189188549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27572441450700666918918065 20679331088025500189188549)
                    ·
                      refine ⟨3877374579004781285472853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20679331088025500189188549 3877374579004781285472853)
                      ·
                        rfl

theorem cell23_7551160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_7551160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551160 prefixEnd_7551160 := by exact prefixLift 7551160
  have htrace : WordTrace (prefixWord ++ tailWord_7551160) baseStart_7551160 baseEnd_7551160 := by
    simpa [prefixWord, tailWord_7551160, baseEnd_7551160] using wordTrace_append hprefix tailTrace_7551160
  have hstable : (prefixWord ++ tailWord_7551160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551160).length < 2 ^ (prefixWord ++ tailWord_7551160).sum := by decide
  have hdescent : baseEnd_7551160 < baseStart_7551160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551231 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 2, 1, 3]
def baseStart_7551231 : Nat := 118140960795 + 7551231 * 2 ^ 59
def prefixEnd_7551231 : Nat := 4983230072969 + 3 ^ 40 * 7551231 * 2
def baseEnd_7551231 : Nat := 3877411036131250507685027

theorem tailTrace_7551231 : CollatzResearch.WordTrace tailWord_7551231 prefixEnd_7551231 3877411036131250507685027 := by
  unfold tailWord_7551231
  simp only [CollatzResearch.WordTrace]
  refine ⟨275416020906187209425821547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183610680604124806283881031 275416020906187209425821547)
  ·
    refine ⟨413124031359280814138732321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275416020906187209425821547 413124031359280814138732321)
    ·
      refine ⟨309843023519460610604049241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413124031359280814138732321 309843023519460610604049241)
      ·
        refine ⟨232382267639595457953036931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309843023519460610604049241 232382267639595457953036931)
        ·
          refine ⟨348573401459393186929555397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232382267639595457953036931 348573401459393186929555397)
          ·
            refine ⟨65357512773636222549291637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348573401459393186929555397 65357512773636222549291637)
            ·
              refine ⟨6127266822528395863996091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65357512773636222549291637 6127266822528395863996091)
              ·
                refine ⟨9190900233792593795994137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127266822528395863996091 9190900233792593795994137)
                ·
                  refine ⟨6893175175344445346995603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9190900233792593795994137 6893175175344445346995603)
                  ·
                    refine ⟨10339762763016668020493405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6893175175344445346995603 10339762763016668020493405)
                    ·
                      refine ⟨3877411036131250507685027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10339762763016668020493405 3877411036131250507685027)
                      ·
                        rfl

theorem cell23_7551231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_7551231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551231 prefixEnd_7551231 := by exact prefixLift 7551231
  have htrace : WordTrace (prefixWord ++ tailWord_7551231) baseStart_7551231 baseEnd_7551231 := by
    simpa [prefixWord, tailWord_7551231, baseEnd_7551231] using wordTrace_append hprefix tailTrace_7551231
  have hstable : (prefixWord ++ tailWord_7551231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551231).length < 2 ^ (prefixWord ++ tailWord_7551231).sum := by decide
  have hdescent : baseEnd_7551231 < baseStart_7551231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551241 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 1, 3, 2]
def baseStart_7551241 : Nat := 118140960795 + 7551241 * 2 ^ 59
def prefixEnd_7551241 : Nat := 4983230072969 + 3 ^ 40 * 7551241 * 2
def baseEnd_7551241 : Nat := 3877416170937795468559981

theorem tailTrace_7551241 : CollatzResearch.WordTrace tailWord_7551241 prefixEnd_7551241 3877416170937795468559981 := by
  unfold tailWord_7551241
  simp only [CollatzResearch.WordTrace]
  refine ⟨275416385636150981133685577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183610923757433987422457051 275416385636150981133685577)
  ·
    refine ⟨206562289227113235850264183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275416385636150981133685577 206562289227113235850264183)
    ·
      refine ⟨309843433840669853775396275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206562289227113235850264183 309843433840669853775396275)
      ·
        refine ⟨464765150761004780663094413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309843433840669853775396275 464765150761004780663094413)
        ·
          refine ⟨174286931535376792748660405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464765150761004780663094413 174286931535376792748660405)
          ·
            refine ⟨16339399831441574320186913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174286931535376792748660405 16339399831441574320186913)
            ·
              refine ⟨12254549873581180740140185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16339399831441574320186913 12254549873581180740140185)
              ·
                refine ⟨9190912405185885555105139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12254549873581180740140185 9190912405185885555105139)
                ·
                  refine ⟨13786368607778828332657709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9190912405185885555105139 13786368607778828332657709)
                  ·
                    refine ⟨5169888227917060624746641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13786368607778828332657709 5169888227917060624746641)
                    ·
                      refine ⟨3877416170937795468559981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169888227917060624746641 3877416170937795468559981)
                      ·
                        rfl

theorem cell23_7551241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 3, 2].length) (baseStart_7551241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551241 prefixEnd_7551241 := by exact prefixLift 7551241
  have htrace : WordTrace (prefixWord ++ tailWord_7551241) baseStart_7551241 baseEnd_7551241 := by
    simpa [prefixWord, tailWord_7551241, baseEnd_7551241] using wordTrace_append hprefix tailTrace_7551241
  have hstable : (prefixWord ++ tailWord_7551241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551241).length < 2 ^ (prefixWord ++ tailWord_7551241).sum := by decide
  have hdescent : baseEnd_7551241 < baseStart_7551241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551280 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_7551280 : Nat := 118140960795 + 7551280 * 2 ^ 59
def prefixEnd_7551280 : Nat := 4983230072969 + 3 ^ 40 * 7551280 * 2
def baseEnd_7551280 : Nat := 3877436196683320815972301

theorem tailTrace_7551280 : CollatzResearch.WordTrace tailWord_7551280 prefixEnd_7551280 3877436196683320815972301 := by
  unfold tailWord_7551280
  simp only [CollatzResearch.WordTrace]
  refine ⟨137708904041504845397177647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183611872055339793862903529 137708904041504845397177647)
  ·
    refine ⟨206563356062257268095766471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137708904041504845397177647 206563356062257268095766471)
    ·
      refine ⟨309845034093385902143649707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206563356062257268095766471 309845034093385902143649707)
      ·
        refine ⟨464767551140078853215474561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309845034093385902143649707 464767551140078853215474561)
        ·
          refine ⟨348575663355059139911605921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464767551140078853215474561 348575663355059139911605921)
          ·
            refine ⟨261431747516294354933704441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348575663355059139911605921 261431747516294354933704441)
            ·
              refine ⟨196073810637220766200278331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261431747516294354933704441 196073810637220766200278331)
              ·
                refine ⟨294110715955831149300417497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196073810637220766200278331 294110715955831149300417497)
                ·
                  refine ⟨220583036966873361975313123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294110715955831149300417497 220583036966873361975313123)
                  ·
                    refine ⟨330874555450310042962969685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220583036966873361975313123 330874555450310042962969685)
                    ·
                      refine ⟨3877436196683320815972301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 330874555450310042962969685 3877436196683320815972301)
                      ·
                        rfl

theorem cell23_7551280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_7551280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551280 prefixEnd_7551280 := by exact prefixLift 7551280
  have htrace : WordTrace (prefixWord ++ tailWord_7551280) baseStart_7551280 baseEnd_7551280 := by
    simpa [prefixWord, tailWord_7551280, baseEnd_7551280] using wordTrace_append hprefix tailTrace_7551280
  have hstable : (prefixWord ++ tailWord_7551280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551280).length < 2 ^ (prefixWord ++ tailWord_7551280).sum := by decide
  have hdescent : baseEnd_7551280 < baseStart_7551280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551287 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_7551287 : Nat := 118140960795 + 7551287 * 2 ^ 59
def prefixEnd_7551287 : Nat := 4983230072969 + 3 ^ 40 * 7551287 * 2
def baseEnd_7551287 : Nat := 3877439791047902288584769

theorem tailTrace_7551287 : CollatzResearch.WordTrace tailWord_7551287 prefixEnd_7551287 3877439791047902288584769 := by
  unfold tailWord_7551287
  simp only [CollatzResearch.WordTrace]
  refine ⟨275418063393984330989860115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183612042262656220659906743 275418063393984330989860115)
  ·
    refine ⟨413127095090976496484790173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275418063393984330989860115 413127095090976496484790173)
    ·
      refine ⟨154922660659116186181796315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413127095090976496484790173 154922660659116186181796315)
      ·
        refine ⟨232383990988674279272694473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154922660659116186181796315 232383990988674279272694473)
        ·
          refine ⟨174287993241505709454520855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232383990988674279272694473 174287993241505709454520855)
          ·
            refine ⟨261431989862258564181781283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174287993241505709454520855 261431989862258564181781283)
            ·
              refine ⟨392147984793387846272671925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261431989862258564181781283 392147984793387846272671925)
              ·
                refine ⟨36763873574380110588062993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392147984793387846272671925 36763873574380110588062993)
                ·
                  refine ⟨27572905180785082941047245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36763873574380110588062993 27572905180785082941047245)
                  ·
                    refine ⟨10339839442794406102892717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27572905180785082941047245 10339839442794406102892717)
                    ·
                      refine ⟨3877439791047902288584769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10339839442794406102892717 3877439791047902288584769)
                      ·
                        rfl

theorem cell23_7551287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_7551287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551287 prefixEnd_7551287 := by exact prefixLift 7551287
  have htrace : WordTrace (prefixWord ++ tailWord_7551287) baseStart_7551287 baseEnd_7551287 := by
    simpa [prefixWord, tailWord_7551287, baseEnd_7551287] using wordTrace_append hprefix tailTrace_7551287
  have hstable : (prefixWord ++ tailWord_7551287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551287).length < 2 ^ (prefixWord ++ tailWord_7551287).sum := by decide
  have hdescent : baseEnd_7551287 < baseStart_7551287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551288 : List Nat := [2, 1, 2, 1, 3, 1, 6, 1, 2, 2, 2]
def baseStart_7551288 : Nat := 118140960795 + 7551288 * 2 ^ 59
def prefixEnd_7551288 : Nat := 4983230072969 + 3 ^ 40 * 7551288 * 2
def baseEnd_7551288 : Nat := 3877440304528556784672265

theorem tailTrace_7551288 : CollatzResearch.WordTrace tailWord_7551288 prefixEnd_7551288 3877440304528556784672265 := by
  unfold tailWord_7551288
  simp only [CollatzResearch.WordTrace]
  refine ⟨137709049933490354080323259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183612066577987138773764345 137709049933490354080323259)
  ·
    refine ⟨206563574900235531120484889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137709049933490354080323259 206563574900235531120484889)
    ·
      refine ⟨154922681175176648340363667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206563574900235531120484889 154922681175176648340363667)
      ·
        refine ⟨232384021762764972510545501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154922681175176648340363667 232384021762764972510545501)
        ·
          refine ⟨87144008161036864691454563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232384021762764972510545501 87144008161036864691454563)
          ·
            refine ⟨130716012241555297037181845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87144008161036864691454563 130716012241555297037181845)
            ·
              refine ⟨6127313073822904548617899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130716012241555297037181845 6127313073822904548617899)
              ·
                refine ⟨9190969610734356822926849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127313073822904548617899 9190969610734356822926849)
                ·
                  refine ⟨6893227208050767617195137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9190969610734356822926849 6893227208050767617195137)
                  ·
                    refine ⟨5169920406038075712896353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6893227208050767617195137 5169920406038075712896353)
                    ·
                      refine ⟨3877440304528556784672265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169920406038075712896353 3877440304528556784672265)
                      ·
                        rfl

theorem cell23_7551288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_7551288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551288 prefixEnd_7551288 := by exact prefixLift 7551288
  have htrace : WordTrace (prefixWord ++ tailWord_7551288) baseStart_7551288 baseEnd_7551288 := by
    simpa [prefixWord, tailWord_7551288, baseEnd_7551288] using wordTrace_append hprefix tailTrace_7551288
  have hstable : (prefixWord ++ tailWord_7551288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551288).length < 2 ^ (prefixWord ++ tailWord_7551288).sum := by decide
  have hdescent : baseEnd_7551288 < baseStart_7551288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551328 : List Nat := [2, 1, 1, 3, 5, 2, 2, 2, 5]
def baseStart_7551328 : Nat := 118140960795 + 7551328 * 2 ^ 59
def prefixEnd_7551328 : Nat := 4983230072969 + 3 ^ 40 * 7551328 * 2
def baseEnd_7551328 : Nat := 430828982639415180908009

theorem tailTrace_7551328 : CollatzResearch.WordTrace tailWord_7551328 prefixEnd_7551328 430828982639415180908009 := by
  unfold tailWord_7551328
  simp only [CollatzResearch.WordTrace]
  refine ⟨137709779393417897496051319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183613039191223863328068425 137709779393417897496051319)
  ·
    refine ⟨206564669090126846244076979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137709779393417897496051319 206564669090126846244076979)
    ·
      refine ⟨309847003635190269366115469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206564669090126846244076979 309847003635190269366115469)
      ·
        refine ⟨116192626363196351012293301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309847003635190269366115469 116192626363196351012293301)
        ·
          refine ⟨10893058721549657907402497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116192626363196351012293301 10893058721549657907402497)
          ·
            refine ⟨8169794041162243430551873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10893058721549657907402497 8169794041162243430551873)
            ·
              refine ⟨6127345530871682572913905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8169794041162243430551873 6127345530871682572913905)
              ·
                refine ⟨4595509148153761929685429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6127345530871682572913905 4595509148153761929685429)
                ·
                  refine ⟨430828982639415180908009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4595509148153761929685429 430828982639415180908009)
                  ·
                    rfl

theorem cell23_7551328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 5].length) (baseStart_7551328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551328 prefixEnd_7551328 := by exact prefixLift 7551328
  have htrace : WordTrace (prefixWord ++ tailWord_7551328) baseStart_7551328 baseEnd_7551328 := by
    simpa [prefixWord, tailWord_7551328, baseEnd_7551328] using wordTrace_append hprefix tailTrace_7551328
  have hstable : (prefixWord ++ tailWord_7551328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551328).length < 2 ^ (prefixWord ++ tailWord_7551328).sum := by decide
  have hdescent : baseEnd_7551328 < baseStart_7551328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551344 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 1, 6, 2]
def baseStart_7551344 : Nat := 118140960795 + 7551344 * 2 ^ 59
def prefixEnd_7551344 : Nat := 4983230072969 + 3 ^ 40 * 7551344 * 2
def baseEnd_7551344 : Nat := 3877469059445208565572007

theorem tailTrace_7551344 : CollatzResearch.WordTrace tailWord_7551344 prefixEnd_7551344 3877469059445208565572007 := by
  unfold tailWord_7551344
  simp only [CollatzResearch.WordTrace]
  refine ⟨137710071177388914862342543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183613428236518553149790057 137710071177388914862342543)
  ·
    refine ⟨206565106766083372293513815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137710071177388914862342543 206565106766083372293513815)
    ·
      refine ⟨309847660149125058440270723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206565106766083372293513815 309847660149125058440270723)
      ·
        refine ⟨464771490223687587660406085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309847660149125058440270723 464771490223687587660406085)
        ·
          refine ⟨87144654416941422686326141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464771490223687587660406085 87144654416941422686326141)
          ·
            refine ⟨32679245406353033507372303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87144654416941422686326141 32679245406353033507372303)
            ·
              refine ⟨49018868109529550261058455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32679245406353033507372303 49018868109529550261058455)
              ·
                refine ⟨73528302164294325391587683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49018868109529550261058455 73528302164294325391587683)
                ·
                  refine ⟨110292453246441488087381525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73528302164294325391587683 110292453246441488087381525)
                  ·
                    refine ⟨5169958745926944754096009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110292453246441488087381525 5169958745926944754096009)
                    ·
                      refine ⟨3877469059445208565572007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5169958745926944754096009 3877469059445208565572007)
                      ·
                        rfl

theorem cell23_7551344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 1, 6, 2].length) (baseStart_7551344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551344 prefixEnd_7551344 := by exact prefixLift 7551344
  have htrace : WordTrace (prefixWord ++ tailWord_7551344) baseStart_7551344 baseEnd_7551344 := by
    simpa [prefixWord, tailWord_7551344, baseEnd_7551344] using wordTrace_append hprefix tailTrace_7551344
  have hstable : (prefixWord ++ tailWord_7551344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551344).length < 2 ^ (prefixWord ++ tailWord_7551344).sum := by decide
  have hdescent : baseEnd_7551344 < baseStart_7551344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551347 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 3]
def baseStart_7551347 : Nat := 118140960795 + 7551347 * 2 ^ 59
def prefixEnd_7551347 : Nat := 4983230072969 + 3 ^ 40 * 7551347 * 2
def baseEnd_7551347 : Nat := 3877470599887172053834493

theorem tailTrace_7551347 : CollatzResearch.WordTrace tailWord_7551347 prefixEnd_7551347 3877470599887172053834493 := by
  unfold tailWord_7551347
  simp only [CollatzResearch.WordTrace]
  refine ⟨275420251773766961237044295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183613501182511307491362863 275420251773766961237044295)
  ·
    refine ⟨413130377660650441855566443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275420251773766961237044295 413130377660650441855566443)
    ·
      refine ⟨619695566490975662783349665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413130377660650441855566443 619695566490975662783349665)
      ·
        refine ⟨464771674868231747087512249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619695566490975662783349665 464771674868231747087512249)
        ·
          refine ⟨348578756151173810315634187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464771674868231747087512249 348578756151173810315634187)
          ·
            refine ⟨522868134226760715473451281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348578756151173810315634187 522868134226760715473451281)
            ·
              refine ⟨392151100670070536605088461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522868134226760715473451281 392151100670070536605088461)
              ·
                refine ⟨147056662751276451226908173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392151100670070536605088461 147056662751276451226908173)
                ·
                  refine ⟨55146248531728669210090565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147056662751276451226908173 55146248531728669210090565)
                  ·
                    refine ⟨10339921599699125476891981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55146248531728669210090565 10339921599699125476891981)
                    ·
                      refine ⟨3877470599887172053834493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10339921599699125476891981 3877470599887172053834493)
                      ·
                        rfl

theorem cell23_7551347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_7551347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551347 prefixEnd_7551347 := by exact prefixLift 7551347
  have htrace : WordTrace (prefixWord ++ tailWord_7551347) baseStart_7551347 baseEnd_7551347 := by
    simpa [prefixWord, tailWord_7551347, baseEnd_7551347] using wordTrace_append hprefix tailTrace_7551347
  have hstable : (prefixWord ++ tailWord_7551347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551347).length < 2 ^ (prefixWord ++ tailWord_7551347).sum := by decide
  have hdescent : baseEnd_7551347 < baseStart_7551347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551361 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_7551361 : Nat := 118140960795 + 7551361 * 2 ^ 59
def prefixEnd_7551361 : Nat := 4983230072969 + 3 ^ 40 * 7551361 * 2
def baseEnd_7551361 : Nat := 3877477788616334999059429

theorem tailTrace_7551361 : CollatzResearch.WordTrace tailWord_7551361 prefixEnd_7551361 3877477788616334999059429 := by
  unfold tailWord_7551361
  simp only [CollatzResearch.WordTrace]
  refine ⟨275420762395716241628053937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183613841597144161085369291 275420762395716241628053937)
  ·
    refine ⟨206565571796787181221040453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275420762395716241628053937 206565571796787181221040453)
    ·
      refine ⟨38731044711897596478945085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206565571796787181221040453 38731044711897596478945085)
      ·
        refine ⟨14524141766961598679604407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38731044711897596478945085 14524141766961598679604407)
        ·
          refine ⟨21786212650442398019406611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524141766961598679604407 21786212650442398019406611)
          ·
            refine ⟨32679318975663597029109917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21786212650442398019406611 32679318975663597029109917)
            ·
              refine ⟨12254744615873848885916219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32679318975663597029109917 12254744615873848885916219)
              ·
                refine ⟨18382116923810773328874329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12254744615873848885916219 18382116923810773328874329)
                ·
                  refine ⟨13786587692858079996655747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18382116923810773328874329 13786587692858079996655747)
                  ·
                    refine ⟨20679881539287119994983621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13786587692858079996655747 20679881539287119994983621)
                    ·
                      refine ⟨3877477788616334999059429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20679881539287119994983621 3877477788616334999059429)
                      ·
                        rfl

theorem cell23_7551361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_7551361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551361 prefixEnd_7551361 := by exact prefixLift 7551361
  have htrace : WordTrace (prefixWord ++ tailWord_7551361) baseStart_7551361 baseEnd_7551361 := by
    simpa [prefixWord, tailWord_7551361, baseEnd_7551361] using wordTrace_append hprefix tailTrace_7551361
  have hstable : (prefixWord ++ tailWord_7551361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551361).length < 2 ^ (prefixWord ++ tailWord_7551361).sum := by decide
  have hdescent : baseEnd_7551361 < baseStart_7551361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551364 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_7551364 : Nat := 118140960795 + 7551364 * 2 ^ 59
def prefixEnd_7551364 : Nat := 4983230072969 + 3 ^ 40 * 7551364 * 2
def baseEnd_7551364 : Nat := 3877479329058298487321915

theorem tailTrace_7551364 : CollatzResearch.WordTrace tailWord_7551364 prefixEnd_7551364 3877479329058298487321915 := by
  unfold tailWord_7551364
  simp only [CollatzResearch.WordTrace]
  refine ⟨137710435907352686570206573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183613914543136915426942097 137710435907352686570206573)
  ·
    refine ⟨51641413465257257463827465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137710435907352686570206573 51641413465257257463827465)
    ·
      refine ⟨38731060098942943097870599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51641413465257257463827465 38731060098942943097870599)
      ·
        refine ⟨58096590148414414646805899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38731060098942943097870599 58096590148414414646805899)
        ·
          refine ⟨87144885222621621970208849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58096590148414414646805899 87144885222621621970208849)
          ·
            refine ⟨65358663916966216477656637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87144885222621621970208849 65358663916966216477656637)
            ·
              refine ⟨24509498968862331179121239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65358663916966216477656637 24509498968862331179121239)
              ·
                refine ⟨36764248453293496768681859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24509498968862331179121239 36764248453293496768681859)
                ·
                  refine ⟨55146372679940245153022789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36764248453293496768681859 55146372679940245153022789)
                  ·
                    refine ⟨10339944877488795966191773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55146372679940245153022789 10339944877488795966191773)
                    ·
                      refine ⟨3877479329058298487321915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10339944877488795966191773 3877479329058298487321915)
                      ·
                        rfl

theorem cell23_7551364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_7551364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551364 prefixEnd_7551364 := by exact prefixLift 7551364
  have htrace : WordTrace (prefixWord ++ tailWord_7551364) baseStart_7551364 baseEnd_7551364 := by
    simpa [prefixWord, tailWord_7551364, baseEnd_7551364] using wordTrace_append hprefix tailTrace_7551364
  have hstable : (prefixWord ++ tailWord_7551364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551364).length < 2 ^ (prefixWord ++ tailWord_7551364).sum := by decide
  have hdescent : baseEnd_7551364 < baseStart_7551364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551367 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 8]
def baseStart_7551367 : Nat := 118140960795 + 7551367 * 2 ^ 59
def prefixEnd_7551367 : Nat := 4983230072969 + 3 ^ 40 * 7551367 * 2
def baseEnd_7551367 : Nat := 430831207722251330620489

theorem tailTrace_7551367 : CollatzResearch.WordTrace tailWord_7551367 prefixEnd_7551367 430831207722251330620489 := by
  unfold tailWord_7551367
  simp only [CollatzResearch.WordTrace]
  refine ⟨275420981233694504652772355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183613987489129669768514903 275420981233694504652772355)
  ·
    refine ⟨413131471850541756979158533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275420981233694504652772355 413131471850541756979158533)
    ·
      refine ⟨77462150971976579433592225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413131471850541756979158533 77462150971976579433592225)
      ·
        refine ⟨58096613228982434575194169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77462150971976579433592225 58096613228982434575194169)
        ·
          refine ⟨43572459921736825931395627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58096613228982434575194169 43572459921736825931395627)
          ·
            refine ⟨65358689882605238897093441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43572459921736825931395627 65358689882605238897093441)
            ·
              refine ⟨49019017411953929172820081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65358689882605238897093441 49019017411953929172820081)
              ·
                refine ⟨36764263058965446879615061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49019017411953929172820081 36764263058965446879615061)
                ·
                  refine ⟨430831207722251330620489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36764263058965446879615061 430831207722251330620489)
                  ·
                    rfl

theorem cell23_7551367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 8].length) (baseStart_7551367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551367 prefixEnd_7551367 := by exact prefixLift 7551367
  have htrace : WordTrace (prefixWord ++ tailWord_7551367) baseStart_7551367 baseEnd_7551367 := by
    simpa [prefixWord, tailWord_7551367, baseEnd_7551367] using wordTrace_append hprefix tailTrace_7551367
  have hstable : (prefixWord ++ tailWord_7551367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551367).length < 2 ^ (prefixWord ++ tailWord_7551367).sum := by decide
  have hdescent : baseEnd_7551367 < baseStart_7551367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551371 : List Nat := [1, 1, 1, 1, 4, 4, 1, 5, 1, 4]
def baseStart_7551371 : Nat := 118140960795 + 7551371 * 2 ^ 59
def prefixEnd_7551371 : Nat := 4983230072969 + 3 ^ 40 * 7551371 * 2
def baseEnd_7551371 : Nat := 1292494307807626653311461

theorem tailTrace_7551371 : CollatzResearch.WordTrace tailWord_7551371 prefixEnd_7551371 1292494307807626653311461 := by
  unfold tailWord_7551371
  simp only [CollatzResearch.WordTrace]
  refine ⟨275421127125680013335917967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183614084750453342223945311 275421127125680013335917967)
  ·
    refine ⟨413131690688520020003876951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275421127125680013335917967 413131690688520020003876951)
    ·
      refine ⟨619697536032780030005815427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413131690688520020003876951 619697536032780030005815427)
      ·
        refine ⟨929546304049170045008723141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619697536032780030005815427 929546304049170045008723141)
        ·
          refine ⟨174289932009219383439135589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 929546304049170045008723141 174289932009219383439135589)
          ·
            refine ⟨32679362251728634394837923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174289932009219383439135589 32679362251728634394837923)
            ·
              refine ⟨49019043377592951592256885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32679362251728634394837923 49019043377592951592256885)
              ·
                refine ⟨4595535316649339211774083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49019043377592951592256885 4595535316649339211774083)
                ·
                  refine ⟨6893302974974008817661125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595535316649339211774083 6893302974974008817661125)
                  ·
                    refine ⟨1292494307807626653311461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6893302974974008817661125 1292494307807626653311461)
                    ·
                      rfl

theorem cell23_7551371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 1, 4].length) (baseStart_7551371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551371 prefixEnd_7551371 := by exact prefixLift 7551371
  have htrace : WordTrace (prefixWord ++ tailWord_7551371) baseStart_7551371 baseEnd_7551371 := by
    simpa [prefixWord, tailWord_7551371, baseEnd_7551371] using wordTrace_append hprefix tailTrace_7551371
  have hstable : (prefixWord ++ tailWord_7551371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551371).length < 2 ^ (prefixWord ++ tailWord_7551371).sum := by decide
  have hdescent : baseEnd_7551371 < baseStart_7551371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551374 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7551374 : Nat := 118140960795 + 7551374 * 2 ^ 59
def prefixEnd_7551374 : Nat := 4983230072969 + 3 ^ 40 * 7551374 * 2
def baseEnd_7551374 : Nat := 3877484463864843448196869

theorem tailTrace_7551374 : CollatzResearch.WordTrace tailWord_7551374 prefixEnd_7551374 3877484463864843448196869 := by
  unfold tailWord_7551374
  simp only [CollatzResearch.WordTrace]
  refine ⟨34427654568083643106034647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183614157696446096565518117 34427654568083643106034647)
  ·
    refine ⟨51641481852125464659051971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34427654568083643106034647 51641481852125464659051971)
    ·
      refine ⟨77462222778188196988577957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51641481852125464659051971 77462222778188196988577957)
      ·
        refine ⟨14524166770910286935358367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77462222778188196988577957 14524166770910286935358367)
        ·
          refine ⟨21786250156365430403037551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524166770910286935358367 21786250156365430403037551)
          ·
            refine ⟨32679375234548145604556327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21786250156365430403037551 32679375234548145604556327)
            ·
              refine ⟨49019062851822218406834491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32679375234548145604556327 49019062851822218406834491)
              ·
                refine ⟨73528594277733327610251737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49019062851822218406834491 73528594277733327610251737)
                ·
                  refine ⟨55146445708299995707688803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73528594277733327610251737 55146445708299995707688803)
                  ·
                    refine ⟨82719668562449993561533205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55146445708299995707688803 82719668562449993561533205)
                    ·
                      refine ⟨3877484463864843448196869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82719668562449993561533205 3877484463864843448196869)
                      ·
                        rfl

theorem cell23_7551374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7551374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551374 prefixEnd_7551374 := by exact prefixLift 7551374
  have htrace : WordTrace (prefixWord ++ tailWord_7551374) baseStart_7551374 baseEnd_7551374 := by
    simpa [prefixWord, tailWord_7551374, baseEnd_7551374] using wordTrace_append hprefix tailTrace_7551374
  have hstable : (prefixWord ++ tailWord_7551374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551374).length < 2 ^ (prefixWord ++ tailWord_7551374).sum := by decide
  have hdescent : baseEnd_7551374 < baseStart_7551374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551384 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 8]
def baseStart_7551384 : Nat := 118140960795 + 7551384 * 2 ^ 59
def prefixEnd_7551384 : Nat := 4983230072969 + 3 ^ 40 * 7551384 * 2
def baseEnd_7551384 : Nat := 430832177630154267674647

theorem tailTrace_7551384 : CollatzResearch.WordTrace tailWord_7551384 prefixEnd_7551384 430832177630154267674647 := by
  unfold tailWord_7551384
  simp only [CollatzResearch.WordTrace]
  refine ⟨137710800637316458278070603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183614400849755277704094137 137710800637316458278070603)
  ·
    refine ⟨206566200955974687417105905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137710800637316458278070603 206566200955974687417105905)
    ·
      refine ⟨154924650716981015562829429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206566200955974687417105905 154924650716981015562829429)
      ·
        refine ⟨14524186004716970209015259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154924650716981015562829429 14524186004716970209015259)
        ·
          refine ⟨21786279007075455313522889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524186004716970209015259 21786279007075455313522889)
          ·
            refine ⟨16339709255306591485142167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21786279007075455313522889 16339709255306591485142167)
            ·
              refine ⟨24509563882959887227713251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16339709255306591485142167 24509563882959887227713251)
              ·
                refine ⟨36764345824439830841569877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24509563882959887227713251 36764345824439830841569877)
                ·
                  refine ⟨430832177630154267674647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36764345824439830841569877 430832177630154267674647)
                  ·
                    rfl

theorem cell23_7551384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 8].length) (baseStart_7551384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551384 prefixEnd_7551384 := by exact prefixLift 7551384
  have htrace : WordTrace (prefixWord ++ tailWord_7551384) baseStart_7551384 baseEnd_7551384 := by
    simpa [prefixWord, tailWord_7551384, baseEnd_7551384] using wordTrace_append hprefix tailTrace_7551384
  have hstable : (prefixWord ++ tailWord_7551384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551384).length < 2 ^ (prefixWord ++ tailWord_7551384).sum := by decide
  have hdescent : baseEnd_7551384 < baseStart_7551384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551421 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_7551421 : Nat := 118140960795 + 7551421 * 2 ^ 59
def prefixEnd_7551421 : Nat := 4983230072969 + 3 ^ 40 * 7551421 * 2
def baseEnd_7551421 : Nat := 3877508597455604764309153

theorem tailTrace_7551421 : CollatzResearch.WordTrace tailWord_7551421 prefixEnd_7551421 3877508597455604764309153 := by
  unfold tailWord_7551421
  simp only [CollatzResearch.WordTrace]
  refine ⟨275422950775498871875238117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183615300516999247916825411 275422950775498871875238117)
  ·
    refine ⟨51641803270406038476607147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275422950775498871875238117 51641803270406038476607147)
    ·
      refine ⟨77462704905609057714910721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51641803270406038476607147 77462704905609057714910721)
      ·
        refine ⟨58097028679206793286183041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77462704905609057714910721 58097028679206793286183041)
        ·
          refine ⟨43572771509405094964637281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58097028679206793286183041 43572771509405094964637281)
          ·
            refine ⟨32679578632053821223477961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43572771509405094964637281 32679578632053821223477961)
            ·
              refine ⟨24509683974040365917608471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32679578632053821223477961 24509683974040365917608471)
              ·
                refine ⟨36764525961060548876412707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24509683974040365917608471 36764525961060548876412707)
                ·
                  refine ⟨55146788941590823314619061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36764525961060548876412707 55146788941590823314619061)
                  ·
                    refine ⟨5170011463274139685745537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55146788941590823314619061 5170011463274139685745537)
                    ·
                      refine ⟨3877508597455604764309153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170011463274139685745537 3877508597455604764309153)
                      ·
                        rfl

theorem cell23_7551421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_7551421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551421 prefixEnd_7551421 := by exact prefixLift 7551421
  have htrace : WordTrace (prefixWord ++ tailWord_7551421) baseStart_7551421 baseEnd_7551421 := by
    simpa [prefixWord, tailWord_7551421, baseEnd_7551421] using wordTrace_append hprefix tailTrace_7551421
  have hstable : (prefixWord ++ tailWord_7551421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551421).length < 2 ^ (prefixWord ++ tailWord_7551421).sum := by decide
  have hdescent : baseEnd_7551421 < baseStart_7551421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551427 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 3, 6]
def baseStart_7551427 : Nat := 118140960795 + 7551427 * 2 ^ 59
def prefixEnd_7551427 : Nat := 4983230072969 + 3 ^ 40 * 7551427 * 2
def baseEnd_7551427 : Nat := 1292503892779843913611375

theorem tailTrace_7551427 : CollatzResearch.WordTrace tailWord_7551427 prefixEnd_7551427 1292503892779843913611375 := by
  unfold tailWord_7551427
  simp only [CollatzResearch.WordTrace]
  refine ⟨275423169613477134899956535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183615446408984756599971023 275423169613477134899956535)
  ·
    refine ⟨413134754420215702349934803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275423169613477134899956535 413134754420215702349934803)
    ·
      refine ⟨619702131630323553524902205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413134754420215702349934803 619702131630323553524902205)
      ·
        refine ⟨232388299361371332571838327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 619702131630323553524902205 232388299361371332571838327)
        ·
          refine ⟨348582449042056998857757491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232388299361371332571838327 348582449042056998857757491)
          ·
            refine ⟨522873673563085498286636237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348582449042056998857757491 522873673563085498286636237)
            ·
              refine ⟨196077627586157061857488589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522873673563085498286636237 196077627586157061857488589)
              ·
                refine ⟨73529110344808898196558221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196077627586157061857488589 73529110344808898196558221)
                ·
                  refine ⟨27573416379303336823709333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73529110344808898196558221 27573416379303336823709333)
                  ·
                    refine ⟨1292503892779843913611375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27573416379303336823709333 1292503892779843913611375)
                    ·
                      rfl

theorem cell23_7551427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 6].length) (baseStart_7551427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551427 prefixEnd_7551427 := by exact prefixLift 7551427
  have htrace : WordTrace (prefixWord ++ tailWord_7551427) baseStart_7551427 baseEnd_7551427 := by
    simpa [prefixWord, tailWord_7551427, baseEnd_7551427] using wordTrace_append hprefix tailTrace_7551427
  have hstable : (prefixWord ++ tailWord_7551427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551427).length < 2 ^ (prefixWord ++ tailWord_7551427).sum := by decide
  have hdescent : baseEnd_7551427 < baseStart_7551427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551464 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_7551464 : Nat := 118140960795 + 7551464 * 2 ^ 59
def prefixEnd_7551464 : Nat := 4983230072969 + 3 ^ 40 * 7551464 * 2
def baseEnd_7551464 : Nat := 3877530677123748096071455

theorem tailTrace_7551464 : CollatzResearch.WordTrace tailWord_7551464 prefixEnd_7551464 3877530677123748096071455 := by
  unfold tailWord_7551464
  simp only [CollatzResearch.WordTrace]
  refine ⟨137712259557171545109526723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183616346076228726812702297 137712259557171545109526723)
  ·
    refine ⟨206568389335757317664290085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137712259557171545109526723 206568389335757317664290085)
    ·
      refine ⟨38731573000454497062054391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206568389335757317664290085 38731573000454497062054391)
      ·
        refine ⟨58097359500681745593081587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38731573000454497062054391 58097359500681745593081587)
        ·
          refine ⟨87146039251022618389622381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58097359500681745593081587 87146039251022618389622381)
          ·
            refine ⟨32679764719133481896108393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87146039251022618389622381 32679764719133481896108393)
            ·
              refine ⟨24509823539350111422081295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32679764719133481896108393 24509823539350111422081295)
              ·
                refine ⟨36764735309025167133121943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24509823539350111422081295 36764735309025167133121943)
                ·
                  refine ⟨55147102963537750699682915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36764735309025167133121943 55147102963537750699682915)
                  ·
                    refine ⟨82720654445306626049524373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55147102963537750699682915 82720654445306626049524373)
                    ·
                      refine ⟨3877530677123748096071455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82720654445306626049524373 3877530677123748096071455)
                      ·
                        rfl

theorem cell23_7551464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_7551464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551464 prefixEnd_7551464 := by exact prefixLift 7551464
  have htrace : WordTrace (prefixWord ++ tailWord_7551464) baseStart_7551464 baseEnd_7551464 := by
    simpa [prefixWord, tailWord_7551464, baseEnd_7551464] using wordTrace_append hprefix tailTrace_7551464
  have hstable : (prefixWord ++ tailWord_7551464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551464).length < 2 ^ (prefixWord ++ tailWord_7551464).sum := by decide
  have hdescent : baseEnd_7551464 < baseStart_7551464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551485 : List Nat := [1, 4, 1, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_7551485 : Nat := 118140960795 + 7551485 * 2 ^ 59
def prefixEnd_7551485 : Nat := 4983230072969 + 3 ^ 40 * 7551485 * 2
def baseEnd_7551485 : Nat := 3877541460217492513908859

theorem tailTrace_7551485 : CollatzResearch.WordTrace tailWord_7551485 prefixEnd_7551485 3877541460217492513908859 := by
  unfold tailWord_7551485
  simp only [CollatzResearch.WordTrace]
  refine ⟨275425285047267010805567909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183616856698178007203711939 275425285047267010805567909)
  ·
    refine ⟨51642240946362564526043983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275425285047267010805567909 51642240946362564526043983)
    ·
      refine ⟨77463361419543846789065975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51642240946362564526043983 77463361419543846789065975)
      ·
        refine ⟨116195042129315770183598963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77463361419543846789065975 116195042129315770183598963)
        ·
          refine ⟨174292563193973655275398445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116195042129315770183598963 174292563193973655275398445)
          ·
            refine ⟨65359711197740120728274417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174292563193973655275398445 65359711197740120728274417)
            ·
              refine ⟨49019783398305090546205813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65359711197740120728274417 49019783398305090546205813)
              ·
                refine ⟨4595604693591102238706795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49019783398305090546205813 4595604693591102238706795)
                ·
                  refine ⟨6893407040386653358060193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595604693591102238706795 6893407040386653358060193)
                  ·
                    refine ⟨5170055280289990018545145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6893407040386653358060193 5170055280289990018545145)
                    ·
                      refine ⟨3877541460217492513908859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170055280289990018545145 3877541460217492513908859)
                      ·
                        rfl

theorem cell23_7551485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_7551485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551485 prefixEnd_7551485 := by exact prefixLift 7551485
  have htrace : WordTrace (prefixWord ++ tailWord_7551485) baseStart_7551485 baseEnd_7551485 := by
    simpa [prefixWord, tailWord_7551485, baseEnd_7551485] using wordTrace_append hprefix tailTrace_7551485
  have hstable : (prefixWord ++ tailWord_7551485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551485).length < 2 ^ (prefixWord ++ tailWord_7551485).sum := by decide
  have hdescent : baseEnd_7551485 < baseStart_7551485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551502 : List Nat := [4, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_7551502 : Nat := 118140960795 + 7551502 * 2 ^ 59
def prefixEnd_7551502 : Nat := 4983230072969 + 3 ^ 40 * 7551502 * 2
def baseEnd_7551502 : Nat := 3877550189388618947396281

theorem tailTrace_7551502 : CollatzResearch.WordTrace tailWord_7551502 prefixEnd_7551502 3877550189388618947396281 := by
  unfold tailWord_7551502
  simp only [CollatzResearch.WordTrace]
  refine ⟨34428238136025677838617095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183617270058803615139291173 34428238136025677838617095)
  ·
    refine ⟨51642357204038516757925643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34428238136025677838617095 51642357204038516757925643)
    ·
      refine ⟨77463535806057775136888465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51642357204038516757925643 77463535806057775136888465)
      ·
        refine ⟨58097651854543331352666349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77463535806057775136888465 58097651854543331352666349)
        ·
          refine ⟨21786619445453749257249881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58097651854543331352666349 21786619445453749257249881)
          ·
            refine ⟨16339964584090311942937411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21786619445453749257249881 16339964584090311942937411)
            ·
              refine ⟨24509946876135467914406117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16339964584090311942937411 24509946876135467914406117)
              ·
                refine ⟨4595615039275400233951147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24509946876135467914406117 4595615039275400233951147)
                ·
                  refine ⟨6893422558913100350926721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595615039275400233951147 6893422558913100350926721)
                  ·
                    refine ⟨5170066919184825263195041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6893422558913100350926721 5170066919184825263195041)
                    ·
                      refine ⟨3877550189388618947396281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170066919184825263195041 3877550189388618947396281)
                      ·
                        rfl

theorem cell23_7551502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_7551502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551502 prefixEnd_7551502 := by exact prefixLift 7551502
  have htrace : WordTrace (prefixWord ++ tailWord_7551502) baseStart_7551502 baseEnd_7551502 := by
    simpa [prefixWord, tailWord_7551502, baseEnd_7551502] using wordTrace_append hprefix tailTrace_7551502
  have hstable : (prefixWord ++ tailWord_7551502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551502).length < 2 ^ (prefixWord ++ tailWord_7551502).sum := by decide
  have hdescent : baseEnd_7551502 < baseStart_7551502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551508 : List Nat := [2, 4, 3, 1, 1, 3, 1, 8]
def baseStart_7551508 : Nat := 118140960795 + 7551508 * 2 ^ 59
def prefixEnd_7551508 : Nat := 4983230072969 + 3 ^ 40 * 7551508 * 2
def baseEnd_7551508 : Nat := 143613084084168367552639

theorem tailTrace_7551508 : CollatzResearch.WordTrace tailWord_7551508 prefixEnd_7551508 143613084084168367552639 := by
  unfold tailWord_7551508
  simp only [CollatzResearch.WordTrace]
  refine ⟨137713061963091842866827589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183617415950789123822436785 137713061963091842866827589)
  ·
    refine ⟨25821199118079720537530173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137713061963091842866827589 25821199118079720537530173)
    ·
      refine ⟨9682949669279895201573815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25821199118079720537530173 9682949669279895201573815)
      ·
        refine ⟨14524424503919842802360723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9682949669279895201573815 14524424503919842802360723)
        ·
          refine ⟨21786636755879764203541085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524424503919842802360723 21786636755879764203541085)
          ·
            refine ⟨8169988783454911576327907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21786636755879764203541085 8169988783454911576327907)
            ·
              refine ⟨12254983175182367364491861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8169988783454911576327907 12254983175182367364491861)
              ·
                refine ⟨143613084084168367552639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12254983175182367364491861 143613084084168367552639)
                ·
                  rfl

theorem cell23_7551508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 8].length) (baseStart_7551508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551508 prefixEnd_7551508 := by exact prefixLift 7551508
  have htrace : WordTrace (prefixWord ++ tailWord_7551508) baseStart_7551508 baseEnd_7551508 := by
    simpa [prefixWord, tailWord_7551508, baseEnd_7551508] using wordTrace_append hprefix tailTrace_7551508
  have hstable : (prefixWord ++ tailWord_7551508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551508).length < 2 ^ (prefixWord ++ tailWord_7551508).sum := by decide
  have hdescent : baseEnd_7551508 < baseStart_7551508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551544 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_7551544 : Nat := 118140960795 + 7551544 * 2 ^ 59
def prefixEnd_7551544 : Nat := 4983230072969 + 3 ^ 40 * 7551544 * 2
def baseEnd_7551544 : Nat := 3877571755576107783071087

theorem tailTrace_7551544 : CollatzResearch.WordTrace tailWord_7551544 prefixEnd_7551544 3877571755576107783071087 := by
  unfold tailWord_7551544
  simp only [CollatzResearch.WordTrace]
  refine ⟨137713718477026631940982843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183618291302702175921310457 137713718477026631940982843)
  ·
    refine ⟨206570577715539947911474265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137713718477026631940982843 206570577715539947911474265)
    ·
      refine ⟨154927933286654960933605699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206570577715539947911474265 154927933286654960933605699)
      ·
        refine ⟨232391899929982441400408549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154927933286654960933605699 232391899929982441400408549)
        ·
          refine ⟨43573481236871707762576603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232391899929982441400408549 43573481236871707762576603)
          ·
            refine ⟨65360221855307561643864905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43573481236871707762576603 65360221855307561643864905)
            ·
              refine ⟨49020166391480671232898679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65360221855307561643864905 49020166391480671232898679)
              ·
                refine ⟨73530249587221006849348019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49020166391480671232898679 73530249587221006849348019)
                ·
                  refine ⟨110295374380831510274022029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73530249587221006849348019 110295374380831510274022029)
                  ·
                    refine ⟨41360765392811816352758261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110295374380831510274022029 41360765392811816352758261)
                    ·
                      refine ⟨3877571755576107783071087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41360765392811816352758261 3877571755576107783071087)
                      ·
                        rfl

theorem cell23_7551544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_7551544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551544 prefixEnd_7551544 := by exact prefixLift 7551544
  have htrace : WordTrace (prefixWord ++ tailWord_7551544) baseStart_7551544 baseEnd_7551544 := by
    simpa [prefixWord, tailWord_7551544, baseEnd_7551544] using wordTrace_append hprefix tailTrace_7551544
  have hstable : (prefixWord ++ tailWord_7551544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551544).length < 2 ^ (prefixWord ++ tailWord_7551544).sum := by decide
  have hdescent : baseEnd_7551544 < baseStart_7551544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551601 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 3, 7, 2]
def baseStart_7551601 : Nat := 118140960795 + 7551601 * 2 ^ 59
def prefixEnd_7551601 : Nat := 4983230072969 + 3 ^ 40 * 7551601 * 2
def baseEnd_7551601 : Nat := 3877601023973414060058325

theorem tailTrace_7551601 : CollatzResearch.WordTrace tailWord_7551601 prefixEnd_7551601 3877601023973414060058325 := by
  unfold tailWord_7551601
  simp only [CollatzResearch.WordTrace]
  refine ⟨275429515914846762616790657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183619677276564508411193771 275429515914846762616790657)
  ·
    refine ⟨206572136936135071962592993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275429515914846762616790657 206572136936135071962592993)
    ·
      refine ⟨154929102702101303971944745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206572136936135071962592993 154929102702101303971944745)
      ·
        refine ⟨116196827026575977978958559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154929102702101303971944745 116196827026575977978958559)
        ·
          refine ⟨174295240539863966968437839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116196827026575977978958559 174295240539863966968437839)
          ·
            refine ⟨261442860809795950452656759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174295240539863966968437839 261442860809795950452656759)
            ·
              refine ⟨392164291214693925678985139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261442860809795950452656759 392164291214693925678985139)
              ·
                refine ⟨588246436822040888518477709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392164291214693925678985139 588246436822040888518477709)
                ·
                  refine ⟨220592413808265333194429141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 588246436822040888518477709 220592413808265333194429141)
                  ·
                    refine ⟨5170134698631218746744433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 220592413808265333194429141 5170134698631218746744433)
                    ·
                      refine ⟨3877601023973414060058325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170134698631218746744433 3877601023973414060058325)
                      ·
                        rfl

theorem cell23_7551601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_7551601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551601 prefixEnd_7551601 := by exact prefixLift 7551601
  have htrace : WordTrace (prefixWord ++ tailWord_7551601) baseStart_7551601 baseEnd_7551601 := by
    simpa [prefixWord, tailWord_7551601, baseEnd_7551601] using wordTrace_append hprefix tailTrace_7551601
  have hstable : (prefixWord ++ tailWord_7551601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551601).length < 2 ^ (prefixWord ++ tailWord_7551601).sum := by decide
  have hdescent : baseEnd_7551601 < baseStart_7551601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551621 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_7551621 : Nat := 118140960795 + 7551621 * 2 ^ 59
def prefixEnd_7551621 : Nat := 4983230072969 + 3 ^ 40 * 7551621 * 2
def baseEnd_7551621 : Nat := 3877611293586503981808233

theorem tailTrace_7551621 : CollatzResearch.WordTrace tailWord_7551621 prefixEnd_7551621 3877611293586503981808233 := by
  unfold tailWord_7551621
  simp only [CollatzResearch.WordTrace]
  refine ⟨275430245374774306032518717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183620163583182870688345811 275430245374774306032518717)
  ·
    refine ⟨103286342015540364762194519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275430245374774306032518717 103286342015540364762194519)
    ·
      refine ⟨154929513023310547143291779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103286342015540364762194519 154929513023310547143291779)
      ·
        refine ⟨232394269534965820714937669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154929513023310547143291779 232394269534965820714937669)
        ·
          refine ⟨43573925537806091384050813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232394269534965820714937669 43573925537806091384050813)
          ·
            refine ⟨16340222076677284269019055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43573925537806091384050813 16340222076677284269019055)
            ·
              refine ⟨24510333115015926403528583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16340222076677284269019055 24510333115015926403528583)
              ·
                refine ⟨36765499672523889605292875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24510333115015926403528583 36765499672523889605292875)
                ·
                  refine ⟨55148249508785834407939313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36765499672523889605292875 55148249508785834407939313)
                  ·
                    refine ⟨41361187131589375805954485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55148249508785834407939313 41361187131589375805954485)
                    ·
                      refine ⟨3877611293586503981808233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41361187131589375805954485 3877611293586503981808233)
                      ·
                        rfl

theorem cell23_7551621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_7551621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551621 prefixEnd_7551621 := by exact prefixLift 7551621
  have htrace : WordTrace (prefixWord ++ tailWord_7551621) baseStart_7551621 baseEnd_7551621 := by
    simpa [prefixWord, tailWord_7551621, baseEnd_7551621] using wordTrace_append hprefix tailTrace_7551621
  have hstable : (prefixWord ++ tailWord_7551621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551621).length < 2 ^ (prefixWord ++ tailWord_7551621).sum := by decide
  have hdescent : baseEnd_7551621 < baseStart_7551621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551626 : List Nat := [3, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_7551626 : Nat := 118140960795 + 7551626 * 2 ^ 59
def prefixEnd_7551626 : Nat := 4983230072969 + 3 ^ 40 * 7551626 * 2
def baseEnd_7551626 : Nat := 3877613860989776462245711

theorem tailTrace_7551626 : CollatzResearch.WordTrace tailWord_7551626 prefixEnd_7551626 3877613860989776462245711 := by
  unfold tailWord_7551626
  simp only [CollatzResearch.WordTrace]
  refine ⟨68857606934939047971612683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183620285159837461257633821 68857606934939047971612683)
  ·
    refine ⟨103286410402408571957419025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68857606934939047971612683 103286410402408571957419025)
    ·
      refine ⟨77464807801806428968064269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103286410402408571957419025 77464807801806428968064269)
      ·
        refine ⟨29049302925677410863024101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77464807801806428968064269 29049302925677410863024101)
        ·
          refine ⟨5446744298564514536817019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29049302925677410863024101 5446744298564514536817019)
          ·
            refine ⟨8170116447846771805225529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5446744298564514536817019 8170116447846771805225529)
            ·
              refine ⟨6127587335885078853919147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8170116447846771805225529 6127587335885078853919147)
              ·
                refine ⟨9191381003827618280878721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127587335885078853919147 9191381003827618280878721)
                ·
                  refine ⟨6893535752870713710659041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9191381003827618280878721 6893535752870713710659041)
                  ·
                    refine ⟨5170151814653035282994281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6893535752870713710659041 5170151814653035282994281)
                    ·
                      refine ⟨3877613860989776462245711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170151814653035282994281 3877613860989776462245711)
                      ·
                        rfl

theorem cell23_7551626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_7551626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551626 prefixEnd_7551626 := by exact prefixLift 7551626
  have htrace : WordTrace (prefixWord ++ tailWord_7551626) baseStart_7551626 baseEnd_7551626 := by
    simpa [prefixWord, tailWord_7551626, baseEnd_7551626] using wordTrace_append hprefix tailTrace_7551626
  have hstable : (prefixWord ++ tailWord_7551626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551626).length < 2 ^ (prefixWord ++ tailWord_7551626).sum := by decide
  have hdescent : baseEnd_7551626 < baseStart_7551626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551641 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 5, 4]
def baseStart_7551641 : Nat := 118140960795 + 7551641 * 2 ^ 59
def prefixEnd_7551641 : Nat := 4983230072969 + 3 ^ 40 * 7551641 * 2
def baseEnd_7551641 : Nat := 1292540521066531301186047

theorem tailTrace_7551641 : CollatzResearch.WordTrace tailWord_7551641 prefixEnd_7551641 1292540521066531301186047 := by
  unfold tailWord_7551641
  simp only [CollatzResearch.WordTrace]
  refine ⟨275430974834701849448246777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183620649889801232965497851 275430974834701849448246777)
  ·
    refine ⟨206573231126026387086185083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275430974834701849448246777 206573231126026387086185083)
    ·
      refine ⟨309859846689039580629277625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206573231126026387086185083 309859846689039580629277625)
      ·
        refine ⟨232394885016779685471958219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309859846689039580629277625 232394885016779685471958219)
        ·
          refine ⟨348592327525169528207937329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232394885016779685471958219 348592327525169528207937329)
          ·
            refine ⟨261444245643877146155952997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348592327525169528207937329 261444245643877146155952997)
            ·
              refine ⟨49020796058226964904241187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261444245643877146155952997 49020796058226964904241187)
              ·
                refine ⟨73531194087340447356361781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49020796058226964904241187 73531194087340447356361781)
                ·
                  refine ⟨6893549445688166939658917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73531194087340447356361781 6893549445688166939658917)
                  ·
                    refine ⟨1292540521066531301186047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6893549445688166939658917 1292540521066531301186047)
                    ·
                      rfl

theorem cell23_7551641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 4].length) (baseStart_7551641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551641 prefixEnd_7551641 := by exact prefixLift 7551641
  have htrace : WordTrace (prefixWord ++ tailWord_7551641) baseStart_7551641 baseEnd_7551641 := by
    simpa [prefixWord, tailWord_7551641, baseEnd_7551641] using wordTrace_append hprefix tailTrace_7551641
  have hstable : (prefixWord ++ tailWord_7551641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551641).length < 2 ^ (prefixWord ++ tailWord_7551641).sum := by decide
  have hdescent : baseEnd_7551641 < baseStart_7551641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551725 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_7551725 : Nat := 118140960795 + 7551725 * 2 ^ 59
def prefixEnd_7551725 : Nat := 4983230072969 + 3 ^ 40 * 7551725 * 2
def baseEnd_7551725 : Nat := 3877664695574571574907755

theorem tailTrace_7551725 : CollatzResearch.WordTrace tailWord_7551725 prefixEnd_7551725 3877664695574571574907755 := by
  unfold tailWord_7551725
  simp only [CollatzResearch.WordTrace]
  refine ⟨275434038566397531794304629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183622692377598354529536419 275434038566397531794304629)
  ·
    refine ⟨25821941115599768605716059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275434038566397531794304629 25821941115599768605716059)
    ·
      refine ⟨38732911673399652908574089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25821941115599768605716059 38732911673399652908574089)
      ·
        refine ⟨29049683755049739681430567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38732911673399652908574089 29049683755049739681430567)
        ·
          refine ⟨43574525632574609522145851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29049683755049739681430567 43574525632574609522145851)
          ·
            refine ⟨65361788448861914283218777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43574525632574609522145851 65361788448861914283218777)
            ·
              refine ⟨49021341336646435712414083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65361788448861914283218777 49021341336646435712414083)
              ·
                refine ⟨73532012004969653568621125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49021341336646435712414083 73532012004969653568621125)
                ·
                  refine ⟨13787252250931810044116461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73532012004969653568621125 13787252250931810044116461)
                  ·
                    refine ⟨5170219594099428766543673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13787252250931810044116461 5170219594099428766543673)
                    ·
                      refine ⟨3877664695574571574907755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170219594099428766543673 3877664695574571574907755)
                      ·
                        rfl

theorem cell23_7551725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_7551725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551725 prefixEnd_7551725 := by exact prefixLift 7551725
  have htrace : WordTrace (prefixWord ++ tailWord_7551725) baseStart_7551725 baseEnd_7551725 := by
    simpa [prefixWord, tailWord_7551725, baseEnd_7551725] using wordTrace_append hprefix tailTrace_7551725
  have hstable : (prefixWord ++ tailWord_7551725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551725).length < 2 ^ (prefixWord ++ tailWord_7551725).sum := by decide
  have hdescent : baseEnd_7551725 < baseStart_7551725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551775 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 3]
def baseStart_7551775 : Nat := 118140960795 + 7551775 * 2 ^ 59
def prefixEnd_7551775 : Nat := 4983230072969 + 3 ^ 40 * 7551775 * 2
def baseEnd_7551775 : Nat := 3877690369607296379282525

theorem tailTrace_7551775 : CollatzResearch.WordTrace tailWord_7551775 prefixEnd_7551775 3877690369607296379282525 := by
  unfold tailWord_7551775
  simp only [CollatzResearch.WordTrace]
  refine ⟨275435862216216390333624779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183623908144144260222416519 275435862216216390333624779)
  ·
    refine ⟨413153793324324585500437169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275435862216216390333624779 413153793324324585500437169)
    ·
      refine ⟨309865344993243439125327877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413153793324324585500437169 309865344993243439125327877)
      ·
        refine ⟨58099752186233144835998977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309865344993243439125327877 58099752186233144835998977)
        ·
          refine ⟨43574814139674858626999233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58099752186233144835998977 43574814139674858626999233)
          ·
            refine ⟨32681110604756143970249425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43574814139674858626999233 32681110604756143970249425)
            ·
              refine ⟨24510832953567107977687069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32681110604756143970249425 24510832953567107977687069)
              ·
                refine ⟨9191562357587665491632651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24510832953567107977687069 9191562357587665491632651)
                ·
                  refine ⟨13787343536381498237448977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9191562357587665491632651 13787343536381498237448977)
                  ·
                    refine ⟨10340507652286123678086733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13787343536381498237448977 10340507652286123678086733)
                    ·
                      refine ⟨3877690369607296379282525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10340507652286123678086733 3877690369607296379282525)
                      ·
                        rfl

theorem cell23_7551775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_7551775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551775 prefixEnd_7551775 := by exact prefixLift 7551775
  have htrace : WordTrace (prefixWord ++ tailWord_7551775) baseStart_7551775 baseEnd_7551775 := by
    simpa [prefixWord, tailWord_7551775, baseEnd_7551775] using wordTrace_append hprefix tailTrace_7551775
  have hstable : (prefixWord ++ tailWord_7551775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551775).length < 2 ^ (prefixWord ++ tailWord_7551775).sum := by decide
  have hdescent : baseEnd_7551775 < baseStart_7551775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551778 : List Nat := [3, 3, 1, 1, 2, 4, 9]
def baseStart_7551778 : Nat := 118140960795 + 7551778 * 2 ^ 59
def prefixEnd_7551778 : Nat := 4983230072969 + 3 ^ 40 * 7551778 * 2
def baseEnd_7551778 : Nat := 47872739630237776142531

theorem tailTrace_7551778 : CollatzResearch.WordTrace tailWord_7551778 prefixEnd_7551778 47872739630237776142531 := by
  unfold tailWord_7551778
  simp only [CollatzResearch.WordTrace]
  refine ⟨68858992908801380461495997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183623981090137014563989325 68858992908801380461495997)
  ·
    refine ⟨25822122340800517673060999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68858992908801380461495997 25822122340800517673060999)
    ·
      refine ⟨38733183511200776509591499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25822122340800517673060999 38733183511200776509591499)
      ·
        refine ⟨58099775266801164764387249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38733183511200776509591499 58099775266801164764387249)
        ·
          refine ⟨43574831450100873573290437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58099775266801164764387249 43574831450100873573290437)
          ·
            refine ⟨8170280896893913794991957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43574831450100873573290437 8170280896893913794991957)
            ·
              refine ⟨47872739630237776142531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8170280896893913794991957 47872739630237776142531)
              ·
                rfl

theorem cell23_7551778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 9].length) (baseStart_7551778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551778 prefixEnd_7551778 := by exact prefixLift 7551778
  have htrace : WordTrace (prefixWord ++ tailWord_7551778) baseStart_7551778 baseEnd_7551778 := by
    simpa [prefixWord, tailWord_7551778, baseEnd_7551778] using wordTrace_append hprefix tailTrace_7551778
  have hstable : (prefixWord ++ tailWord_7551778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551778).length < 2 ^ (prefixWord ++ tailWord_7551778).sum := by decide
  have hdescent : baseEnd_7551778 < baseStart_7551778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551858 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_7551858 : Nat := 118140960795 + 7551858 * 2 ^ 59
def prefixEnd_7551858 : Nat := 4983230072969 + 3 ^ 40 * 7551858 * 2
def baseEnd_7551858 : Nat := 3877732988501619554544643

theorem tailTrace_7551858 : CollatzResearch.WordTrace tailWord_7551858 prefixEnd_7551858 3877732988501619554544643 := by
  unfold tailWord_7551858
  simp only [CollatzResearch.WordTrace]
  refine ⟨68859722368728923877224057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183625926316610463672597485 68859722368728923877224057)
  ·
    refine ⟨51644791776546692907918043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68859722368728923877224057 51644791776546692907918043)
    ·
      refine ⟨77467187664820039361877065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51644791776546692907918043 77467187664820039361877065)
      ·
        refine ⟨58100390748615029521407799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77467187664820039361877065 58100390748615029521407799)
        ·
          refine ⟨87150586122922544282111699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58100390748615029521407799 87150586122922544282111699)
          ·
            refine ⟨130725879184383816423167549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87150586122922544282111699 130725879184383816423167549)
            ·
              refine ⟨49022204694143931158687831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130725879184383816423167549 49022204694143931158687831)
              ·
                refine ⟨73533307041215896738031747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49022204694143931158687831 73533307041215896738031747)
                ·
                  refine ⟨110299960561823845107047621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73533307041215896738031747 110299960561823845107047621)
                  ·
                    refine ⟨20681242605341970957571429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110299960561823845107047621 20681242605341970957571429)
                    ·
                      refine ⟨3877732988501619554544643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20681242605341970957571429 3877732988501619554544643)
                      ·
                        rfl

theorem cell23_7551858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_7551858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551858 prefixEnd_7551858 := by exact prefixLift 7551858
  have htrace : WordTrace (prefixWord ++ tailWord_7551858) baseStart_7551858 baseEnd_7551858 := by
    simpa [prefixWord, tailWord_7551858, baseEnd_7551858] using wordTrace_append hprefix tailTrace_7551858
  have hstable : (prefixWord ++ tailWord_7551858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551858).length < 2 ^ (prefixWord ++ tailWord_7551858).sum := by decide
  have hdescent : baseEnd_7551858 < baseStart_7551858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551908 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_7551908 : Nat := 118140960795 + 7551908 * 2 ^ 59
def prefixEnd_7551908 : Nat := 4983230072969 + 3 ^ 40 * 7551908 * 2
def baseEnd_7551908 : Nat := 3877758662534344358919413

theorem tailTrace_7551908 : CollatzResearch.WordTrace tailWord_7551908 prefixEnd_7551908 3877758662534344358919413 := by
  unfold tailWord_7551908
  simp only [CollatzResearch.WordTrace]
  refine ⟨137720356562367277024108189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183627142083156369365477585 137720356562367277024108189)
  ·
    refine ⟨51645133710887728884040571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137720356562367277024108189 51645133710887728884040571)
    ·
      refine ⟨77467700566331593326060857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51645133710887728884040571 77467700566331593326060857)
      ·
        refine ⟨58100775424748694994545643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77467700566331593326060857 58100775424748694994545643)
        ·
          refine ⟨87151163137123042491818465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58100775424748694994545643 87151163137123042491818465)
          ·
            refine ⟨65363372352842281868863849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87151163137123042491818465 65363372352842281868863849)
            ·
              refine ⟨49022529264631711401647887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65363372352842281868863849 49022529264631711401647887)
              ·
                refine ⟨73533793896947567102471831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49022529264631711401647887 73533793896947567102471831)
                ·
                  refine ⟨110300690845421350653707747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73533793896947567102471831 110300690845421350653707747)
                  ·
                    refine ⟨165451036268132025980561621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110300690845421350653707747 165451036268132025980561621)
                    ·
                      refine ⟨3877758662534344358919413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165451036268132025980561621 3877758662534344358919413)
                      ·
                        rfl

theorem cell23_7551908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_7551908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551908 prefixEnd_7551908 := by exact prefixLift 7551908
  have htrace : WordTrace (prefixWord ++ tailWord_7551908) baseStart_7551908 baseEnd_7551908 := by
    simpa [prefixWord, tailWord_7551908, baseEnd_7551908] using wordTrace_append hprefix tailTrace_7551908
  have hstable : (prefixWord ++ tailWord_7551908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551908).length < 2 ^ (prefixWord ++ tailWord_7551908).sum := by decide
  have hdescent : baseEnd_7551908 < baseStart_7551908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551935 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 4, 4, 2]
def baseStart_7551935 : Nat := 118140960795 + 7551935 * 2 ^ 59
def prefixEnd_7551935 : Nat := 4983230072969 + 3 ^ 40 * 7551935 * 2
def baseEnd_7551935 : Nat := 3877772526512015753281789

theorem tailTrace_7551935 : CollatzResearch.WordTrace tailWord_7551935 prefixEnd_7551935 3877772526512015753281789 := by
  unfold tailWord_7551935
  simp only [CollatzResearch.WordTrace]
  refine ⟨275441697895636737659449259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183627798597091158439632839 275441697895636737659449259)
  ·
    refine ⟨413162546843455106489173889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275441697895636737659449259 413162546843455106489173889)
    ·
      refine ⟨309871910132591329866880417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413162546843455106489173889 309871910132591329866880417)
      ·
        refine ⟨232403932599443497400160313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309871910132591329866880417 232403932599443497400160313)
        ·
          refine ⟨174302949449582623050120235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232403932599443497400160313 174302949449582623050120235)
          ·
            refine ⟨261454424174373934575180353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174302949449582623050120235 261454424174373934575180353)
            ·
              refine ⟨196090818130780450931385265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261454424174373934575180353 196090818130780450931385265)
              ·
                refine ⟨147068113598085338198538949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196090818130780450931385265 147068113598085338198538949)
                ·
                  refine ⟨27575271299641000912226053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147068113598085338198538949 27575271299641000912226053)
                  ·
                    refine ⟨5170363368682687671042385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27575271299641000912226053 5170363368682687671042385)
                    ·
                      refine ⟨3877772526512015753281789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170363368682687671042385 3877772526512015753281789)
                      ·
                        rfl

theorem cell23_7551935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_7551935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551935 prefixEnd_7551935 := by exact prefixLift 7551935
  have htrace : WordTrace (prefixWord ++ tailWord_7551935) baseStart_7551935 baseEnd_7551935 := by
    simpa [prefixWord, tailWord_7551935, baseEnd_7551935] using wordTrace_append hprefix tailTrace_7551935
  have hstable : (prefixWord ++ tailWord_7551935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551935).length < 2 ^ (prefixWord ++ tailWord_7551935).sum := by decide
  have hdescent : baseEnd_7551935 < baseStart_7551935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7551962 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_7551962 : Nat := 118140960795 + 7551962 * 2 ^ 59
def prefixEnd_7551962 : Nat := 4983230072969 + 3 ^ 40 * 7551962 * 2
def baseEnd_7551962 : Nat := 1292595463496562382548055

theorem tailTrace_7551962 : CollatzResearch.WordTrace tailWord_7551962 prefixEnd_7551962 1292595463496562382548055 := by
  unfold tailWord_7551962
  simp only [CollatzResearch.WordTrace]
  refine ⟨68860670666634730317670535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183628455111025947513788093 68860670666634730317670535)
  ·
    refine ⟨103291005999952095476505803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68860670666634730317670535 103291005999952095476505803)
    ·
      refine ⟨154936508999928143214758705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103291005999952095476505803 154936508999928143214758705)
      ·
        refine ⟨116202381749946107411069029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154936508999928143214758705 116202381749946107411069029)
        ·
          refine ⟨21787946578114895139575443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116202381749946107411069029 21787946578114895139575443)
          ·
            refine ⟨32681919867172342709363165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21787946578114895139575443 32681919867172342709363165)
            ·
              refine ⟨12255719950189628516011187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32681919867172342709363165 12255719950189628516011187)
              ·
                refine ⟨18383579925284442774016781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12255719950189628516011187 18383579925284442774016781)
                ·
                  refine ⟨6893842471981666040256293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18383579925284442774016781 6893842471981666040256293)
                  ·
                    refine ⟨1292595463496562382548055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6893842471981666040256293 1292595463496562382548055)
                    ·
                      rfl

theorem cell23_7551962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_7551962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7551962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7551962 prefixEnd_7551962 := by exact prefixLift 7551962
  have htrace : WordTrace (prefixWord ++ tailWord_7551962) baseStart_7551962 baseEnd_7551962 := by
    simpa [prefixWord, tailWord_7551962, baseEnd_7551962] using wordTrace_append hprefix tailTrace_7551962
  have hstable : (prefixWord ++ tailWord_7551962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7551962).length < 2 ^ (prefixWord ++ tailWord_7551962).sum := by decide
  have hdescent : baseEnd_7551962 < baseStart_7551962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7551962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552025 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_7552025 : Nat := 118140960795 + 7552025 * 2 ^ 59
def prefixEnd_7552025 : Nat := 4983230072969 + 3 ^ 40 * 7552025 * 2
def baseEnd_7552025 : Nat := 3877818739770920401156375

theorem tailTrace_7552025 : CollatzResearch.WordTrace tailWord_7552025 prefixEnd_7552025 3877818739770920401156375 := by
  unfold tailWord_7552025
  simp only [CollatzResearch.WordTrace]
  refine ⟨275444980465310683030225529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183629986976873788686817019 275444980465310683030225529)
  ·
    refine ⟨206583735348983012272669147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275444980465310683030225529 206583735348983012272669147)
    ·
      refine ⟨309875603023474518409003721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206583735348983012272669147 309875603023474518409003721)
      ·
        refine ⟨232406702267605888806752791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309875603023474518409003721 232406702267605888806752791)
        ·
          refine ⟨348610053401408833210129187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232406702267605888806752791 348610053401408833210129187)
          ·
            refine ⟨522915080102113249815193781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348610053401408833210129187 522915080102113249815193781)
            ·
              refine ⟨49023288759573117170174417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 522915080102113249815193781 49023288759573117170174417)
              ·
                refine ⟨36767466569679837877630813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49023288759573117170174417 36767466569679837877630813)
                ·
                  refine ⟨13787799963629939204111555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36767466569679837877630813 13787799963629939204111555)
                  ·
                    refine ⟨20681699945444908806167333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13787799963629939204111555 20681699945444908806167333)
                    ·
                      refine ⟨3877818739770920401156375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20681699945444908806167333 3877818739770920401156375)
                      ·
                        rfl

theorem cell23_7552025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_7552025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552025 prefixEnd_7552025 := by exact prefixLift 7552025
  have htrace : WordTrace (prefixWord ++ tailWord_7552025) baseStart_7552025 baseEnd_7552025 := by
    simpa [prefixWord, tailWord_7552025, baseEnd_7552025] using wordTrace_append hprefix tailTrace_7552025
  have hstable : (prefixWord ++ tailWord_7552025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552025).length < 2 ^ (prefixWord ++ tailWord_7552025).sum := by decide
  have hdescent : baseEnd_7552025 < baseStart_7552025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552035 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 1, 6]
def baseStart_7552035 : Nat := 118140960795 + 7552035 * 2 ^ 59
def prefixEnd_7552035 : Nat := 4983230072969 + 3 ^ 40 * 7552035 * 2
def baseEnd_7552035 : Nat := 1292607958192488454010443

theorem tailTrace_7552035 : CollatzResearch.WordTrace tailWord_7552035 prefixEnd_7552035 1292607958192488454010443 := by
  unfold tailWord_7552035
  simp only [CollatzResearch.WordTrace]
  refine ⟨275445345195274454738089559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183630230130182969825393039 275445345195274454738089559)
  ·
    refine ⟨413168017792911682107134339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275445345195274454738089559 413168017792911682107134339)
    ·
      refine ⟨619752026689367523160701509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413168017792911682107134339 619752026689367523160701509)
      ·
        refine ⟨116203505004256410592631533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 619752026689367523160701509 116203505004256410592631533)
        ·
          refine ⟨43576314376596153972236825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116203505004256410592631533 43576314376596153972236825)
          ·
            refine ⟨32682235782447115479177619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43576314376596153972236825 32682235782447115479177619)
            ·
              refine ⟨49023353673670673218766429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32682235782447115479177619 49023353673670673218766429)
              ·
                refine ⟨18383757627626502457037411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49023353673670673218766429 18383757627626502457037411)
                ·
                  refine ⟨27575636441439753685556117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18383757627626502457037411 27575636441439753685556117)
                  ·
                    refine ⟨1292607958192488454010443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27575636441439753685556117 1292607958192488454010443)
                    ·
                      rfl

theorem cell23_7552035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 6].length) (baseStart_7552035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552035 prefixEnd_7552035 := by exact prefixLift 7552035
  have htrace : WordTrace (prefixWord ++ tailWord_7552035) baseStart_7552035 baseEnd_7552035 := by
    simpa [prefixWord, tailWord_7552035, baseEnd_7552035] using wordTrace_append hprefix tailTrace_7552035
  have hstable : (prefixWord ++ tailWord_7552035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552035).length < 2 ^ (prefixWord ++ tailWord_7552035).sum := by decide
  have hdescent : baseEnd_7552035 < baseStart_7552035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552105 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_7552105 : Nat := 118140960795 + 7552105 * 2 ^ 59
def prefixEnd_7552105 : Nat := 4983230072969 + 3 ^ 40 * 7552105 * 2
def baseEnd_7552105 : Nat := 3877859818223280088156007

theorem tailTrace_7552105 : CollatzResearch.WordTrace tailWord_7552105 prefixEnd_7552105 3877859818223280088156007 := by
  unfold tailWord_7552105
  simp only [CollatzResearch.WordTrace]
  refine ⟨275447898305020856693137769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183631932203347237795425179 275447898305020856693137769)
  ·
    refine ⟨206585923728765642519853327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275447898305020856693137769 206585923728765642519853327)
    ·
      refine ⟨309878885593148463779779991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206585923728765642519853327 309878885593148463779779991)
      ·
        refine ⟨464818328389722695669669987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309878885593148463779779991 464818328389722695669669987)
        ·
          refine ⟨697227492584584043504504981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464818328389722695669669987 697227492584584043504504981)
          ·
            refine ⟨32682538714902377039273671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 697227492584584043504504981 32682538714902377039273671)
            ·
              refine ⟨49023808072353565558910507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32682538714902377039273671 49023808072353565558910507)
              ·
                refine ⟨73535712108530348338365761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49023808072353565558910507 73535712108530348338365761)
                ·
                  refine ⟨55151784081397761253774321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73535712108530348338365761 55151784081397761253774321)
                  ·
                    refine ⟨41363838061048320940330741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55151784081397761253774321 41363838061048320940330741)
                    ·
                      refine ⟨3877859818223280088156007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41363838061048320940330741 3877859818223280088156007)
                      ·
                        rfl

theorem cell23_7552105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_7552105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552105 prefixEnd_7552105 := by exact prefixLift 7552105
  have htrace : WordTrace (prefixWord ++ tailWord_7552105) baseStart_7552105 baseEnd_7552105 := by
    simpa [prefixWord, tailWord_7552105, baseEnd_7552105] using wordTrace_append hprefix tailTrace_7552105
  have hstable : (prefixWord ++ tailWord_7552105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552105).length < 2 ^ (prefixWord ++ tailWord_7552105).sum := by decide
  have hdescent : baseEnd_7552105 < baseStart_7552105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552109 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_7552109 : Nat := 118140960795 + 7552109 * 2 ^ 59
def prefixEnd_7552109 : Nat := 4983230072969 + 3 ^ 40 * 7552109 * 2
def baseEnd_7552109 : Nat := 3877861872145898072505989

theorem tailTrace_7552109 : CollatzResearch.WordTrace tailWord_7552109 prefixEnd_7552109 3877861872145898072505989 := by
  unfold tailWord_7552109
  simp only [CollatzResearch.WordTrace]
  refine ⟨275448044197006365376283381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183632029464670910250855587 275448044197006365376283381)
  ·
    refine ⟨25823254143469346754026567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 275448044197006365376283381 25823254143469346754026567)
    ·
      refine ⟨38734881215204020131039851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25823254143469346754026567 38734881215204020131039851)
      ·
        refine ⟨58102321822806030196559777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38734881215204020131039851 58102321822806030196559777)
        ·
          refine ⟨43576741367104522647419833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58102321822806030196559777 43576741367104522647419833)
          ·
            refine ⟨32682556025328391985564875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43576741367104522647419833 32682556025328391985564875)
            ·
              refine ⟨49023834037992587978347313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32682556025328391985564875 49023834037992587978347313)
              ·
                refine ⟨36767875528494440983760485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49023834037992587978347313 36767875528494440983760485)
                ·
                  refine ⟨6893976661592707684455091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36767875528494440983760485 6893976661592707684455091)
                  ·
                    refine ⟨10340964992389061526682637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6893976661592707684455091 10340964992389061526682637)
                    ·
                      refine ⟨3877861872145898072505989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10340964992389061526682637 3877861872145898072505989)
                      ·
                        rfl

theorem cell23_7552109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_7552109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552109 prefixEnd_7552109 := by exact prefixLift 7552109
  have htrace : WordTrace (prefixWord ++ tailWord_7552109) baseStart_7552109 baseEnd_7552109 := by
    simpa [prefixWord, tailWord_7552109, baseEnd_7552109] using wordTrace_append hprefix tailTrace_7552109
  have hstable : (prefixWord ++ tailWord_7552109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552109).length < 2 ^ (prefixWord ++ tailWord_7552109).sum := by decide
  have hdescent : baseEnd_7552109 < baseStart_7552109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552110 : List Nat := [4, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_7552110 : Nat := 118140960795 + 7552110 * 2 ^ 59
def prefixEnd_7552110 : Nat := 4983230072969 + 3 ^ 40 * 7552110 * 2
def baseEnd_7552110 : Nat := 3877862385626552568593485

theorem tailTrace_7552110 : CollatzResearch.WordTrace tailWord_7552110 prefixEnd_7552110 3877862385626552568593485 := by
  unfold tailWord_7552110
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431010083750342818383723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183632053780001828364713189 34431010083750342818383723)
  ·
    refine ⟨51646515125625514227575585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34431010083750342818383723 51646515125625514227575585)
    ·
      refine ⟨38734886344219135670681689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51646515125625514227575585 38734886344219135670681689)
      ·
        refine ⟨29051164758164351753011267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38734886344219135670681689 29051164758164351753011267)
        ·
          refine ⟨43576747137246527629516901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29051164758164351753011267 43576747137246527629516901)
          ·
            refine ⟨8170640088233723930534419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43576747137246527629516901 8170640088233723930534419)
            ·
              refine ⟨12255960132350585895801629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8170640088233723930534419 12255960132350585895801629)
              ·
                refine ⟨4595985049631469710925611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12255960132350585895801629 4595985049631469710925611)
                ·
                  refine ⟨6893977574447204566388417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595985049631469710925611 6893977574447204566388417)
                  ·
                    refine ⟨5170483180835403424791313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6893977574447204566388417 5170483180835403424791313)
                    ·
                      refine ⟨3877862385626552568593485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170483180835403424791313 3877862385626552568593485)
                      ·
                        rfl

theorem cell23_7552110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_7552110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552110 prefixEnd_7552110 := by exact prefixLift 7552110
  have htrace : WordTrace (prefixWord ++ tailWord_7552110) baseStart_7552110 baseEnd_7552110 := by
    simpa [prefixWord, tailWord_7552110, baseEnd_7552110] using wordTrace_append hprefix tailTrace_7552110
  have hstable : (prefixWord ++ tailWord_7552110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552110).length < 2 ^ (prefixWord ++ tailWord_7552110).sum := by decide
  have hdescent : baseEnd_7552110 < baseStart_7552110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552119 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 1, 3, 2]
def baseStart_7552119 : Nat := 118140960795 + 7552119 * 2 ^ 59
def prefixEnd_7552119 : Nat := 4983230072969 + 3 ^ 40 * 7552119 * 2
def baseEnd_7552119 : Nat := 3877867006952443033380943

theorem tailTrace_7552119 : CollatzResearch.WordTrace tailWord_7552119 prefixEnd_7552119 3877867006952443033380943 := by
  unfold tailWord_7552119
  simp only [CollatzResearch.WordTrace]
  refine ⟨275448408926970137084147411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183632272617980091389431607 275448408926970137084147411)
  ·
    refine ⟨413172613390455205626221117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275448408926970137084147411 413172613390455205626221117)
    ·
      refine ⟨154939730021420702109832919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413172613390455205626221117 154939730021420702109832919)
      ·
        refine ⟨232409595032131053164749379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154939730021420702109832919 232409595032131053164749379)
        ·
          refine ⟨348614392548196579747124069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232409595032131053164749379 348614392548196579747124069)
          ·
            refine ⟨65365198602786858702585763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348614392548196579747124069 65365198602786858702585763)
            ·
              refine ⟨98047797904180288053878645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65365198602786858702585763 98047797904180288053878645)
              ·
                refine ⟨9191981053516902005051123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98047797904180288053878645 9191981053516902005051123)
                ·
                  refine ⟨13787971580275353007576685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9191981053516902005051123 13787971580275353007576685)
                  ·
                    refine ⟨5170489342603257377841257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13787971580275353007576685 5170489342603257377841257)
                    ·
                      refine ⟨3877867006952443033380943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170489342603257377841257 3877867006952443033380943)
                      ·
                        rfl

theorem cell23_7552119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_7552119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552119 prefixEnd_7552119 := by exact prefixLift 7552119
  have htrace : WordTrace (prefixWord ++ tailWord_7552119) baseStart_7552119 baseEnd_7552119 := by
    simpa [prefixWord, tailWord_7552119, baseEnd_7552119] using wordTrace_append hprefix tailTrace_7552119
  have hstable : (prefixWord ++ tailWord_7552119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552119).length < 2 ^ (prefixWord ++ tailWord_7552119).sum := by decide
  have hdescent : baseEnd_7552119 < baseStart_7552119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552135 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_7552135 : Nat := 118140960795 + 7552135 * 2 ^ 59
def prefixEnd_7552135 : Nat := 4983230072969 + 3 ^ 40 * 7552135 * 2
def baseEnd_7552135 : Nat := 3877875222642914970780869

theorem tailTrace_7552135 : CollatzResearch.WordTrace tailWord_7552135 prefixEnd_7552135 3877875222642914970780869 := by
  unfold tailWord_7552135
  simp only [CollatzResearch.WordTrace]
  refine ⟨275448992494912171816729859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183632661663274781211153239 275448992494912171816729859)
  ·
    refine ⟨413173488742368257725094789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275448992494912171816729859 413173488742368257725094789)
    ·
      refine ⟨77470029139194048323455273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 413173488742368257725094789 77470029139194048323455273)
      ·
        refine ⟨58102521854395536242591455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77470029139194048323455273 58102521854395536242591455)
        ·
          refine ⟨87153782781593304363887183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58102521854395536242591455 87153782781593304363887183)
          ·
            refine ⟨130730674172389956545830775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87153782781593304363887183 130730674172389956545830775)
            ·
              refine ⟨196096011258584934818746163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130730674172389956545830775 196096011258584934818746163)
              ·
                refine ⟨294144016887877402228119245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196096011258584934818746163 294144016887877402228119245)
                ·
                  refine ⟨110304006332954025835544717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294144016887877402228119245 110304006332954025835544717)
                  ·
                    refine ⟨41364002374857759688329269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110304006332954025835544717 41364002374857759688329269)
                    ·
                      refine ⟨3877875222642914970780869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41364002374857759688329269 3877875222642914970780869)
                      ·
                        rfl

theorem cell23_7552135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_7552135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552135 prefixEnd_7552135 := by exact prefixLift 7552135
  have htrace : WordTrace (prefixWord ++ tailWord_7552135) baseStart_7552135 baseEnd_7552135 := by
    simpa [prefixWord, tailWord_7552135, baseEnd_7552135] using wordTrace_append hprefix tailTrace_7552135
  have hstable : (prefixWord ++ tailWord_7552135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552135).length < 2 ^ (prefixWord ++ tailWord_7552135).sum := by decide
  have hdescent : baseEnd_7552135 < baseStart_7552135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552149 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_7552149 : Nat := 118140960795 + 7552149 * 2 ^ 59
def prefixEnd_7552149 : Nat := 4983230072969 + 3 ^ 40 * 7552149 * 2
def baseEnd_7552149 : Nat := 3877882411372077916005805

theorem tailTrace_7552149 : CollatzResearch.WordTrace tailWord_7552149 prefixEnd_7552149 3877882411372077916005805 := by
  unfold tailWord_7552149
  simp only [CollatzResearch.WordTrace]
  refine ⟨275449503116861452207739501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183633002077907634805159667 275449503116861452207739501)
  ·
    refine ⟨103293563668823044577902313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275449503116861452207739501 103293563668823044577902313)
    ·
      refine ⟨77470172751617283433426735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103293563668823044577902313 77470172751617283433426735)
      ·
        refine ⟨116205259127425925150140103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77470172751617283433426735 116205259127425925150140103)
        ·
          refine ⟨174307888691138887725210155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116205259127425925150140103 174307888691138887725210155)
          ·
            refine ⟨261461833036708331587815233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174307888691138887725210155 261461833036708331587815233)
            ·
              refine ⟨196096374777531248690861425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261461833036708331587815233 196096374777531248690861425)
              ·
                refine ⟨147072281083148436518146069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196096374777531248690861425 147072281083148436518146069)
                ·
                  refine ⟨6894013175772582961788097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147072281083148436518146069 6894013175772582961788097)
                  ·
                    refine ⟨5170509881829437221341073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6894013175772582961788097 5170509881829437221341073)
                    ·
                      refine ⟨3877882411372077916005805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170509881829437221341073 3877882411372077916005805)
                      ·
                        rfl

theorem cell23_7552149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_7552149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552149 prefixEnd_7552149 := by exact prefixLift 7552149
  have htrace : WordTrace (prefixWord ++ tailWord_7552149) baseStart_7552149 baseEnd_7552149 := by
    simpa [prefixWord, tailWord_7552149, baseEnd_7552149] using wordTrace_append hprefix tailTrace_7552149
  have hstable : (prefixWord ++ tailWord_7552149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552149).length < 2 ^ (prefixWord ++ tailWord_7552149).sum := by decide
  have hdescent : baseEnd_7552149 < baseStart_7552149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552152 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7552152 : Nat := 118140960795 + 7552152 * 2 ^ 59
def prefixEnd_7552152 : Nat := 4983230072969 + 3 ^ 40 * 7552152 * 2
def baseEnd_7552152 : Nat := 3877883951814041404268291

theorem tailTrace_7552152 : CollatzResearch.WordTrace tailWord_7552152 prefixEnd_7552152 3877883951814041404268291 := by
  unfold tailWord_7552152
  simp only [CollatzResearch.WordTrace]
  refine ⟨137724806267925291860049355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183633075023900389146732473 137724806267925291860049355)
  ·
    refine ⟨206587209401887937790074033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137724806267925291860049355 206587209401887937790074033)
    ·
      refine ⟨154940407051415953342555525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206587209401887937790074033 154940407051415953342555525)
      ·
        refine ⟨29051326322140491251729161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154940407051415953342555525 29051326322140491251729161)
        ·
          refine ⟨21788494741605368438796871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29051326322140491251729161 21788494741605368438796871)
          ·
            refine ⟨32682742112408052658195307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21788494741605368438796871 32682742112408052658195307)
            ·
              refine ⟨49024113168612078987292961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32682742112408052658195307 49024113168612078987292961)
              ·
                refine ⟨36768084876459059240469721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49024113168612078987292961 36768084876459059240469721)
                ·
                  refine ⟨27576063657344294430352291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36768084876459059240469721 27576063657344294430352291)
                  ·
                    refine ⟨41364095486016441645528437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27576063657344294430352291 41364095486016441645528437)
                    ·
                      refine ⟨3877883951814041404268291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41364095486016441645528437 3877883951814041404268291)
                      ·
                        rfl

theorem cell23_7552152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7552152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552152 prefixEnd_7552152 := by exact prefixLift 7552152
  have htrace : WordTrace (prefixWord ++ tailWord_7552152) baseStart_7552152 baseEnd_7552152 := by
    simpa [prefixWord, tailWord_7552152, baseEnd_7552152] using wordTrace_append hprefix tailTrace_7552152
  have hstable : (prefixWord ++ tailWord_7552152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552152).length < 2 ^ (prefixWord ++ tailWord_7552152).sum := by decide
  have hdescent : baseEnd_7552152 < baseStart_7552152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552170 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7552170 : Nat := 118140960795 + 7552170 * 2 ^ 59
def prefixEnd_7552170 : Nat := 4983230072969 + 3 ^ 40 * 7552170 * 2
def baseEnd_7552170 : Nat := 3877893194465822333843209

theorem tailTrace_7552170 : CollatzResearch.WordTrace tailWord_7552170 prefixEnd_7552170 3877893194465822333843209 := by
  unfold tailWord_7552170
  simp only [CollatzResearch.WordTrace]
  refine ⟨68862567262446343198563491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183633512699856915196169309 68862567262446343198563491)
  ·
    refine ⟨103293850893669514797845237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68862567262446343198563491 103293850893669514797845237)
    ·
      refine ⟨9683798521281517012297991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103293850893669514797845237 9683798521281517012297991)
      ·
        refine ⟨14525697781922275518446987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9683798521281517012297991 14525697781922275518446987)
        ·
          refine ⟨21788546672883413277670481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14525697781922275518446987 21788546672883413277670481)
          ·
            refine ⟨16341410004662559958252861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21788546672883413277670481 16341410004662559958252861)
            ·
              refine ⟨6128028751748459984344823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16341410004662559958252861 6128028751748459984344823)
              ·
                refine ⟨9192043127622689976517235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128028751748459984344823 9192043127622689976517235)
                ·
                  refine ⟨13788064691434034964775853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192043127622689976517235 13788064691434034964775853)
                  ·
                    refine ⟨5170524259287763111790945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13788064691434034964775853 5170524259287763111790945)
                    ·
                      refine ⟨3877893194465822333843209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170524259287763111790945 3877893194465822333843209)
                      ·
                        rfl

theorem cell23_7552170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7552170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552170 prefixEnd_7552170 := by exact prefixLift 7552170
  have htrace : WordTrace (prefixWord ++ tailWord_7552170) baseStart_7552170 baseEnd_7552170 := by
    simpa [prefixWord, tailWord_7552170, baseEnd_7552170] using wordTrace_append hprefix tailTrace_7552170
  have hstable : (prefixWord ++ tailWord_7552170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552170).length < 2 ^ (prefixWord ++ tailWord_7552170).sum := by decide
  have hdescent : baseEnd_7552170 < baseStart_7552170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552195 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 7]
def baseStart_7552195 : Nat := 118140960795 + 7552195 * 2 ^ 59
def prefixEnd_7552195 : Nat := 4983230072969 + 3 ^ 40 * 7552195 * 2
def baseEnd_7552195 : Nat := 3877906031482184736030593

theorem tailTrace_7552195 : CollatzResearch.WordTrace tailWord_7552195 prefixEnd_7552195 3877906031482184736030593 := by
  unfold tailWord_7552195
  simp only [CollatzResearch.WordTrace]
  refine ⟨275451180874694802063914039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183634120583129868042609359 275451180874694802063914039)
  ·
    refine ⟨413176771312042203095871059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275451180874694802063914039 413176771312042203095871059)
    ·
      refine ⟨619765156968063304643806589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413176771312042203095871059 619765156968063304643806589)
      ·
        refine ⟨232411933863023739241427471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 619765156968063304643806589 232411933863023739241427471)
        ·
          refine ⟨348617900794535608862141207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232411933863023739241427471 348617900794535608862141207)
          ·
            refine ⟨522926851191803413293211811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348617900794535608862141207 522926851191803413293211811)
            ·
              refine ⟨784390276787705119939817717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522926851191803413293211811 784390276787705119939817717)
              ·
                refine ⟨73536588448847354994357911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 784390276787705119939817717 73536588448847354994357911)
                ·
                  refine ⟨110304882673271032491536867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73536588448847354994357911 110304882673271032491536867)
                  ·
                    refine ⟨165457324009906548737305301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110304882673271032491536867 165457324009906548737305301)
                    ·
                      refine ⟨3877906031482184736030593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165457324009906548737305301 3877906031482184736030593)
                      ·
                        rfl

theorem cell23_7552195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_7552195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552195 prefixEnd_7552195 := by exact prefixLift 7552195
  have htrace : WordTrace (prefixWord ++ tailWord_7552195) baseStart_7552195 baseEnd_7552195 := by
    simpa [prefixWord, tailWord_7552195, baseEnd_7552195] using wordTrace_append hprefix tailTrace_7552195
  have hstable : (prefixWord ++ tailWord_7552195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552195).length < 2 ^ (prefixWord ++ tailWord_7552195).sum := by decide
  have hdescent : baseEnd_7552195 < baseStart_7552195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552249 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 3, 4]
def baseStart_7552249 : Nat := 118140960795 + 7552249 * 2 ^ 59
def prefixEnd_7552249 : Nat := 4983230072969 + 3 ^ 40 * 7552249 * 2
def baseEnd_7552249 : Nat := 1292644586479175841585115

theorem tailTrace_7552249 : CollatzResearch.WordTrace tailWord_7552249 prefixEnd_7552249 1292644586479175841585115 := by
  unfold tailWord_7552249
  simp only [CollatzResearch.WordTrace]
  refine ⟨275453150416499169286379801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183635433610999446190919867 275453150416499169286379801)
  ·
    refine ⟨206589862812374376964784851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275453150416499169286379801 206589862812374376964784851)
    ·
      refine ⟨309884794218561565447177277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206589862812374376964784851 309884794218561565447177277)
      ·
        refine ⟨116206797831960587042691479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309884794218561565447177277 116206797831960587042691479)
        ·
          refine ⟨174310196747940880564037219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116206797831960587042691479 174310196747940880564037219)
          ·
            refine ⟨261465295121911320846055829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174310196747940880564037219 261465295121911320846055829)
            ·
              refine ⟨12256185708839593164658867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 261465295121911320846055829 12256185708839593164658867)
              ·
                refine ⟨18384278563259389746988301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12256185708839593164658867 18384278563259389746988301)
                ·
                  refine ⟨6894104461222271155120613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18384278563259389746988301 6894104461222271155120613)
                  ·
                    refine ⟨1292644586479175841585115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894104461222271155120613 1292644586479175841585115)
                    ·
                      rfl

theorem cell23_7552249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 4].length) (baseStart_7552249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552249 prefixEnd_7552249 := by exact prefixLift 7552249
  have htrace : WordTrace (prefixWord ++ tailWord_7552249) baseStart_7552249 baseEnd_7552249 := by
    simpa [prefixWord, tailWord_7552249, baseEnd_7552249] using wordTrace_append hprefix tailTrace_7552249
  have hstable : (prefixWord ++ tailWord_7552249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552249).length < 2 ^ (prefixWord ++ tailWord_7552249).sum := by decide
  have hdescent : baseEnd_7552249 < baseStart_7552249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552312 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 2, 5, 4]
def baseStart_7552312 : Nat := 118140960795 + 7552312 * 2 ^ 59
def prefixEnd_7552312 : Nat := 4983230072969 + 3 ^ 40 * 7552312 * 2
def baseEnd_7552312 : Nat := 3877966108718760778267555

theorem tailTrace_7552312 : CollatzResearch.WordTrace tailWord_7552312 prefixEnd_7552312 3877966108718760778267555 := by
  unfold tailWord_7552312
  simp only [CollatzResearch.WordTrace]
  refine ⟨137727724107635465522961595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183636965476847287363948793 137727724107635465522961595)
  ·
    refine ⟨206591586161453198284442393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137727724107635465522961595 206591586161453198284442393)
    ·
      refine ⟨154943689621089898713331795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206591586161453198284442393 154943689621089898713331795)
      ·
        refine ⟨232415534431634848069997693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154943689621089898713331795 232415534431634848069997693)
        ·
          refine ⟨87155825411863068026249135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232415534431634848069997693 87155825411863068026249135)
          ·
            refine ⟨130733738117794602039373703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87155825411863068026249135 130733738117794602039373703)
            ·
              refine ⟨196100607176691903059060555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130733738117794602039373703 196100607176691903059060555)
              ·
                refine ⟨294150910765037854588590833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196100607176691903059060555 294150910765037854588590833)
                ·
                  refine ⟨220613183073778390941443125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294150910765037854588590833 220613183073778390941443125)
                  ·
                    refine ⟨20682485913166724150760293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220613183073778390941443125 20682485913166724150760293)
                    ·
                      refine ⟨3877966108718760778267555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20682485913166724150760293 3877966108718760778267555)
                      ·
                        rfl

theorem cell23_7552312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_7552312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552312 prefixEnd_7552312 := by exact prefixLift 7552312
  have htrace : WordTrace (prefixWord ++ tailWord_7552312) baseStart_7552312 baseEnd_7552312 := by
    simpa [prefixWord, tailWord_7552312, baseEnd_7552312] using wordTrace_append hprefix tailTrace_7552312
  have hstable : (prefixWord ++ tailWord_7552312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552312).length < 2 ^ (prefixWord ++ tailWord_7552312).sum := by decide
  have hdescent : baseEnd_7552312 < baseStart_7552312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552313 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 6]
def baseStart_7552313 : Nat := 118140960795 + 7552313 * 2 ^ 59
def prefixEnd_7552313 : Nat := 4983230072969 + 3 ^ 40 * 7552313 * 2
def baseEnd_7552313 : Nat := 430885180244379474928339

theorem tailTrace_7552313 : CollatzResearch.WordTrace tailWord_7552313 prefixEnd_7552313 430885180244379474928339 := by
  unfold tailWord_7552313
  simp only [CollatzResearch.WordTrace]
  refine ⟨275455484688267308216709593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183636989792178205477806395 275455484688267308216709593)
  ·
    refine ⟨206591613516200481162532195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275455484688267308216709593 206591613516200481162532195)
    ·
      refine ⟨309887420274300721743798293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206591613516200481162532195 309887420274300721743798293)
      ·
        refine ⟨14525972825357846331740545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 309887420274300721743798293 14525972825357846331740545)
        ·
          refine ⟨10894479619018384748805409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14525972825357846331740545 10894479619018384748805409)
          ·
            refine ⟨8170859714263788561604057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10894479619018384748805409 8170859714263788561604057)
            ·
              refine ⟨6128144785697841421203043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8170859714263788561604057 6128144785697841421203043)
              ·
                refine ⟨9192217178546762131804565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128144785697841421203043 9192217178546762131804565)
                ·
                  refine ⟨430885180244379474928339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9192217178546762131804565 430885180244379474928339)
                  ·
                    rfl

theorem cell23_7552313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 6].length) (baseStart_7552313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552313 prefixEnd_7552313 := by exact prefixLift 7552313
  have htrace : WordTrace (prefixWord ++ tailWord_7552313) baseStart_7552313 baseEnd_7552313 := by
    simpa [prefixWord, tailWord_7552313, baseEnd_7552313] using wordTrace_append hprefix tailTrace_7552313
  have hstable : (prefixWord ++ tailWord_7552313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552313).length < 2 ^ (prefixWord ++ tailWord_7552313).sum := by decide
  have hdescent : baseEnd_7552313 < baseStart_7552313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552329 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 2, 6, 2]
def baseStart_7552329 : Nat := 118140960795 + 7552329 * 2 ^ 59
def prefixEnd_7552329 : Nat := 4983230072969 + 3 ^ 40 * 7552329 * 2
def baseEnd_7552329 : Nat := 3877974837889887211754977

theorem tailTrace_7552329 : CollatzResearch.WordTrace tailWord_7552329 prefixEnd_7552329 3877974837889887211754977 := by
  unfold tailWord_7552329
  simp only [CollatzResearch.WordTrace]
  refine ⟨275456068256209342949292041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183637378837472895299528027 275456068256209342949292041)
  ·
    refine ⟨206592051192157007211969031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275456068256209342949292041 206592051192157007211969031)
    ·
      refine ⟨309888076788235510817953547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206592051192157007211969031 309888076788235510817953547)
      ·
        refine ⟨464832115182353266226930321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309888076788235510817953547 464832115182353266226930321)
        ·
          refine ⟨348624086386764949670197741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464832115182353266226930321 348624086386764949670197741)
          ·
            refine ⟨130734032395036856126324153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348624086386764949670197741 130734032395036856126324153)
            ·
              refine ⟨98050524296277642094743115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130734032395036856126324153 98050524296277642094743115)
              ·
                refine ⟨147075786444416463142114673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98050524296277642094743115 147075786444416463142114673)
                ·
                  refine ⟨110306839833312347356586005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147075786444416463142114673 110306839833312347356586005)
                  ·
                    refine ⟨5170633117186516282339969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110306839833312347356586005 5170633117186516282339969)
                    ·
                      refine ⟨3877974837889887211754977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170633117186516282339969 3877974837889887211754977)
                      ·
                        rfl

theorem cell23_7552329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 6, 2].length) (baseStart_7552329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552329 prefixEnd_7552329 := by exact prefixLift 7552329
  have htrace : WordTrace (prefixWord ++ tailWord_7552329) baseStart_7552329 baseEnd_7552329 := by
    simpa [prefixWord, tailWord_7552329, baseEnd_7552329] using wordTrace_append hprefix tailTrace_7552329
  have hstable : (prefixWord ++ tailWord_7552329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552329).length < 2 ^ (prefixWord ++ tailWord_7552329).sum := by decide
  have hdescent : baseEnd_7552329 < baseStart_7552329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552352 : List Nat := [2, 1, 1, 3, 4, 12]
def baseStart_7552352 : Nat := 118140960795 + 7552352 * 2 ^ 59
def prefixEnd_7552352 : Nat := 4983230072969 + 3 ^ 40 * 7552352 * 2
def baseEnd_7552352 : Nat := 15958792789896874986697

theorem tailTrace_7552352 : CollatzResearch.WordTrace tailWord_7552352 prefixEnd_7552352 15958792789896874986697 := by
  unfold tailWord_7552352
  simp only [CollatzResearch.WordTrace]
  refine ⟨137728453567563008938689655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183637938090084011918252873 137728453567563008938689655)
  ·
    refine ⟨206592680351344513408034483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137728453567563008938689655 206592680351344513408034483)
    ·
      refine ⟨309889020527016770112051725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206592680351344513408034483 309889020527016770112051725)
      ·
        refine ⟨116208382697631288792019397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309889020527016770112051725 116208382697631288792019397)
        ·
          refine ⟨21789071755805866648503637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116208382697631288792019397 21789071755805866648503637)
          ·
            refine ⟨15958792789896874986697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21789071755805866648503637 15958792789896874986697)
            ·
              rfl

theorem cell23_7552352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 12].length) (baseStart_7552352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552352 prefixEnd_7552352 := by exact prefixLift 7552352
  have htrace : WordTrace (prefixWord ++ tailWord_7552352) baseStart_7552352 baseEnd_7552352 := by
    simpa [prefixWord, tailWord_7552352, baseEnd_7552352] using wordTrace_append hprefix tailTrace_7552352
  have hstable : (prefixWord ++ tailWord_7552352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552352).length < 2 ^ (prefixWord ++ tailWord_7552352).sum := by decide
  have hdescent : baseEnd_7552352 < baseStart_7552352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552356 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_7552356 : Nat := 118140960795 + 7552356 * 2 ^ 59
def prefixEnd_7552356 : Nat := 4983230072969 + 3 ^ 40 * 7552356 * 2
def baseEnd_7552356 : Nat := 1292662900622519535372451

theorem tailTrace_7552356 : CollatzResearch.WordTrace tailWord_7552356 prefixEnd_7552356 1292662900622519535372451 := by
  unfold tailWord_7552356
  simp only [CollatzResearch.WordTrace]
  refine ⟨137728526513555763280262461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183638035351407684373683281 137728526513555763280262461)
  ·
    refine ⟨51648197442583411230098423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137728526513555763280262461 51648197442583411230098423)
    ·
      refine ⟨77472296163875116845147635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51648197442583411230098423 77472296163875116845147635)
      ·
        refine ⟨116208444245812675267721453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77472296163875116845147635 116208444245812675267721453)
        ·
          refine ⟨43578166592179753225395545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116208444245812675267721453 43578166592179753225395545)
          ·
            refine ⟨32683624944134814919046659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43578166592179753225395545 32683624944134814919046659)
            ·
              refine ⟨49025437416202222378569989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32683624944134814919046659 49025437416202222378569989)
              ·
                refine ⟨9192269515537916695981873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49025437416202222378569989 9192269515537916695981873)
                ·
                  refine ⟨6894202136653437521986405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192269515537916695981873 6894202136653437521986405)
                  ·
                    refine ⟨1292662900622519535372451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894202136653437521986405 1292662900622519535372451)
                    ·
                      rfl

theorem cell23_7552356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_7552356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552356 prefixEnd_7552356 := by exact prefixLift 7552356
  have htrace : WordTrace (prefixWord ++ tailWord_7552356) baseStart_7552356 baseEnd_7552356 := by
    simpa [prefixWord, tailWord_7552356, baseEnd_7552356] using wordTrace_append hprefix tailTrace_7552356
  have hstable : (prefixWord ++ tailWord_7552356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552356).length < 2 ^ (prefixWord ++ tailWord_7552356).sum := by decide
  have hdescent : baseEnd_7552356 < baseStart_7552356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552396 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_7552396 : Nat := 118140960795 + 7552396 * 2 ^ 59
def prefixEnd_7552396 : Nat := 4983230072969 + 3 ^ 40 * 7552396 * 2
def baseEnd_7552396 : Nat := 3878009241093738449617169

theorem tailTrace_7552396 : CollatzResearch.WordTrace tailWord_7552396 prefixEnd_7552396 3878009241093738449617169 := by
  unfold tailWord_7552396
  simp only [CollatzResearch.WordTrace]
  refine ⟨137729255973483306695990521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183639007964644408927987361 137729255973483306695990521)
  ·
    refine ⟨103296941980112480021992891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137729255973483306695990521 103296941980112480021992891)
    ·
      refine ⟨154945412970168720032989337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103296941980112480021992891 154945412970168720032989337)
      ·
        refine ⟨116209059727626540024742003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154945412970168720032989337 116209059727626540024742003)
        ·
          refine ⟨174313589591439810037113005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116209059727626540024742003 174313589591439810037113005)
          ·
            refine ⟨65367596096789928763917377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174313589591439810037113005 65367596096789928763917377)
            ·
              refine ⟨49025697072592446572938033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65367596096789928763917377 49025697072592446572938033)
              ·
                refine ⟨36769272804444334929703525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49025697072592446572938033 36769272804444334929703525)
                ·
                  refine ⟨6894238650833312799319411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36769272804444334929703525 6894238650833312799319411)
                  ·
                    refine ⟨10341357976249969198979117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6894238650833312799319411 10341357976249969198979117)
                    ·
                      refine ⟨3878009241093738449617169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10341357976249969198979117 3878009241093738449617169)
                      ·
                        rfl

theorem cell23_7552396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_7552396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552396 prefixEnd_7552396 := by exact prefixLift 7552396
  have htrace : WordTrace (prefixWord ++ tailWord_7552396) baseStart_7552396 baseEnd_7552396 := by
    simpa [prefixWord, tailWord_7552396, baseEnd_7552396] using wordTrace_append hprefix tailTrace_7552396
  have hstable : (prefixWord ++ tailWord_7552396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552396).length < 2 ^ (prefixWord ++ tailWord_7552396).sum := by decide
  have hdescent : baseEnd_7552396 < baseStart_7552396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552413 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_7552413 : Nat := 118140960795 + 7552413 * 2 ^ 59
def prefixEnd_7552413 : Nat := 4983230072969 + 3 ^ 40 * 7552413 * 2
def baseEnd_7552413 : Nat := 3878017970264864883104591

theorem tailTrace_7552413 : CollatzResearch.WordTrace tailWord_7552413 prefixEnd_7552413 3878017970264864883104591 := by
  unfold tailWord_7552413
  simp only [CollatzResearch.WordTrace]
  refine ⟨275459131987905025295349893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183639421325270016863566595 275459131987905025295349893)
  ·
    refine ⟨51648587247732192242878105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275459131987905025295349893 51648587247732192242878105)
    ·
      refine ⟨38736440435799144182158579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51648587247732192242878105 38736440435799144182158579)
      ·
        refine ⟨58104660653698716273237869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38736440435799144182158579 58104660653698716273237869)
        ·
          refine ⟨21789247745137018602464201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58104660653698716273237869 21789247745137018602464201)
          ·
            refine ⟨16341935808852763951848151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21789247745137018602464201 16341935808852763951848151)
            ·
              refine ⟨24512903713279145927772227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16341935808852763951848151 24512903713279145927772227)
              ·
                refine ⟨36769355569918718891658341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24512903713279145927772227 36769355569918718891658341)
                ·
                  refine ⟨6894254169359759792185939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36769355569918718891658341 6894254169359759792185939)
                  ·
                    refine ⟨10341381254039639688278909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6894254169359759792185939 10341381254039639688278909)
                    ·
                      refine ⟨3878017970264864883104591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10341381254039639688278909 3878017970264864883104591)
                      ·
                        rfl

theorem cell23_7552413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_7552413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552413 prefixEnd_7552413 := by exact prefixLift 7552413
  have htrace : WordTrace (prefixWord ++ tailWord_7552413) baseStart_7552413 baseEnd_7552413 := by
    simpa [prefixWord, tailWord_7552413, baseEnd_7552413] using wordTrace_append hprefix tailTrace_7552413
  have hstable : (prefixWord ++ tailWord_7552413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552413).length < 2 ^ (prefixWord ++ tailWord_7552413).sum := by decide
  have hdescent : baseEnd_7552413 < baseStart_7552413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552439 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_7552439 : Nat := 118140960795 + 7552439 * 2 ^ 59
def prefixEnd_7552439 : Nat := 4983230072969 + 3 ^ 40 * 7552439 * 2
def baseEnd_7552439 : Nat := 3878031320761881781379471

theorem tailTrace_7552439 : CollatzResearch.WordTrace tailWord_7552439 prefixEnd_7552439 3878031320761881781379471 := by
  unfold tailWord_7552439
  simp only [CollatzResearch.WordTrace]
  refine ⟨275460080285810831735796371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183640053523873887823864247 275460080285810831735796371)
  ·
    refine ⟨413190120428716247603694557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275460080285810831735796371 413190120428716247603694557)
    ·
      refine ⟨154946295160768592851385459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413190120428716247603694557 154946295160768592851385459)
      ·
        refine ⟨232419442741152889277078189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154946295160768592851385459 232419442741152889277078189)
        ·
          refine ⟨87157291027932333478904321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232419442741152889277078189 87157291027932333478904321)
          ·
            refine ⟨65367968270949250109178241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87157291027932333478904321 65367968270949250109178241)
            ·
              refine ⟨49025976203211937581883681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65367968270949250109178241 49025976203211937581883681)
              ·
                refine ⟨36769482152408953186412761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49025976203211937581883681 36769482152408953186412761)
                ·
                  refine ⟨27577111614306714889809571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36769482152408953186412761 27577111614306714889809571)
                  ·
                    refine ⟨41365667421460072334714357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27577111614306714889809571 41365667421460072334714357)
                    ·
                      refine ⟨3878031320761881781379471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41365667421460072334714357 3878031320761881781379471)
                      ·
                        rfl

theorem cell23_7552439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_7552439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552439 prefixEnd_7552439 := by exact prefixLift 7552439
  have htrace : WordTrace (prefixWord ++ tailWord_7552439) baseStart_7552439 baseEnd_7552439 := by
    simpa [prefixWord, tailWord_7552439, baseEnd_7552439] using wordTrace_append hprefix tailTrace_7552439
  have hstable : (prefixWord ++ tailWord_7552439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552439).length < 2 ^ (prefixWord ++ tailWord_7552439).sum := by decide
  have hdescent : baseEnd_7552439 < baseStart_7552439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552469 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7552469 : Nat := 118140960795 + 7552469 * 2 ^ 59
def prefixEnd_7552469 : Nat := 4983230072969 + 3 ^ 40 * 7552469 * 2
def baseEnd_7552469 : Nat := 3878046725181516664004333

theorem tailTrace_7552469 : CollatzResearch.WordTrace tailWord_7552469 prefixEnd_7552469 3878046725181516664004333 := by
  unfold tailWord_7552469
  simp only [CollatzResearch.WordTrace]
  refine ⟨275461174475702146859388461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183640782983801431239592307 275461174475702146859388461)
  ·
    refine ⟨103297940428388305072270673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275461174475702146859388461 103297940428388305072270673)
    ·
      refine ⟨77473455321291228804203005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103297940428388305072270673 77473455321291228804203005)
      ·
        refine ⟨29052545745484210801576127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77473455321291228804203005 29052545745484210801576127)
        ·
          refine ⟨43578818618226316202364191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29052545745484210801576127 43578818618226316202364191)
          ·
            refine ⟨65368227927339474303546287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43578818618226316202364191 65368227927339474303546287)
            ·
              refine ⟨98052341891009211455319431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65368227927339474303546287 98052341891009211455319431)
              ·
                refine ⟨147078512836513817182979147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98052341891009211455319431 147078512836513817182979147)
                ·
                  refine ⟨220617769254770725774468721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147078512836513817182979147 220617769254770725774468721)
                  ·
                    refine ⟨165463326941078044330851541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 220617769254770725774468721 165463326941078044330851541)
                    ·
                      refine ⟨3878046725181516664004333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165463326941078044330851541 3878046725181516664004333)
                      ·
                        rfl

theorem cell23_7552469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7552469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552469 prefixEnd_7552469 := by exact prefixLift 7552469
  have htrace : WordTrace (prefixWord ++ tailWord_7552469) baseStart_7552469 baseEnd_7552469 := by
    simpa [prefixWord, tailWord_7552469, baseEnd_7552469] using wordTrace_append hprefix tailTrace_7552469
  have hstable : (prefixWord ++ tailWord_7552469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552469).length < 2 ^ (prefixWord ++ tailWord_7552469).sum := by decide
  have hdescent : baseEnd_7552469 < baseStart_7552469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552487 : List Nat := [1, 1, 5, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_7552487 : Nat := 118140960795 + 7552487 * 2 ^ 59
def prefixEnd_7552487 : Nat := 4983230072969 + 3 ^ 40 * 7552487 * 2
def baseEnd_7552487 : Nat := 3878055967833297593579251

theorem tailTrace_7552487 : CollatzResearch.WordTrace tailWord_7552487 prefixEnd_7552487 3878055967833297593579251 := by
  unfold tailWord_7552487
  simp only [CollatzResearch.WordTrace]
  refine ⟨275461830989636935933543715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183641220659757957289029143 275461830989636935933543715)
  ·
    refine ⟨413192746484455403900315573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275461830989636935933543715 413192746484455403900315573)
    ·
      refine ⟨38736819982917694115654585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 413192746484455403900315573 38736819982917694115654585)
      ·
        refine ⟨29052614987188270586740939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38736819982917694115654585 29052614987188270586740939)
        ·
          refine ⟨43578922480782405880111409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29052614987188270586740939 43578922480782405880111409)
          ·
            refine ⟨32684191860586804410083557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43578922480782405880111409 32684191860586804410083557)
            ·
              refine ⟨6128285973860025826890667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32684191860586804410083557 6128285973860025826890667)
              ·
                refine ⟨9192428960790038740336001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128285973860025826890667 9192428960790038740336001)
                ·
                  refine ⟨6894321720592529055252001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192428960790038740336001 6894321720592529055252001)
                  ·
                    refine ⟨5170741290444396791439001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6894321720592529055252001 5170741290444396791439001)
                    ·
                      refine ⟨3878055967833297593579251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170741290444396791439001 3878055967833297593579251)
                      ·
                        rfl

theorem cell23_7552487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_7552487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552487 prefixEnd_7552487 := by exact prefixLift 7552487
  have htrace : WordTrace (prefixWord ++ tailWord_7552487) baseStart_7552487 baseEnd_7552487 := by
    simpa [prefixWord, tailWord_7552487, baseEnd_7552487] using wordTrace_append hprefix tailTrace_7552487
  have hstable : (prefixWord ++ tailWord_7552487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552487).length < 2 ^ (prefixWord ++ tailWord_7552487).sum := by decide
  have hdescent : baseEnd_7552487 < baseStart_7552487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552506 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_7552506 : Nat := 118140960795 + 7552506 * 2 ^ 59
def prefixEnd_7552506 : Nat := 4983230072969 + 3 ^ 40 * 7552506 * 2
def baseEnd_7552506 : Nat := 1292688574655244339747221

theorem tailTrace_7552506 : CollatzResearch.WordTrace tailWord_7552506 prefixEnd_7552506 1292688574655244339747221 := by
  unfold tailWord_7552506
  simp only [CollatzResearch.WordTrace]
  refine ⟨68865630994142025544621343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183641682651045401452323581 68865630994142025544621343)
  ·
    refine ⟨103298446491213038316932015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68865630994142025544621343 103298446491213038316932015)
    ·
      refine ⟨154947669736819557475398023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103298446491213038316932015 154947669736819557475398023)
      ·
        refine ⟨232421504605229336213097035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154947669736819557475398023 232421504605229336213097035)
        ·
          refine ⟨348632256907844004319645553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232421504605229336213097035 348632256907844004319645553)
          ·
            refine ⟨261474192680883003239734165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348632256907844004319645553 261474192680883003239734165)
            ·
              refine ⟨12256602781916390776862539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 261474192680883003239734165 12256602781916390776862539)
              ·
                refine ⟨18384904172874586165293809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12256602781916390776862539 18384904172874586165293809)
                ·
                  refine ⟨13788678129655939623970357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18384904172874586165293809 13788678129655939623970357)
                  ·
                    refine ⟨1292688574655244339747221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13788678129655939623970357 1292688574655244339747221)
                    ·
                      rfl

theorem cell23_7552506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_7552506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552506 prefixEnd_7552506 := by exact prefixLift 7552506
  have htrace : WordTrace (prefixWord ++ tailWord_7552506) baseStart_7552506 baseEnd_7552506 := by
    simpa [prefixWord, tailWord_7552506, baseEnd_7552506] using wordTrace_append hprefix tailTrace_7552506
  have hstable : (prefixWord ++ tailWord_7552506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552506).length < 2 ^ (prefixWord ++ tailWord_7552506).sum := by decide
  have hdescent : baseEnd_7552506 < baseStart_7552506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552529 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_7552529 : Nat := 118140960795 + 7552529 * 2 ^ 59
def prefixEnd_7552529 : Nat := 4983230072969 + 3 ^ 40 * 7552529 * 2
def baseEnd_7552529 : Nat := 3878077534020786429254057

theorem tailTrace_7552529 : CollatzResearch.WordTrace tailWord_7552529 prefixEnd_7552529 3878077534020786429254057 := by
  unfold tailWord_7552529
  simp only [CollatzResearch.WordTrace]
  refine ⟨275463362855484777106572641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183642241903656518071048427 275463362855484777106572641)
  ·
    refine ⟨206597522141613582829929481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275463362855484777106572641 206597522141613582829929481)
    ·
      refine ⟨154948141606210187122447111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206597522141613582829929481 154948141606210187122447111)
      ·
        refine ⟨232422212409315280683670667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154948141606210187122447111 232422212409315280683670667)
        ·
          refine ⟨348633318613972921025506001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232422212409315280683670667 348633318613972921025506001)
          ·
            refine ⟨261474988960479690769129501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348633318613972921025506001 261474988960479690769129501)
            ·
              refine ⟨98053120860179884038423563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261474988960479690769129501 98053120860179884038423563)
              ·
                refine ⟨147079681290269826057635345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98053120860179884038423563 147079681290269826057635345)
                ·
                  refine ⟨110309760967702369543226509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147079681290269826057635345 110309760967702369543226509)
                  ·
                    refine ⟨41366160362888388578709941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110309760967702369543226509 41366160362888388578709941)
                    ·
                      refine ⟨3878077534020786429254057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41366160362888388578709941 3878077534020786429254057)
                      ·
                        rfl

theorem cell23_7552529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_7552529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552529 prefixEnd_7552529 := by exact prefixLift 7552529
  have htrace : WordTrace (prefixWord ++ tailWord_7552529) baseStart_7552529 baseEnd_7552529 := by
    simpa [prefixWord, tailWord_7552529, baseEnd_7552529] using wordTrace_append hprefix tailTrace_7552529
  have hstable : (prefixWord ++ tailWord_7552529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552529).length < 2 ^ (prefixWord ++ tailWord_7552529).sum := by decide
  have hdescent : baseEnd_7552529 < baseStart_7552529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552549 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 10]
def baseStart_7552549 : Nat := 118140960795 + 7552549 * 2 ^ 59
def prefixEnd_7552549 : Nat := 4983230072969 + 3 ^ 40 * 7552549 * 2
def baseEnd_7552549 : Nat := 430898644848208483444885

theorem tailTrace_7552549 : CollatzResearch.WordTrace tailWord_7552549 prefixEnd_7552549 430898644848208483444885 := by
  unfold tailWord_7552549
  simp only [CollatzResearch.WordTrace]
  refine ⟨275464092315412320522300701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183642728210274880348200467 275464092315412320522300701)
  ·
    refine ⟨103299034618279620195862763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275464092315412320522300701 103299034618279620195862763)
    ·
      refine ⟨154948551927419430293794145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103299034618279620195862763 154948551927419430293794145)
      ·
        refine ⟨116211413945564572720345609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154948551927419430293794145 116211413945564572720345609)
        ·
          refine ⟨87158560459173429540259207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116211413945564572720345609 87158560459173429540259207)
          ·
            refine ⟨130737840688760144310388811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87158560459173429540259207 130737840688760144310388811)
            ·
              refine ⟨196106761033140216465583217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130737840688760144310388811 196106761033140216465583217)
              ·
                refine ⟨147080070774855162349187413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196106761033140216465583217 147080070774855162349187413)
                ·
                  refine ⟨430898644848208483444885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 147080070774855162349187413 430898644848208483444885)
                  ·
                    rfl

theorem cell23_7552549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_7552549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552549 prefixEnd_7552549 := by exact prefixLift 7552549
  have htrace : WordTrace (prefixWord ++ tailWord_7552549) baseStart_7552549 baseEnd_7552549 := by
    simpa [prefixWord, tailWord_7552549, baseEnd_7552549] using wordTrace_append hprefix tailTrace_7552549
  have hstable : (prefixWord ++ tailWord_7552549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552549).length < 2 ^ (prefixWord ++ tailWord_7552549).sum := by decide
  have hdescent : baseEnd_7552549 < baseStart_7552549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552563 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 3]
def baseStart_7552563 : Nat := 118140960795 + 7552563 * 2 ^ 59
def prefixEnd_7552563 : Nat := 4983230072969 + 3 ^ 40 * 7552563 * 2
def baseEnd_7552563 : Nat := 3878094992363039296228901

theorem tailTrace_7552563 : CollatzResearch.WordTrace tailWord_7552563 prefixEnd_7552563 3878094992363039296228901 := by
  unfold tailWord_7552563
  simp only [CollatzResearch.WordTrace]
  refine ⟨275464602937361600913310343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183643068624907733942206895 275464602937361600913310343)
  ·
    refine ⟨413196904406042401369965515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275464602937361600913310343 413196904406042401369965515)
    ·
      refine ⟨619795356609063602054948273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413196904406042401369965515 619795356609063602054948273)
      ·
        refine ⟨464846517456797701541211205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619795356609063602054948273 464846517456797701541211205)
        ·
          refine ⟨87158722023149569038977101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 464846517456797701541211205 87158722023149569038977101)
          ·
            refine ⟨32684520758681088389616413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87158722023149569038977101 32684520758681088389616413)
            ·
              refine ⟨12256695284505408146106155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32684520758681088389616413 12256695284505408146106155)
              ·
                refine ⟨18385042926758112219159233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12256695284505408146106155 18385042926758112219159233)
                ·
                  refine ⟨13788782195068584164369425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18385042926758112219159233 13788782195068584164369425)
                  ·
                    refine ⟨10341586646301438123277069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13788782195068584164369425 10341586646301438123277069)
                    ·
                      refine ⟨3878094992363039296228901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10341586646301438123277069 3878094992363039296228901)
                      ·
                        rfl

theorem cell23_7552563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_7552563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552563 prefixEnd_7552563 := by exact prefixLift 7552563
  have htrace : WordTrace (prefixWord ++ tailWord_7552563) baseStart_7552563 baseEnd_7552563 := by
    simpa [prefixWord, tailWord_7552563, baseEnd_7552563] using wordTrace_append hprefix tailTrace_7552563
  have hstable : (prefixWord ++ tailWord_7552563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552563).length < 2 ^ (prefixWord ++ tailWord_7552563).sum := by decide
  have hdescent : baseEnd_7552563 < baseStart_7552563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552570 : List Nat := [3, 1, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_7552570 : Nat := 118140960795 + 7552570 * 2 ^ 59
def prefixEnd_7552570 : Nat := 4983230072969 + 3 ^ 40 * 7552570 * 2
def baseEnd_7552570 : Nat := 1292699528909206922947123

theorem tailTrace_7552570 : CollatzResearch.WordTrace tailWord_7552570 prefixEnd_7552570 1292699528909206922947123 := by
  unfold tailWord_7552570
  simp only [CollatzResearch.WordTrace]
  refine ⟨68866214562084060277203791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183643238832224160739210109 68866214562084060277203791)
  ·
    refine ⟨103299321843126090415805687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68866214562084060277203791 103299321843126090415805687)
    ·
      refine ⟨154948982764689135623708531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103299321843126090415805687 154948982764689135623708531)
      ·
        refine ⟨232423474147033703435562797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154948982764689135623708531 232423474147033703435562797)
        ·
          refine ⟨87158802805137638788336049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232423474147033703435562797 87158802805137638788336049)
          ·
            refine ⟨65369102103853229091252037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87158802805137638788336049 65369102103853229091252037)
            ·
              refine ⟨12256706644472480454609757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65369102103853229091252037 12256706644472480454609757)
              ·
                refine ⟨4596264991677180170478659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12256706644472480454609757 4596264991677180170478659)
                ·
                  refine ⟨6894397487515770255717989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596264991677180170478659 6894397487515770255717989)
                  ·
                    refine ⟨1292699528909206922947123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894397487515770255717989 1292699528909206922947123)
                    ·
                      rfl

theorem cell23_7552570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_7552570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552570 prefixEnd_7552570 := by exact prefixLift 7552570
  have htrace : WordTrace (prefixWord ++ tailWord_7552570) baseStart_7552570 baseEnd_7552570 := by
    simpa [prefixWord, tailWord_7552570, baseEnd_7552570] using wordTrace_append hprefix tailTrace_7552570
  have hstable : (prefixWord ++ tailWord_7552570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552570).length < 2 ^ (prefixWord ++ tailWord_7552570).sum := by decide
  have hdescent : baseEnd_7552570 < baseStart_7552570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552613 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_7552613 : Nat := 118140960795 + 7552613 * 2 ^ 59
def prefixEnd_7552613 : Nat := 4983230072969 + 3 ^ 40 * 7552613 * 2
def baseEnd_7552613 : Nat := 1292706888798588033534557

theorem tailTrace_7552613 : CollatzResearch.WordTrace tailWord_7552613 prefixEnd_7552613 1292706888798588033534557 := by
  unfold tailWord_7552613
  simp only [CollatzResearch.WordTrace]
  refine ⟨275466426587180459452630493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183644284391453639635086995 275466426587180459452630493)
  ·
    refine ⟨103299909970192672294736435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275466426587180459452630493 103299909970192672294736435)
    ·
      refine ⟨154949864955289008442104653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103299909970192672294736435 154949864955289008442104653)
      ·
        refine ⟨58106199358233378165789245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154949864955289008442104653 58106199358233378165789245)
        ·
          refine ⟨21789824759337516812170967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58106199358233378165789245 21789824759337516812170967)
          ·
            refine ⟨32684737139006275218256451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21789824759337516812170967 32684737139006275218256451)
            ·
              refine ⟨49027105708509412827384677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32684737139006275218256451 49027105708509412827384677)
              ·
                refine ⟨9192582320345514905134627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49027105708509412827384677 9192582320345514905134627)
                ·
                  refine ⟨13788873480518272357701941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192582320345514905134627 13788873480518272357701941)
                  ·
                    refine ⟨1292706888798588033534557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13788873480518272357701941 1292706888798588033534557)
                    ·
                      rfl

theorem cell23_7552613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_7552613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552613 prefixEnd_7552613 := by exact prefixLift 7552613
  have htrace : WordTrace (prefixWord ++ tailWord_7552613) baseStart_7552613 baseEnd_7552613 := by
    simpa [prefixWord, tailWord_7552613, baseEnd_7552613] using wordTrace_append hprefix tailTrace_7552613
  have hstable : (prefixWord ++ tailWord_7552613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552613).length < 2 ^ (prefixWord ++ tailWord_7552613).sum := by decide
  have hdescent : baseEnd_7552613 < baseStart_7552613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552630 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_7552630 : Nat := 118140960795 + 7552630 * 2 ^ 59
def prefixEnd_7552630 : Nat := 4983230072969 + 3 ^ 40 * 7552630 * 2
def baseEnd_7552630 : Nat := 1292709798522296844697031

theorem tailTrace_7552630 : CollatzResearch.WordTrace tailWord_7552630 prefixEnd_7552630 1292709798522296844697031 := by
  unfold tailWord_7552630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216690414257429459749959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183644697752079247570666229 17216690414257429459749959)
  ·
    refine ⟨25825035621386144189624939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17216690414257429459749959 25825035621386144189624939)
    ·
      refine ⟨38737553432079216284437409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25825035621386144189624939 38737553432079216284437409)
      ·
        refine ⟨29053165074059412213328057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38737553432079216284437409 29053165074059412213328057)
        ·
          refine ⟨21789873805544559159996043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29053165074059412213328057 21789873805544559159996043)
          ·
            refine ⟨32684810708316838739994065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21789873805544559159996043 32684810708316838739994065)
            ·
              refine ⟨24513608031237629054995549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32684810708316838739994065 24513608031237629054995549)
              ·
                refine ⟨9192603011714110895623331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24513608031237629054995549 9192603011714110895623331)
                ·
                  refine ⟨13788904517571166343434997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192603011714110895623331 13788904517571166343434997)
                  ·
                    refine ⟨1292709798522296844697031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13788904517571166343434997 1292709798522296844697031)
                    ·
                      rfl

theorem cell23_7552630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_7552630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552630 prefixEnd_7552630 := by exact prefixLift 7552630
  have htrace : WordTrace (prefixWord ++ tailWord_7552630) baseStart_7552630 baseEnd_7552630 := by
    simpa [prefixWord, tailWord_7552630, baseEnd_7552630] using wordTrace_append hprefix tailTrace_7552630
  have hstable : (prefixWord ++ tailWord_7552630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552630).length < 2 ^ (prefixWord ++ tailWord_7552630).sum := by decide
  have hdescent : baseEnd_7552630 < baseStart_7552630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552633 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 4]
def baseStart_7552633 : Nat := 118140960795 + 7552633 * 2 ^ 59
def prefixEnd_7552633 : Nat := 4983230072969 + 3 ^ 40 * 7552633 * 2
def baseEnd_7552633 : Nat := 3878130936008854022353579

theorem tailTrace_7552633 : CollatzResearch.WordTrace tailWord_7552633 prefixEnd_7552633 3878130936008854022353579 := by
  unfold tailWord_7552633
  simp only [CollatzResearch.WordTrace]
  refine ⟨275467156047108002868358553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183644770698072001912239035 275467156047108002868358553)
  ·
    refine ⟨206600367035331002151268915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275467156047108002868358553 206600367035331002151268915)
    ·
      refine ⟨309900550552996503226903373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206600367035331002151268915 309900550552996503226903373)
      ·
        refine ⟨116212706457373688710088765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309900550552996503226903373 116212706457373688710088765)
        ·
          refine ⟨43579764921515133266283287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116212706457373688710088765 43579764921515133266283287)
          ·
            refine ⟨65369647382272699899424931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43579764921515133266283287 65369647382272699899424931)
            ·
              refine ⟨98054471073409049849137397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65369647382272699899424931 98054471073409049849137397)
              ·
                refine ⟨9192606663132098423356631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98054471073409049849137397 9192606663132098423356631)
                ·
                  refine ⟨13788909994698147635034947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192606663132098423356631 13788909994698147635034947)
                  ·
                    refine ⟨20683364992047221452552421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13788909994698147635034947 20683364992047221452552421)
                    ·
                      refine ⟨3878130936008854022353579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20683364992047221452552421 3878130936008854022353579)
                      ·
                        rfl

theorem cell23_7552633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_7552633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552633 prefixEnd_7552633 := by exact prefixLift 7552633
  have htrace : WordTrace (prefixWord ++ tailWord_7552633) baseStart_7552633 baseEnd_7552633 := by
    simpa [prefixWord, tailWord_7552633, baseEnd_7552633] using wordTrace_append hprefix tailTrace_7552633
  have hstable : (prefixWord ++ tailWord_7552633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552633).length < 2 ^ (prefixWord ++ tailWord_7552633).sum := by decide
  have hdescent : baseEnd_7552633 < baseStart_7552633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552643 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 2, 4]
def baseStart_7552643 : Nat := 118140960795 + 7552643 * 2 ^ 59
def prefixEnd_7552643 : Nat := 4983230072969 + 3 ^ 40 * 7552643 * 2
def baseEnd_7552643 : Nat := 1292712023605132994409511

theorem tailTrace_7552643 : CollatzResearch.WordTrace tailWord_7552643 prefixEnd_7552643 1292712023605132994409511 := by
  unfold tailWord_7552643
  simp only [CollatzResearch.WordTrace]
  refine ⟨275467520777071774576222583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183645013851381183050815055 275467520777071774576222583)
  ·
    refine ⟨413201281165607661864333875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275467520777071774576222583 413201281165607661864333875)
    ·
      refine ⟨619801921748411492796500813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413201281165607661864333875 619801921748411492796500813)
      ·
        refine ⟨232425720655654309798687805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 619801921748411492796500813 232425720655654309798687805)
        ·
          refine ⟨87159645245870366174507927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232425720655654309798687805 87159645245870366174507927)
          ·
            refine ⟨130739467868805549261761891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87159645245870366174507927 130739467868805549261761891)
            ·
              refine ⟨196109201803208323892642837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130739467868805549261761891 196109201803208323892642837)
              ·
                refine ⟨9192618834525390182467633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196109201803208323892642837 9192618834525390182467633)
                ·
                  refine ⟨6894464125894042636850725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192618834525390182467633 6894464125894042636850725)
                  ·
                    refine ⟨1292712023605132994409511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894464125894042636850725 1292712023605132994409511)
                    ·
                      rfl

theorem cell23_7552643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 4].length) (baseStart_7552643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552643 prefixEnd_7552643 := by exact prefixLift 7552643
  have htrace : WordTrace (prefixWord ++ tailWord_7552643) baseStart_7552643 baseEnd_7552643 := by
    simpa [prefixWord, tailWord_7552643, baseEnd_7552643] using wordTrace_append hprefix tailTrace_7552643
  have hstable : (prefixWord ++ tailWord_7552643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552643).length < 2 ^ (prefixWord ++ tailWord_7552643).sum := by decide
  have hdescent : baseEnd_7552643 < baseStart_7552643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552644 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_7552644 : Nat := 118140960795 + 7552644 * 2 ^ 59
def prefixEnd_7552644 : Nat := 4983230072969 + 3 ^ 40 * 7552644 * 2
def baseEnd_7552644 : Nat := 3878136584296053479316029

theorem tailTrace_7552644 : CollatzResearch.WordTrace tailWord_7552644 prefixEnd_7552644 3878136584296053479316029 := by
  unfold tailWord_7552644
  simp only [CollatzResearch.WordTrace]
  refine ⟨137733778625034075873504493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183645038166712101164672657 137733778625034075873504493)
  ·
    refine ⟨51650166984387778452564185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137733778625034075873504493 51650166984387778452564185)
    ·
      refine ⟨38737625238290833839423139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51650166984387778452564185 38737625238290833839423139)
      ·
        refine ⟨58106437857436250759134709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38737625238290833839423139 58106437857436250759134709)
        ·
          refine ⟨5447478549134648508668879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58106437857436250759134709 5447478549134648508668879)
          ·
            refine ⟨8171217823701972763003319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447478549134648508668879 8171217823701972763003319)
            ·
              refine ⟨12256826735552959144504979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171217823701972763003319 12256826735552959144504979)
              ·
                refine ⟨18385240103329438716757469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12256826735552959144504979 18385240103329438716757469)
                ·
                  refine ⟨6894465038748539518784051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18385240103329438716757469 6894465038748539518784051)
                  ·
                    refine ⟨10341697558122809278176077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6894465038748539518784051 10341697558122809278176077)
                    ·
                      refine ⟨3878136584296053479316029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10341697558122809278176077 3878136584296053479316029)
                      ·
                        rfl

theorem cell23_7552644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_7552644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552644 prefixEnd_7552644 := by exact prefixLift 7552644
  have htrace : WordTrace (prefixWord ++ tailWord_7552644) baseStart_7552644 baseEnd_7552644 := by
    simpa [prefixWord, tailWord_7552644, baseEnd_7552644] using wordTrace_append hprefix tailTrace_7552644
  have hstable : (prefixWord ++ tailWord_7552644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552644).length < 2 ^ (prefixWord ++ tailWord_7552644).sum := by decide
  have hdescent : baseEnd_7552644 < baseStart_7552644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552694 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7552694 : Nat := 118140960795 + 7552694 * 2 ^ 59
def prefixEnd_7552694 : Nat := 4983230072969 + 3 ^ 40 * 7552694 * 2
def baseEnd_7552694 : Nat := 1292720752776259427896933

theorem tailTrace_7552694 : CollatzResearch.WordTrace tailWord_7552694 prefixEnd_7552694 1292720752776259427896933 := by
  unfold tailWord_7552694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216836306242938142895571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 183646253933258006857552757 17216836306242938142895571)
  ·
    refine ⟨25825254459364407214343357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17216836306242938142895571 25825254459364407214343357)
    ·
      refine ⟨9684470422261652705378759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25825254459364407214343357 9684470422261652705378759)
      ·
        refine ⟨14526705633392479058068139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9684470422261652705378759 14526705633392479058068139)
        ·
          refine ⟨21790058450088718587102209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14526705633392479058068139 21790058450088718587102209)
          ·
            refine ⟨16342543837566538940326657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21790058450088718587102209 16342543837566538940326657)
            ·
              refine ⟨12256907878174904205244993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16342543837566538940326657 12256907878174904205244993)
              ·
                refine ⟨9192680908631178153933745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12256907878174904205244993 9192680908631178153933745)
                ·
                  refine ⟨6894510681473383615450309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192680908631178153933745 6894510681473383615450309)
                  ·
                    refine ⟨1292720752776259427896933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894510681473383615450309 1292720752776259427896933)
                    ·
                      rfl

theorem cell23_7552694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7552694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552694 prefixEnd_7552694 := by exact prefixLift 7552694
  have htrace : WordTrace (prefixWord ++ tailWord_7552694) baseStart_7552694 baseEnd_7552694 := by
    simpa [prefixWord, tailWord_7552694, baseEnd_7552694] using wordTrace_append hprefix tailTrace_7552694
  have hstable : (prefixWord ++ tailWord_7552694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552694).length < 2 ^ (prefixWord ++ tailWord_7552694).sum := by decide
  have hdescent : baseEnd_7552694 < baseStart_7552694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552696 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_7552696 : Nat := 118140960795 + 7552696 * 2 ^ 59
def prefixEnd_7552696 : Nat := 4983230072969 + 3 ^ 40 * 7552696 * 2
def baseEnd_7552696 : Nat := 3878163285290087275865789

theorem tailTrace_7552696 : CollatzResearch.WordTrace tailWord_7552696 prefixEnd_7552696 3878163285290087275865789 := by
  unfold tailWord_7552696
  simp only [CollatzResearch.WordTrace]
  refine ⟨137734726922939882313950971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183646302563919843085267961 137734726922939882313950971)
  ·
    refine ⟨206602090384409823470926457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137734726922939882313950971 206602090384409823470926457)
    ·
      refine ⟨154951567788307367603194843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206602090384409823470926457 154951567788307367603194843)
      ·
        refine ⟨232427351682461051404792265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154951567788307367603194843 232427351682461051404792265)
        ·
          refine ⟨174320513761845788553594199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232427351682461051404792265 174320513761845788553594199)
          ·
            refine ⟨261480770642768682830391299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174320513761845788553594199 261480770642768682830391299)
            ·
              refine ⟨392221155964153024245586949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261480770642768682830391299 392221155964153024245586949)
              ·
                refine ⟨73541466743278692046047553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392221155964153024245586949 73541466743278692046047553)
                ·
                  refine ⟨55156100057459019034535665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73541466743278692046047553 55156100057459019034535665)
                  ·
                    refine ⟨41367075043094264275901749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55156100057459019034535665 41367075043094264275901749)
                    ·
                      refine ⟨3878163285290087275865789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41367075043094264275901749 3878163285290087275865789)
                      ·
                        rfl

theorem cell23_7552696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_7552696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552696 prefixEnd_7552696 := by exact prefixLift 7552696
  have htrace : WordTrace (prefixWord ++ tailWord_7552696) baseStart_7552696 baseEnd_7552696 := by
    simpa [prefixWord, tailWord_7552696, baseEnd_7552696] using wordTrace_append hprefix tailTrace_7552696
  have hstable : (prefixWord ++ tailWord_7552696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552696).length < 2 ^ (prefixWord ++ tailWord_7552696).sum := by decide
  have hdescent : baseEnd_7552696 < baseStart_7552696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552717 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_7552717 : Nat := 118140960795 + 7552717 * 2 ^ 59
def prefixEnd_7552717 : Nat := 4983230072969 + 3 ^ 40 * 7552717 * 2
def baseEnd_7552717 : Nat := 3878174068383831693703193

theorem tailTrace_7552717 : CollatzResearch.WordTrace tailWord_7552717 prefixEnd_7552717 3878174068383831693703193 := by
  unfold tailWord_7552717
  simp only [CollatzResearch.WordTrace]
  refine ⟨275470219778803685214416405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183646813185869123476277603 275470219778803685214416405)
  ·
    refine ⟨12912666552131422744425769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 275470219778803685214416405 12912666552131422744425769)
    ·
      refine ⟨9684499914098567058319327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12912666552131422744425769 9684499914098567058319327)
      ·
        refine ⟨14526749871147850587478991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9684499914098567058319327 14526749871147850587478991)
        ·
          refine ⟨21790124806721775881218487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14526749871147850587478991 21790124806721775881218487)
          ·
            refine ⟨32685187210082663821827731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21790124806721775881218487 32685187210082663821827731)
            ·
              refine ⟨49027780815123995732741597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32685187210082663821827731 49027780815123995732741597)
              ·
                refine ⟨18385417805671498399778099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49027780815123995732741597 18385417805671498399778099)
                ·
                  refine ⟨27578126708507247599667149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18385417805671498399778099 27578126708507247599667149)
                  ·
                    refine ⟨10341797515690217849875181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27578126708507247599667149 10341797515690217849875181)
                    ·
                      refine ⟨3878174068383831693703193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10341797515690217849875181 3878174068383831693703193)
                      ·
                        rfl

theorem cell23_7552717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_7552717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552717 prefixEnd_7552717 := by exact prefixLift 7552717
  have htrace : WordTrace (prefixWord ++ tailWord_7552717) baseStart_7552717 baseEnd_7552717 := by
    simpa [prefixWord, tailWord_7552717, baseEnd_7552717] using wordTrace_append hprefix tailTrace_7552717
  have hstable : (prefixWord ++ tailWord_7552717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552717).length < 2 ^ (prefixWord ++ tailWord_7552717).sum := by decide
  have hdescent : baseEnd_7552717 < baseStart_7552717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552740 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_7552740 : Nat := 118140960795 + 7552740 * 2 ^ 59
def prefixEnd_7552740 : Nat := 4983230072969 + 3 ^ 40 * 7552740 * 2
def baseEnd_7552740 : Nat := 3878185878438885103715587

theorem tailTrace_7552740 : CollatzResearch.WordTrace tailWord_7552740 prefixEnd_7552740 3878185878438885103715587 := by
  unfold tailWord_7552740
  simp only [CollatzResearch.WordTrace]
  refine ⟨137735529328860180071251837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183647372438480240095002449 137735529328860180071251837)
  ·
    refine ⟨51650823498322567526719439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137735529328860180071251837 51650823498322567526719439)
    ·
      refine ⟨77476235247483851290079159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51650823498322567526719439 77476235247483851290079159)
      ·
        refine ⟨116214352871225776935118739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77476235247483851290079159 116214352871225776935118739)
        ·
          refine ⟨174321529306838665402678109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116214352871225776935118739 174321529306838665402678109)
          ·
            refine ⟨65370573490064499526004291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174321529306838665402678109 65370573490064499526004291)
            ·
              refine ⟨98055860235096749289006437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65370573490064499526004291 98055860235096749289006437)
              ·
                refine ⟨18385473794080640491688707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98055860235096749289006437 18385473794080640491688707)
                ·
                  refine ⟨27578210691120960737533061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18385473794080640491688707 27578210691120960737533061)
                  ·
                    refine ⟨5170914504585180138287449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27578210691120960737533061 5170914504585180138287449)
                    ·
                      refine ⟨3878185878438885103715587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170914504585180138287449 3878185878438885103715587)
                      ·
                        rfl

theorem cell23_7552740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_7552740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552740 prefixEnd_7552740 := by exact prefixLift 7552740
  have htrace : WordTrace (prefixWord ++ tailWord_7552740) baseStart_7552740 baseEnd_7552740 := by
    simpa [prefixWord, tailWord_7552740, baseEnd_7552740] using wordTrace_append hprefix tailTrace_7552740
  have hstable : (prefixWord ++ tailWord_7552740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552740).length < 2 ^ (prefixWord ++ tailWord_7552740).sum := by decide
  have hdescent : baseEnd_7552740 < baseStart_7552740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552744 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_7552744 : Nat := 118140960795 + 7552744 * 2 ^ 59
def prefixEnd_7552744 : Nat := 4983230072969 + 3 ^ 40 * 7552744 * 2
def baseEnd_7552744 : Nat := 3878187932361503088065569

theorem tailTrace_7552744 : CollatzResearch.WordTrace tailWord_7552744 prefixEnd_7552744 3878187932361503088065569 := by
  unfold tailWord_7552744
  simp only [CollatzResearch.WordTrace]
  refine ⟨137735602274852934412824643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183647469699803912550432857 137735602274852934412824643)
  ·
    refine ⟨206603403412279401619236965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137735602274852934412824643 206603403412279401619236965)
    ·
      refine ⟨38738138139802387803606931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206603403412279401619236965 38738138139802387803606931)
      ·
        refine ⟨58107207209703581705410397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38738138139802387803606931 58107207209703581705410397)
        ·
          refine ⟨21790202703638843139528899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58107207209703581705410397 21790202703638843139528899)
          ·
            refine ⟨32685304055458264709293349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21790202703638843139528899 32685304055458264709293349)
            ·
              refine ⟨6128494510398424632992503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32685304055458264709293349 6128494510398424632992503)
              ·
                refine ⟨9192741765597636949488755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128494510398424632992503 9192741765597636949488755)
                ·
                  refine ⟨13789112648396455424233133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192741765597636949488755 13789112648396455424233133)
                  ·
                    refine ⟨5170917243148670784087425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13789112648396455424233133 5170917243148670784087425)
                    ·
                      refine ⟨3878187932361503088065569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170917243148670784087425 3878187932361503088065569)
                      ·
                        rfl

theorem cell23_7552744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_7552744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552744 prefixEnd_7552744 := by exact prefixLift 7552744
  have htrace : WordTrace (prefixWord ++ tailWord_7552744) baseStart_7552744 baseEnd_7552744 := by
    simpa [prefixWord, tailWord_7552744, baseEnd_7552744] using wordTrace_append hprefix tailTrace_7552744
  have hstable : (prefixWord ++ tailWord_7552744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552744).length < 2 ^ (prefixWord ++ tailWord_7552744).sum := by decide
  have hdescent : baseEnd_7552744 < baseStart_7552744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552753 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_7552753 : Nat := 118140960795 + 7552753 * 2 ^ 59
def prefixEnd_7552753 : Nat := 4983230072969 + 3 ^ 40 * 7552753 * 2
def baseEnd_7552753 : Nat := 3878192553687393552853027

theorem tailTrace_7552753 : CollatzResearch.WordTrace tailWord_7552753 prefixEnd_7552753 3878192553687393552853027 := by
  unfold tailWord_7552753
  simp only [CollatzResearch.WordTrace]
  refine ⟨275471532806673263362726913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183647688537782175575151275 275471532806673263362726913)
  ·
    refine ⟨206603649605004947522045185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275471532806673263362726913 206603649605004947522045185)
    ·
      refine ⟨154952737203753710641533889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206603649605004947522045185 154952737203753710641533889)
      ·
        refine ⟨116214552902815282981150417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154952737203753710641533889 116214552902815282981150417)
        ·
          refine ⟨87160914677111462235862813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116214552902815282981150417 87160914677111462235862813)
          ·
            refine ⟨32685343003916798338448555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87160914677111462235862813 32685343003916798338448555)
            ·
              refine ⟨49028014505875197507672833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32685343003916798338448555 49028014505875197507672833)
              ·
                refine ⟨36771010879406398130754625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49028014505875197507672833 36771010879406398130754625)
                ·
                  refine ⟨27578258159554798598065969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36771010879406398130754625 27578258159554798598065969)
                  ·
                    refine ⟨20683693619666098948549477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27578258159554798598065969 20683693619666098948549477)
                    ·
                      refine ⟨3878192553687393552853027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20683693619666098948549477 3878192553687393552853027)
                      ·
                        rfl

theorem cell23_7552753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_7552753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552753 prefixEnd_7552753 := by exact prefixLift 7552753
  have htrace : WordTrace (prefixWord ++ tailWord_7552753) baseStart_7552753 baseEnd_7552753 := by
    simpa [prefixWord, tailWord_7552753, baseEnd_7552753] using wordTrace_append hprefix tailTrace_7552753
  have hstable : (prefixWord ++ tailWord_7552753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552753).length < 2 ^ (prefixWord ++ tailWord_7552753).sum := by decide
  have hdescent : baseEnd_7552753 < baseStart_7552753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552770 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_7552770 : Nat := 118140960795 + 7552770 * 2 ^ 59
def prefixEnd_7552770 : Nat := 4983230072969 + 3 ^ 40 * 7552770 * 2
def baseEnd_7552770 : Nat := 3878201282858519986340449

theorem tailTrace_7552770 : CollatzResearch.WordTrace tailWord_7552770 prefixEnd_7552770 3878201282858519986340449 := by
  unfold tailWord_7552770
  simp only [CollatzResearch.WordTrace]
  refine ⟨68868038211902918816523941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183648101898407783510730509 68868038211902918816523941)
  ·
    refine ⟨12912757164731797278098239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68868038211902918816523941 12912757164731797278098239)
    ·
      refine ⟨19369135747097695917147359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12912757164731797278098239 19369135747097695917147359)
      ·
        refine ⟨29053703620646543875721039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19369135747097695917147359 29053703620646543875721039)
        ·
          refine ⟨43580555430969815813581559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29053703620646543875721039 43580555430969815813581559)
          ·
            refine ⟨65370833146454723720372339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43580555430969815813581559 65370833146454723720372339)
            ·
              refine ⟨98056249719682085580558509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65370833146454723720372339 98056249719682085580558509)
              ·
                refine ⟨36771093644880782092709441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98056249719682085580558509 36771093644880782092709441)
                ·
                  refine ⟨27578320233660586569532081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36771093644880782092709441 27578320233660586569532081)
                  ·
                    refine ⟨20683740175245439927149061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27578320233660586569532081 20683740175245439927149061)
                    ·
                      refine ⟨3878201282858519986340449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20683740175245439927149061 3878201282858519986340449)
                      ·
                        rfl

theorem cell23_7552770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_7552770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552770 prefixEnd_7552770 := by exact prefixLift 7552770
  have htrace : WordTrace (prefixWord ++ tailWord_7552770) baseStart_7552770 baseEnd_7552770 := by
    simpa [prefixWord, tailWord_7552770, baseEnd_7552770] using wordTrace_append hprefix tailTrace_7552770
  have hstable : (prefixWord ++ tailWord_7552770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552770).length < 2 ^ (prefixWord ++ tailWord_7552770).sum := by decide
  have hdescent : baseEnd_7552770 < baseStart_7552770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552814 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_7552814 : Nat := 118140960795 + 7552814 * 2 ^ 59
def prefixEnd_7552814 : Nat := 4983230072969 + 3 ^ 40 * 7552814 * 2
def baseEnd_7552814 : Nat := 430913764000813090465583

theorem tailTrace_7552814 : CollatzResearch.WordTrace tailWord_7552814 prefixEnd_7552814 430913764000813090465583 := by
  unfold tailWord_7552814
  simp only [CollatzResearch.WordTrace]
  refine ⟨34434219707431533847587187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183649171772968180520464997 34434219707431533847587187)
  ·
    refine ⟨51651329561147300771380781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34434219707431533847587187 51651329561147300771380781)
    ·
      refine ⟨19369248585430237789267793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51651329561147300771380781 19369248585430237789267793)
      ·
        refine ⟨14526936439072678341950845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19369248585430237789267793 14526936439072678341950845)
        ·
          refine ⟨5447601164652254378231567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14526936439072678341950845 5447601164652254378231567)
          ·
            refine ⟨8171401746978381567347351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447601164652254378231567 8171401746978381567347351)
            ·
              refine ⟨12257102620467572351021027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171401746978381567347351 12257102620467572351021027)
              ·
                refine ⟨18385653930701358526531541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12257102620467572351021027 18385653930701358526531541)
                ·
                  refine ⟨430913764000813090465583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18385653930701358526531541 430913764000813090465583)
                  ·
                    rfl

theorem cell23_7552814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_7552814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552814 prefixEnd_7552814 := by exact prefixLift 7552814
  have htrace : WordTrace (prefixWord ++ tailWord_7552814) baseStart_7552814 baseEnd_7552814 := by
    simpa [prefixWord, tailWord_7552814, baseEnd_7552814] using wordTrace_append hprefix tailTrace_7552814
  have hstable : (prefixWord ++ tailWord_7552814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552814).length < 2 ^ (prefixWord ++ tailWord_7552814).sum := by decide
  have hdescent : baseEnd_7552814 < baseStart_7552814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552820 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_7552820 : Nat := 118140960795 + 7552820 * 2 ^ 59
def prefixEnd_7552820 : Nat := 4983230072969 + 3 ^ 40 * 7552820 * 2
def baseEnd_7552820 : Nat := 3878226956891244790715219

theorem tailTrace_7552820 : CollatzResearch.WordTrace tailWord_7552820 prefixEnd_7552820 3878226956891244790715219 := by
  unfold tailWord_7552820
  simp only [CollatzResearch.WordTrace]
  refine ⟨137736988248715266902707957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183649317664953689203610609 137736988248715266902707957)
  ·
    refine ⟨12912842648317056272128871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137736988248715266902707957 12912842648317056272128871)
    ·
      refine ⟨19369263972475584408193307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12912842648317056272128871 19369263972475584408193307)
      ·
        refine ⟨29053895958713376612289961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19369263972475584408193307 29053895958713376612289961)
        ·
          refine ⟨21790421969035032459217471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29053895958713376612289961 21790421969035032459217471)
          ·
            refine ⟨32685632953552548688826207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21790421969035032459217471 32685632953552548688826207)
            ·
              refine ⟨49028449430328823033239311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32685632953552548688826207 49028449430328823033239311)
              ·
                refine ⟨73542674145493234549858967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49028449430328823033239311 73542674145493234549858967)
                ·
                  refine ⟨110314011218239851824788451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73542674145493234549858967 110314011218239851824788451)
                  ·
                    refine ⟨165471016827359777737182677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110314011218239851824788451 165471016827359777737182677)
                    ·
                      refine ⟨3878226956891244790715219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165471016827359777737182677 3878226956891244790715219)
                      ·
                        rfl

theorem cell23_7552820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_7552820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552820 prefixEnd_7552820 := by exact prefixLift 7552820
  have htrace : WordTrace (prefixWord ++ tailWord_7552820) baseStart_7552820 baseEnd_7552820 := by
    simpa [prefixWord, tailWord_7552820, baseEnd_7552820] using wordTrace_append hprefix tailTrace_7552820
  have hstable : (prefixWord ++ tailWord_7552820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552820).length < 2 ^ (prefixWord ++ tailWord_7552820).sum := by decide
  have hdescent : baseEnd_7552820 < baseStart_7552820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552825 : List Nat := [1, 2, 1, 7, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7552825 : Nat := 118140960795 + 7552825 * 2 ^ 59
def prefixEnd_7552825 : Nat := 4983230072969 + 3 ^ 40 * 7552825 * 2
def baseEnd_7552825 : Nat := 3878229524294517271152697

theorem tailTrace_7552825 : CollatzResearch.WordTrace tailWord_7552825 prefixEnd_7552825 3878229524294517271152697 := by
  unfold tailWord_7552825
  simp only [CollatzResearch.WordTrace]
  refine ⟨275474158862412419659347929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183649439241608279772898619 275474158862412419659347929)
  ·
    refine ⟨206605619146809314744510947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275474158862412419659347929 206605619146809314744510947)
    ·
      refine ⟨309908428720213972116766421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206605619146809314744510947 309908428720213972116766421)
      ·
        refine ⟨7263478798130014971486713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 309908428720213972116766421 7263478798130014971486713)
        ·
          refine ⟨5447609098597511228615035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7263478798130014971486713 5447609098597511228615035)
          ·
            refine ⟨8171413647896266842922553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447609098597511228615035 8171413647896266842922553)
            ·
              refine ⟨6128560235922200132191915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8171413647896266842922553 6128560235922200132191915)
              ·
                refine ⟨9192840353883300198287873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128560235922200132191915 9192840353883300198287873)
                ·
                  refine ⟨6894630265412475148715905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192840353883300198287873 6894630265412475148715905)
                  ·
                    refine ⟨5170972699059356361536929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6894630265412475148715905 5170972699059356361536929)
                    ·
                      refine ⟨3878229524294517271152697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5170972699059356361536929 3878229524294517271152697)
                      ·
                        rfl

theorem cell23_7552825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7552825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552825 prefixEnd_7552825 := by exact prefixLift 7552825
  have htrace : WordTrace (prefixWord ++ tailWord_7552825) baseStart_7552825 baseEnd_7552825 := by
    simpa [prefixWord, tailWord_7552825, baseEnd_7552825] using wordTrace_append hprefix tailTrace_7552825
  have hstable : (prefixWord ++ tailWord_7552825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552825).length < 2 ^ (prefixWord ++ tailWord_7552825).sum := by decide
  have hdescent : baseEnd_7552825 < baseStart_7552825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552857 : List Nat := [1, 2, 1, 2, 2, 3, 2, 5, 1, 4]
def baseStart_7552857 : Nat := 118140960795 + 7552857 * 2 ^ 59
def prefixEnd_7552857 : Nat := 4983230072969 + 3 ^ 40 * 7552857 * 2
def baseEnd_7552857 : Nat := 1292748651891820381984183

theorem tailTrace_7552857 : CollatzResearch.WordTrace tailWord_7552857 prefixEnd_7552857 1292748651891820381984183 := by
  unfold tailWord_7552857
  simp only [CollatzResearch.WordTrace]
  refine ⟨275475325998296489124512825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183650217332197659416341883 275475325998296489124512825)
  ·
    refine ⟨206606494498722366843384619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275475325998296489124512825 206606494498722366843384619)
    ·
      refine ⟨309909741748083550265076929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206606494498722366843384619 309909741748083550265076929)
      ·
        refine ⟨232432306311062662698807697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309909741748083550265076929 232432306311062662698807697)
        ·
          refine ⟨174324229733296997024105773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232432306311062662698807697 174324229733296997024105773)
          ·
            refine ⟨65371586149986373884039665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174324229733296997024105773 65371586149986373884039665)
            ·
              refine ⟨49028689612489780413029749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65371586149986373884039665 49028689612489780413029749)
              ·
                refine ⟨4596439651170916913721539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49028689612489780413029749 4596439651170916913721539)
                ·
                  refine ⟨6894659476756375370582309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596439651170916913721539 6894659476756375370582309)
                  ·
                    refine ⟨1292748651891820381984183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894659476756375370582309 1292748651891820381984183)
                    ·
                      rfl

theorem cell23_7552857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 1, 4].length) (baseStart_7552857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552857 prefixEnd_7552857 := by exact prefixLift 7552857
  have htrace : WordTrace (prefixWord ++ tailWord_7552857) baseStart_7552857 baseEnd_7552857 := by
    simpa [prefixWord, tailWord_7552857, baseEnd_7552857] using wordTrace_append hprefix tailTrace_7552857
  have hstable : (prefixWord ++ tailWord_7552857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552857).length < 2 ^ (prefixWord ++ tailWord_7552857).sum := by decide
  have hdescent : baseEnd_7552857 < baseStart_7552857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552893 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_7552893 : Nat := 118140960795 + 7552893 * 2 ^ 59
def prefixEnd_7552893 : Nat := 4983230072969 + 3 ^ 40 * 7552893 * 2
def baseEnd_7552893 : Nat := 3878264440979023005102383

theorem tailTrace_7552893 : CollatzResearch.WordTrace tailWord_7552893 prefixEnd_7552893 3878264440979023005102383 := by
  unfold tailWord_7552893
  simp only [CollatzResearch.WordTrace]
  refine ⟨275476639026166067272823333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183651092684110711515215555 275476639026166067272823333)
  ·
    refine ⟨51651869817406137613654375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275476639026166067272823333 51651869817406137613654375)
    ·
      refine ⟨77477804726109206420481563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51651869817406137613654375 77477804726109206420481563)
      ·
        refine ⟨116216707089163809630722345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77477804726109206420481563 116216707089163809630722345)
        ·
          refine ⟨87162530316872857223041759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116216707089163809630722345 87162530316872857223041759)
          ·
            refine ⟨130743795475309285834562639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87162530316872857223041759 130743795475309285834562639)
            ·
              refine ⟨196115693212963928751843959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130743795475309285834562639 196115693212963928751843959)
              ·
                refine ⟨294173539819445893127765939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196115693212963928751843959 294173539819445893127765939)
                ·
                  refine ⟨441260309729168839691648909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294173539819445893127765939 441260309729168839691648909)
                  ·
                    refine ⟨165472616148438314884368341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 441260309729168839691648909 165472616148438314884368341)
                    ·
                      refine ⟨3878264440979023005102383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 165472616148438314884368341 3878264440979023005102383)
                      ·
                        rfl

theorem cell23_7552893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_7552893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552893 prefixEnd_7552893 := by exact prefixLift 7552893
  have htrace : WordTrace (prefixWord ++ tailWord_7552893) baseStart_7552893 baseEnd_7552893 := by
    simpa [prefixWord, tailWord_7552893, baseEnd_7552893] using wordTrace_append hprefix tailTrace_7552893
  have hstable : (prefixWord ++ tailWord_7552893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552893).length < 2 ^ (prefixWord ++ tailWord_7552893).sum := by decide
  have hdescent : baseEnd_7552893 < baseStart_7552893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552900 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_7552900 : Nat := 118140960795 + 7552900 * 2 ^ 59
def prefixEnd_7552900 : Nat := 4983230072969 + 3 ^ 40 * 7552900 * 2
def baseEnd_7552900 : Nat := 1292756011781201492571617

theorem tailTrace_7552900 : CollatzResearch.WordTrace tailWord_7552900 prefixEnd_7552900 1292756011781201492571617 := by
  unfold tailWord_7552900
  simp only [CollatzResearch.WordTrace]
  refine ⟨137738447168570353734164077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183651262891427138312218769 137738447168570353734164077)
  ·
    refine ⟨51651917688213882650311529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137738447168570353734164077 51651917688213882650311529)
    ·
      refine ⟨38738938266160411987733647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51651917688213882650311529 38738938266160411987733647)
      ·
        refine ⟨58108407399240617981600471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38738938266160411987733647 58108407399240617981600471)
        ·
          refine ⟨87162611098860926972400707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58108407399240617981600471 87162611098860926972400707)
          ·
            refine ⟨130743916648291390458601061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87162611098860926972400707 130743916648291390458601061)
            ·
              refine ⟨24514484371554635710987699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130743916648291390458601061 24514484371554635710987699)
              ·
                refine ⟨36771726557331953566481549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24514484371554635710987699 36771726557331953566481549)
                ·
                  refine ⟨13789397458999482587430581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36771726557331953566481549 13789397458999482587430581)
                  ·
                    refine ⟨1292756011781201492571617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13789397458999482587430581 1292756011781201492571617)
                    ·
                      rfl

theorem cell23_7552900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_7552900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552900 prefixEnd_7552900 := by exact prefixLift 7552900
  have htrace : WordTrace (prefixWord ++ tailWord_7552900) baseStart_7552900 baseEnd_7552900 := by
    simpa [prefixWord, tailWord_7552900, baseEnd_7552900] using wordTrace_append hprefix tailTrace_7552900
  have hstable : (prefixWord ++ tailWord_7552900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552900).length < 2 ^ (prefixWord ++ tailWord_7552900).sum := by decide
  have hdescent : baseEnd_7552900 < baseStart_7552900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552943 : List Nat := [1, 1, 2, 1, 2, 2, 4, 10]
def baseStart_7552943 : Nat := 118140960795 + 7552943 * 2 ^ 59
def prefixEnd_7552943 : Nat := 4983230072969 + 3 ^ 40 * 7552943 * 2
def baseEnd_7552943 : Nat := 143640374630064733684339

theorem tailTrace_7552943 : CollatzResearch.WordTrace tailWord_7552943 prefixEnd_7552943 143640374630064733684339 := by
  unfold tailWord_7552943
  simp only [CollatzResearch.WordTrace]
  refine ⟨275478462675984925812143483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183652308450656617208095655 275478462675984925812143483)
  ·
    refine ⟨413217694013977388718215225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275478462675984925812143483 413217694013977388718215225)
    ·
      refine ⟨309913270510483041538661419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 413217694013977388718215225 309913270510483041538661419)
      ·
        refine ⟨464869905765724562307992129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309913270510483041538661419 464869905765724562307992129)
        ·
          refine ⟨348652429324293421730994097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464869905765724562307992129 348652429324293421730994097)
          ·
            refine ⟨261489321993220066298245573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348652429324293421730994097 261489321993220066298245573)
            ·
              refine ⟨49029247873728762430921045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261489321993220066298245573 49029247873728762430921045)
              ·
                refine ⟨143640374630064733684339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49029247873728762430921045 143640374630064733684339)
                ·
                  rfl

theorem cell23_7552943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 10].length) (baseStart_7552943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552943 prefixEnd_7552943 := by exact prefixLift 7552943
  have htrace : WordTrace (prefixWord ++ tailWord_7552943) baseStart_7552943 baseEnd_7552943 := by
    simpa [prefixWord, tailWord_7552943, baseEnd_7552943] using wordTrace_append hprefix tailTrace_7552943
  have hstable : (prefixWord ++ tailWord_7552943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552943).length < 2 ^ (prefixWord ++ tailWord_7552943).sum := by decide
  have hdescent : baseEnd_7552943 < baseStart_7552943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7552994 : List Nat := [3, 3, 3, 1, 2, 1, 2, 8]
def baseStart_7552994 : Nat := 118140960795 + 7552994 * 2 ^ 59
def prefixEnd_7552994 : Nat := 4983230072969 + 3 ^ 40 * 7552994 * 2
def baseEnd_7552994 : Nat := 143641344537967670738497

theorem tailTrace_7552994 : CollatzResearch.WordTrace tailWord_7552994 prefixEnd_7552994 143641344537967670738497 := by
  unfold tailWord_7552994
  simp only [CollatzResearch.WordTrace]
  refine ⟨68870080699700040380562509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183653548532533441014833357 68870080699700040380562509)
  ·
    refine ⟨25826280262387515142710941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68870080699700040380562509 25826280262387515142710941)
    ·
      refine ⟨9684855098395318178516603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25826280262387515142710941 9684855098395318178516603)
      ·
        refine ⟨14527282647592977267774905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9684855098395318178516603 14527282647592977267774905)
        ·
          refine ⟨10895461985694732950831179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14527282647592977267774905 10895461985694732950831179)
          ·
            refine ⟨16343192978542099426246769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10895461985694732950831179 16343192978542099426246769)
            ·
              refine ⟨12257394733906574569685077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16343192978542099426246769 12257394733906574569685077)
              ·
                refine ⟨143641344537967670738497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12257394733906574569685077 143641344537967670738497)
                ·
                  rfl

theorem cell23_7552994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 8].length) (baseStart_7552994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7552994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7552994 prefixEnd_7552994 := by exact prefixLift 7552994
  have htrace : WordTrace (prefixWord ++ tailWord_7552994) baseStart_7552994 baseEnd_7552994 := by
    simpa [prefixWord, tailWord_7552994, baseEnd_7552994] using wordTrace_append hprefix tailTrace_7552994
  have hstable : (prefixWord ++ tailWord_7552994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7552994).length < 2 ^ (prefixWord ++ tailWord_7552994).sum := by decide
  have hdescent : baseEnd_7552994 < baseStart_7552994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7552994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553040 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 4]
def baseStart_7553040 : Nat := 118140960795 + 7553040 * 2 ^ 59
def prefixEnd_7553040 : Nat := 4983230072969 + 3 ^ 40 * 7553040 * 2
def baseEnd_7553040 : Nat := 3878339922635233929964207

theorem tailTrace_7553040 : CollatzResearch.WordTrace tailWord_7553040 prefixEnd_7553040 3878339922635233929964207 := by
  unfold tailWord_7553040
  simp only [CollatzResearch.WordTrace]
  refine ⟨137741000278316755689212287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183654667037755674252283049 137741000278316755689212287)
  ·
    refine ⟨206611500417475133533818431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137741000278316755689212287 206611500417475133533818431)
    ·
      refine ⟨309917250626212700300727647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206611500417475133533818431 309917250626212700300727647)
      ·
        refine ⟨464875875939319050451091471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309917250626212700300727647 464875875939319050451091471)
        ·
          refine ⟨697313813908978575676637207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464875875939319050451091471 697313813908978575676637207)
          ·
            refine ⟨1045970720863467863514955811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697313813908978575676637207 1045970720863467863514955811)
            ·
              refine ⟨1568956081295201795272433717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045970720863467863514955811 1568956081295201795272433717)
              ·
                refine ⟨147089632621425168306790661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1568956081295201795272433717 147089632621425168306790661)
                ·
                  refine ⟨27579306116517219057523249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147089632621425168306790661 27579306116517219057523249)
                  ·
                    refine ⟨20684479587387914293142437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27579306116517219057523249 20684479587387914293142437)
                    ·
                      refine ⟨3878339922635233929964207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20684479587387914293142437 3878339922635233929964207)
                      ·
                        rfl

theorem cell23_7553040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_7553040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553040 prefixEnd_7553040 := by exact prefixLift 7553040
  have htrace : WordTrace (prefixWord ++ tailWord_7553040) baseStart_7553040 baseEnd_7553040 := by
    simpa [prefixWord, tailWord_7553040, baseEnd_7553040] using wordTrace_append hprefix tailTrace_7553040
  have hstable : (prefixWord ++ tailWord_7553040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553040).length < 2 ^ (prefixWord ++ tailWord_7553040).sum := by decide
  have hdescent : baseEnd_7553040 < baseStart_7553040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553061 : List Nat := [1, 3, 1, 2, 2, 3, 2, 3, 2, 2, 2]
def baseStart_7553061 : Nat := 118140960795 + 7553061 * 2 ^ 59
def prefixEnd_7553061 : Nat := 4983230072969 + 3 ^ 40 * 7553061 * 2
def baseEnd_7553061 : Nat := 3878350705728978347801611

theorem tailTrace_7553061 : CollatzResearch.WordTrace tailWord_7553061 prefixEnd_7553061 3878350705728978347801611 := by
  unfold tailWord_7553061
  simp only [CollatzResearch.WordTrace]
  refine ⟨275482766489557431964939037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183655177659704954643292691 275482766489557431964939037)
  ·
    refine ⟨103306037433584036986852139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275482766489557431964939037 103306037433584036986852139)
    ·
      refine ⟨154959056150376055480278209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103306037433584036986852139 154959056150376055480278209)
      ·
        refine ⟨116219292112782041610208657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154959056150376055480278209 116219292112782041610208657)
        ·
          refine ⟨87164469084586531207656493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116219292112782041610208657 87164469084586531207656493)
          ·
            refine ⟨32686675906719949202871185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87164469084586531207656493 32686675906719949202871185)
            ·
              refine ⟨24515006930039961902153389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32686675906719949202871185 24515006930039961902153389)
              ·
                refine ⟨9193127598764985713307521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24515006930039961902153389 9193127598764985713307521)
                ·
                  refine ⟨6894845699073739284980641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9193127598764985713307521 6894845699073739284980641)
                  ·
                    refine ⟨5171134274305304463735481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6894845699073739284980641 5171134274305304463735481)
                    ·
                      refine ⟨3878350705728978347801611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171134274305304463735481 3878350705728978347801611)
                      ·
                        rfl

theorem cell23_7553061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_7553061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553061 prefixEnd_7553061 := by exact prefixLift 7553061
  have htrace : WordTrace (prefixWord ++ tailWord_7553061) baseStart_7553061 baseEnd_7553061 := by
    simpa [prefixWord, tailWord_7553061, baseEnd_7553061] using wordTrace_append hprefix tailTrace_7553061
  have hstable : (prefixWord ++ tailWord_7553061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553061).length < 2 ^ (prefixWord ++ tailWord_7553061).sum := by decide
  have hdescent : baseEnd_7553061 < baseStart_7553061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553084 : List Nat := [2, 2, 2, 2, 2, 1, 4, 3, 5]
def baseStart_7553084 : Nat := 118140960795 + 7553084 * 2 ^ 59
def prefixEnd_7553084 : Nat := 4983230072969 + 3 ^ 40 * 7553084 * 2
def baseEnd_7553084 : Nat := 430929168420447973090445

theorem tailTrace_7553084 : CollatzResearch.WordTrace tailWord_7553084 prefixEnd_7553084 430929168420447973090445 := by
  unfold tailWord_7553084
  simp only [CollatzResearch.WordTrace]
  refine ⟨137741802684237053446513153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183655736912316071262017537 137741802684237053446513153)
  ·
    refine ⟨103306352013177790084884865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137741802684237053446513153 103306352013177790084884865)
    ·
      refine ⟨77479764009883342563663649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103306352013177790084884865 77479764009883342563663649)
      ·
        refine ⟨58109823007412506922747737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77479764009883342563663649 58109823007412506922747737)
        ·
          refine ⟨43582367255559380192060803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58109823007412506922747737 43582367255559380192060803)
          ·
            refine ⟨65373550883339070288091205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43582367255559380192060803 65373550883339070288091205)
            ·
              refine ⟨12257540790626075679017101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65373550883339070288091205 12257540790626075679017101)
              ·
                refine ⟨4596577796484778379631413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12257540790626075679017101 4596577796484778379631413)
                ·
                  refine ⟨430929168420447973090445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4596577796484778379631413 430929168420447973090445)
                  ·
                    rfl

theorem cell23_7553084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_7553084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553084 prefixEnd_7553084 := by exact prefixLift 7553084
  have htrace : WordTrace (prefixWord ++ tailWord_7553084) baseStart_7553084 baseEnd_7553084 := by
    simpa [prefixWord, tailWord_7553084, baseEnd_7553084] using wordTrace_append hprefix tailTrace_7553084
  have hstable : (prefixWord ++ tailWord_7553084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553084).length < 2 ^ (prefixWord ++ tailWord_7553084).sum := by decide
  have hdescent : baseEnd_7553084 < baseStart_7553084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553134 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7553134 : Nat := 118140960795 + 7553134 * 2 ^ 59
def prefixEnd_7553134 : Nat := 4983230072969 + 3 ^ 40 * 7553134 * 2
def baseEnd_7553134 : Nat := 3878388189816756562188775

theorem tailTrace_7553134 : CollatzResearch.WordTrace tailWord_7553134 prefixEnd_7553134 3878388189816756562188775 := by
  unfold tailWord_7553134
  simp only [CollatzResearch.WordTrace]
  refine ⟨34435678627286620679043307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183656952678861976954897637 34435678627286620679043307)
  ·
    refine ⟨51653517940929931018564961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34435678627286620679043307 51653517940929931018564961)
    ·
      refine ⟨38740138455697448263923721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51653517940929931018564961 38740138455697448263923721)
      ·
        refine ⟨29055103841773086197942791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38740138455697448263923721 29055103841773086197942791)
        ·
          refine ⟨43582655762659629296914187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29055103841773086197942791 43582655762659629296914187)
          ·
            refine ⟨65373983643989443945371281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43582655762659629296914187 65373983643989443945371281)
            ·
              refine ⟨49030487732992082959028461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65373983643989443945371281 49030487732992082959028461)
              ·
                refine ⟨18386432899872031109635673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49030487732992082959028461 18386432899872031109635673)
                ·
                  refine ⟨13789824674904023332226755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18386432899872031109635673 13789824674904023332226755)
                  ·
                    refine ⟨20684737012356034998340133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13789824674904023332226755 20684737012356034998340133)
                    ·
                      refine ⟨3878388189816756562188775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20684737012356034998340133 3878388189816756562188775)
                      ·
                        rfl

theorem cell23_7553134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7553134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553134 prefixEnd_7553134 := by exact prefixLift 7553134
  have htrace : WordTrace (prefixWord ++ tailWord_7553134) baseStart_7553134 baseEnd_7553134 := by
    simpa [prefixWord, tailWord_7553134, baseEnd_7553134] using wordTrace_append hprefix tailTrace_7553134
  have hstable : (prefixWord ++ tailWord_7553134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553134).length < 2 ^ (prefixWord ++ tailWord_7553134).sum := by decide
  have hdescent : baseEnd_7553134 < baseStart_7553134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553137 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_7553137 : Nat := 118140960795 + 7553137 * 2 ^ 59
def prefixEnd_7553137 : Nat := 4983230072969 + 3 ^ 40 * 7553137 * 2
def baseEnd_7553137 : Nat := 3878389730258720050451261

theorem tailTrace_7553137 : CollatzResearch.WordTrace tailWord_7553137 prefixEnd_7553137 3878389730258720050451261 := by
  unfold tailWord_7553137
  simp only [CollatzResearch.WordTrace]
  refine ⟨275485538437282096944705665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183657025624854731296470443 275485538437282096944705665)
  ·
    refine ⟨206614153827961572708529249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275485538437282096944705665 206614153827961572708529249)
    ·
      refine ⟨154960615370971179531396937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206614153827961572708529249 154960615370971179531396937)
      ·
        refine ⟨116220461528228384648547703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154960615370971179531396937 116220461528228384648547703)
        ·
          refine ⟨174330692292342576972821555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116220461528228384648547703 174330692292342576972821555)
          ·
            refine ⟨261496038438513865459232333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174330692292342576972821555 261496038438513865459232333)
            ·
              refine ⟨98061014414442699547212125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261496038438513865459232333 98061014414442699547212125)
              ·
                refine ⟨36772880405416012330204547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98061014414442699547212125 36772880405416012330204547)
                ·
                  refine ⟨55159320608124018495306821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36772880405416012330204547 55159320608124018495306821)
                  ·
                    refine ⟨10342372614023253467870029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55159320608124018495306821 10342372614023253467870029)
                    ·
                      refine ⟨3878389730258720050451261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10342372614023253467870029 3878389730258720050451261)
                      ·
                        rfl

theorem cell23_7553137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_7553137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553137 prefixEnd_7553137 := by exact prefixLift 7553137
  have htrace : WordTrace (prefixWord ++ tailWord_7553137) baseStart_7553137 baseEnd_7553137 := by
    simpa [prefixWord, tailWord_7553137, baseEnd_7553137] using wordTrace_append hprefix tailTrace_7553137
  have hstable : (prefixWord ++ tailWord_7553137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553137).length < 2 ^ (prefixWord ++ tailWord_7553137).sum := by decide
  have hdescent : baseEnd_7553137 < baseStart_7553137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553157 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 8]
def baseStart_7553157 : Nat := 118140960795 + 7553157 * 2 ^ 59
def prefixEnd_7553157 : Nat := 4983230072969 + 3 ^ 40 * 7553157 * 2
def baseEnd_7553157 : Nat := 430933333319089996911241

theorem tailTrace_7553157 : CollatzResearch.WordTrace tailWord_7553157 prefixEnd_7553157 430933333319089996911241 := by
  unfold tailWord_7553157
  simp only [CollatzResearch.WordTrace]
  refine ⟨275486267897209640360433725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183657511931473093573622483 275486267897209640360433725)
  ·
    refine ⟨103307350461453615135162647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275486267897209640360433725 103307350461453615135162647)
    ·
      refine ⟨154961025692180422702743971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103307350461453615135162647 154961025692180422702743971)
      ·
        refine ⟨232441538538270634054115957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154961025692180422702743971 232441538538270634054115957)
        ·
          refine ⟨21791394237962871942573371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232441538538270634054115957 21791394237962871942573371)
          ·
            refine ⟨32687091356944307913860057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21791394237962871942573371 32687091356944307913860057)
            ·
              refine ⟨24515318517708230935395043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32687091356944307913860057 24515318517708230935395043)
              ·
                refine ⟨36772977776562346403092565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24515318517708230935395043 36772977776562346403092565)
                ·
                  refine ⟨430933333319089996911241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36772977776562346403092565 430933333319089996911241)
                  ·
                    rfl

theorem cell23_7553157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_7553157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553157 prefixEnd_7553157 := by exact prefixLift 7553157
  have htrace : WordTrace (prefixWord ++ tailWord_7553157) baseStart_7553157 baseEnd_7553157 := by
    simpa [prefixWord, tailWord_7553157, baseEnd_7553157] using wordTrace_append hprefix tailTrace_7553157
  have hstable : (prefixWord ++ tailWord_7553157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553157).length < 2 ^ (prefixWord ++ tailWord_7553157).sum := by decide
  have hdescent : baseEnd_7553157 < baseStart_7553157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553212 : List Nat := [2, 2, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_7553212 : Nat := 118140960795 + 7553212 * 2 ^ 59
def prefixEnd_7553212 : Nat := 4983230072969 + 3 ^ 40 * 7553212 * 2
def baseEnd_7553212 : Nat := 1292809413769269085671139

theorem tailTrace_7553212 : CollatzResearch.WordTrace tailWord_7553212 prefixEnd_7553212 1292809413769269085671139 := by
  unfold tailWord_7553212
  simp only [CollatzResearch.WordTrace]
  refine ⟨137744136956005192376842945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183658849274673589835790593 137744136956005192376842945)
  ·
    refine ⟨103308102717003894282632209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137744136956005192376842945 103308102717003894282632209)
    ·
      refine ⟨77481077037752920711974157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103308102717003894282632209 77481077037752920711974157)
      ·
        refine ⟨29055403889157345266990309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77481077037752920711974157 29055403889157345266990309)
        ·
          refine ⟨5447888229217002237560683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29055403889157345266990309 5447888229217002237560683)
          ·
            refine ⟨8171832343825503356341025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447888229217002237560683 8171832343825503356341025)
            ·
              refine ⟨6128874257869127517255769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8171832343825503356341025 6128874257869127517255769)
              ·
                refine ⟨4596655693401845637941827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6128874257869127517255769 4596655693401845637941827)
                ·
                  refine ⟨6894983540102768456912741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596655693401845637941827 6894983540102768456912741)
                  ·
                    refine ⟨1292809413769269085671139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6894983540102768456912741 1292809413769269085671139)
                    ·
                      rfl

theorem cell23_7553212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_7553212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553212 prefixEnd_7553212 := by exact prefixLift 7553212
  have htrace : WordTrace (prefixWord ++ tailWord_7553212) baseStart_7553212 baseEnd_7553212 := by
    simpa [prefixWord, tailWord_7553212, baseEnd_7553212] using wordTrace_append hprefix tailTrace_7553212
  have hstable : (prefixWord ++ tailWord_7553212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553212).length < 2 ^ (prefixWord ++ tailWord_7553212).sum := by decide
  have hdescent : baseEnd_7553212 < baseStart_7553212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553224 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_7553224 : Nat := 118140960795 + 7553224 * 2 ^ 59
def prefixEnd_7553224 : Nat := 4983230072969 + 3 ^ 40 * 7553224 * 2
def baseEnd_7553224 : Nat := 3878434403075661210063361

theorem tailTrace_7553224 : CollatzResearch.WordTrace tailWord_7553224 prefixEnd_7553224 3878434403075661210063361 := by
  unfold tailWord_7553224
  simp only [CollatzResearch.WordTrace]
  refine ⟨137744355793983455401561363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183659141058644607202081817 137744355793983455401561363)
  ·
    refine ⟨206616533690975183102342045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137744355793983455401561363 206616533690975183102342045)
    ·
      refine ⟨77481200134115693663378267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206616533690975183102342045 77481200134115693663378267)
      ·
        refine ⟨116221800201173540495067401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77481200134115693663378267 116221800201173540495067401)
        ·
          refine ⟨87166350150880155371300551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116221800201173540495067401 87166350150880155371300551)
          ·
            refine ⟨130749525226320233056950827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87166350150880155371300551 130749525226320233056950827)
            ·
              refine ⟨196124287839480349585426241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130749525226320233056950827 196124287839480349585426241)
              ·
                refine ⟨147093215879610262189069681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196124287839480349585426241 147093215879610262189069681)
                ·
                  refine ⟨110319911909707696641802261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147093215879610262189069681 110319911909707696641802261)
                  ·
                    refine ⟨5171245870767548280084481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110319911909707696641802261 5171245870767548280084481)
                    ·
                      refine ⟨3878434403075661210063361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171245870767548280084481 3878434403075661210063361)
                      ·
                        rfl

theorem cell23_7553224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_7553224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553224 prefixEnd_7553224 := by exact prefixLift 7553224
  have htrace : WordTrace (prefixWord ++ tailWord_7553224) baseStart_7553224 baseEnd_7553224 := by
    simpa [prefixWord, tailWord_7553224, baseEnd_7553224] using wordTrace_append hprefix tailTrace_7553224
  have hstable : (prefixWord ++ tailWord_7553224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553224).length < 2 ^ (prefixWord ++ tailWord_7553224).sum := by decide
  have hdescent : baseEnd_7553224 < baseStart_7553224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553227 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 5]
def baseStart_7553227 : Nat := 118140960795 + 7553227 * 2 ^ 59
def prefixEnd_7553227 : Nat := 4983230072969 + 3 ^ 40 * 7553227 * 2
def baseEnd_7553227 : Nat := 3878435943517624698325847

theorem tailTrace_7553227 : CollatzResearch.WordTrace tailWord_7553227 prefixEnd_7553227 3878435943517624698325847 := by
  unfold tailWord_7553227
  simp only [CollatzResearch.WordTrace]
  refine ⟨275488821006956042315481935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183659214004637361543654623 275488821006956042315481935)
  ·
    refine ⟨413233231510434063473222903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275488821006956042315481935 413233231510434063473222903)
    ·
      refine ⟨619849847265651095209834355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413233231510434063473222903 619849847265651095209834355)
      ·
        refine ⟨929774770898476642814751533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619849847265651095209834355 929774770898476642814751533)
        ·
          refine ⟨348665539086928741055531825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 929774770898476642814751533 348665539086928741055531825)
          ·
            refine ⟨261499154315196555791648869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348665539086928741055531825 261499154315196555791648869)
            ·
              refine ⟨49031091434099354210934163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261499154315196555791648869 49031091434099354210934163)
              ·
                refine ⟨73546637151149031316401245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49031091434099354210934163 73546637151149031316401245)
                ·
                  refine ⟨27579988931680886743650467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73546637151149031316401245 27579988931680886743650467)
                  ·
                    refine ⟨41369983397521330115475701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27579988931680886743650467 41369983397521330115475701)
                    ·
                      refine ⟨3878435943517624698325847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41369983397521330115475701 3878435943517624698325847)
                      ·
                        rfl

theorem cell23_7553227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_7553227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553227 prefixEnd_7553227 := by exact prefixLift 7553227
  have htrace : WordTrace (prefixWord ++ tailWord_7553227) baseStart_7553227 baseEnd_7553227 := by
    simpa [prefixWord, tailWord_7553227, baseEnd_7553227] using wordTrace_append hprefix tailTrace_7553227
  have hstable : (prefixWord ++ tailWord_7553227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553227).length < 2 ^ (prefixWord ++ tailWord_7553227).sum := by decide
  have hdescent : baseEnd_7553227 < baseStart_7553227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553234 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_7553234 : Nat := 118140960795 + 7553234 * 2 ^ 59
def prefixEnd_7553234 : Nat := 4983230072969 + 3 ^ 40 * 7553234 * 2
def baseEnd_7553234 : Nat := 1292813179294068723646105

theorem tailTrace_7553234 : CollatzResearch.WordTrace tailWord_7553234 prefixEnd_7553234 1292813179294068723646105 := by
  unfold tailWord_7553234
  simp only [CollatzResearch.WordTrace]
  refine ⟨68872269079482670627746689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183659384211953788340657837 68872269079482670627746689)
  ·
    refine ⟨51654201809612002970810017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68872269079482670627746689 51654201809612002970810017)
    ·
      refine ⟨38740651357209002228107513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51654201809612002970810017 38740651357209002228107513)
      ·
        refine ⟨29055488517906751671080635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38740651357209002228107513 29055488517906751671080635)
        ·
          refine ⟨43583232776860127506620953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29055488517906751671080635 43583232776860127506620953)
          ·
            refine ⟨32687424582645095629965715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43583232776860127506620953 32687424582645095629965715)
            ·
              refine ⟨49031136873967643444948573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32687424582645095629965715 49031136873967643444948573)
              ·
                refine ⟨18386676327737866291855715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49031136873967643444948573 18386676327737866291855715)
                ·
                  refine ⟨27580014491606799437783573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18386676327737866291855715 27580014491606799437783573)
                  ·
                    refine ⟨1292813179294068723646105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27580014491606799437783573 1292813179294068723646105)
                    ·
                      rfl

theorem cell23_7553234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_7553234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553234 prefixEnd_7553234 := by exact prefixLift 7553234
  have htrace : WordTrace (prefixWord ++ tailWord_7553234) baseStart_7553234 baseEnd_7553234 := by
    simpa [prefixWord, tailWord_7553234, baseEnd_7553234] using wordTrace_append hprefix tailTrace_7553234
  have hstable : (prefixWord ++ tailWord_7553234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553234).length < 2 ^ (prefixWord ++ tailWord_7553234).sum := by decide
  have hdescent : baseEnd_7553234 < baseStart_7553234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553241 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 5, 2, 2]
def baseStart_7553241 : Nat := 118140960795 + 7553241 * 2 ^ 59
def prefixEnd_7553241 : Nat := 4983230072969 + 3 ^ 40 * 7553241 * 2
def baseEnd_7553241 : Nat := 3878443132246787643550783

theorem tailTrace_7553241 : CollatzResearch.WordTrace tailWord_7553241 prefixEnd_7553241 3878443132246787643550783 := by
  unfold tailWord_7553241
  simp only [CollatzResearch.WordTrace]
  refine ⟨275489331628905322706491577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183659554419270215137661051 275489331628905322706491577)
  ·
    refine ⟨206616998721678992029868683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275489331628905322706491577 206616998721678992029868683)
    ·
      refine ⟨309925498082518488044803025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206616998721678992029868683 309925498082518488044803025)
      ·
        refine ⟨232444123561888866033602269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309925498082518488044803025 232444123561888866033602269)
        ·
          refine ⟨87166546335708324762600851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232444123561888866033602269 87166546335708324762600851)
          ·
            refine ⟨130749819503562487143901277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87166546335708324762600851 130749819503562487143901277)
            ·
              refine ⟨49031182313835932678962979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130749819503562487143901277 49031182313835932678962979)
              ·
                refine ⟨73546773470753899018444469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49031182313835932678962979 73546773470753899018444469)
                ·
                  refine ⟨6895010012883178032979169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73546773470753899018444469 6895010012883178032979169)
                  ·
                    refine ⟨5171257509662383524734377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6895010012883178032979169 5171257509662383524734377)
                    ·
                      refine ⟨3878443132246787643550783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171257509662383524734377 3878443132246787643550783)
                      ·
                        rfl

theorem cell23_7553241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_7553241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553241 prefixEnd_7553241 := by exact prefixLift 7553241
  have htrace : WordTrace (prefixWord ++ tailWord_7553241) baseStart_7553241 baseEnd_7553241 := by
    simpa [prefixWord, tailWord_7553241, baseEnd_7553241] using wordTrace_append hprefix tailTrace_7553241
  have hstable : (prefixWord ++ tailWord_7553241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553241).length < 2 ^ (prefixWord ++ tailWord_7553241).sum := by decide
  have hdescent : baseEnd_7553241 < baseStart_7553241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553245 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7553245 : Nat := 118140960795 + 7553245 * 2 ^ 59
def prefixEnd_7553245 : Nat := 4983230072969 + 3 ^ 40 * 7553245 * 2
def baseEnd_7553245 : Nat := 3878445186169405627900765

theorem tailTrace_7553245 : CollatzResearch.WordTrace tailWord_7553245 prefixEnd_7553245 3878445186169405627900765 := by
  unfold tailWord_7553245
  simp only [CollatzResearch.WordTrace]
  refine ⟨275489477520890831389637189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183659651680593887593091459 275489477520890831389637189)
  ·
    refine ⟨51654277035167030885556973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275489477520890831389637189 51654277035167030885556973)
    ·
      refine ⟨19370353888187636582083865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51654277035167030885556973 19370353888187636582083865)
      ·
        refine ⟨14527765416140727436562899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19370353888187636582083865 14527765416140727436562899)
        ·
          refine ⟨21791648124211091154844349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14527765416140727436562899 21791648124211091154844349)
          ·
            refine ⟨8171868046579159183066631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21791648124211091154844349 8171868046579159183066631)
            ·
              refine ⟨12257802069868738774599947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171868046579159183066631 12257802069868738774599947)
              ·
                refine ⟨18386703104803108161899921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12257802069868738774599947 18386703104803108161899921)
                ·
                  refine ⟨13790027328602331121424941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18386703104803108161899921 13790027328602331121424941)
                  ·
                    refine ⟨5171260248225874170534353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13790027328602331121424941 5171260248225874170534353)
                    ·
                      refine ⟨3878445186169405627900765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171260248225874170534353 3878445186169405627900765)
                      ·
                        rfl

theorem cell23_7553245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7553245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553245 prefixEnd_7553245 := by exact prefixLift 7553245
  have htrace : WordTrace (prefixWord ++ tailWord_7553245) baseStart_7553245 baseEnd_7553245 := by
    simpa [prefixWord, tailWord_7553245, baseEnd_7553245] using wordTrace_append hprefix tailTrace_7553245
  have hstable : (prefixWord ++ tailWord_7553245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553245).length < 2 ^ (prefixWord ++ tailWord_7553245).sum := by decide
  have hdescent : baseEnd_7553245 < baseStart_7553245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553277 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_7553277 : Nat := 118140960795 + 7553277 * 2 ^ 59
def prefixEnd_7553277 : Nat := 4983230072969 + 3 ^ 40 * 7553277 * 2
def baseEnd_7553277 : Nat := 1292820539183449834233539

theorem tailTrace_7553277 : CollatzResearch.WordTrace tailWord_7553277 prefixEnd_7553277 1292820539183449834233539 := by
  unfold tailWord_7553277
  simp only [CollatzResearch.WordTrace]
  refine ⟨275490644656774900854802085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183660429771183267236534723 275490644656774900854802085)
  ·
    refine ⟨51654495873145293910275391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275490644656774900854802085 51654495873145293910275391)
    ·
      refine ⟨77481743809717940865413087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51654495873145293910275391 77481743809717940865413087)
      ·
        refine ⟨116222615714576911298119631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77481743809717940865413087 116222615714576911298119631)
        ·
          refine ⟨174333923571865366947179447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116222615714576911298119631 174333923571865366947179447)
          ·
            refine ⟨261500885357798050420769171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174333923571865366947179447 261500885357798050420769171)
            ·
              refine ⟨392251328036697075631153757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261500885357798050420769171 392251328036697075631153757)
              ·
                refine ⟨147094248013761403361682659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 392251328036697075631153757 147094248013761403361682659)
                ·
                  refine ⟨220641372020642105042523989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147094248013761403361682659 220641372020642105042523989)
                  ·
                    refine ⟨1292820539183449834233539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 220641372020642105042523989 1292820539183449834233539)
                    ·
                      rfl

theorem cell23_7553277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_7553277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553277 prefixEnd_7553277 := by exact prefixLift 7553277
  have htrace : WordTrace (prefixWord ++ tailWord_7553277) baseStart_7553277 baseEnd_7553277 := by
    simpa [prefixWord, tailWord_7553277, baseEnd_7553277] using wordTrace_append hprefix tailTrace_7553277
  have hstable : (prefixWord ++ tailWord_7553277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553277).length < 2 ^ (prefixWord ++ tailWord_7553277).sum := by decide
  have hdescent : baseEnd_7553277 < baseStart_7553277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553301 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_7553301 : Nat := 118140960795 + 7553301 * 2 ^ 59
def prefixEnd_7553301 : Nat := 4983230072969 + 3 ^ 40 * 7553301 * 2
def baseEnd_7553301 : Nat := 3878473941086057408800507

theorem tailTrace_7553301 : CollatzResearch.WordTrace tailWord_7553301 prefixEnd_7553301 3878473941086057408800507 := by
  unfold tailWord_7553301
  simp only [CollatzResearch.WordTrace]
  refine ⟨275491520008687952953675757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183661013339125301969117171 275491520008687952953675757)
  ·
    refine ⟨103309320003257982357628409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275491520008687952953675757 103309320003257982357628409)
    ·
      refine ⟨77481990002443486768221307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103309320003257982357628409 77481990002443486768221307)
      ·
        refine ⟨116222985003665230152331961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77481990002443486768221307 116222985003665230152331961)
        ·
          refine ⟨87167238752748922614248971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116222985003665230152331961 87167238752748922614248971)
          ·
            refine ⟨130750858129123383921373457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87167238752748922614248971 130750858129123383921373457)
            ·
              refine ⟨98063143596842537941030093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130750858129123383921373457 98063143596842537941030093)
              ·
                refine ⟨36773678848815951727886285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98063143596842537941030093 36773678848815951727886285)
                ·
                  refine ⟨13790129568305981897957357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36773678848815951727886285 13790129568305981897957357)
                  ·
                    refine ⟨5171298588114743211734009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13790129568305981897957357 5171298588114743211734009)
                    ·
                      refine ⟨3878473941086057408800507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171298588114743211734009 3878473941086057408800507)
                      ·
                        rfl

theorem cell23_7553301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_7553301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553301 prefixEnd_7553301 := by exact prefixLift 7553301
  have htrace : WordTrace (prefixWord ++ tailWord_7553301) baseStart_7553301 baseEnd_7553301 := by
    simpa [prefixWord, tailWord_7553301, baseEnd_7553301] using wordTrace_append hprefix tailTrace_7553301
  have hstable : (prefixWord ++ tailWord_7553301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553301).length < 2 ^ (prefixWord ++ tailWord_7553301).sum := by decide
  have hdescent : baseEnd_7553301 < baseStart_7553301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553307 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 1, 8]
def baseStart_7553307 : Nat := 118140960795 + 7553307 * 2 ^ 59
def prefixEnd_7553307 : Nat := 4983230072969 + 3 ^ 40 * 7553307 * 2
def baseEnd_7553307 : Nat := 1292825673989994795108493

theorem tailTrace_7553307 : CollatzResearch.WordTrace tailWord_7553307 prefixEnd_7553307 1292825673989994795108493 := by
  unfold tailWord_7553307
  simp only [CollatzResearch.WordTrace]
  refine ⟨275491738846666215978394175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183661159231110810652262783 275491738846666215978394175)
  ·
    refine ⟨413237608269999323967591263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275491738846666215978394175 413237608269999323967591263)
    ·
      refine ⟨619856412404998985951386895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413237608269999323967591263 619856412404998985951386895)
      ·
        refine ⟨929784618607498478927080343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619856412404998985951386895 929784618607498478927080343)
        ·
          refine ⟨1394676927911247718390620515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929784618607498478927080343 1394676927911247718390620515)
          ·
            refine ⟨2092015391866871577585930773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394676927911247718390620515 2092015391866871577585930773)
            ·
              refine ⟨98063221493759605199340505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2092015391866871577585930773 98063221493759605199340505)
              ·
                refine ⟨73547416120319703899505379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98063221493759605199340505 73547416120319703899505379)
                ·
                  refine ⟨110321124180479555849258069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73547416120319703899505379 110321124180479555849258069)
                  ·
                    refine ⟨1292825673989994795108493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110321124180479555849258069 1292825673989994795108493)
                    ·
                      rfl

theorem cell23_7553307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 8].length) (baseStart_7553307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553307 prefixEnd_7553307 := by exact prefixLift 7553307
  have htrace : WordTrace (prefixWord ++ tailWord_7553307) baseStart_7553307 baseEnd_7553307 := by
    simpa [prefixWord, tailWord_7553307, baseEnd_7553307] using wordTrace_append hprefix tailTrace_7553307
  have hstable : (prefixWord ++ tailWord_7553307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553307).length < 2 ^ (prefixWord ++ tailWord_7553307).sum := by decide
  have hdescent : baseEnd_7553307 < baseStart_7553307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553309 : List Nat := [1, 4, 2, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_7553309 : Nat := 118140960795 + 7553309 * 2 ^ 59
def prefixEnd_7553309 : Nat := 4983230072969 + 3 ^ 40 * 7553309 * 2
def baseEnd_7553309 : Nat := 3878478048931293377500471

theorem tailTrace_7553309 : CollatzResearch.WordTrace tailWord_7553309 prefixEnd_7553309 3878478048931293377500471 := by
  unfold tailWord_7553309
  simp only [CollatzResearch.WordTrace]
  refine ⟨275491811792658970319966981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183661207861772646879977987 275491811792658970319966981)
  ·
    refine ⟨51654714711123556934993809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 275491811792658970319966981 51654714711123556934993809)
    ·
      refine ⟨38741036033342667701245357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51654714711123556934993809 38741036033342667701245357)
      ·
        refine ⟨14527888512503500387967009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38741036033342667701245357 14527888512503500387967009)
        ·
          refine ⟨10895916384377625290975257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14527888512503500387967009 10895916384377625290975257)
          ·
            refine ⟨8171937288283218968231443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10895916384377625290975257 8171937288283218968231443)
            ·
              refine ⟨12257905932424828452347165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171937288283218968231443 12257905932424828452347165)
              ·
                refine ⟨4596714724659310669630187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12257905932424828452347165 4596714724659310669630187)
                ·
                  refine ⟨6895072086988966004445281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596714724659310669630187 6895072086988966004445281)
                  ·
                    refine ⟨5171304065241724503333961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6895072086988966004445281 5171304065241724503333961)
                    ·
                      refine ⟨3878478048931293377500471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171304065241724503333961 3878478048931293377500471)
                      ·
                        rfl

theorem cell23_7553309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_7553309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553309 prefixEnd_7553309 := by exact prefixLift 7553309
  have htrace : WordTrace (prefixWord ++ tailWord_7553309) baseStart_7553309 baseEnd_7553309 := by
    simpa [prefixWord, tailWord_7553309, baseEnd_7553309] using wordTrace_append hprefix tailTrace_7553309
  have hstable : (prefixWord ++ tailWord_7553309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553309).length < 2 ^ (prefixWord ++ tailWord_7553309).sum := by decide
  have hdescent : baseEnd_7553309 < baseStart_7553309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553326 : List Nat := [4, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_7553326 : Nat := 118140960795 + 7553326 * 2 ^ 59
def prefixEnd_7553326 : Nat := 4983230072969 + 3 ^ 40 * 7553326 * 2
def baseEnd_7553326 : Nat := 3878486778102419810987893

theorem tailTrace_7553326 : CollatzResearch.WordTrace tailWord_7553326 prefixEnd_7553326 3878486778102419810987893 := by
  unfold tailWord_7553326
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436553979199672777916979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183661621222398254815557221 34436553979199672777916979)
  ·
    refine ⟨51654830968799509166875469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34436553979199672777916979 51654830968799509166875469)
    ·
      refine ⟨19370561613299815937578301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51654830968799509166875469 19370561613299815937578301)
      ·
        refine ⟨7263960604987430976591863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19370561613299815937578301 7263960604987430976591863)
        ·
          refine ⟨10895940907481146464887795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7263960604987430976591863 10895940907481146464887795)
          ·
            refine ⟨16343911361221719697331693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10895940907481146464887795 16343911361221719697331693)
            ·
              refine ⟨6128966760458144886499385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16343911361221719697331693 6128966760458144886499385)
              ·
                refine ⟨4596725070343608664874539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6128966760458144886499385 4596725070343608664874539)
                ·
                  refine ⟨6895087605515412997311809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596725070343608664874539 6895087605515412997311809)
                  ·
                    refine ⟨5171315704136559747983857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6895087605515412997311809 5171315704136559747983857)
                    ·
                      refine ⟨3878486778102419810987893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171315704136559747983857 3878486778102419810987893)
                      ·
                        rfl

theorem cell23_7553326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_7553326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553326 prefixEnd_7553326 := by exact prefixLift 7553326
  have htrace : WordTrace (prefixWord ++ tailWord_7553326) baseStart_7553326 baseEnd_7553326 := by
    simpa [prefixWord, tailWord_7553326, baseEnd_7553326] using wordTrace_append hprefix tailTrace_7553326
  have hstable : (prefixWord ++ tailWord_7553326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553326).length < 2 ^ (prefixWord ++ tailWord_7553326).sum := by decide
  have hdescent : baseEnd_7553326 < baseStart_7553326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553342 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_7553342 : Nat := 118140960795 + 7553342 * 2 ^ 59
def prefixEnd_7553342 : Nat := 4983230072969 + 3 ^ 40 * 7553342 * 2
def baseEnd_7553342 : Nat := 3878494993792891748387819

theorem tailTrace_7553342 : CollatzResearch.WordTrace tailWord_7553342 prefixEnd_7553342 3878494993792891748387819 := by
  unfold tailWord_7553342
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436626925192427119489785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 183662010267692944637278853 34436626925192427119489785)
  ·
    refine ⟨25827470193894320339617339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34436626925192427119489785 25827470193894320339617339)
    ·
      refine ⟨38741205290841480509426009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25827470193894320339617339 38741205290841480509426009)
      ·
        refine ⟨29055903968131110382069507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38741205290841480509426009 29055903968131110382069507)
        ·
          refine ⟨43583855952196665573104261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29055903968131110382069507 43583855952196665573104261)
          ·
            refine ⟨8171972991036874794957049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43583855952196665573104261 8171972991036874794957049)
            ·
              refine ⟨6128979743277656096217787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8171972991036874794957049 6128979743277656096217787)
              ·
                refine ⟨9193469614916484144326681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128979743277656096217787 9193469614916484144326681)
                ·
                  refine ⟨6895102211187363108245011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9193469614916484144326681 6895102211187363108245011)
                  ·
                    refine ⟨10342653316781044662367517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6895102211187363108245011 10342653316781044662367517)
                    ·
                      refine ⟨3878494993792891748387819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10342653316781044662367517 3878494993792891748387819)
                      ·
                        rfl

theorem cell23_7553342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_7553342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553342 prefixEnd_7553342 := by exact prefixLift 7553342
  have htrace : WordTrace (prefixWord ++ tailWord_7553342) baseStart_7553342 baseEnd_7553342 := by
    simpa [prefixWord, tailWord_7553342, baseEnd_7553342] using wordTrace_append hprefix tailTrace_7553342
  have hstable : (prefixWord ++ tailWord_7553342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553342).length < 2 ^ (prefixWord ++ tailWord_7553342).sum := by decide
  have hdescent : baseEnd_7553342 < baseStart_7553342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553388 : List Nat := [2, 2, 1, 1, 6, 1, 1, 4, 5]
def baseStart_7553388 : Nat := 118140960795 + 7553388 * 2 ^ 59
def prefixEnd_7553388 : Nat := 4983230072969 + 3 ^ 40 * 7553388 * 2
def baseEnd_7553388 : Nat := 430946512655888729823623

theorem tailTrace_7553388 : CollatzResearch.WordTrace tailWord_7553388 prefixEnd_7553388 430946512655888729823623 := by
  unfold tailWord_7553388
  simp only [CollatzResearch.WordTrace]
  refine ⟨137747346579686383406046409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183663128772915177874728545 137747346579686383406046409)
  ·
    refine ⟨103310509934764787554534807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137747346579686383406046409 103310509934764787554534807)
    ·
      refine ⟨154965764902147181331802211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103310509934764787554534807 154965764902147181331802211)
      ·
        refine ⟨232448647353220771997703317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154965764902147181331802211 232448647353220771997703317)
        ·
          refine ⟨10896030344682223687392343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232448647353220771997703317 10896030344682223687392343)
          ·
            refine ⟨16344045517023335531088515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10896030344682223687392343 16344045517023335531088515)
            ·
              refine ⟨24516068275535003296632773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16344045517023335531088515 24516068275535003296632773)
              ·
                refine ⟨4596762801662813118118645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24516068275535003296632773 4596762801662813118118645)
                ·
                  refine ⟨430946512655888729823623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4596762801662813118118645 430946512655888729823623)
                  ·
                    rfl

theorem cell23_7553388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_7553388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553388 prefixEnd_7553388 := by exact prefixLift 7553388
  have htrace : WordTrace (prefixWord ++ tailWord_7553388) baseStart_7553388 baseEnd_7553388 := by
    simpa [prefixWord, tailWord_7553388, baseEnd_7553388] using wordTrace_append hprefix tailTrace_7553388
  have hstable : (prefixWord ++ tailWord_7553388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553388).length < 2 ^ (prefixWord ++ tailWord_7553388).sum := by decide
  have hdescent : baseEnd_7553388 < baseStart_7553388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553418 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_7553418 : Nat := 118140960795 + 7553418 * 2 ^ 59
def prefixEnd_7553418 : Nat := 4983230072969 + 3 ^ 40 * 7553418 * 2
def baseEnd_7553418 : Nat := 1292844672774211150345823

theorem tailTrace_7553418 : CollatzResearch.WordTrace tailWord_7553418 prefixEnd_7553418 1292844672774211150345823 := by
  unfold tailWord_7553418
  simp only [CollatzResearch.WordTrace]
  refine ⟨68873946837316020483921227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 183663858232842721290456605 68873946837316020483921227)
  ·
    refine ⟨103310920255974030725881841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68873946837316020483921227 103310920255974030725881841)
    ·
      refine ⟨77483190191980523044411381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103310920255974030725881841 77483190191980523044411381)
      ·
        refine ⟨7264049080498174035413567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77483190191980523044411381 7264049080498174035413567)
        ·
          refine ⟨10896073620747261053120351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7264049080498174035413567 10896073620747261053120351)
          ·
            refine ⟨16344110431120891579680527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10896073620747261053120351 16344110431120891579680527)
            ·
              refine ⟨24516165646681337369520791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16344110431120891579680527 24516165646681337369520791)
              ·
                refine ⟨36774248470022006054281187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24516165646681337369520791 36774248470022006054281187)
                ·
                  refine ⟨55161372705033009081421781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36774248470022006054281187 55161372705033009081421781)
                  ·
                    refine ⟨1292844672774211150345823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55161372705033009081421781 1292844672774211150345823)
                    ·
                      rfl

theorem cell23_7553418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_7553418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553418 prefixEnd_7553418 := by exact prefixLift 7553418
  have htrace : WordTrace (prefixWord ++ tailWord_7553418) baseStart_7553418 baseEnd_7553418 := by
    simpa [prefixWord, tailWord_7553418, baseEnd_7553418] using wordTrace_append hprefix tailTrace_7553418
  have hstable : (prefixWord ++ tailWord_7553418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553418).length < 2 ^ (prefixWord ++ tailWord_7553418).sum := by decide
  have hdescent : baseEnd_7553418 < baseStart_7553418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553464 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_7553464 : Nat := 118140960795 + 7553464 * 2 ^ 59
def prefixEnd_7553464 : Nat := 4983230072969 + 3 ^ 40 * 7553464 * 2
def baseEnd_7553464 : Nat := 3878557638432740271062257

theorem tailTrace_7553464 : CollatzResearch.WordTrace tailWord_7553464 prefixEnd_7553464 3878557638432740271062257 := by
  unfold tailWord_7553464
  simp only [CollatzResearch.WordTrace]
  refine ⟨137748732553548715895929723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183664976738064954527906297 137748732553548715895929723)
  ·
    refine ⟨206623098830323073843894585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137748732553548715895929723 206623098830323073843894585)
    ·
      refine ⟨154967324122742305382920939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206623098830323073843894585 154967324122742305382920939)
      ·
        refine ⟨232450986184113458074381409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154967324122742305382920939 232450986184113458074381409)
        ·
          refine ⟨174338239638085093555786057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232450986184113458074381409 174338239638085093555786057)
          ·
            refine ⟨130753679728563820166839543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174338239638085093555786057 130753679728563820166839543)
            ·
              refine ⟨196130519592845730250259315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130753679728563820166839543 196130519592845730250259315)
              ·
                refine ⟨294195779389268595375388973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196130519592845730250259315 294195779389268595375388973)
                ·
                  refine ⟨110323417270975723265770865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294195779389268595375388973 110323417270975723265770865)
                  ·
                    refine ⟨82742562953231792449328149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110323417270975723265770865 82742562953231792449328149)
                    ·
                      refine ⟨3878557638432740271062257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82742562953231792449328149 3878557638432740271062257)
                      ·
                        rfl

theorem cell23_7553464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_7553464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553464 prefixEnd_7553464 := by exact prefixLift 7553464
  have htrace : WordTrace (prefixWord ++ tailWord_7553464) baseStart_7553464 baseEnd_7553464 := by
    simpa [prefixWord, tailWord_7553464, baseEnd_7553464] using wordTrace_append hprefix tailTrace_7553464
  have hstable : (prefixWord ++ tailWord_7553464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553464).length < 2 ^ (prefixWord ++ tailWord_7553464).sum := by decide
  have hdescent : baseEnd_7553464 < baseStart_7553464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553521 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 1, 6]
def baseStart_7553521 : Nat := 118140960795 + 7553521 * 2 ^ 59
def prefixEnd_7553521 : Nat := 4983230072969 + 3 ^ 40 * 7553521 * 2
def baseEnd_7553521 : Nat := 1292862302276682182683165

theorem tailTrace_7553521 : CollatzResearch.WordTrace tailWord_7553521 prefixEnd_7553521 1292862302276682182683165 := by
  unfold tailWord_7553521
  simp only [CollatzResearch.WordTrace]
  refine ⟨275499544067890930526684417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183666362711927287017789611 275499544067890930526684417)
  ·
    refine ⟨206624658050918197895013313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 275499544067890930526684417 206624658050918197895013313)
    ·
      refine ⟨154968493538188648421259985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206624658050918197895013313 154968493538188648421259985)
      ·
        refine ⟨116226370153641486315944989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154968493538188648421259985 116226370153641486315944989)
        ·
          refine ⟨43584888807615557368479371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116226370153641486315944989 43584888807615557368479371)
          ·
            refine ⟨65377333211423336052719057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43584888807615557368479371 65377333211423336052719057)
            ·
              refine ⟨49032999908567502039539293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65377333211423336052719057 49032999908567502039539293)
              ·
                refine ⟨18387374965712813264827235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49032999908567502039539293 18387374965712813264827235)
                ·
                  refine ⟨27581062448569219897240853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18387374965712813264827235 27581062448569219897240853)
                  ·
                    refine ⟨1292862302276682182683165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27581062448569219897240853 1292862302276682182683165)
                    ·
                      rfl

theorem cell23_7553521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_7553521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553521 prefixEnd_7553521 := by exact prefixLift 7553521
  have htrace : WordTrace (prefixWord ++ tailWord_7553521) baseStart_7553521 baseEnd_7553521 := by
    simpa [prefixWord, tailWord_7553521, baseEnd_7553521] using wordTrace_append hprefix tailTrace_7553521
  have hstable : (prefixWord ++ tailWord_7553521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553521).length < 2 ^ (prefixWord ++ tailWord_7553521).sum := by decide
  have hdescent : baseEnd_7553521 < baseStart_7553521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553525 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7553525 : Nat := 118140960795 + 7553525 * 2 ^ 59
def prefixEnd_7553525 : Nat := 4983230072969 + 3 ^ 40 * 7553525 * 2
def baseEnd_7553525 : Nat := 1292862986917554844133159

theorem tailTrace_7553525 : CollatzResearch.WordTrace tailWord_7553525 prefixEnd_7553525 1292862986917554844133159 := by
  unfold tailWord_7553525
  simp only [CollatzResearch.WordTrace]
  refine ⟨275499689959876439209830029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183666459973250959473220019 275499689959876439209830029)
  ·
    refine ⟨103312383734953664703686261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275499689959876439209830029 103312383734953664703686261)
    ·
      refine ⟨9685535975151906065970587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103312383734953664703686261 9685535975151906065970587)
      ·
        refine ⟨14528303962727859098955881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685535975151906065970587 14528303962727859098955881)
        ·
          refine ⟨10896227972045894324216911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14528303962727859098955881 10896227972045894324216911)
          ·
            refine ⟨16344341958068841486325367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10896227972045894324216911 16344341958068841486325367)
            ·
              refine ⟨24516512937103262229488051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16344341958068841486325367 24516512937103262229488051)
              ·
                refine ⟨36774769405654893344232077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24516512937103262229488051 36774769405654893344232077)
                ·
                  refine ⟨13790538527120585004087029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36774769405654893344232077 13790538527120585004087029)
                  ·
                    refine ⟨1292862986917554844133159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13790538527120585004087029 1292862986917554844133159)
                    ·
                      rfl

theorem cell23_7553525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7553525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553525 prefixEnd_7553525 := by exact prefixLift 7553525
  have htrace : WordTrace (prefixWord ++ tailWord_7553525) baseStart_7553525 baseEnd_7553525 := by
    simpa [prefixWord, tailWord_7553525, baseEnd_7553525] using wordTrace_append hprefix tailTrace_7553525
  have hstable : (prefixWord ++ tailWord_7553525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553525).length < 2 ^ (prefixWord ++ tailWord_7553525).sum := by decide
  have hdescent : baseEnd_7553525 < baseStart_7553525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553541 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_7553541 : Nat := 118140960795 + 7553541 * 2 ^ 59
def prefixEnd_7553541 : Nat := 4983230072969 + 3 ^ 40 * 7553541 * 2
def baseEnd_7553541 : Nat := 3878597176443136469799403

theorem tailTrace_7553541 : CollatzResearch.WordTrace tailWord_7553541 prefixEnd_7553541 3878597176443136469799403 := by
  unfold tailWord_7553541
  simp only [CollatzResearch.WordTrace]
  refine ⟨275500273527818473942412477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183666849018545649294941651 275500273527818473942412477)
  ·
    refine ⟨103312602572931927728404679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 275500273527818473942412477 103312602572931927728404679)
    ·
      refine ⟨154968903859397891592607019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103312602572931927728404679 154968903859397891592607019)
      ·
        refine ⟨232453355789096837388910529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154968903859397891592607019 232453355789096837388910529)
        ·
          refine ⟨174340016841822628041682897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232453355789096837388910529 174340016841822628041682897)
          ·
            refine ⟨130755012631366971031262173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174340016841822628041682897 130755012631366971031262173)
            ·
              refine ⟨49033129736762614136723315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130755012631366971031262173 49033129736762614136723315)
              ·
                refine ⟨73549694605143921205084973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49033129736762614136723315 73549694605143921205084973)
                ·
                  refine ⟨27581135476928970451906865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73549694605143921205084973 27581135476928970451906865)
                  ·
                    refine ⟨20685851607696727838930149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27581135476928970451906865 20685851607696727838930149)
                    ·
                      refine ⟨3878597176443136469799403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20685851607696727838930149 3878597176443136469799403)
                      ·
                        rfl

theorem cell23_7553541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_7553541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553541 prefixEnd_7553541 := by exact prefixLift 7553541
  have htrace : WordTrace (prefixWord ++ tailWord_7553541) baseStart_7553541 baseEnd_7553541 := by
    simpa [prefixWord, tailWord_7553541, baseEnd_7553541] using wordTrace_append hprefix tailTrace_7553541
  have hstable : (prefixWord ++ tailWord_7553541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553541).length < 2 ^ (prefixWord ++ tailWord_7553541).sum := by decide
  have hdescent : baseEnd_7553541 < baseStart_7553541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553548 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_7553548 : Nat := 118140960795 + 7553548 * 2 ^ 59
def prefixEnd_7553548 : Nat := 4983230072969 + 3 ^ 40 * 7553548 * 2
def baseEnd_7553548 : Nat := 3878600770807717942411871

theorem tailTrace_7553548 : CollatzResearch.WordTrace tailWord_7553548 prefixEnd_7553548 3878600770807717942411871 := by
  unfold tailWord_7553548
  simp only [CollatzResearch.WordTrace]
  refine ⟨137750264419396557068958649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183667019225862076091944865 137750264419396557068958649)
  ·
    refine ⟨103312698314547417801718987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137750264419396557068958649 103312698314547417801718987)
    ·
      refine ⟨154969047471821126702578481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103312698314547417801718987 154969047471821126702578481)
      ·
        refine ⟨116226785603865845026933861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154969047471821126702578481 116226785603865845026933861)
        ·
          refine ⟨21792522300724845942550099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116226785603865845026933861 21792522300724845942550099)
          ·
            refine ⟨32688783451087268913825149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21792522300724845942550099 32688783451087268913825149)
            ·
              refine ⟨12258293794157725842684431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32688783451087268913825149 12258293794157725842684431)
              ·
                refine ⟨18387440691236588764026647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12258293794157725842684431 18387440691236588764026647)
                ·
                  refine ⟨27581161036854883146039971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18387440691236588764026647 27581161036854883146039971)
                  ·
                    refine ⟨41371741555282324719059957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27581161036854883146039971 41371741555282324719059957)
                    ·
                      refine ⟨3878600770807717942411871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41371741555282324719059957 3878600770807717942411871)
                      ·
                        rfl

theorem cell23_7553548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_7553548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553548 prefixEnd_7553548 := by exact prefixLift 7553548
  have htrace : WordTrace (prefixWord ++ tailWord_7553548) baseStart_7553548 baseEnd_7553548 := by
    simpa [prefixWord, tailWord_7553548, baseEnd_7553548] using wordTrace_append hprefix tailTrace_7553548
  have hstable : (prefixWord ++ tailWord_7553548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553548).length < 2 ^ (prefixWord ++ tailWord_7553548).sum := by decide
  have hdescent : baseEnd_7553548 < baseStart_7553548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7553549 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7553549 : Nat := 118140960795 + 7553549 * 2 ^ 59
def prefixEnd_7553549 : Nat := 4983230072969 + 3 ^ 40 * 7553549 * 2
def baseEnd_7553549 : Nat := 3878601284288372438499367

theorem tailTrace_7553549 : CollatzResearch.WordTrace tailWord_7553549 prefixEnd_7553549 3878601284288372438499367 := by
  unfold tailWord_7553549
  simp only [CollatzResearch.WordTrace]
  refine ⟨275500565311789491308703701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183667043541192994205802467 275500565311789491308703701)
  ·
    refine ⟨6457044499495066202547743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 275500565311789491308703701 6457044499495066202547743)
    ·
      refine ⟨9685566749242599303821615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6457044499495066202547743 9685566749242599303821615)
      ·
        refine ⟨14528350123863898955732423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685566749242599303821615 14528350123863898955732423)
        ·
          refine ⟨21792525185795848433598635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14528350123863898955732423 21792525185795848433598635)
          ·
            refine ⟨32688787778693772650397953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21792525185795848433598635 32688787778693772650397953)
            ·
              refine ⟨24516590834020329487798465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32688787778693772650397953 24516590834020329487798465)
              ·
                refine ⟨18387443125515247115848849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24516590834020329487798465 18387443125515247115848849)
                ·
                  refine ⟨13790582344136435336886637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18387443125515247115848849 13790582344136435336886637)
                  ·
                    refine ⟨5171468379051163251332489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13790582344136435336886637 5171468379051163251332489)
                    ·
                      refine ⟨3878601284288372438499367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5171468379051163251332489 3878601284288372438499367)
                      ·
                        rfl

theorem cell23_7553549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7553549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7553549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7553549 prefixEnd_7553549 := by exact prefixLift 7553549
  have htrace : WordTrace (prefixWord ++ tailWord_7553549) baseStart_7553549 baseEnd_7553549 := by
    simpa [prefixWord, tailWord_7553549, baseEnd_7553549] using wordTrace_append hprefix tailTrace_7553549
  have hstable : (prefixWord ++ tailWord_7553549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7553549).length < 2 ^ (prefixWord ++ tailWord_7553549).sum := by decide
  have hdescent : baseEnd_7553549 < baseStart_7553549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7553549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
